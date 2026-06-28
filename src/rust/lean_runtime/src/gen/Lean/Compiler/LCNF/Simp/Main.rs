// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Main
// Imports: Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.Used Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.ConstantFold
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::l_Lean_Name_mkStr1;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Alt_getParams, l_Lean_Compiler_LCNF_Cases_extractAlt_x21,
    l_Lean_Compiler_LCNF_Code_isFun___redArg, l_Lean_Compiler_LCNF_Code_isReturnOf___redArg,
    l_Lean_Compiler_LCNF_Decl_getArity___redArg, l_Lean_Compiler_LCNF_hasLocalInst___redArg,
    l_Lean_Compiler_LCNF_instBEqLetDecl_beq, l_Lean_Compiler_LCNF_instBEqLetValue_beq,
    l_Lean_Compiler_LCNF_instInhabitedAlt_default__1,
    l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
    l_Lean_Compiler_LCNF_instInhabitedParam_default,
};
use crate::r#gen::Lean::Compiler::LCNF::Bind::{
    l_Lean_Compiler_LCNF_CompilerM_codeBind, l_Lean_Compiler_LCNF_FunDecl_etaExpand,
    l_Lean_Compiler_LCNF_isEtaExpandCandidateCore, l_Lean_Compiler_LCNF_mkNewParams,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg,
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg,
    l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg, l_Lean_Compiler_LCNF_Phase_toPurity,
    l_Lean_Compiler_LCNF_eraseCode___redArg, l_Lean_Compiler_LCNF_eraseParam___redArg,
    l_Lean_Compiler_LCNF_eraseParams___redArg, l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg,
    l_Lean_Compiler_LCNF_getPhase___redArg, l_Lean_Compiler_LCNF_mkAuxParam,
    l_Lean_Compiler_LCNF_mkReturnErased, l_Lean_Compiler_LCNF_normFVarImp___redArg,
    l_Lean_Compiler_LCNF_normFunDeclImp, l_Lean_Compiler_LCNF_replaceExprFVars___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    l_Lean_Compiler_LCNF_Code_inferType, l_Lean_Compiler_LCNF_inferAppType,
    l_Lean_Compiler_LCNF_mkAuxFunDecl, l_Lean_Compiler_LCNF_mkAuxJpDecl,
    l_Lean_Compiler_LCNF_mkAuxLetDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::l_Lean_Compiler_LCNF_Code_internalize;
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::l_Lean_Compiler_LCNF_getDeclAt_x3f;
use crate::r#gen::Lean::Compiler::LCNF::Simp::ConstantFold::{
    initialize_Lean_Compiler_LCNF_Simp_ConstantFold,
    l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants,
    runtime_initialize_Lean_Compiler_LCNF_Simp_ConstantFold,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::DefaultAlt::{
    initialize_Lean_Compiler_LCNF_Simp_DefaultAlt, l_Lean_Compiler_LCNF_Simp_addDefaultAlt,
    runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::DiscrM::{
    l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx,
    l_Lean_Compiler_LCNF_Simp_CtorInfo_getName, l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::InlineCandidate::{
    initialize_Lean_Compiler_LCNF_Simp_InlineCandidate,
    l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity,
    l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f,
    runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::InlineProj::{
    initialize_Lean_Compiler_LCNF_Simp_InlineProj, l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f,
    runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpM::{
    l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth,
    l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check,
    l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg, l_Lean_Compiler_LCNF_Simp_betaReduce,
    l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg,
    l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg, l_Lean_Compiler_LCNF_Simp_incVisited___redArg,
    l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg,
    l_Lean_Compiler_LCNF_Simp_markSimplified___redArg,
    l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg,
    l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpValue::{
    initialize_Lean_Compiler_LCNF_Simp_SimpValue, l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::Used::{
    initialize_Lean_Compiler_LCNF_Simp_Used, l_Lean_Compiler_LCNF_Simp_attachCodeDecls,
    l_Lean_Compiler_LCNF_Simp_isUsed___redArg, l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg,
    l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg, l_Lean_Compiler_LCNF_Simp_markUsedFunDecl,
    l_Lean_Compiler_LCNF_Simp_markUsedLetDecl, runtime_initialize_Lean_Compiler_LCNF_Simp_Used,
};
use crate::r#gen::Lean::Compiler::LCNF::Types::{
    l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg, l_Lean_Expr_isErased,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_checkSystem;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_headBeta, l_Lean_Expr_isForall, l_Lean_instBEqFVarId_beq,
    l_Lean_instHashableFVarId_hash,
};
use crate::r#gen::Lean::ReducibilityAttrs::l_Lean_isImplicitReducibleCore;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
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
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mod, lean_nat_mul,
    lean_nat_sub, lean_panic_fn_borrowed, lean_uint64_of_nat, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
static mut l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value:
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
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 102, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value)
            as *mut crate::leanh::LeanObject,
        12317437071847932413 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value:
    crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 3,
    m_capacity: 3,
    m_length: 2,
    m_data: [95, 120, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        7699194985028780469 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__2_value: crate::leanh::LeanStringObject<34> =
    crate::leanh::LeanStringObject {
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__1_value: crate::leanh::LeanStringObject<68> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 68,
        m_capacity: 68,
        m_length: 67,
        m_data: [
            95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105,
            108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97,
            110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 117, 112, 100,
            97, 116, 101, 70, 117, 110, 73, 109, 112, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__0_value: crate::leanh::LeanStringObject<25> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 25,
        m_capacity: 25,
        m_length: 24,
        m_data: [
            76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46,
            66, 97, 115, 105, 99, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [95, 106, 112, 0],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        12958253247387092313 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__4_value: crate::leanh::LeanStringObject<10> =
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
        m_data: [76, 67, 78, 70, 32, 115, 105, 109, 112, 0],
    };
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3712_: u8 = 0;
    let mut v___x_3713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3712_ = 0;
    v___x_3713_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_3712_);
    return v___x_3713_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(
    mut v_c_3714_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_c_3714_) {
                0 => {
                    v_k_3715_ = crate::leanh::lean_ctor_get(v_c_3714_, 1);
                    v_c_3714_ = v_k_3715_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_k_3717_ = crate::leanh::lean_ctor_get(v_c_3714_, 1);
                    v_c_3714_ = v_k_3717_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_3719_ = crate::leanh::lean_ctor_get(v_c_3714_, 0);
                    v_alts_3720_ = crate::leanh::lean_ctor_get(v_cases_3719_, 3);
                    v___x_3721_ = lean_array_get_size(v_alts_3720_);
                    v___x_3722_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3723_ = lean_nat_dec_eq(v___x_3721_, v___x_3722_);
                    if v___x_3723_ == 0 {
                        return v___x_3723_;
                    } else {
                        v___x_3724_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
                        v___x_3725_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_3726_ =
                            lean_array_get_borrowed(v___x_3724_, v_alts_3720_, v___x_3725_);
                        match crate::leanh::lean_obj_tag(v___x_3726_) {
                            0 => {
                                v_code_3727_ = crate::leanh::lean_ctor_get(v___x_3726_, 2);
                                v_c_3714_ = v_code_3727_;
                                state = 0;
                                continue;
                            }
                            1 => {
                                v_code_3729_ = crate::leanh::lean_ctor_get(v___x_3726_, 1);
                                v_c_3714_ = v_code_3729_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                v_code_3731_ = crate::leanh::lean_ctor_get(v___x_3726_, 0);
                                v_c_3714_ = v_code_3731_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                }
                5 => {
                    v___x_3733_ = 1;
                    return v___x_3733_;
                }
                _ => {
                    v___x_3734_ = 0;
                    return v___x_3734_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(
    mut v_c_3735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3736_: u8 = 0;
    let mut v_r_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3736_ =
        l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(
            v_c_3735_,
        );
    crate::leanh::lean_dec_ref(v_c_3735_);
    v_r_3737_ = crate::leanh::lean_box((v_res_3736_) as usize);
    return v_r_3737_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(
    mut v_c_3738_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3739_: u8 = 0;
    v___x_3739_ =
        l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(
            v_c_3738_,
        );
    return v___x_3739_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(
    mut v_c_3740_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3741_: u8 = 0;
    let mut v_r_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3741_ =
        l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(
            v_c_3740_,
        );
    crate::leanh::lean_dec_ref(v_c_3740_);
    v_r_3742_ = crate::leanh::lean_box((v_res_3741_) as usize);
    return v_r_3742_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(
    mut v_a_3743_: *mut crate::leanh::LeanObject,
    mut v_x_3744_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3745_: u8 = 0;
    let mut v_key_3746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3744_) == 0 {
                    v___x_3745_ = 0;
                    return v___x_3745_;
                } else {
                    v_key_3746_ = crate::leanh::lean_ctor_get(v_x_3744_, 0);
                    v_tail_3747_ = crate::leanh::lean_ctor_get(v_x_3744_, 2);
                    v___x_3748_ = l_Lean_instBEqFVarId_beq(v_key_3746_, v_a_3743_);
                    if v___x_3748_ == 0 {
                        v_x_3744_ = v_tail_3747_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3748_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg___boxed(
    mut v_a_3750_: *mut crate::leanh::LeanObject,
    mut v_x_3751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3752_: u8 = 0;
    let mut v_r_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_3750_, v_x_3751_);
    crate::leanh::lean_dec(v_x_3751_);
    crate::leanh::lean_dec(v_a_3750_);
    v_r_3753_ = crate::leanh::lean_box((v_res_3752_) as usize);
    return v_r_3753_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_x_3754_: *mut crate::leanh::LeanObject,
    mut v_x_3755_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v___x_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: u64 = 0;
    let mut v___x_3764_: u64 = 0;
    let mut v___x_3765_: u64 = 0;
    let mut v_fold_3766_: u64 = 0;
    let mut v___x_3767_: u64 = 0;
    let mut v___x_3768_: u64 = 0;
    let mut v___x_3769_: u64 = 0;
    let mut v___x_3770_: usize = 0;
    let mut v___x_3771_: usize = 0;
    let mut v___x_3772_: usize = 0;
    let mut v___x_3773_: usize = 0;
    let mut v___x_3774_: usize = 0;
    let mut v___x_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3755_) == 0 {
                    return v_x_3754_;
                } else {
                    v_key_3756_ = crate::leanh::lean_ctor_get(v_x_3755_, 0);
                    v_value_3757_ = crate::leanh::lean_ctor_get(v_x_3755_, 1);
                    v_tail_3758_ = crate::leanh::lean_ctor_get(v_x_3755_, 2);
                    v_isSharedCheck_3781_ = (!crate::leanh::lean_is_exclusive(v_x_3755_)) as u8;
                    if v_isSharedCheck_3781_ == 0 {
                        v___x_3760_ = v_x_3755_;
                        v_isShared_3761_ = v_isSharedCheck_3781_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3758_);
                        crate::leanh::lean_inc(v_value_3757_);
                        crate::leanh::lean_inc(v_key_3756_);
                        crate::leanh::lean_dec(v_x_3755_);
                        v___x_3760_ = crate::leanh::lean_box(0);
                        v_isShared_3761_ = v_isSharedCheck_3781_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3762_ = lean_array_get_size(v_x_3754_);
                v___x_3763_ = l_Lean_instHashableFVarId_hash(v_key_3756_);
                v___x_3764_ = 32u64;
                v___x_3765_ = lean_uint64_shift_right(v___x_3763_, v___x_3764_);
                v_fold_3766_ = lean_uint64_xor(v___x_3763_, v___x_3765_);
                v___x_3767_ = 16u64;
                v___x_3768_ = lean_uint64_shift_right(v_fold_3766_, v___x_3767_);
                v___x_3769_ = lean_uint64_xor(v_fold_3766_, v___x_3768_);
                v___x_3770_ = lean_uint64_to_usize(v___x_3769_);
                v___x_3771_ = lean_usize_of_nat(v___x_3762_);
                v___x_3772_ = 1usize;
                v___x_3773_ = lean_usize_sub(v___x_3771_, v___x_3772_);
                v___x_3774_ = lean_usize_land(v___x_3770_, v___x_3773_);
                v___x_3775_ = lean_array_uget_borrowed(v_x_3754_, v___x_3774_);
                crate::leanh::lean_inc(v___x_3775_);
                if v_isShared_3761_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3760_, 2, v___x_3775_);
                    v___x_3777_ = v___x_3760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_key_3756_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_value_3757_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3780_, 2, v___x_3775_);
                    v___x_3777_ = v_reuseFailAlloc_3780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3778_ = lean_array_uset(v_x_3754_, v___x_3774_, v___x_3777_);
                v_x_3754_ = v___x_3778_;
                v_x_3755_ = v_tail_3758_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(
    mut v_i_3782_: *mut crate::leanh::LeanObject,
    mut v_source_3783_: *mut crate::leanh::LeanObject,
    mut v_target_3784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v_es_3787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3785_ = lean_array_get_size(v_source_3783_);
                v___x_3786_ = lean_nat_dec_lt(v_i_3782_, v___x_3785_);
                if v___x_3786_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3783_);
                    crate::leanh::lean_dec(v_i_3782_);
                    return v_target_3784_;
                } else {
                    v_es_3787_ = lean_array_fget(v_source_3783_, v_i_3782_);
                    v___x_3788_ = crate::leanh::lean_box(0);
                    v_source_3789_ = lean_array_fset(v_source_3783_, v_i_3782_, v___x_3788_);
                    v_target_3790_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3784_, v_es_3787_);
                    v___x_3791_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3792_ = lean_nat_add(v_i_3782_, v___x_3791_);
                    crate::leanh::lean_dec(v_i_3782_);
                    v_i_3782_ = v___x_3792_;
                    v_source_3783_ = v_source_3789_;
                    v_target_3784_ = v_target_3790_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(
    mut v_data_3794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3795_ = lean_array_get_size(v_data_3794_);
    v___x_3796_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3797_ = lean_nat_mul(v___x_3795_, v___x_3796_);
    v___x_3798_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3799_ = crate::leanh::lean_box(0);
    v___x_3800_ = lean_mk_array(v_nbuckets_3797_, v___x_3799_);
    v___x_3801_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v___x_3798_, v_data_3794_, v___x_3800_);
    return v___x_3801_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(
    mut v_a_3802_: *mut crate::leanh::LeanObject,
    mut v_b_3803_: *mut crate::leanh::LeanObject,
    mut v_x_3804_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3804_) == 0 {
                    crate::leanh::lean_dec(v_b_3803_);
                    crate::leanh::lean_dec(v_a_3802_);
                    return v_x_3804_;
                } else {
                    v_key_3805_ = crate::leanh::lean_ctor_get(v_x_3804_, 0);
                    v_value_3806_ = crate::leanh::lean_ctor_get(v_x_3804_, 1);
                    v_tail_3807_ = crate::leanh::lean_ctor_get(v_x_3804_, 2);
                    v_isSharedCheck_3819_ = (!crate::leanh::lean_is_exclusive(v_x_3804_)) as u8;
                    if v_isSharedCheck_3819_ == 0 {
                        v___x_3809_ = v_x_3804_;
                        v_isShared_3810_ = v_isSharedCheck_3819_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3807_);
                        crate::leanh::lean_inc(v_value_3806_);
                        crate::leanh::lean_inc(v_key_3805_);
                        crate::leanh::lean_dec(v_x_3804_);
                        v___x_3809_ = crate::leanh::lean_box(0);
                        v_isShared_3810_ = v_isSharedCheck_3819_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3811_ = l_Lean_instBEqFVarId_beq(v_key_3805_, v_a_3802_);
                if v___x_3811_ == 0 {
                    v___x_3812_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_3802_, v_b_3803_, v_tail_3807_);
                    if v_isShared_3810_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3809_, 2, v___x_3812_);
                        v___x_3814_ = v___x_3809_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3815_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_key_3805_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_value_3806_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3815_, 2, v___x_3812_);
                        v___x_3814_ = v_reuseFailAlloc_3815_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3806_);
                    crate::leanh::lean_dec(v_key_3805_);
                    if v_isShared_3810_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3809_, 1, v_b_3803_);
                        crate::leanh::lean_ctor_set(v___x_3809_, 0, v_a_3802_);
                        v___x_3817_ = v___x_3809_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3818_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3802_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_b_3803_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_tail_3807_);
                        v___x_3817_ = v_reuseFailAlloc_3818_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3814_;
            }
            3 => {
                return v___x_3817_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(
    mut v_m_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
    mut v_b_3822_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: u64 = 0;
    let mut v___x_3830_: u64 = 0;
    let mut v___x_3831_: u64 = 0;
    let mut v_fold_3832_: u64 = 0;
    let mut v___x_3833_: u64 = 0;
    let mut v___x_3834_: u64 = 0;
    let mut v___x_3835_: u64 = 0;
    let mut v___x_3836_: usize = 0;
    let mut v___x_3837_: usize = 0;
    let mut v___x_3838_: usize = 0;
    let mut v___x_3839_: usize = 0;
    let mut v___x_3840_: usize = 0;
    let mut v_bkt_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u8 = 0;
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: u8 = 0;
    let mut v_val_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3823_ = crate::leanh::lean_ctor_get(v_m_3820_, 0);
                v_buckets_3824_ = crate::leanh::lean_ctor_get(v_m_3820_, 1);
                v_isSharedCheck_3867_ = (!crate::leanh::lean_is_exclusive(v_m_3820_)) as u8;
                if v_isSharedCheck_3867_ == 0 {
                    v___x_3826_ = v_m_3820_;
                    v_isShared_3827_ = v_isSharedCheck_3867_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3824_);
                    crate::leanh::lean_inc(v_size_3823_);
                    crate::leanh::lean_dec(v_m_3820_);
                    v___x_3826_ = crate::leanh::lean_box(0);
                    v_isShared_3827_ = v_isSharedCheck_3867_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3828_ = lean_array_get_size(v_buckets_3824_);
                v___x_3829_ = l_Lean_instHashableFVarId_hash(v_a_3821_);
                v___x_3830_ = 32u64;
                v___x_3831_ = lean_uint64_shift_right(v___x_3829_, v___x_3830_);
                v_fold_3832_ = lean_uint64_xor(v___x_3829_, v___x_3831_);
                v___x_3833_ = 16u64;
                v___x_3834_ = lean_uint64_shift_right(v_fold_3832_, v___x_3833_);
                v___x_3835_ = lean_uint64_xor(v_fold_3832_, v___x_3834_);
                v___x_3836_ = lean_uint64_to_usize(v___x_3835_);
                v___x_3837_ = lean_usize_of_nat(v___x_3828_);
                v___x_3838_ = 1usize;
                v___x_3839_ = lean_usize_sub(v___x_3837_, v___x_3838_);
                v___x_3840_ = lean_usize_land(v___x_3836_, v___x_3839_);
                v_bkt_3841_ = lean_array_uget_borrowed(v_buckets_3824_, v___x_3840_);
                v___x_3842_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_3821_, v_bkt_3841_);
                if v___x_3842_ == 0 {
                    v___x_3843_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3844_ = lean_nat_add(v_size_3823_, v___x_3843_);
                    crate::leanh::lean_dec(v_size_3823_);
                    crate::leanh::lean_inc(v_bkt_3841_);
                    v___x_3845_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3845_, 0, v_a_3821_);
                    crate::leanh::lean_ctor_set(v___x_3845_, 1, v_b_3822_);
                    crate::leanh::lean_ctor_set(v___x_3845_, 2, v_bkt_3841_);
                    v_buckets_x27_3846_ =
                        lean_array_uset(v_buckets_3824_, v___x_3840_, v___x_3845_);
                    v___x_3847_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3848_ = lean_nat_mul(v_size_x27_3844_, v___x_3847_);
                    v___x_3849_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3850_ = lean_nat_div(v___x_3848_, v___x_3849_);
                    crate::leanh::lean_dec(v___x_3848_);
                    v___x_3851_ = lean_array_get_size(v_buckets_x27_3846_);
                    v___x_3852_ = lean_nat_dec_le(v___x_3850_, v___x_3851_);
                    crate::leanh::lean_dec(v___x_3850_);
                    if v___x_3852_ == 0 {
                        v_val_3853_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_buckets_x27_3846_);
                        if v_isShared_3827_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3826_, 1, v_val_3853_);
                            crate::leanh::lean_ctor_set(v___x_3826_, 0, v_size_x27_3844_);
                            v___x_3855_ = v___x_3826_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3856_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3856_,
                                0,
                                v_size_x27_3844_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_val_3853_);
                            v___x_3855_ = v_reuseFailAlloc_3856_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3827_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3826_, 1, v_buckets_x27_3846_);
                            crate::leanh::lean_ctor_set(v___x_3826_, 0, v_size_x27_3844_);
                            v___x_3858_ = v___x_3826_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3859_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3859_,
                                0,
                                v_size_x27_3844_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3859_,
                                1,
                                v_buckets_x27_3846_,
                            );
                            v___x_3858_ = v_reuseFailAlloc_3859_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3841_);
                    v___x_3860_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3861_ =
                        lean_array_uset(v_buckets_3824_, v___x_3840_, v___x_3860_);
                    v___x_3862_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_3821_, v_b_3822_, v_bkt_3841_);
                    v___x_3863_ = lean_array_uset(v_buckets_x27_3861_, v___x_3840_, v___x_3862_);
                    if v_isShared_3827_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3826_, 1, v___x_3863_);
                        v___x_3865_ = v___x_3826_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_size_3823_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3866_, 1, v___x_3863_);
                        v___x_3865_ = v_reuseFailAlloc_3866_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3855_;
            }
            3 => {
                return v___x_3858_;
            }
            4 => {
                return v___x_3865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(
    mut v_as_3868_: *mut crate::leanh::LeanObject,
    mut v_sz_3869_: usize,
    mut v_i_3870_: usize,
    mut v_b_3871_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3873_: u8 = 0;
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v_array_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3890_: u8 = 0;
    let mut v_a_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: usize = 0;
    let mut v___x_3902_: usize = 0;
    let mut v_reuseFailAlloc_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_unused_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3873_ = lean_usize_dec_lt(v_i_3870_, v_sz_3869_);
                if v___x_3873_ == 0 {
                    v___x_3874_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3874_, 0, v_b_3871_);
                    return v___x_3874_;
                } else {
                    v_snd_3875_ = crate::leanh::lean_ctor_get(v_b_3871_, 1);
                    v_fst_3876_ = crate::leanh::lean_ctor_get(v_b_3871_, 0);
                    v_isSharedCheck_3910_ = (!crate::leanh::lean_is_exclusive(v_b_3871_)) as u8;
                    if v_isSharedCheck_3910_ == 0 {
                        v___x_3878_ = v_b_3871_;
                        v_isShared_3879_ = v_isSharedCheck_3910_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3875_);
                        crate::leanh::lean_inc(v_fst_3876_);
                        crate::leanh::lean_dec(v_b_3871_);
                        v___x_3878_ = crate::leanh::lean_box(0);
                        v_isShared_3879_ = v_isSharedCheck_3910_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_3880_ = crate::leanh::lean_ctor_get(v_snd_3875_, 0);
                v_start_3881_ = crate::leanh::lean_ctor_get(v_snd_3875_, 1);
                v_stop_3882_ = crate::leanh::lean_ctor_get(v_snd_3875_, 2);
                v___x_3883_ = lean_nat_dec_lt(v_start_3881_, v_stop_3882_);
                if v___x_3883_ == 0 {
                    if v_isShared_3879_ == 0 {
                        v___x_3885_ = v___x_3878_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3887_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_fst_3876_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_snd_3875_);
                        v___x_3885_ = v_reuseFailAlloc_3887_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_3882_);
                    crate::leanh::lean_inc(v_start_3881_);
                    crate::leanh::lean_inc_ref(v_array_3880_);
                    v_isSharedCheck_3906_ = (!crate::leanh::lean_is_exclusive(v_snd_3875_)) as u8;
                    if v_isSharedCheck_3906_ == 0 {
                        v_unused_3907_ = crate::leanh::lean_ctor_get(v_snd_3875_, 2);
                        crate::leanh::lean_dec(v_unused_3907_);
                        v_unused_3908_ = crate::leanh::lean_ctor_get(v_snd_3875_, 1);
                        crate::leanh::lean_dec(v_unused_3908_);
                        v_unused_3909_ = crate::leanh::lean_ctor_get(v_snd_3875_, 0);
                        crate::leanh::lean_dec(v_unused_3909_);
                        v___x_3889_ = v_snd_3875_;
                        v_isShared_3890_ = v_isSharedCheck_3906_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_3875_);
                        v___x_3889_ = crate::leanh::lean_box(0);
                        v_isShared_3890_ = v_isSharedCheck_3906_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3886_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3886_, 0, v___x_3885_);
                return v___x_3886_;
            }
            3 => {
                v_a_3891_ = lean_array_uget_borrowed(v_as_3868_, v_i_3870_);
                v_fvarId_3892_ = crate::leanh::lean_ctor_get(v_a_3891_, 0);
                v___x_3893_ = lean_array_fget(v_array_3880_, v_start_3881_);
                v___x_3894_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3895_ = lean_nat_add(v_start_3881_, v___x_3894_);
                crate::leanh::lean_dec(v_start_3881_);
                if v_isShared_3890_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3889_, 1, v___x_3895_);
                    v___x_3897_ = v___x_3889_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_array_3880_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 1, v___x_3895_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_stop_3882_);
                    v___x_3897_ = v_reuseFailAlloc_3905_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc(v_fvarId_3892_);
                v___x_3898_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_3876_, v_fvarId_3892_, v___x_3893_);
                if v_isShared_3879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3878_, 1, v___x_3897_);
                    crate::leanh::lean_ctor_set(v___x_3878_, 0, v___x_3898_);
                    v___x_3900_ = v___x_3878_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3898_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3897_);
                    v___x_3900_ = v_reuseFailAlloc_3904_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3901_ = 1usize;
                v___x_3902_ = lean_usize_add(v_i_3870_, v___x_3901_);
                v_i_3870_ = v___x_3902_;
                v_b_3871_ = v___x_3900_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg___boxed(
    mut v_as_3911_: *mut crate::leanh::LeanObject,
    mut v_sz_3912_: *mut crate::leanh::LeanObject,
    mut v_i_3913_: *mut crate::leanh::LeanObject,
    mut v_b_3914_: *mut crate::leanh::LeanObject,
    mut v___y_3915_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3916_: usize = 0;
    let mut v_i_boxed_3917_: usize = 0;
    let mut v_res_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3916_ = crate::leanh::lean_unbox_usize(v_sz_3912_);
    crate::leanh::lean_dec(v_sz_3912_);
    v_i_boxed_3917_ = crate::leanh::lean_unbox_usize(v_i_3913_);
    crate::leanh::lean_dec(v_i_3913_);
    v_res_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_3911_, v_sz_boxed_3916_, v_i_boxed_3917_, v_b_3914_);
    crate::leanh::lean_dec_ref(v_as_3911_);
    return v_res_3918_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(
    mut v_a_3919_: *mut crate::leanh::LeanObject,
    mut v_b_3920_: *mut crate::leanh::LeanObject,
    mut v___y_3921_: *mut crate::leanh::LeanObject,
    mut v___y_3922_: *mut crate::leanh::LeanObject,
    mut v___y_3923_: *mut crate::leanh::LeanObject,
    mut v___y_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: u8 = 0;
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v_a_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3926_ = crate::leanh::lean_ctor_get(v_a_3919_, 0);
                v_start_3927_ = crate::leanh::lean_ctor_get(v_a_3919_, 1);
                v_stop_3928_ = crate::leanh::lean_ctor_get(v_a_3919_, 2);
                v_isSharedCheck_3978_ = (!crate::leanh::lean_is_exclusive(v_a_3919_)) as u8;
                if v_isSharedCheck_3978_ == 0 {
                    v___x_3930_ = v_a_3919_;
                    v_isShared_3931_ = v_isSharedCheck_3978_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_3928_);
                    crate::leanh::lean_inc(v_start_3927_);
                    crate::leanh::lean_inc(v_array_3926_);
                    crate::leanh::lean_dec(v_a_3919_);
                    v___x_3930_ = crate::leanh::lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3932_ = lean_nat_dec_lt(v_start_3927_, v_stop_3928_);
                if v___x_3932_ == 0 {
                    crate::leanh::lean_del_object(v___x_3930_);
                    crate::leanh::lean_dec(v_stop_3928_);
                    crate::leanh::lean_dec(v_start_3927_);
                    crate::leanh::lean_dec_ref(v_array_3926_);
                    v___x_3933_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3933_, 0, v_b_3920_);
                    return v___x_3933_;
                } else {
                    v_fst_3934_ = crate::leanh::lean_ctor_get(v_b_3920_, 0);
                    v_snd_3935_ = crate::leanh::lean_ctor_get(v_b_3920_, 1);
                    v_isSharedCheck_3977_ = (!crate::leanh::lean_is_exclusive(v_b_3920_)) as u8;
                    if v_isSharedCheck_3977_ == 0 {
                        v___x_3937_ = v_b_3920_;
                        v_isShared_3938_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3935_);
                        crate::leanh::lean_inc(v_fst_3934_);
                        crate::leanh::lean_dec(v_b_3920_);
                        v___x_3937_ = crate::leanh::lean_box(0);
                        v_isShared_3938_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3939_ = lean_array_fget_borrowed(v_array_3926_, v_start_3927_);
                v_fvarId_3940_ = crate::leanh::lean_ctor_get(v___x_3939_, 0);
                crate::leanh::lean_inc(v_fvarId_3940_);
                v_type_3941_ = crate::leanh::lean_ctor_get(v___x_3939_, 2);
                v___x_3942_ = 0;
                crate::leanh::lean_inc_ref(v_type_3941_);
                v___x_3943_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(
                    v___x_3942_,
                    v_type_3941_,
                    v_fst_3934_,
                    v___x_3932_,
                );
                if crate::leanh::lean_obj_tag(v___x_3943_) == 0 {
                    v_a_3944_ = crate::leanh::lean_ctor_get(v___x_3943_, 0);
                    crate::leanh::lean_inc(v_a_3944_);
                    crate::leanh::lean_dec_ref_known(v___x_3943_, 1);
                    v___x_3945_ = 0;
                    v___x_3946_ = l_Lean_Compiler_LCNF_mkAuxParam(
                        v___x_3942_,
                        v_a_3944_,
                        v___x_3945_,
                        v___y_3921_,
                        v___y_3922_,
                        v___y_3923_,
                        v___y_3924_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3946_) == 0 {
                        v_a_3947_ = crate::leanh::lean_ctor_get(v___x_3946_, 0);
                        crate::leanh::lean_inc(v_a_3947_);
                        crate::leanh::lean_dec_ref_known(v___x_3946_, 1);
                        v_fvarId_3948_ = crate::leanh::lean_ctor_get(v_a_3947_, 0);
                        crate::leanh::lean_inc(v_fvarId_3948_);
                        v___x_3949_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3950_ = lean_nat_add(v_start_3927_, v___x_3949_);
                        crate::leanh::lean_dec(v_start_3927_);
                        if v_isShared_3931_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3930_, 1, v___x_3950_);
                            v___x_3952_ = v___x_3930_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3960_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_array_3926_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3950_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3960_, 2, v_stop_3928_);
                            v___x_3952_ = v_reuseFailAlloc_3960_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_3940_);
                        crate::leanh::lean_del_object(v___x_3937_);
                        crate::leanh::lean_dec(v_snd_3935_);
                        crate::leanh::lean_dec(v_fst_3934_);
                        crate::leanh::lean_del_object(v___x_3930_);
                        crate::leanh::lean_dec(v_stop_3928_);
                        crate::leanh::lean_dec(v_start_3927_);
                        crate::leanh::lean_dec_ref(v_array_3926_);
                        v_a_3961_ = crate::leanh::lean_ctor_get(v___x_3946_, 0);
                        v_isSharedCheck_3968_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3946_)) as u8;
                        if v_isSharedCheck_3968_ == 0 {
                            v___x_3963_ = v___x_3946_;
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3961_);
                            crate::leanh::lean_dec(v___x_3946_);
                            v___x_3963_ = crate::leanh::lean_box(0);
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_3940_);
                    crate::leanh::lean_del_object(v___x_3937_);
                    crate::leanh::lean_dec(v_snd_3935_);
                    crate::leanh::lean_dec(v_fst_3934_);
                    crate::leanh::lean_del_object(v___x_3930_);
                    crate::leanh::lean_dec(v_stop_3928_);
                    crate::leanh::lean_dec(v_start_3927_);
                    crate::leanh::lean_dec_ref(v_array_3926_);
                    v_a_3969_ = crate::leanh::lean_ctor_get(v___x_3943_, 0);
                    v_isSharedCheck_3976_ = (!crate::leanh::lean_is_exclusive(v___x_3943_)) as u8;
                    if v_isSharedCheck_3976_ == 0 {
                        v___x_3971_ = v___x_3943_;
                        v_isShared_3972_ = v_isSharedCheck_3976_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3969_);
                        crate::leanh::lean_dec(v___x_3943_);
                        v___x_3971_ = crate::leanh::lean_box(0);
                        v_isShared_3972_ = v_isSharedCheck_3976_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3953_ = lean_array_push(v_snd_3935_, v_a_3947_);
                v___x_3954_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3954_, 0, v_fvarId_3948_);
                v___x_3955_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_3934_, v_fvarId_3940_, v___x_3954_);
                if v_isShared_3938_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3937_, 1, v___x_3953_);
                    crate::leanh::lean_ctor_set(v___x_3937_, 0, v___x_3955_);
                    v___x_3957_ = v___x_3937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3955_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3959_, 1, v___x_3953_);
                    v___x_3957_ = v_reuseFailAlloc_3959_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_a_3919_ = v___x_3952_;
                v_b_3920_ = v___x_3957_;
                state = 0;
                continue;
            }
            5 => {
                if v_isShared_3964_ == 0 {
                    v___x_3966_ = v___x_3963_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3967_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
                    v___x_3966_ = v_reuseFailAlloc_3967_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3966_;
            }
            7 => {
                if v_isShared_3972_ == 0 {
                    v___x_3974_ = v___x_3971_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
                    v___x_3974_ = v_reuseFailAlloc_3975_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg___boxed(
    mut v_a_3979_: *mut crate::leanh::LeanObject,
    mut v_b_3980_: *mut crate::leanh::LeanObject,
    mut v___y_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_3979_, v_b_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
    crate::leanh::lean_dec(v___y_3984_);
    crate::leanh::lean_dec_ref(v___y_3983_);
    crate::leanh::lean_dec(v___y_3982_);
    crate::leanh::lean_dec_ref(v___y_3981_);
    return v_res_3986_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3987_ = crate::leanh::lean_box(0);
    v___x_3988_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3989_ = lean_mk_array(v___x_3988_, v___x_3987_);
    return v___x_3989_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3990_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0,
    );
    v___x_3991_ = crate::leanh::lean_unsigned_to_nat(0);
    v_subst_3992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_subst_3992_, 0, v___x_3991_);
    crate::leanh::lean_ctor_set(v_subst_3992_, 1, v___x_3990_);
    return v_subst_3992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_specializePartialApp(
    mut v_info_3998_: *mut crate::leanh::LeanObject,
    mut v_a_3999_: *mut crate::leanh::LeanObject,
    mut v_a_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
    mut v_a_4002_: *mut crate::leanh::LeanObject,
    mut v_a_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
    mut v_a_4005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4015_: usize = 0;
    let mut v___x_4016_: usize = 0;
    let mut v___x_4017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_4025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v___x_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4048_: u8 = 0;
    let mut v_a_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v_a_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_reuseFailAlloc_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: u8 = 0;
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut v_unused_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4073_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_4007_ = crate::leanh::lean_ctor_get(v_info_3998_, 0);
                crate::leanh::lean_inc_ref(v_params_4007_);
                v_value_4008_ = crate::leanh::lean_ctor_get(v_info_3998_, 1);
                crate::leanh::lean_inc_ref(v_value_4008_);
                v_args_4009_ = crate::leanh::lean_ctor_get(v_info_3998_, 3);
                crate::leanh::lean_inc_ref(v_args_4009_);
                crate::leanh::lean_dec_ref(v_info_3998_);
                v___x_4010_ = crate::leanh::lean_unsigned_to_nat(0);
                v_subst_4011_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1,
                );
                v___x_4012_ = lean_array_get_size(v_args_4009_);
                v___x_4013_ = l_Array_toSubarray___redArg(v_args_4009_, v___x_4010_, v___x_4012_);
                v___x_4014_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4014_, 0, v_subst_4011_);
                crate::leanh::lean_ctor_set(v___x_4014_, 1, v___x_4013_);
                v_sz_4015_ = lean_array_size(v_params_4007_);
                v___x_4016_ = 0usize;
                v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_params_4007_, v_sz_4015_, v___x_4016_, v___x_4014_);
                if crate::leanh::lean_obj_tag(v___x_4017_) == 0 {
                    v_a_4018_ = crate::leanh::lean_ctor_get(v___x_4017_, 0);
                    crate::leanh::lean_inc(v_a_4018_);
                    crate::leanh::lean_dec_ref_known(v___x_4017_, 1);
                    v_fst_4019_ = crate::leanh::lean_ctor_get(v_a_4018_, 0);
                    v_isSharedCheck_4068_ = (!crate::leanh::lean_is_exclusive(v_a_4018_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v_unused_4069_ = crate::leanh::lean_ctor_get(v_a_4018_, 1);
                        crate::leanh::lean_dec(v_unused_4069_);
                        v___x_4021_ = v_a_4018_;
                        v_isShared_4022_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fst_4019_);
                        crate::leanh::lean_dec(v_a_4018_);
                        v___x_4021_ = crate::leanh::lean_box(0);
                        v_isShared_4022_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_4008_);
                    crate::leanh::lean_dec_ref(v_params_4007_);
                    v_a_4070_ = crate::leanh::lean_ctor_get(v___x_4017_, 0);
                    v_isSharedCheck_4077_ = (!crate::leanh::lean_is_exclusive(v___x_4017_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_4072_ = v___x_4017_;
                        v_isShared_4073_ = v_isSharedCheck_4077_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4070_);
                        crate::leanh::lean_dec(v___x_4017_);
                        v___x_4072_ = crate::leanh::lean_box(0);
                        v_isShared_4073_ = v_isSharedCheck_4077_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4023_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2;
                v___x_4066_ = lean_array_get_size(v_params_4007_);
                v___x_4067_ = lean_nat_dec_le(v___x_4012_, v___x_4010_);
                if v___x_4067_ == 0 {
                    v_lower_4025_ = v___x_4012_;
                    v_upper_4026_ = v___x_4066_;
                    state = 2;
                    continue;
                } else {
                    v_lower_4025_ = v___x_4010_;
                    v_upper_4026_ = v___x_4066_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4027_ =
                    l_Array_toSubarray___redArg(v_params_4007_, v_lower_4025_, v_upper_4026_);
                if v_isShared_4022_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4021_, 1, v___x_4023_);
                    v___x_4029_ = v___x_4021_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_fst_4019_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4065_, 1, v___x_4023_);
                    v___x_4029_ = v_reuseFailAlloc_4065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v___x_4027_, v___x_4029_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_);
                if crate::leanh::lean_obj_tag(v___x_4030_) == 0 {
                    v_a_4031_ = crate::leanh::lean_ctor_get(v___x_4030_, 0);
                    crate::leanh::lean_inc(v_a_4031_);
                    crate::leanh::lean_dec_ref_known(v___x_4030_, 1);
                    v_fst_4032_ = crate::leanh::lean_ctor_get(v_a_4031_, 0);
                    crate::leanh::lean_inc(v_fst_4032_);
                    v_snd_4033_ = crate::leanh::lean_ctor_get(v_a_4031_, 1);
                    crate::leanh::lean_inc(v_snd_4033_);
                    crate::leanh::lean_dec(v_a_4031_);
                    v___x_4034_ = 0;
                    v___x_4035_ = 0;
                    v___x_4036_ = l_Lean_Compiler_LCNF_Code_internalize(
                        v___x_4034_,
                        v_value_4008_,
                        v_fst_4032_,
                        v___x_4035_,
                        v_a_4002_,
                        v_a_4003_,
                        v_a_4004_,
                        v_a_4005_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4036_) == 0 {
                        v_a_4037_ = crate::leanh::lean_ctor_get(v___x_4036_, 0);
                        crate::leanh::lean_inc_n(v_a_4037_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4036_, 1);
                        v___x_4038_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(
                            v_a_4037_,
                            v___x_4035_,
                            v_a_4000_,
                            v_a_4002_,
                            v_a_4003_,
                            v_a_4004_,
                            v_a_4005_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4038_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4038_, 1);
                            v___x_4039_ =
                                l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
                            v___x_4040_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(
                                v_snd_4033_,
                                v_a_4037_,
                                v___x_4039_,
                                v_a_4002_,
                                v_a_4003_,
                                v_a_4004_,
                                v_a_4005_,
                            );
                            return v___x_4040_;
                        } else {
                            crate::leanh::lean_dec(v_a_4037_);
                            crate::leanh::lean_dec(v_snd_4033_);
                            v_a_4041_ = crate::leanh::lean_ctor_get(v___x_4038_, 0);
                            v_isSharedCheck_4048_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4038_)) as u8;
                            if v_isSharedCheck_4048_ == 0 {
                                v___x_4043_ = v___x_4038_;
                                v_isShared_4044_ = v_isSharedCheck_4048_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4041_);
                                crate::leanh::lean_dec(v___x_4038_);
                                v___x_4043_ = crate::leanh::lean_box(0);
                                v_isShared_4044_ = v_isSharedCheck_4048_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_snd_4033_);
                        v_a_4049_ = crate::leanh::lean_ctor_get(v___x_4036_, 0);
                        v_isSharedCheck_4056_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4036_)) as u8;
                        if v_isSharedCheck_4056_ == 0 {
                            v___x_4051_ = v___x_4036_;
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4049_);
                            crate::leanh::lean_dec(v___x_4036_);
                            v___x_4051_ = crate::leanh::lean_box(0);
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_value_4008_);
                    v_a_4057_ = crate::leanh::lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4064_ = (!crate::leanh::lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4064_ == 0 {
                        v___x_4059_ = v___x_4030_;
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4057_);
                        crate::leanh::lean_dec(v___x_4030_);
                        v___x_4059_ = crate::leanh::lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_4044_ == 0 {
                    v___x_4046_ = v___x_4043_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
                    v___x_4046_ = v_reuseFailAlloc_4047_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4046_;
            }
            6 => {
                if v_isShared_4052_ == 0 {
                    v___x_4054_ = v___x_4051_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4055_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
                    v___x_4054_ = v_reuseFailAlloc_4055_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4054_;
            }
            8 => {
                if v_isShared_4060_ == 0 {
                    v___x_4062_ = v___x_4059_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4062_;
            }
            10 => {
                if v_isShared_4073_ == 0 {
                    v___x_4075_ = v___x_4072_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
                    v___x_4075_ = v_reuseFailAlloc_4076_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4075_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(
    mut v_info_4078_: *mut crate::leanh::LeanObject,
    mut v_a_4079_: *mut crate::leanh::LeanObject,
    mut v_a_4080_: *mut crate::leanh::LeanObject,
    mut v_a_4081_: *mut crate::leanh::LeanObject,
    mut v_a_4082_: *mut crate::leanh::LeanObject,
    mut v_a_4083_: *mut crate::leanh::LeanObject,
    mut v_a_4084_: *mut crate::leanh::LeanObject,
    mut v_a_4085_: *mut crate::leanh::LeanObject,
    mut v_a_4086_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4087_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(
        v_info_4078_,
        v_a_4079_,
        v_a_4080_,
        v_a_4081_,
        v_a_4082_,
        v_a_4083_,
        v_a_4084_,
        v_a_4085_,
    );
    crate::leanh::lean_dec(v_a_4085_);
    crate::leanh::lean_dec_ref(v_a_4084_);
    crate::leanh::lean_dec(v_a_4083_);
    crate::leanh::lean_dec_ref(v_a_4082_);
    crate::leanh::lean_dec_ref(v_a_4081_);
    crate::leanh::lean_dec(v_a_4080_);
    crate::leanh::lean_dec_ref(v_a_4079_);
    return v_res_4087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(
    mut v_00_u03b2_4088_: *mut crate::leanh::LeanObject,
    mut v_m_4089_: *mut crate::leanh::LeanObject,
    mut v_a_4090_: *mut crate::leanh::LeanObject,
    mut v_b_4091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_m_4089_, v_a_4090_, v_b_4091_);
    return v___x_4092_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(
    mut v_as_4093_: *mut crate::leanh::LeanObject,
    mut v_sz_4094_: usize,
    mut v_i_4095_: usize,
    mut v_b_4096_: *mut crate::leanh::LeanObject,
    mut v___y_4097_: *mut crate::leanh::LeanObject,
    mut v___y_4098_: *mut crate::leanh::LeanObject,
    mut v___y_4099_: *mut crate::leanh::LeanObject,
    mut v___y_4100_: *mut crate::leanh::LeanObject,
    mut v___y_4101_: *mut crate::leanh::LeanObject,
    mut v___y_4102_: *mut crate::leanh::LeanObject,
    mut v___y_4103_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_4093_, v_sz_4094_, v_i_4095_, v_b_4096_);
    return v___x_4105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(
    mut v_as_4106_: *mut crate::leanh::LeanObject,
    mut v_sz_4107_: *mut crate::leanh::LeanObject,
    mut v_i_4108_: *mut crate::leanh::LeanObject,
    mut v_b_4109_: *mut crate::leanh::LeanObject,
    mut v___y_4110_: *mut crate::leanh::LeanObject,
    mut v___y_4111_: *mut crate::leanh::LeanObject,
    mut v___y_4112_: *mut crate::leanh::LeanObject,
    mut v___y_4113_: *mut crate::leanh::LeanObject,
    mut v___y_4114_: *mut crate::leanh::LeanObject,
    mut v___y_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4118_: usize = 0;
    let mut v_i_boxed_4119_: usize = 0;
    let mut v_res_4120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4118_ = crate::leanh::lean_unbox_usize(v_sz_4107_);
    crate::leanh::lean_dec(v_sz_4107_);
    v_i_boxed_4119_ = crate::leanh::lean_unbox_usize(v_i_4108_);
    crate::leanh::lean_dec(v_i_4108_);
    v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(v_as_4106_, v_sz_boxed_4118_, v_i_boxed_4119_, v_b_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
    crate::leanh::lean_dec(v___y_4116_);
    crate::leanh::lean_dec_ref(v___y_4115_);
    crate::leanh::lean_dec(v___y_4114_);
    crate::leanh::lean_dec_ref(v___y_4113_);
    crate::leanh::lean_dec_ref(v___y_4112_);
    crate::leanh::lean_dec(v___y_4111_);
    crate::leanh::lean_dec_ref(v___y_4110_);
    crate::leanh::lean_dec_ref(v_as_4106_);
    return v_res_4120_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(
    mut v_inst_4121_: *mut crate::leanh::LeanObject,
    mut v_R_4122_: *mut crate::leanh::LeanObject,
    mut v_a_4123_: *mut crate::leanh::LeanObject,
    mut v_b_4124_: *mut crate::leanh::LeanObject,
    mut v_c_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
    mut v___y_4127_: *mut crate::leanh::LeanObject,
    mut v___y_4128_: *mut crate::leanh::LeanObject,
    mut v___y_4129_: *mut crate::leanh::LeanObject,
    mut v___y_4130_: *mut crate::leanh::LeanObject,
    mut v___y_4131_: *mut crate::leanh::LeanObject,
    mut v___y_4132_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4134_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_4123_, v_b_4124_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
    return v___x_4134_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(
    mut v_inst_4135_: *mut crate::leanh::LeanObject,
    mut v_R_4136_: *mut crate::leanh::LeanObject,
    mut v_a_4137_: *mut crate::leanh::LeanObject,
    mut v_b_4138_: *mut crate::leanh::LeanObject,
    mut v_c_4139_: *mut crate::leanh::LeanObject,
    mut v___y_4140_: *mut crate::leanh::LeanObject,
    mut v___y_4141_: *mut crate::leanh::LeanObject,
    mut v___y_4142_: *mut crate::leanh::LeanObject,
    mut v___y_4143_: *mut crate::leanh::LeanObject,
    mut v___y_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4148_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(
            v_inst_4135_,
            v_R_4136_,
            v_a_4137_,
            v_b_4138_,
            v_c_4139_,
            v___y_4140_,
            v___y_4141_,
            v___y_4142_,
            v___y_4143_,
            v___y_4144_,
            v___y_4145_,
            v___y_4146_,
        );
    crate::leanh::lean_dec(v___y_4146_);
    crate::leanh::lean_dec_ref(v___y_4145_);
    crate::leanh::lean_dec(v___y_4144_);
    crate::leanh::lean_dec_ref(v___y_4143_);
    crate::leanh::lean_dec_ref(v___y_4142_);
    crate::leanh::lean_dec(v___y_4141_);
    crate::leanh::lean_dec_ref(v___y_4140_);
    return v_res_4148_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(
    mut v_00_u03b2_4149_: *mut crate::leanh::LeanObject,
    mut v_a_4150_: *mut crate::leanh::LeanObject,
    mut v_x_4151_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4152_: u8 = 0;
    v___x_4152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_4150_, v_x_4151_);
    return v___x_4152_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(
    mut v_00_u03b2_4153_: *mut crate::leanh::LeanObject,
    mut v_a_4154_: *mut crate::leanh::LeanObject,
    mut v_x_4155_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4156_: u8 = 0;
    let mut v_r_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(v_00_u03b2_4153_, v_a_4154_, v_x_4155_);
    crate::leanh::lean_dec(v_x_4155_);
    crate::leanh::lean_dec(v_a_4154_);
    v_r_4157_ = crate::leanh::lean_box((v_res_4156_) as usize);
    return v_r_4157_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(
    mut v_00_u03b2_4158_: *mut crate::leanh::LeanObject,
    mut v_data_4159_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_data_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(
    mut v_00_u03b2_4161_: *mut crate::leanh::LeanObject,
    mut v_a_4162_: *mut crate::leanh::LeanObject,
    mut v_b_4163_: *mut crate::leanh::LeanObject,
    mut v_x_4164_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_4162_, v_b_4163_, v_x_4164_);
    return v___x_4165_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4166_: *mut crate::leanh::LeanObject,
    mut v_i_4167_: *mut crate::leanh::LeanObject,
    mut v_source_4168_: *mut crate::leanh::LeanObject,
    mut v_target_4169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4170_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v_i_4167_, v_source_4168_, v_target_4169_);
    return v___x_4170_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_4171_: *mut crate::leanh::LeanObject,
    mut v_x_4172_: *mut crate::leanh::LeanObject,
    mut v_x_4173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4174_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_x_4172_, v_x_4173_);
    return v___x_4174_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(
    mut v_fvarId_4175_: *mut crate::leanh::LeanObject,
    mut v_args_4176_: *mut crate::leanh::LeanObject,
    mut v_a_4177_: *mut crate::leanh::LeanObject,
    mut v_a_4178_: *mut crate::leanh::LeanObject,
    mut v_a_4179_: *mut crate::leanh::LeanObject,
    mut v_a_4180_: *mut crate::leanh::LeanObject,
    mut v_a_4181_: *mut crate::leanh::LeanObject,
    mut v_a_4182_: *mut crate::leanh::LeanObject,
    mut v_a_4183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v_val_4191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4194_: u8 = 0;
    let mut v___x_4195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4200_: u8 = 0;
    let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4213_: u8 = 0;
    let mut v___x_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_a_4221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut v_a_4229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut v_isSharedCheck_4237_: u8 = 0;
    let mut v_a_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_a_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4185_ = 0;
                v___x_4186_ = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(
                    v___x_4185_,
                    v_fvarId_4175_,
                    v_a_4181_,
                );
                if crate::leanh::lean_obj_tag(v___x_4186_) == 0 {
                    v_a_4187_ = crate::leanh::lean_ctor_get(v___x_4186_, 0);
                    v_isSharedCheck_4251_ = (!crate::leanh::lean_is_exclusive(v___x_4186_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4189_ = v___x_4186_;
                        v_isShared_4190_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4187_);
                        crate::leanh::lean_dec(v___x_4186_);
                        v___x_4189_ = crate::leanh::lean_box(0);
                        v_isShared_4190_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_args_4176_);
                    v_a_4252_ = crate::leanh::lean_ctor_get(v___x_4186_, 0);
                    v_isSharedCheck_4259_ = (!crate::leanh::lean_is_exclusive(v___x_4186_)) as u8;
                    if v_isSharedCheck_4259_ == 0 {
                        v___x_4254_ = v___x_4186_;
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4252_);
                        crate::leanh::lean_dec(v___x_4186_);
                        v___x_4254_ = crate::leanh::lean_box(0);
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4187_) == 1 {
                    crate::leanh::lean_del_object(v___x_4189_);
                    v_val_4191_ = crate::leanh::lean_ctor_get(v_a_4187_, 0);
                    v_isSharedCheck_4246_ = (!crate::leanh::lean_is_exclusive(v_a_4187_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4193_ = v_a_4187_;
                        v_isShared_4194_ = v_isSharedCheck_4246_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4191_);
                        crate::leanh::lean_dec(v_a_4187_);
                        v___x_4193_ = crate::leanh::lean_box(0);
                        v_isShared_4194_ = v_isSharedCheck_4246_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4187_);
                    crate::leanh::lean_dec_ref(v_args_4176_);
                    v___x_4247_ = crate::leanh::lean_box(0);
                    if v_isShared_4190_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4189_, 0, v___x_4247_);
                        v___x_4249_ = v___x_4189_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4250_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
                        v___x_4249_ = v_reuseFailAlloc_4250_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4195_ = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal___redArg(
                    v_val_4191_,
                    v_a_4178_,
                    v_a_4180_,
                );
                if crate::leanh::lean_obj_tag(v___x_4195_) == 0 {
                    v_a_4196_ = crate::leanh::lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4237_ = (!crate::leanh::lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4237_ == 0 {
                        v___x_4198_ = v___x_4195_;
                        v_isShared_4199_ = v_isSharedCheck_4237_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4196_);
                        crate::leanh::lean_dec(v___x_4195_);
                        v___x_4198_ = crate::leanh::lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4237_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4193_);
                    crate::leanh::lean_dec(v_val_4191_);
                    crate::leanh::lean_dec_ref(v_args_4176_);
                    v_a_4238_ = crate::leanh::lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4245_ = (!crate::leanh::lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4245_ == 0 {
                        v___x_4240_ = v___x_4195_;
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4238_);
                        crate::leanh::lean_dec(v___x_4195_);
                        v___x_4240_ = crate::leanh::lean_box(0);
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4200_ = (crate::leanh::lean_unbox(v_a_4196_) as u8);
                crate::leanh::lean_dec(v_a_4196_);
                if v___x_4200_ == 0 {
                    crate::leanh::lean_del_object(v___x_4193_);
                    crate::leanh::lean_dec(v_val_4191_);
                    crate::leanh::lean_dec_ref(v_args_4176_);
                    v___x_4201_ = crate::leanh::lean_box(0);
                    if v_isShared_4199_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4198_, 0, v___x_4201_);
                        v___x_4203_ = v___x_4198_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4204_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
                        v___x_4203_ = v_reuseFailAlloc_4204_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4198_);
                    v___x_4205_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_4178_);
                    if crate::leanh::lean_obj_tag(v___x_4205_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4205_, 1);
                        v_params_4206_ = crate::leanh::lean_ctor_get(v_val_4191_, 2);
                        crate::leanh::lean_inc_ref(v_params_4206_);
                        v_value_4207_ = crate::leanh::lean_ctor_get(v_val_4191_, 4);
                        crate::leanh::lean_inc_ref(v_value_4207_);
                        crate::leanh::lean_dec(v_val_4191_);
                        v___x_4208_ = 0;
                        v___x_4209_ = l_Lean_Compiler_LCNF_Simp_betaReduce(
                            v_params_4206_,
                            v_value_4207_,
                            v_args_4176_,
                            v___x_4208_,
                            v_a_4177_,
                            v_a_4178_,
                            v_a_4179_,
                            v_a_4180_,
                            v_a_4181_,
                            v_a_4182_,
                            v_a_4183_,
                        );
                        crate::leanh::lean_dec_ref(v_params_4206_);
                        if crate::leanh::lean_obj_tag(v___x_4209_) == 0 {
                            v_a_4210_ = crate::leanh::lean_ctor_get(v___x_4209_, 0);
                            v_isSharedCheck_4220_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4209_)) as u8;
                            if v_isSharedCheck_4220_ == 0 {
                                v___x_4212_ = v___x_4209_;
                                v_isShared_4213_ = v_isSharedCheck_4220_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4210_);
                                crate::leanh::lean_dec(v___x_4209_);
                                v___x_4212_ = crate::leanh::lean_box(0);
                                v_isShared_4213_ = v_isSharedCheck_4220_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4193_);
                            v_a_4221_ = crate::leanh::lean_ctor_get(v___x_4209_, 0);
                            v_isSharedCheck_4228_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4209_)) as u8;
                            if v_isSharedCheck_4228_ == 0 {
                                v___x_4223_ = v___x_4209_;
                                v_isShared_4224_ = v_isSharedCheck_4228_;
                                state = 8;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4221_);
                                crate::leanh::lean_dec(v___x_4209_);
                                v___x_4223_ = crate::leanh::lean_box(0);
                                v_isShared_4224_ = v_isSharedCheck_4228_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4193_);
                        crate::leanh::lean_dec(v_val_4191_);
                        crate::leanh::lean_dec_ref(v_args_4176_);
                        v_a_4229_ = crate::leanh::lean_ctor_get(v___x_4205_, 0);
                        v_isSharedCheck_4236_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4205_)) as u8;
                        if v_isSharedCheck_4236_ == 0 {
                            v___x_4231_ = v___x_4205_;
                            v_isShared_4232_ = v_isSharedCheck_4236_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4229_);
                            crate::leanh::lean_dec(v___x_4205_);
                            v___x_4231_ = crate::leanh::lean_box(0);
                            v_isShared_4232_ = v_isSharedCheck_4236_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_4203_;
            }
            5 => {
                if v_isShared_4194_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4193_, 0, v_a_4210_);
                    v___x_4215_ = v___x_4193_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4210_);
                    v___x_4215_ = v_reuseFailAlloc_4219_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4213_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4212_, 0, v___x_4215_);
                    v___x_4217_ = v___x_4212_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
                    v___x_4217_ = v_reuseFailAlloc_4218_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4217_;
            }
            8 => {
                if v_isShared_4224_ == 0 {
                    v___x_4226_ = v___x_4223_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4227_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
                    v___x_4226_ = v_reuseFailAlloc_4227_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4226_;
            }
            10 => {
                if v_isShared_4232_ == 0 {
                    v___x_4234_ = v___x_4231_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4235_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
                    v___x_4234_ = v_reuseFailAlloc_4235_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4234_;
            }
            12 => {
                if v_isShared_4241_ == 0 {
                    v___x_4243_ = v___x_4240_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
                    v___x_4243_ = v_reuseFailAlloc_4244_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4243_;
            }
            14 => {
                return v___x_4249_;
            }
            15 => {
                if v_isShared_4255_ == 0 {
                    v___x_4257_ = v___x_4254_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4258_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
                    v___x_4257_ = v_reuseFailAlloc_4258_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4257_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(
    mut v_fvarId_4260_: *mut crate::leanh::LeanObject,
    mut v_args_4261_: *mut crate::leanh::LeanObject,
    mut v_a_4262_: *mut crate::leanh::LeanObject,
    mut v_a_4263_: *mut crate::leanh::LeanObject,
    mut v_a_4264_: *mut crate::leanh::LeanObject,
    mut v_a_4265_: *mut crate::leanh::LeanObject,
    mut v_a_4266_: *mut crate::leanh::LeanObject,
    mut v_a_4267_: *mut crate::leanh::LeanObject,
    mut v_a_4268_: *mut crate::leanh::LeanObject,
    mut v_a_4269_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4270_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(
        v_fvarId_4260_,
        v_args_4261_,
        v_a_4262_,
        v_a_4263_,
        v_a_4264_,
        v_a_4265_,
        v_a_4266_,
        v_a_4267_,
        v_a_4268_,
    );
    crate::leanh::lean_dec(v_a_4268_);
    crate::leanh::lean_dec_ref(v_a_4267_);
    crate::leanh::lean_dec(v_a_4266_);
    crate::leanh::lean_dec_ref(v_a_4265_);
    crate::leanh::lean_dec_ref(v_a_4264_);
    crate::leanh::lean_dec(v_a_4263_);
    crate::leanh::lean_dec_ref(v_a_4262_);
    crate::leanh::lean_dec(v_fvarId_4260_);
    return v_res_4270_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(
    mut v_declName_4271_: *mut crate::leanh::LeanObject,
    mut v___y_4272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4274_ = lean_st_ref_get(v___y_4272_);
    v_env_4275_ = crate::leanh::lean_ctor_get(v___x_4274_, 0);
    crate::leanh::lean_inc_ref(v_env_4275_);
    crate::leanh::lean_dec(v___x_4274_);
    v___x_4276_ = l_Lean_isImplicitReducibleCore(v_env_4275_, v_declName_4271_);
    v___x_4277_ = crate::leanh::lean_box((v___x_4276_) as usize);
    v___x_4278_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4278_, 0, v___x_4277_);
    v___x_4279_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4279_, 0, v___x_4278_);
    return v___x_4279_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(
    mut v_declName_4280_: *mut crate::leanh::LeanObject,
    mut v___y_4281_: *mut crate::leanh::LeanObject,
    mut v___y_4282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4283_ =
        l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(
            v_declName_4280_,
            v___y_4281_,
        );
    crate::leanh::lean_dec(v___y_4281_);
    return v_res_4283_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(
    mut v_declName_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
    mut v___y_4290_: *mut crate::leanh::LeanObject,
    mut v___y_4291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ =
        l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(
            v_declName_4284_,
            v___y_4291_,
        );
    return v___x_4293_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(
    mut v_declName_4294_: *mut crate::leanh::LeanObject,
    mut v___y_4295_: *mut crate::leanh::LeanObject,
    mut v___y_4296_: *mut crate::leanh::LeanObject,
    mut v___y_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4303_ =
        l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(
            v_declName_4294_,
            v___y_4295_,
            v___y_4296_,
            v___y_4297_,
            v___y_4298_,
            v___y_4299_,
            v___y_4300_,
            v___y_4301_,
        );
    crate::leanh::lean_dec(v___y_4301_);
    crate::leanh::lean_dec_ref(v___y_4300_);
    crate::leanh::lean_dec(v___y_4299_);
    crate::leanh::lean_dec_ref(v___y_4298_);
    crate::leanh::lean_dec_ref(v___y_4297_);
    crate::leanh::lean_dec(v___y_4296_);
    crate::leanh::lean_dec_ref(v___y_4295_);
    return v_res_4303_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(
    mut v_sz_4304_: usize,
    mut v_i_4305_: usize,
    mut v_bs_4306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4307_: u8 = 0;
    let mut v_v_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: usize = 0;
    let mut v___x_4314_: usize = 0;
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4307_ = lean_usize_dec_lt(v_i_4305_, v_sz_4304_);
                if v___x_4307_ == 0 {
                    return v_bs_4306_;
                } else {
                    v_v_4308_ = lean_array_uget_borrowed(v_bs_4306_, v_i_4305_);
                    v_fvarId_4309_ = crate::leanh::lean_ctor_get(v_v_4308_, 0);
                    crate::leanh::lean_inc(v_fvarId_4309_);
                    v___x_4310_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_4311_ = lean_array_uset(v_bs_4306_, v_i_4305_, v___x_4310_);
                    v___x_4312_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4312_, 0, v_fvarId_4309_);
                    v___x_4313_ = 1usize;
                    v___x_4314_ = lean_usize_add(v_i_4305_, v___x_4313_);
                    v___x_4315_ = lean_array_uset(v_bs_x27_4311_, v_i_4305_, v___x_4312_);
                    v_i_4305_ = v___x_4314_;
                    v_bs_4306_ = v___x_4315_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg___boxed(
    mut v_sz_4317_: *mut crate::leanh::LeanObject,
    mut v_i_4318_: *mut crate::leanh::LeanObject,
    mut v_bs_4319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4320_: usize = 0;
    let mut v_i_boxed_4321_: usize = 0;
    let mut v_res_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4320_ = crate::leanh::lean_unbox_usize(v_sz_4317_);
    crate::leanh::lean_dec(v_sz_4317_);
    v_i_boxed_4321_ = crate::leanh::lean_unbox_usize(v_i_4318_);
    crate::leanh::lean_dec(v_i_4318_);
    v_res_4322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_boxed_4320_, v_i_boxed_4321_, v_bs_4319_);
    return v_res_4322_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(
    mut v_letDecl_4326_: *mut crate::leanh::LeanObject,
    mut v_a_4327_: *mut crate::leanh::LeanObject,
    mut v_a_4328_: *mut crate::leanh::LeanObject,
    mut v_a_4329_: *mut crate::leanh::LeanObject,
    mut v_a_4330_: *mut crate::leanh::LeanObject,
    mut v_a_4331_: *mut crate::leanh::LeanObject,
    mut v_a_4332_: *mut crate::leanh::LeanObject,
    mut v_a_4333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_config_4335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_etaPoly_4336_: u8 = 0;
    let mut v___x_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4347_: u8 = 0;
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: u8 = 0;
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4368_: u8 = 0;
    let mut v_val_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4372_: u8 = 0;
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4394_: u8 = 0;
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: u8 = 0;
    let mut v___x_4399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4405_: usize = 0;
    let mut v___x_4406_: usize = 0;
    let mut v___x_4407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut v_unused_4434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___x_4440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4442_: u8 = 0;
    let mut v_a_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut v_a_4451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v_reuseFailAlloc_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_reuseFailAlloc_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_a_4479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4482_: u8 = 0;
    let mut v___x_4484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_a_4488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut v___x_4496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_a_4503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v___x_4511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v___x_4514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_4335_ = crate::leanh::lean_ctor_get(v_a_4327_, 1);
                v_etaPoly_4336_ = crate::leanh::lean_ctor_get_uint8(v_config_4335_, 0 as u32);
                if v_etaPoly_4336_ == 0 {
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    v___x_4337_ = crate::leanh::lean_box(0);
                    v___x_4338_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4338_, 0, v___x_4337_);
                    return v___x_4338_;
                } else {
                    v_value_4339_ = crate::leanh::lean_ctor_get(v_letDecl_4326_, 3);
                    crate::leanh::lean_inc(v_value_4339_);
                    if crate::leanh::lean_obj_tag(v_value_4339_) == 3 {
                        v_fvarId_4340_ = crate::leanh::lean_ctor_get(v_letDecl_4326_, 0);
                        v_type_4341_ = crate::leanh::lean_ctor_get(v_letDecl_4326_, 2);
                        v_declName_4342_ = crate::leanh::lean_ctor_get(v_value_4339_, 0);
                        v_us_4343_ = crate::leanh::lean_ctor_get(v_value_4339_, 1);
                        v_args_4344_ = crate::leanh::lean_ctor_get(v_value_4339_, 2);
                        v_isSharedCheck_4513_ =
                            (!crate::leanh::lean_is_exclusive(v_value_4339_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v___x_4346_ = v_value_4339_;
                            v_isShared_4347_ = v_isSharedCheck_4513_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_args_4344_);
                            crate::leanh::lean_inc(v_us_4343_);
                            crate::leanh::lean_inc(v_declName_4342_);
                            crate::leanh::lean_dec(v_value_4339_);
                            v___x_4346_ = crate::leanh::lean_box(0);
                            v_isShared_4347_ = v_isSharedCheck_4513_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_value_4339_);
                        crate::leanh::lean_dec_ref(v_letDecl_4326_);
                        v___x_4514_ = crate::leanh::lean_box(0);
                        v___x_4515_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4515_, 0, v___x_4514_);
                        return v___x_4515_;
                    }
                }
            }
            1 => {
                v___x_4348_ = lean_st_ref_get(v_a_4333_);
                v_env_4349_ = crate::leanh::lean_ctor_get(v___x_4348_, 0);
                crate::leanh::lean_inc_ref(v_env_4349_);
                crate::leanh::lean_dec(v___x_4348_);
                v___x_4350_ = 0;
                crate::leanh::lean_inc(v_declName_4342_);
                v___x_4351_ =
                    l_Lean_Environment_find_x3f(v_env_4349_, v_declName_4342_, v___x_4350_);
                if crate::leanh::lean_obj_tag(v___x_4351_) == 1 {
                    v_val_4352_ = crate::leanh::lean_ctor_get(v___x_4351_, 0);
                    crate::leanh::lean_inc(v_val_4352_);
                    crate::leanh::lean_dec_ref_known(v___x_4351_, 1);
                    v___x_4353_ = l_Lean_ConstantInfo_type(v_val_4352_);
                    crate::leanh::lean_dec(v_val_4352_);
                    v___x_4354_ =
                        l_Lean_Compiler_LCNF_hasLocalInst___redArg(v___x_4353_, v_a_4333_);
                    if crate::leanh::lean_obj_tag(v___x_4354_) == 0 {
                        v_a_4355_ = crate::leanh::lean_ctor_get(v___x_4354_, 0);
                        v_isSharedCheck_4502_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4354_)) as u8;
                        if v_isSharedCheck_4502_ == 0 {
                            v___x_4357_ = v___x_4354_;
                            v_isShared_4358_ = v_isSharedCheck_4502_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4355_);
                            crate::leanh::lean_dec(v___x_4354_);
                            v___x_4357_ = crate::leanh::lean_box(0);
                            v_isShared_4358_ = v_isSharedCheck_4502_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4346_);
                        crate::leanh::lean_dec_ref(v_args_4344_);
                        crate::leanh::lean_dec(v_us_4343_);
                        crate::leanh::lean_dec(v_declName_4342_);
                        crate::leanh::lean_dec_ref(v_letDecl_4326_);
                        v_a_4503_ = crate::leanh::lean_ctor_get(v___x_4354_, 0);
                        v_isSharedCheck_4510_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4354_)) as u8;
                        if v_isSharedCheck_4510_ == 0 {
                            v___x_4505_ = v___x_4354_;
                            v_isShared_4506_ = v_isSharedCheck_4510_;
                            state = 32;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4503_);
                            crate::leanh::lean_dec(v___x_4354_);
                            v___x_4505_ = crate::leanh::lean_box(0);
                            v_isShared_4506_ = v_isSharedCheck_4510_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4351_);
                    crate::leanh::lean_del_object(v___x_4346_);
                    crate::leanh::lean_dec_ref(v_args_4344_);
                    crate::leanh::lean_dec(v_us_4343_);
                    crate::leanh::lean_dec(v_declName_4342_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    v___x_4511_ = crate::leanh::lean_box(0);
                    v___x_4512_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                    return v___x_4512_;
                }
            }
            2 => {
                v___x_4359_ = (crate::leanh::lean_unbox(v_a_4355_) as u8);
                crate::leanh::lean_dec(v_a_4355_);
                if v___x_4359_ == 0 {
                    crate::leanh::lean_del_object(v___x_4346_);
                    crate::leanh::lean_dec_ref(v_args_4344_);
                    crate::leanh::lean_dec(v_us_4343_);
                    crate::leanh::lean_dec(v_declName_4342_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    v___x_4360_ = crate::leanh::lean_box(0);
                    if v_isShared_4358_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4357_, 0, v___x_4360_);
                        v___x_4362_ = v___x_4357_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4363_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4360_);
                        v___x_4362_ = v_reuseFailAlloc_4363_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4357_);
                    crate::leanh::lean_inc(v_declName_4342_);
                    v___x_4364_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_4342_, v_a_4333_);
                    v_a_4365_ = crate::leanh::lean_ctor_get(v___x_4364_, 0);
                    v_isSharedCheck_4501_ = (!crate::leanh::lean_is_exclusive(v___x_4364_)) as u8;
                    if v_isSharedCheck_4501_ == 0 {
                        v___x_4367_ = v___x_4364_;
                        v_isShared_4368_ = v_isSharedCheck_4501_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4365_);
                        crate::leanh::lean_dec(v___x_4364_);
                        v___x_4367_ = crate::leanh::lean_box(0);
                        v_isShared_4368_ = v_isSharedCheck_4501_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_4362_;
            }
            4 => {
                v_val_4369_ = crate::leanh::lean_ctor_get(v_a_4365_, 0);
                v_isSharedCheck_4500_ = (!crate::leanh::lean_is_exclusive(v_a_4365_)) as u8;
                if v_isSharedCheck_4500_ == 0 {
                    v___x_4371_ = v_a_4365_;
                    v_isShared_4372_ = v_isSharedCheck_4500_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_4369_);
                    crate::leanh::lean_dec(v_a_4365_);
                    v___x_4371_ = crate::leanh::lean_box(0);
                    v_isShared_4372_ = v_isSharedCheck_4500_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4373_ = (crate::leanh::lean_unbox(v_val_4369_) as u8);
                crate::leanh::lean_dec(v_val_4369_);
                if v___x_4373_ == 0 {
                    crate::leanh::lean_del_object(v___x_4367_);
                    v___x_4374_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_4330_);
                    if crate::leanh::lean_obj_tag(v___x_4374_) == 0 {
                        v_a_4375_ = crate::leanh::lean_ctor_get(v___x_4374_, 0);
                        v_isSharedCheck_4487_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4374_)) as u8;
                        if v_isSharedCheck_4487_ == 0 {
                            v___x_4377_ = v___x_4374_;
                            v_isShared_4378_ = v_isSharedCheck_4487_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4375_);
                            crate::leanh::lean_dec(v___x_4374_);
                            v___x_4377_ = crate::leanh::lean_box(0);
                            v_isShared_4378_ = v_isSharedCheck_4487_;
                            state = 6;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4371_);
                        crate::leanh::lean_del_object(v___x_4346_);
                        crate::leanh::lean_dec_ref(v_args_4344_);
                        crate::leanh::lean_dec(v_us_4343_);
                        crate::leanh::lean_dec(v_declName_4342_);
                        crate::leanh::lean_dec_ref(v_letDecl_4326_);
                        v_a_4488_ = crate::leanh::lean_ctor_get(v___x_4374_, 0);
                        v_isSharedCheck_4495_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4374_)) as u8;
                        if v_isSharedCheck_4495_ == 0 {
                            v___x_4490_ = v___x_4374_;
                            v_isShared_4491_ = v_isSharedCheck_4495_;
                            state = 29;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4488_);
                            crate::leanh::lean_dec(v___x_4374_);
                            v___x_4490_ = crate::leanh::lean_box(0);
                            v_isShared_4491_ = v_isSharedCheck_4495_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4371_);
                    crate::leanh::lean_del_object(v___x_4346_);
                    crate::leanh::lean_dec_ref(v_args_4344_);
                    crate::leanh::lean_dec(v_us_4343_);
                    crate::leanh::lean_dec(v_declName_4342_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    v___x_4496_ = crate::leanh::lean_box(0);
                    if v_isShared_4368_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4367_, 0, v___x_4496_);
                        v___x_4498_ = v___x_4367_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_4499_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
                        v___x_4498_ = v_reuseFailAlloc_4499_;
                        state = 31;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4379_ = (crate::leanh::lean_unbox(v_a_4375_) as u8);
                crate::leanh::lean_inc(v_declName_4342_);
                v___x_4380_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                    v_declName_4342_,
                    v___x_4379_,
                    v_a_4332_,
                    v_a_4333_,
                );
                if crate::leanh::lean_obj_tag(v___x_4380_) == 0 {
                    v_a_4381_ = crate::leanh::lean_ctor_get(v___x_4380_, 0);
                    v_isSharedCheck_4478_ = (!crate::leanh::lean_is_exclusive(v___x_4380_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4383_ = v___x_4380_;
                        v_isShared_4384_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4381_);
                        crate::leanh::lean_dec(v___x_4380_);
                        v___x_4383_ = crate::leanh::lean_box(0);
                        v_isShared_4384_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4377_);
                    crate::leanh::lean_dec(v_a_4375_);
                    crate::leanh::lean_del_object(v___x_4371_);
                    crate::leanh::lean_del_object(v___x_4346_);
                    crate::leanh::lean_dec_ref(v_args_4344_);
                    crate::leanh::lean_dec(v_us_4343_);
                    crate::leanh::lean_dec(v_declName_4342_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    v_a_4479_ = crate::leanh::lean_ctor_get(v___x_4380_, 0);
                    v_isSharedCheck_4486_ = (!crate::leanh::lean_is_exclusive(v___x_4380_)) as u8;
                    if v_isSharedCheck_4486_ == 0 {
                        v___x_4481_ = v___x_4380_;
                        v_isShared_4482_ = v_isSharedCheck_4486_;
                        state = 27;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4479_);
                        crate::leanh::lean_dec(v___x_4380_);
                        v___x_4481_ = crate::leanh::lean_box(0);
                        v_isShared_4482_ = v_isSharedCheck_4486_;
                        state = 27;
                        continue;
                    }
                }
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_4381_) == 1 {
                    v_val_4390_ = crate::leanh::lean_ctor_get(v_a_4381_, 0);
                    v_isSharedCheck_4477_ = (!crate::leanh::lean_is_exclusive(v_a_4381_)) as u8;
                    if v_isSharedCheck_4477_ == 0 {
                        v___x_4392_ = v_a_4381_;
                        v_isShared_4393_ = v_isSharedCheck_4477_;
                        state = 10;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_4390_);
                        crate::leanh::lean_dec(v_a_4381_);
                        v___x_4392_ = crate::leanh::lean_box(0);
                        v_isShared_4393_ = v_isSharedCheck_4477_;
                        state = 10;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4381_);
                    crate::leanh::lean_del_object(v___x_4377_);
                    crate::leanh::lean_dec(v_a_4375_);
                    crate::leanh::lean_del_object(v___x_4371_);
                    crate::leanh::lean_del_object(v___x_4346_);
                    crate::leanh::lean_dec_ref(v_args_4344_);
                    crate::leanh::lean_dec(v_us_4343_);
                    crate::leanh::lean_dec(v_declName_4342_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4386_ = crate::leanh::lean_box(0);
                if v_isShared_4384_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4383_, 0, v___x_4386_);
                    v___x_4388_ = v___x_4383_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4388_;
            }
            10 => {
                v___x_4394_ = (crate::leanh::lean_unbox(v_a_4375_) as u8);
                crate::leanh::lean_dec(v_a_4375_);
                v___x_4395_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_4394_);
                if v___x_4395_ == 0 {
                    crate::leanh::lean_del_object(v___x_4383_);
                    v___x_4396_ = lean_array_get_size(v_args_4344_);
                    v___x_4397_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_4390_);
                    crate::leanh::lean_dec(v_val_4390_);
                    v___x_4398_ = lean_nat_dec_lt(v___x_4396_, v___x_4397_);
                    crate::leanh::lean_dec(v___x_4397_);
                    if v___x_4398_ == 0 {
                        crate::leanh::lean_del_object(v___x_4392_);
                        crate::leanh::lean_del_object(v___x_4371_);
                        crate::leanh::lean_del_object(v___x_4346_);
                        crate::leanh::lean_dec_ref(v_args_4344_);
                        crate::leanh::lean_dec(v_us_4343_);
                        crate::leanh::lean_dec(v_declName_4342_);
                        crate::leanh::lean_dec_ref(v_letDecl_4326_);
                        v___x_4399_ = crate::leanh::lean_box(0);
                        if v_isShared_4378_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4377_, 0, v___x_4399_);
                            v___x_4401_ = v___x_4377_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4402_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4399_);
                            v___x_4401_ = v_reuseFailAlloc_4402_;
                            state = 11;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_4377_);
                        crate::leanh::lean_inc_ref(v_type_4341_);
                        v___x_4403_ = l_Lean_Compiler_LCNF_mkNewParams(
                            v___x_4395_,
                            v_type_4341_,
                            v_a_4330_,
                            v_a_4331_,
                            v_a_4332_,
                            v_a_4333_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_4403_) == 0 {
                            v_a_4404_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
                            crate::leanh::lean_inc_n(v_a_4404_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_4403_, 1);
                            v_sz_4405_ = lean_array_size(v_a_4404_);
                            v___x_4406_ = 0usize;
                            v___x_4407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_4405_, v___x_4406_, v_a_4404_);
                            v___x_4408_ = l_Array_append___redArg(v_args_4344_, v___x_4407_);
                            crate::leanh::lean_dec_ref(v___x_4407_);
                            if v_isShared_4347_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_4346_, 2, v___x_4408_);
                                v___x_4410_ = v___x_4346_;
                                state = 12;
                                continue;
                            } else {
                                v_reuseFailAlloc_4468_ =
                                    crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_4468_,
                                    0,
                                    v_declName_4342_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_us_4343_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_4468_, 2, v___x_4408_);
                                v___x_4410_ = v_reuseFailAlloc_4468_;
                                state = 12;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_4392_);
                            crate::leanh::lean_del_object(v___x_4371_);
                            crate::leanh::lean_del_object(v___x_4346_);
                            crate::leanh::lean_dec_ref(v_args_4344_);
                            crate::leanh::lean_dec(v_us_4343_);
                            crate::leanh::lean_dec(v_declName_4342_);
                            crate::leanh::lean_dec_ref(v_letDecl_4326_);
                            v_a_4469_ = crate::leanh::lean_ctor_get(v___x_4403_, 0);
                            v_isSharedCheck_4476_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4403_)) as u8;
                            if v_isSharedCheck_4476_ == 0 {
                                v___x_4471_ = v___x_4403_;
                                v_isShared_4472_ = v_isSharedCheck_4476_;
                                state = 25;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4469_);
                                crate::leanh::lean_dec(v___x_4403_);
                                v___x_4471_ = crate::leanh::lean_box(0);
                                v_isShared_4472_ = v_isSharedCheck_4476_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4392_);
                    crate::leanh::lean_dec(v_val_4390_);
                    crate::leanh::lean_del_object(v___x_4377_);
                    crate::leanh::lean_del_object(v___x_4371_);
                    crate::leanh::lean_del_object(v___x_4346_);
                    crate::leanh::lean_dec_ref(v_args_4344_);
                    crate::leanh::lean_dec(v_us_4343_);
                    crate::leanh::lean_dec(v_declName_4342_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    state = 8;
                    continue;
                }
            }
            11 => {
                return v___x_4401_;
            }
            12 => {
                v___x_4411_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
                v___x_4412_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
                    v___x_4395_,
                    v___x_4410_,
                    v___x_4411_,
                    v_a_4330_,
                    v_a_4331_,
                    v_a_4332_,
                    v_a_4333_,
                );
                if crate::leanh::lean_obj_tag(v___x_4412_) == 0 {
                    v_a_4413_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                    crate::leanh::lean_inc(v_a_4413_);
                    crate::leanh::lean_dec_ref_known(v___x_4412_, 1);
                    v_fvarId_4414_ = crate::leanh::lean_ctor_get(v_a_4413_, 0);
                    crate::leanh::lean_inc(v_fvarId_4414_);
                    if v_isShared_4372_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4371_, 5);
                        crate::leanh::lean_ctor_set(v___x_4371_, 0, v_fvarId_4414_);
                        v___x_4416_ = v___x_4371_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4459_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_fvarId_4414_);
                        v___x_4416_ = v_reuseFailAlloc_4459_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_4404_);
                    crate::leanh::lean_del_object(v___x_4392_);
                    crate::leanh::lean_del_object(v___x_4371_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    v_a_4460_ = crate::leanh::lean_ctor_get(v___x_4412_, 0);
                    v_isSharedCheck_4467_ = (!crate::leanh::lean_is_exclusive(v___x_4412_)) as u8;
                    if v_isSharedCheck_4467_ == 0 {
                        v___x_4462_ = v___x_4412_;
                        v_isShared_4463_ = v_isSharedCheck_4467_;
                        state = 23;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4460_);
                        crate::leanh::lean_dec(v___x_4412_);
                        v___x_4462_ = crate::leanh::lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4467_;
                        state = 23;
                        continue;
                    }
                }
            }
            13 => {
                v___x_4417_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4417_, 0, v_a_4413_);
                crate::leanh::lean_ctor_set(v___x_4417_, 1, v___x_4416_);
                v___x_4418_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
                v___x_4419_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(
                    v_a_4404_,
                    v___x_4417_,
                    v___x_4418_,
                    v_a_4330_,
                    v_a_4331_,
                    v_a_4332_,
                    v_a_4333_,
                );
                if crate::leanh::lean_obj_tag(v___x_4419_) == 0 {
                    v_a_4420_ = crate::leanh::lean_ctor_get(v___x_4419_, 0);
                    crate::leanh::lean_inc(v_a_4420_);
                    crate::leanh::lean_dec_ref_known(v___x_4419_, 1);
                    v_fvarId_4421_ = crate::leanh::lean_ctor_get(v_a_4420_, 0);
                    crate::leanh::lean_inc(v_fvarId_4421_);
                    crate::leanh::lean_inc(v_fvarId_4340_);
                    v___x_4422_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_4340_,
                        v_fvarId_4421_,
                        v_a_4328_,
                        v_a_4330_,
                        v_a_4331_,
                        v_a_4332_,
                        v_a_4333_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4422_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_4422_, 1);
                        v___x_4423_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
                            v_letDecl_4326_,
                            v_a_4328_,
                            v_a_4331_,
                        );
                        crate::leanh::lean_dec_ref(v_letDecl_4326_);
                        if crate::leanh::lean_obj_tag(v___x_4423_) == 0 {
                            v_isSharedCheck_4433_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4423_)) as u8;
                            if v_isSharedCheck_4433_ == 0 {
                                v_unused_4434_ = crate::leanh::lean_ctor_get(v___x_4423_, 0);
                                crate::leanh::lean_dec(v_unused_4434_);
                                v___x_4425_ = v___x_4423_;
                                v_isShared_4426_ = v_isSharedCheck_4433_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4423_);
                                v___x_4425_ = crate::leanh::lean_box(0);
                                v_isShared_4426_ = v_isSharedCheck_4433_;
                                state = 14;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_4420_);
                            crate::leanh::lean_del_object(v___x_4392_);
                            v_a_4435_ = crate::leanh::lean_ctor_get(v___x_4423_, 0);
                            v_isSharedCheck_4442_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4423_)) as u8;
                            if v_isSharedCheck_4442_ == 0 {
                                v___x_4437_ = v___x_4423_;
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4435_);
                                crate::leanh::lean_dec(v___x_4423_);
                                v___x_4437_ = crate::leanh::lean_box(0);
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4420_);
                        crate::leanh::lean_del_object(v___x_4392_);
                        crate::leanh::lean_dec_ref(v_letDecl_4326_);
                        v_a_4443_ = crate::leanh::lean_ctor_get(v___x_4422_, 0);
                        v_isSharedCheck_4450_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4422_)) as u8;
                        if v_isSharedCheck_4450_ == 0 {
                            v___x_4445_ = v___x_4422_;
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4443_);
                            crate::leanh::lean_dec(v___x_4422_);
                            v___x_4445_ = crate::leanh::lean_box(0);
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4392_);
                    crate::leanh::lean_dec_ref(v_letDecl_4326_);
                    v_a_4451_ = crate::leanh::lean_ctor_get(v___x_4419_, 0);
                    v_isSharedCheck_4458_ = (!crate::leanh::lean_is_exclusive(v___x_4419_)) as u8;
                    if v_isSharedCheck_4458_ == 0 {
                        v___x_4453_ = v___x_4419_;
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4451_);
                        crate::leanh::lean_dec(v___x_4419_);
                        v___x_4453_ = crate::leanh::lean_box(0);
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 21;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4393_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4392_, 0, v_a_4420_);
                    v___x_4428_ = v___x_4392_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4420_);
                    v___x_4428_ = v_reuseFailAlloc_4432_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4426_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4425_, 0, v___x_4428_);
                    v___x_4430_ = v___x_4425_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
                    v___x_4430_ = v_reuseFailAlloc_4431_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4430_;
            }
            17 => {
                if v_isShared_4438_ == 0 {
                    v___x_4440_ = v___x_4437_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_4441_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
                    v___x_4440_ = v_reuseFailAlloc_4441_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_4440_;
            }
            19 => {
                if v_isShared_4446_ == 0 {
                    v___x_4448_ = v___x_4445_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_4449_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
                    v___x_4448_ = v_reuseFailAlloc_4449_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_4448_;
            }
            21 => {
                if v_isShared_4454_ == 0 {
                    v___x_4456_ = v___x_4453_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_4457_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
                    v___x_4456_ = v_reuseFailAlloc_4457_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_4456_;
            }
            23 => {
                if v_isShared_4463_ == 0 {
                    v___x_4465_ = v___x_4462_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
                    v___x_4465_ = v_reuseFailAlloc_4466_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_4465_;
            }
            25 => {
                if v_isShared_4472_ == 0 {
                    v___x_4474_ = v___x_4471_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
                    v___x_4474_ = v_reuseFailAlloc_4475_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4474_;
            }
            27 => {
                if v_isShared_4482_ == 0 {
                    v___x_4484_ = v___x_4481_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_4485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
                    v___x_4484_ = v_reuseFailAlloc_4485_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_4484_;
            }
            29 => {
                if v_isShared_4491_ == 0 {
                    v___x_4493_ = v___x_4490_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_4494_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
                    v___x_4493_ = v_reuseFailAlloc_4494_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_4493_;
            }
            31 => {
                return v___x_4498_;
            }
            32 => {
                if v_isShared_4506_ == 0 {
                    v___x_4508_ = v___x_4505_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_4509_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
                    v___x_4508_ = v_reuseFailAlloc_4509_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_4508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(
    mut v_letDecl_4516_: *mut crate::leanh::LeanObject,
    mut v_a_4517_: *mut crate::leanh::LeanObject,
    mut v_a_4518_: *mut crate::leanh::LeanObject,
    mut v_a_4519_: *mut crate::leanh::LeanObject,
    mut v_a_4520_: *mut crate::leanh::LeanObject,
    mut v_a_4521_: *mut crate::leanh::LeanObject,
    mut v_a_4522_: *mut crate::leanh::LeanObject,
    mut v_a_4523_: *mut crate::leanh::LeanObject,
    mut v_a_4524_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4525_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(
        v_letDecl_4516_,
        v_a_4517_,
        v_a_4518_,
        v_a_4519_,
        v_a_4520_,
        v_a_4521_,
        v_a_4522_,
        v_a_4523_,
    );
    crate::leanh::lean_dec(v_a_4523_);
    crate::leanh::lean_dec_ref(v_a_4522_);
    crate::leanh::lean_dec(v_a_4521_);
    crate::leanh::lean_dec_ref(v_a_4520_);
    crate::leanh::lean_dec_ref(v_a_4519_);
    crate::leanh::lean_dec(v_a_4518_);
    crate::leanh::lean_dec_ref(v_a_4517_);
    return v_res_4525_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(
    mut v___x_4526_: u8,
    mut v_sz_4527_: usize,
    mut v_i_4528_: usize,
    mut v_bs_4529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_4527_, v_i_4528_, v_bs_4529_);
    return v___x_4530_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(
    mut v___x_4531_: *mut crate::leanh::LeanObject,
    mut v_sz_4532_: *mut crate::leanh::LeanObject,
    mut v_i_4533_: *mut crate::leanh::LeanObject,
    mut v_bs_4534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_24447__boxed_4535_: u8 = 0;
    let mut v_sz_boxed_4536_: usize = 0;
    let mut v_i_boxed_4537_: usize = 0;
    let mut v_res_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_24447__boxed_4535_ = (crate::leanh::lean_unbox(v___x_4531_) as u8);
    v_sz_boxed_4536_ = crate::leanh::lean_unbox_usize(v_sz_4532_);
    crate::leanh::lean_dec(v_sz_4532_);
    v_i_boxed_4537_ = crate::leanh::lean_unbox_usize(v_i_4533_);
    crate::leanh::lean_dec(v_i_4533_);
    v_res_4538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_24447__boxed_4535_, v_sz_boxed_4536_, v_i_boxed_4537_, v_bs_4534_);
    return v_res_4538_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(
    mut v_c_4539_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4540_: *mut crate::leanh::LeanObject,
    mut v_a_4541_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4546_: u8 = 0;
    let mut v___x_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: u8 = 0;
    let mut v___x_4550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4554_: u8 = 0;
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v___x_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_c_4539_) == 5 {
                    v_fvarId_4543_ = crate::leanh::lean_ctor_get(v_c_4539_, 0);
                    v_isSharedCheck_4565_ = (!crate::leanh::lean_is_exclusive(v_c_4539_)) as u8;
                    if v_isSharedCheck_4565_ == 0 {
                        v___x_4545_ = v_c_4539_;
                        v_isShared_4546_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4543_);
                        crate::leanh::lean_dec(v_c_4539_);
                        v___x_4545_ = crate::leanh::lean_box(0);
                        v_isShared_4546_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_c_4539_);
                    v___x_4566_ = 0;
                    v___x_4567_ = crate::leanh::lean_box((v___x_4566_) as usize);
                    v___x_4568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4568_, 0, v___x_4567_);
                    return v___x_4568_;
                }
            }
            1 => {
                v___x_4547_ = lean_st_ref_get(v_a_4541_);
                v_subst_4548_ = crate::leanh::lean_ctor_get(v___x_4547_, 0);
                crate::leanh::lean_inc_ref(v_subst_4548_);
                crate::leanh::lean_dec(v___x_4547_);
                v___x_4549_ = 0;
                v___x_4550_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v_subst_4548_,
                    v_fvarId_4543_,
                    v___x_4549_,
                );
                crate::leanh::lean_dec_ref(v_subst_4548_);
                if crate::leanh::lean_obj_tag(v___x_4550_) == 0 {
                    crate::leanh::lean_del_object(v___x_4545_);
                    v_fvarId_4551_ = crate::leanh::lean_ctor_get(v___x_4550_, 0);
                    v_isSharedCheck_4560_ = (!crate::leanh::lean_is_exclusive(v___x_4550_)) as u8;
                    if v_isSharedCheck_4560_ == 0 {
                        v___x_4553_ = v___x_4550_;
                        v_isShared_4554_ = v_isSharedCheck_4560_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4551_);
                        crate::leanh::lean_dec(v___x_4550_);
                        v___x_4553_ = crate::leanh::lean_box(0);
                        v_isShared_4554_ = v_isSharedCheck_4560_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4561_ = crate::leanh::lean_box((v___x_4549_) as usize);
                    if v_isShared_4546_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_4545_, 0);
                        crate::leanh::lean_ctor_set(v___x_4545_, 0, v___x_4561_);
                        v___x_4563_ = v___x_4545_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
                        v___x_4563_ = v_reuseFailAlloc_4564_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4555_ = l_Lean_instBEqFVarId_beq(v_fvarId_4551_, v_fvarId_4540_);
                crate::leanh::lean_dec(v_fvarId_4551_);
                v___x_4556_ = crate::leanh::lean_box((v___x_4555_) as usize);
                if v_isShared_4554_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4553_, 0, v___x_4556_);
                    v___x_4558_ = v___x_4553_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4559_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
                    v___x_4558_ = v_reuseFailAlloc_4559_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4558_;
            }
            4 => {
                return v___x_4563_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(
    mut v_c_4569_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4570_: *mut crate::leanh::LeanObject,
    mut v_a_4571_: *mut crate::leanh::LeanObject,
    mut v_a_4572_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4573_ =
        l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_4569_, v_fvarId_4570_, v_a_4571_);
    crate::leanh::lean_dec(v_a_4571_);
    crate::leanh::lean_dec(v_fvarId_4570_);
    return v_res_4573_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isReturnOf(
    mut v_c_4574_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4575_: *mut crate::leanh::LeanObject,
    mut v_a_4576_: *mut crate::leanh::LeanObject,
    mut v_a_4577_: *mut crate::leanh::LeanObject,
    mut v_a_4578_: *mut crate::leanh::LeanObject,
    mut v_a_4579_: *mut crate::leanh::LeanObject,
    mut v_a_4580_: *mut crate::leanh::LeanObject,
    mut v_a_4581_: *mut crate::leanh::LeanObject,
    mut v_a_4582_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4584_ =
        l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_4574_, v_fvarId_4575_, v_a_4577_);
    return v___x_4584_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(
    mut v_c_4585_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4586_: *mut crate::leanh::LeanObject,
    mut v_a_4587_: *mut crate::leanh::LeanObject,
    mut v_a_4588_: *mut crate::leanh::LeanObject,
    mut v_a_4589_: *mut crate::leanh::LeanObject,
    mut v_a_4590_: *mut crate::leanh::LeanObject,
    mut v_a_4591_: *mut crate::leanh::LeanObject,
    mut v_a_4592_: *mut crate::leanh::LeanObject,
    mut v_a_4593_: *mut crate::leanh::LeanObject,
    mut v_a_4594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4595_ = l_Lean_Compiler_LCNF_Simp_isReturnOf(
        v_c_4585_,
        v_fvarId_4586_,
        v_a_4587_,
        v_a_4588_,
        v_a_4589_,
        v_a_4590_,
        v_a_4591_,
        v_a_4592_,
        v_a_4593_,
    );
    crate::leanh::lean_dec(v_a_4593_);
    crate::leanh::lean_dec_ref(v_a_4592_);
    crate::leanh::lean_dec(v_a_4591_);
    crate::leanh::lean_dec_ref(v_a_4590_);
    crate::leanh::lean_dec_ref(v_a_4589_);
    crate::leanh::lean_dec(v_a_4588_);
    crate::leanh::lean_dec_ref(v_a_4587_);
    crate::leanh::lean_dec(v_fvarId_4586_);
    return v_res_4595_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(
    mut v_value_4596_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_4602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_value_4596_) == 4 {
                    v_fvarId_4601_ = crate::leanh::lean_ctor_get(v_value_4596_, 0);
                    v_args_4602_ = crate::leanh::lean_ctor_get(v_value_4596_, 1);
                    v___x_4603_ = lean_array_get_size(v_args_4602_);
                    v___x_4604_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4605_ = lean_nat_dec_eq(v___x_4603_, v___x_4604_);
                    if v___x_4605_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_fvarId_4601_);
                        v___x_4606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4606_, 0, v_fvarId_4601_);
                        v___x_4607_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4607_, 0, v___x_4606_);
                        return v___x_4607_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4599_ = crate::leanh::lean_box(0);
                v___x_4600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4600_, 0, v___x_4599_);
                return v___x_4600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(
    mut v_value_4608_: *mut crate::leanh::LeanObject,
    mut v_a_4609_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4610_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_4608_);
    crate::leanh::lean_dec(v_value_4608_);
    return v_res_4610_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f(
    mut v_value_4611_: *mut crate::leanh::LeanObject,
    mut v_a_4612_: *mut crate::leanh::LeanObject,
    mut v_a_4613_: *mut crate::leanh::LeanObject,
    mut v_a_4614_: *mut crate::leanh::LeanObject,
    mut v_a_4615_: *mut crate::leanh::LeanObject,
    mut v_a_4616_: *mut crate::leanh::LeanObject,
    mut v_a_4617_: *mut crate::leanh::LeanObject,
    mut v_a_4618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4620_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_4611_);
    return v___x_4620_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(
    mut v_value_4621_: *mut crate::leanh::LeanObject,
    mut v_a_4622_: *mut crate::leanh::LeanObject,
    mut v_a_4623_: *mut crate::leanh::LeanObject,
    mut v_a_4624_: *mut crate::leanh::LeanObject,
    mut v_a_4625_: *mut crate::leanh::LeanObject,
    mut v_a_4626_: *mut crate::leanh::LeanObject,
    mut v_a_4627_: *mut crate::leanh::LeanObject,
    mut v_a_4628_: *mut crate::leanh::LeanObject,
    mut v_a_4629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4630_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(
        v_value_4621_,
        v_a_4622_,
        v_a_4623_,
        v_a_4624_,
        v_a_4625_,
        v_a_4626_,
        v_a_4627_,
        v_a_4628_,
    );
    crate::leanh::lean_dec(v_a_4628_);
    crate::leanh::lean_dec_ref(v_a_4627_);
    crate::leanh::lean_dec(v_a_4626_);
    crate::leanh::lean_dec_ref(v_a_4625_);
    crate::leanh::lean_dec_ref(v_a_4624_);
    crate::leanh::lean_dec(v_a_4623_);
    crate::leanh::lean_dec_ref(v_a_4622_);
    crate::leanh::lean_dec(v_value_4621_);
    return v_res_4630_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(
    mut v_a_4631_: *mut crate::leanh::LeanObject,
    mut v___x_4632_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4633_: *mut crate::leanh::LeanObject,
    mut v___y_4634_: *mut crate::leanh::LeanObject,
    mut v___y_4635_: *mut crate::leanh::LeanObject,
    mut v___y_4636_: *mut crate::leanh::LeanObject,
    mut v___y_4637_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_fvarId_4639_ = crate::leanh::lean_ctor_get(v_a_4631_, 0);
    v___x_4640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4640_, 0, v_fvarId_4633_);
    v___x_4641_ = lean_mk_empty_array_with_capacity(v___x_4632_);
    v___x_4642_ = lean_array_push(v___x_4641_, v___x_4640_);
    crate::leanh::lean_inc(v_fvarId_4639_);
    v___x_4643_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4643_, 0, v_fvarId_4639_);
    crate::leanh::lean_ctor_set(v___x_4643_, 1, v___x_4642_);
    v___x_4644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4644_, 0, v___x_4643_);
    return v___x_4644_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(
    mut v_a_4645_: *mut crate::leanh::LeanObject,
    mut v___x_4646_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4647_: *mut crate::leanh::LeanObject,
    mut v___y_4648_: *mut crate::leanh::LeanObject,
    mut v___y_4649_: *mut crate::leanh::LeanObject,
    mut v___y_4650_: *mut crate::leanh::LeanObject,
    mut v___y_4651_: *mut crate::leanh::LeanObject,
    mut v___y_4652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(
        v_a_4645_,
        v___x_4646_,
        v_fvarId_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
        v___y_4651_,
    );
    crate::leanh::lean_dec(v___y_4651_);
    crate::leanh::lean_dec_ref(v___y_4650_);
    crate::leanh::lean_dec(v___y_4649_);
    crate::leanh::lean_dec_ref(v___y_4648_);
    crate::leanh::lean_dec(v___x_4646_);
    crate::leanh::lean_dec_ref(v_a_4645_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(
    mut v_pu_4654_: u8,
    mut v_t_4655_: u8,
    mut v_args_4656_: *mut crate::leanh::LeanObject,
    mut v___y_4657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4659_ = lean_st_ref_get(v___y_4657_);
    v_subst_4660_ = crate::leanh::lean_ctor_get(v___x_4659_, 0);
    crate::leanh::lean_inc_ref(v_subst_4660_);
    crate::leanh::lean_dec(v___x_4659_);
    v___x_4661_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_4654_,
        v_subst_4660_,
        v_args_4656_,
        v_t_4655_,
    );
    crate::leanh::lean_dec_ref(v_subst_4660_);
    v___x_4662_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_4662_, 0, v___x_4661_);
    return v___x_4662_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(
    mut v_pu_4663_: *mut crate::leanh::LeanObject,
    mut v_t_4664_: *mut crate::leanh::LeanObject,
    mut v_args_4665_: *mut crate::leanh::LeanObject,
    mut v___y_4666_: *mut crate::leanh::LeanObject,
    mut v___y_4667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4668_: u8 = 0;
    let mut v_t_boxed_4669_: u8 = 0;
    let mut v_res_4670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4668_ = (crate::leanh::lean_unbox(v_pu_4663_) as u8);
    v_t_boxed_4669_ = (crate::leanh::lean_unbox(v_t_4664_) as u8);
    v_res_4670_ =
        l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(
            v_pu_boxed_4668_,
            v_t_boxed_4669_,
            v_args_4665_,
            v___y_4666_,
        );
    crate::leanh::lean_dec(v___y_4666_);
    return v_res_4670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(
    mut v_as_4671_: *mut crate::leanh::LeanObject,
    mut v_i_4672_: usize,
    mut v_stop_4673_: usize,
    mut v_b_4674_: *mut crate::leanh::LeanObject,
    mut v___y_4675_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: usize = 0;
    let mut v___x_4682_: usize = 0;
    let mut v___x_4684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4677_ = lean_usize_dec_eq(v_i_4672_, v_stop_4673_);
                if v___x_4677_ == 0 {
                    v___x_4678_ = lean_array_uget_borrowed(v_as_4671_, v_i_4672_);
                    crate::leanh::lean_inc(v___x_4678_);
                    v___x_4679_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_4678_, v___y_4675_);
                    if crate::leanh::lean_obj_tag(v___x_4679_) == 0 {
                        v_a_4680_ = crate::leanh::lean_ctor_get(v___x_4679_, 0);
                        crate::leanh::lean_inc(v_a_4680_);
                        crate::leanh::lean_dec_ref_known(v___x_4679_, 1);
                        v___x_4681_ = 1usize;
                        v___x_4682_ = lean_usize_add(v_i_4672_, v___x_4681_);
                        v_i_4672_ = v___x_4682_;
                        v_b_4674_ = v_a_4680_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4679_;
                    }
                } else {
                    v___x_4684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4684_, 0, v_b_4674_);
                    return v___x_4684_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(
    mut v_as_4685_: *mut crate::leanh::LeanObject,
    mut v_i_4686_: *mut crate::leanh::LeanObject,
    mut v_stop_4687_: *mut crate::leanh::LeanObject,
    mut v_b_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4691_: usize = 0;
    let mut v_stop_boxed_4692_: usize = 0;
    let mut v_res_4693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4691_ = crate::leanh::lean_unbox_usize(v_i_4686_);
    crate::leanh::lean_dec(v_i_4686_);
    v_stop_boxed_4692_ = crate::leanh::lean_unbox_usize(v_stop_4687_);
    crate::leanh::lean_dec(v_stop_4687_);
    v_res_4693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_4685_, v_i_boxed_4691_, v_stop_boxed_4692_, v_b_4688_, v___y_4689_);
    crate::leanh::lean_dec(v___y_4689_);
    crate::leanh::lean_dec_ref(v_as_4685_);
    return v_res_4693_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(
    mut v_as_4694_: *mut crate::leanh::LeanObject,
    mut v_i_4695_: usize,
    mut v_stop_4696_: usize,
) -> u8 {
    let mut v___x_4697_: u8 = 0;
    let mut v___x_4698_: u8 = 0;
    let mut v___y_4700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: usize = 0;
    let mut v___x_4702_: usize = 0;
    let mut v___x_4704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_4707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4697_ = lean_usize_dec_eq(v_i_4695_, v_stop_4696_);
                if v___x_4697_ == 0 {
                    v___x_4698_ = 1;
                    v___x_4704_ = lean_array_uget_borrowed(v_as_4694_, v_i_4695_);
                    match crate::leanh::lean_obj_tag(v___x_4704_) {
                        0 => {
                            v_code_4705_ = crate::leanh::lean_ctor_get(v___x_4704_, 2);
                            v___y_4700_ = v_code_4705_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_4706_ = crate::leanh::lean_ctor_get(v___x_4704_, 1);
                            v___y_4700_ = v_code_4706_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_4707_ = crate::leanh::lean_ctor_get(v___x_4704_, 0);
                            v___y_4700_ = v_code_4707_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_4708_ = 0;
                    return v___x_4708_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v___y_4700_) == 6 {
                    if v___x_4697_ == 0 {
                        v___x_4701_ = 1usize;
                        v___x_4702_ = lean_usize_add(v_i_4695_, v___x_4701_);
                        v_i_4695_ = v___x_4702_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_4698_;
                    }
                } else {
                    return v___x_4698_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11___boxed(
    mut v_as_4709_: *mut crate::leanh::LeanObject,
    mut v_i_4710_: *mut crate::leanh::LeanObject,
    mut v_stop_4711_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4712_: usize = 0;
    let mut v_stop_boxed_4713_: usize = 0;
    let mut v_res_4714_: u8 = 0;
    let mut v_r_4715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4712_ = crate::leanh::lean_unbox_usize(v_i_4710_);
    crate::leanh::lean_dec(v_i_4710_);
    v_stop_boxed_4713_ = crate::leanh::lean_unbox_usize(v_stop_4711_);
    crate::leanh::lean_dec(v_stop_4711_);
    v_res_4714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_4709_, v_i_boxed_4712_, v_stop_boxed_4713_);
    crate::leanh::lean_dec_ref(v_as_4709_);
    v_r_4715_ = crate::leanh::lean_box((v_res_4714_) as usize);
    return v_r_4715_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(
    mut v_pu_4716_: u8,
    mut v_t_4717_: u8,
    mut v_i_4718_: *mut crate::leanh::LeanObject,
    mut v_as_4719_: *mut crate::leanh::LeanObject,
    mut v___y_4720_: *mut crate::leanh::LeanObject,
    mut v___y_4721_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: usize = 0;
    let mut v___x_4734_: usize = 0;
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4746_: u8 = 0;
    let mut v___x_4748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4723_ = lean_array_get_size(v_as_4719_);
                v___x_4724_ = lean_nat_dec_lt(v_i_4718_, v___x_4723_);
                if v___x_4724_ == 0 {
                    crate::leanh::lean_dec(v_i_4718_);
                    v___x_4725_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4725_, 0, v_as_4719_);
                    return v___x_4725_;
                } else {
                    v_a_4726_ = lean_array_fget_borrowed(v_as_4719_, v_i_4718_);
                    v_type_4727_ = crate::leanh::lean_ctor_get(v_a_4726_, 2);
                    v___x_4728_ = lean_st_ref_get(v___y_4720_);
                    v_subst_4729_ = crate::leanh::lean_ctor_get(v___x_4728_, 0);
                    crate::leanh::lean_inc_ref(v_subst_4729_);
                    crate::leanh::lean_dec(v___x_4728_);
                    crate::leanh::lean_inc_ref(v_type_4727_);
                    v___x_4730_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4716_, v_subst_4729_, v_t_4717_, v_type_4727_);
                    crate::leanh::lean_dec_ref(v_subst_4729_);
                    crate::leanh::lean_inc(v_a_4726_);
                    v___x_4731_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_4716_, v_a_4726_, v___x_4730_, v___y_4721_);
                    if crate::leanh::lean_obj_tag(v___x_4731_) == 0 {
                        v_a_4732_ = crate::leanh::lean_ctor_get(v___x_4731_, 0);
                        crate::leanh::lean_inc(v_a_4732_);
                        crate::leanh::lean_dec_ref_known(v___x_4731_, 1);
                        v___x_4733_ = lean_ptr_addr(v_a_4726_);
                        v___x_4734_ = lean_ptr_addr(v_a_4732_);
                        v___x_4735_ = lean_usize_dec_eq(v___x_4733_, v___x_4734_);
                        if v___x_4735_ == 0 {
                            v___x_4736_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4737_ = lean_nat_add(v_i_4718_, v___x_4736_);
                            v___x_4738_ = lean_array_fset(v_as_4719_, v_i_4718_, v_a_4732_);
                            crate::leanh::lean_dec(v_i_4718_);
                            v_i_4718_ = v___x_4737_;
                            v_as_4719_ = v___x_4738_;
                            state = 0;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_4732_);
                            v___x_4740_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_4741_ = lean_nat_add(v_i_4718_, v___x_4740_);
                            crate::leanh::lean_dec(v_i_4718_);
                            v_i_4718_ = v___x_4741_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_as_4719_);
                        crate::leanh::lean_dec(v_i_4718_);
                        v_a_4743_ = crate::leanh::lean_ctor_get(v___x_4731_, 0);
                        v_isSharedCheck_4750_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4731_)) as u8;
                        if v_isSharedCheck_4750_ == 0 {
                            v___x_4745_ = v___x_4731_;
                            v_isShared_4746_ = v_isSharedCheck_4750_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4743_);
                            crate::leanh::lean_dec(v___x_4731_);
                            v___x_4745_ = crate::leanh::lean_box(0);
                            v_isShared_4746_ = v_isSharedCheck_4750_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_4746_ == 0 {
                    v___x_4748_ = v___x_4745_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4749_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
                    v___x_4748_ = v_reuseFailAlloc_4749_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4748_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg___boxed(
    mut v_pu_4751_: *mut crate::leanh::LeanObject,
    mut v_t_4752_: *mut crate::leanh::LeanObject,
    mut v_i_4753_: *mut crate::leanh::LeanObject,
    mut v_as_4754_: *mut crate::leanh::LeanObject,
    mut v___y_4755_: *mut crate::leanh::LeanObject,
    mut v___y_4756_: *mut crate::leanh::LeanObject,
    mut v___y_4757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4758_: u8 = 0;
    let mut v_t_boxed_4759_: u8 = 0;
    let mut v_res_4760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4758_ = (crate::leanh::lean_unbox(v_pu_4751_) as u8);
    v_t_boxed_4759_ = (crate::leanh::lean_unbox(v_t_4752_) as u8);
    v_res_4760_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_4758_, v_t_boxed_4759_, v_i_4753_, v_as_4754_, v___y_4755_, v___y_4756_);
    crate::leanh::lean_dec(v___y_4756_);
    crate::leanh::lean_dec(v___y_4755_);
    return v_res_4760_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(
    mut v_pu_4761_: u8,
    mut v_t_4762_: u8,
    mut v_ps_4763_: *mut crate::leanh::LeanObject,
    mut v___y_4764_: *mut crate::leanh::LeanObject,
    mut v___y_4765_: *mut crate::leanh::LeanObject,
    mut v___y_4766_: *mut crate::leanh::LeanObject,
    mut v___y_4767_: *mut crate::leanh::LeanObject,
    mut v___y_4768_: *mut crate::leanh::LeanObject,
    mut v___y_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4772_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4773_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_4761_, v_t_4762_, v___x_4772_, v_ps_4763_, v___y_4765_, v___y_4768_);
    return v___x_4773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(
    mut v_pu_4774_: *mut crate::leanh::LeanObject,
    mut v_t_4775_: *mut crate::leanh::LeanObject,
    mut v_ps_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
    mut v___y_4779_: *mut crate::leanh::LeanObject,
    mut v___y_4780_: *mut crate::leanh::LeanObject,
    mut v___y_4781_: *mut crate::leanh::LeanObject,
    mut v___y_4782_: *mut crate::leanh::LeanObject,
    mut v___y_4783_: *mut crate::leanh::LeanObject,
    mut v___y_4784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4785_: u8 = 0;
    let mut v_t_boxed_4786_: u8 = 0;
    let mut v_res_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4785_ = (crate::leanh::lean_unbox(v_pu_4774_) as u8);
    v_t_boxed_4786_ = (crate::leanh::lean_unbox(v_t_4775_) as u8);
    v_res_4787_ =
        l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(
            v_pu_boxed_4785_,
            v_t_boxed_4786_,
            v_ps_4776_,
            v___y_4777_,
            v___y_4778_,
            v___y_4779_,
            v___y_4780_,
            v___y_4781_,
            v___y_4782_,
            v___y_4783_,
        );
    crate::leanh::lean_dec(v___y_4783_);
    crate::leanh::lean_dec_ref(v___y_4782_);
    crate::leanh::lean_dec(v___y_4781_);
    crate::leanh::lean_dec_ref(v___y_4780_);
    crate::leanh::lean_dec_ref(v___y_4779_);
    crate::leanh::lean_dec(v___y_4778_);
    crate::leanh::lean_dec_ref(v___y_4777_);
    return v_res_4787_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(
    mut v_pu_4788_: u8,
    mut v_t_4789_: u8,
    mut v_decl_4790_: *mut crate::leanh::LeanObject,
    mut v___y_4791_: *mut crate::leanh::LeanObject,
    mut v___y_4792_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_type_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_4795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_type_4794_ = crate::leanh::lean_ctor_get(v_decl_4790_, 2);
    v_value_4795_ = crate::leanh::lean_ctor_get(v_decl_4790_, 3);
    v___x_4796_ = lean_st_ref_get(v___y_4791_);
    v_subst_4797_ = crate::leanh::lean_ctor_get(v___x_4796_, 0);
    crate::leanh::lean_inc_ref(v_subst_4797_);
    crate::leanh::lean_dec(v___x_4796_);
    v___x_4798_ = lean_st_ref_get(v___y_4791_);
    v_subst_4799_ = crate::leanh::lean_ctor_get(v___x_4798_, 0);
    crate::leanh::lean_inc_ref(v_subst_4799_);
    crate::leanh::lean_dec(v___x_4798_);
    crate::leanh::lean_inc_ref(v_type_4794_);
    v___x_4800_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_4788_,
        v_subst_4797_,
        v_t_4789_,
        v_type_4794_,
    );
    crate::leanh::lean_dec_ref(v_subst_4797_);
    crate::leanh::lean_inc(v_value_4795_);
    v___x_4801_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_4788_,
        v_subst_4799_,
        v_value_4795_,
        v_t_4789_,
    );
    crate::leanh::lean_dec_ref(v_subst_4799_);
    v___x_4802_ =
        l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(
            v_pu_4788_,
            v_decl_4790_,
            v___x_4800_,
            v___x_4801_,
            v___y_4792_,
        );
    return v___x_4802_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg___boxed(
    mut v_pu_4803_: *mut crate::leanh::LeanObject,
    mut v_t_4804_: *mut crate::leanh::LeanObject,
    mut v_decl_4805_: *mut crate::leanh::LeanObject,
    mut v___y_4806_: *mut crate::leanh::LeanObject,
    mut v___y_4807_: *mut crate::leanh::LeanObject,
    mut v___y_4808_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_4809_: u8 = 0;
    let mut v_t_boxed_4810_: u8 = 0;
    let mut v_res_4811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_4809_ = (crate::leanh::lean_unbox(v_pu_4803_) as u8);
    v_t_boxed_4810_ = (crate::leanh::lean_unbox(v_t_4804_) as u8);
    v_res_4811_ =
        l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(
            v_pu_boxed_4809_,
            v_t_boxed_4810_,
            v_decl_4805_,
            v___y_4806_,
            v___y_4807_,
        );
    crate::leanh::lean_dec(v___y_4807_);
    crate::leanh::lean_dec(v___y_4806_);
    return v_res_4811_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(
    mut v___y_4812_: *mut crate::leanh::LeanObject,
    mut v___f_4813_: *mut crate::leanh::LeanObject,
    mut v___y_4814_: *mut crate::leanh::LeanObject,
    mut v___y_4815_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4816_: *mut crate::leanh::LeanObject,
    mut v___y_4817_: *mut crate::leanh::LeanObject,
    mut v___y_4818_: *mut crate::leanh::LeanObject,
    mut v___y_4819_: *mut crate::leanh::LeanObject,
    mut v___y_4820_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4827_: u8 = 0;
    let mut v___x_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc(v_fvarId_4816_);
                v___x_4822_ =
                    l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_4816_, v___y_4812_);
                if crate::leanh::lean_obj_tag(v___x_4822_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4822_, 1);
                    crate::leanh::lean_inc(v___y_4820_);
                    crate::leanh::lean_inc_ref(v___y_4819_);
                    crate::leanh::lean_inc(v___y_4818_);
                    crate::leanh::lean_inc_ref(v___y_4817_);
                    crate::leanh::lean_inc_ref(v___y_4815_);
                    crate::leanh::lean_inc(v___y_4812_);
                    crate::leanh::lean_inc_ref(v___y_4814_);
                    v___x_4823_ = crate::leanh::lean_apply_9(
                        v___f_4813_,
                        v_fvarId_4816_,
                        v___y_4814_,
                        v___y_4812_,
                        v___y_4815_,
                        v___y_4817_,
                        v___y_4818_,
                        v___y_4819_,
                        v___y_4820_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_4823_;
                } else {
                    crate::leanh::lean_dec(v_fvarId_4816_);
                    crate::leanh::lean_dec_ref(v___f_4813_);
                    v_a_4824_ = crate::leanh::lean_ctor_get(v___x_4822_, 0);
                    v_isSharedCheck_4831_ = (!crate::leanh::lean_is_exclusive(v___x_4822_)) as u8;
                    if v_isSharedCheck_4831_ == 0 {
                        v___x_4826_ = v___x_4822_;
                        v_isShared_4827_ = v_isSharedCheck_4831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4824_);
                        crate::leanh::lean_dec(v___x_4822_);
                        v___x_4826_ = crate::leanh::lean_box(0);
                        v_isShared_4827_ = v_isSharedCheck_4831_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4827_ == 0 {
                    v___x_4829_ = v___x_4826_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
                    v___x_4829_ = v_reuseFailAlloc_4830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4829_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed(
    mut v___y_4832_: *mut crate::leanh::LeanObject,
    mut v___f_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
    mut v_fvarId_4836_: *mut crate::leanh::LeanObject,
    mut v___y_4837_: *mut crate::leanh::LeanObject,
    mut v___y_4838_: *mut crate::leanh::LeanObject,
    mut v___y_4839_: *mut crate::leanh::LeanObject,
    mut v___y_4840_: *mut crate::leanh::LeanObject,
    mut v___y_4841_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4842_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(
        v___y_4832_,
        v___f_4833_,
        v___y_4834_,
        v___y_4835_,
        v_fvarId_4836_,
        v___y_4837_,
        v___y_4838_,
        v___y_4839_,
        v___y_4840_,
    );
    crate::leanh::lean_dec(v___y_4840_);
    crate::leanh::lean_dec_ref(v___y_4839_);
    crate::leanh::lean_dec(v___y_4838_);
    crate::leanh::lean_dec_ref(v___y_4837_);
    crate::leanh::lean_dec_ref(v___y_4835_);
    crate::leanh::lean_dec_ref(v___y_4834_);
    crate::leanh::lean_dec(v___y_4832_);
    return v_res_4842_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(
    mut v_x_4843_: *mut crate::leanh::LeanObject,
    mut v_x_4844_: *mut crate::leanh::LeanObject,
    mut v_x_4845_: *mut crate::leanh::LeanObject,
    mut v_x_4846_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: u8 = 0;
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: u8 = 0;
    let mut v___x_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4847_ = crate::leanh::lean_ctor_get(v_x_4843_, 0);
                v_vs_4848_ = crate::leanh::lean_ctor_get(v_x_4843_, 1);
                v_isSharedCheck_4872_ = (!crate::leanh::lean_is_exclusive(v_x_4843_)) as u8;
                if v_isSharedCheck_4872_ == 0 {
                    v___x_4850_ = v_x_4843_;
                    v_isShared_4851_ = v_isSharedCheck_4872_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_4848_);
                    crate::leanh::lean_inc(v_ks_4847_);
                    crate::leanh::lean_dec(v_x_4843_);
                    v___x_4850_ = crate::leanh::lean_box(0);
                    v_isShared_4851_ = v_isSharedCheck_4872_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4852_ = lean_array_get_size(v_ks_4847_);
                v___x_4853_ = lean_nat_dec_lt(v_x_4844_, v___x_4852_);
                if v___x_4853_ == 0 {
                    crate::leanh::lean_dec(v_x_4844_);
                    v___x_4854_ = lean_array_push(v_ks_4847_, v_x_4845_);
                    v___x_4855_ = lean_array_push(v_vs_4848_, v_x_4846_);
                    if v_isShared_4851_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4850_, 1, v___x_4855_);
                        crate::leanh::lean_ctor_set(v___x_4850_, 0, v___x_4854_);
                        v___x_4857_ = v___x_4850_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4858_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4854_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4858_, 1, v___x_4855_);
                        v___x_4857_ = v_reuseFailAlloc_4858_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4859_ = lean_array_fget_borrowed(v_ks_4847_, v_x_4844_);
                    v___x_4860_ = lean_name_eq(v_x_4845_, v_k_x27_4859_);
                    if v___x_4860_ == 0 {
                        if v_isShared_4851_ == 0 {
                            v___x_4862_ = v___x_4850_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4866_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_ks_4847_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4866_, 1, v_vs_4848_);
                            v___x_4862_ = v_reuseFailAlloc_4866_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4867_ = lean_array_fset(v_ks_4847_, v_x_4844_, v_x_4845_);
                        v___x_4868_ = lean_array_fset(v_vs_4848_, v_x_4844_, v_x_4846_);
                        crate::leanh::lean_dec(v_x_4844_);
                        if v_isShared_4851_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_4850_, 1, v___x_4868_);
                            crate::leanh::lean_ctor_set(v___x_4850_, 0, v___x_4867_);
                            v___x_4870_ = v___x_4850_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4871_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4867_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_4871_, 1, v___x_4868_);
                            v___x_4870_ = v_reuseFailAlloc_4871_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4857_;
            }
            3 => {
                v___x_4863_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4864_ = lean_nat_add(v_x_4844_, v___x_4863_);
                crate::leanh::lean_dec(v_x_4844_);
                v_x_4843_ = v___x_4862_;
                v_x_4844_ = v___x_4864_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4870_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(
    mut v_n_4873_: *mut crate::leanh::LeanObject,
    mut v_k_4874_: *mut crate::leanh::LeanObject,
    mut v_v_4875_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4876_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_4877_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_4873_, v___x_4876_, v_k_4874_, v_v_4875_);
    return v___x_4877_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0()
-> u64 {
    let mut v___x_4878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: u64 = 0;
    v___x_4878_ = crate::leanh::lean_unsigned_to_nat(1723);
    v___x_4879_ = lean_uint64_of_nat(v___x_4878_);
    return v___x_4879_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_4880_: usize = 0;
    let mut v___x_4881_: usize = 0;
    let mut v___x_4882_: usize = 0;
    v___x_4880_ = 5usize;
    v___x_4881_ = 1usize;
    v___x_4882_ = lean_usize_shift_left(v___x_4881_, v___x_4880_);
    return v___x_4882_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_4883_: usize = 0;
    let mut v___x_4884_: usize = 0;
    let mut v___x_4885_: usize = 0;
    v___x_4883_ = 1usize;
    v___x_4884_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
    v___x_4885_ = lean_usize_sub(v___x_4884_, v___x_4883_);
    return v___x_4885_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4886_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_4886_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(
    mut v_x_4887_: *mut crate::leanh::LeanObject,
    mut v_x_4888_: usize,
    mut v_x_4889_: usize,
    mut v_x_4890_: *mut crate::leanh::LeanObject,
    mut v_x_4891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_4892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: usize = 0;
    let mut v___x_4894_: usize = 0;
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: usize = 0;
    let mut v_j_4897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: u8 = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v_v_4903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4917_: u8 = 0;
    let mut v___x_4918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_node_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v___x_4928_: usize = 0;
    let mut v___x_4929_: usize = 0;
    let mut v___x_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4934_: u8 = 0;
    let mut v___x_4935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut v_unused_4937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4947_: u8 = 0;
    let mut v_ks_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: usize = 0;
    let mut v___x_4954_: u8 = 0;
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: u8 = 0;
    let mut v_reuseFailAlloc_4958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4887_) == 0 {
                    v_es_4892_ = crate::leanh::lean_ctor_get(v_x_4887_, 0);
                    v___x_4893_ = 5usize;
                    v___x_4894_ = 1usize;
                    v___x_4895_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_4896_ = lean_usize_land(v_x_4888_, v___x_4895_);
                    v_j_4897_ = lean_usize_to_nat(v___x_4896_);
                    v___x_4898_ = lean_array_get_size(v_es_4892_);
                    v___x_4899_ = lean_nat_dec_lt(v_j_4897_, v___x_4898_);
                    if v___x_4899_ == 0 {
                        crate::leanh::lean_dec(v_j_4897_);
                        crate::leanh::lean_dec(v_x_4891_);
                        crate::leanh::lean_dec(v_x_4890_);
                        return v_x_4887_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_4892_);
                        v_isSharedCheck_4936_ = (!crate::leanh::lean_is_exclusive(v_x_4887_)) as u8;
                        if v_isSharedCheck_4936_ == 0 {
                            v_unused_4937_ = crate::leanh::lean_ctor_get(v_x_4887_, 0);
                            crate::leanh::lean_dec(v_unused_4937_);
                            v___x_4901_ = v_x_4887_;
                            v_isShared_4902_ = v_isSharedCheck_4936_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_4887_);
                            v___x_4901_ = crate::leanh::lean_box(0);
                            v_isShared_4902_ = v_isSharedCheck_4936_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4938_ = crate::leanh::lean_ctor_get(v_x_4887_, 0);
                    v_vs_4939_ = crate::leanh::lean_ctor_get(v_x_4887_, 1);
                    v_isSharedCheck_4959_ = (!crate::leanh::lean_is_exclusive(v_x_4887_)) as u8;
                    if v_isSharedCheck_4959_ == 0 {
                        v___x_4941_ = v_x_4887_;
                        v_isShared_4942_ = v_isSharedCheck_4959_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_4939_);
                        crate::leanh::lean_inc(v_ks_4938_);
                        crate::leanh::lean_dec(v_x_4887_);
                        v___x_4941_ = crate::leanh::lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4959_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4903_ = lean_array_fget(v_es_4892_, v_j_4897_);
                v___x_4904_ = crate::leanh::lean_box(0);
                v_xs_x27_4905_ = lean_array_fset(v_es_4892_, v_j_4897_, v___x_4904_);
                match crate::leanh::lean_obj_tag(v_v_4903_) {
                    0 => {
                        v_key_4912_ = crate::leanh::lean_ctor_get(v_v_4903_, 0);
                        v_val_4913_ = crate::leanh::lean_ctor_get(v_v_4903_, 1);
                        v_isSharedCheck_4923_ = (!crate::leanh::lean_is_exclusive(v_v_4903_)) as u8;
                        if v_isSharedCheck_4923_ == 0 {
                            v___x_4915_ = v_v_4903_;
                            v_isShared_4916_ = v_isSharedCheck_4923_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_4913_);
                            crate::leanh::lean_inc(v_key_4912_);
                            crate::leanh::lean_dec(v_v_4903_);
                            v___x_4915_ = crate::leanh::lean_box(0);
                            v_isShared_4916_ = v_isSharedCheck_4923_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4924_ = crate::leanh::lean_ctor_get(v_v_4903_, 0);
                        v_isSharedCheck_4934_ = (!crate::leanh::lean_is_exclusive(v_v_4903_)) as u8;
                        if v_isSharedCheck_4934_ == 0 {
                            v___x_4926_ = v_v_4903_;
                            v_isShared_4927_ = v_isSharedCheck_4934_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_4924_);
                            crate::leanh::lean_dec(v_v_4903_);
                            v___x_4926_ = crate::leanh::lean_box(0);
                            v_isShared_4927_ = v_isSharedCheck_4934_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4935_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_4935_, 0, v_x_4890_);
                        crate::leanh::lean_ctor_set(v___x_4935_, 1, v_x_4891_);
                        v___y_4907_ = v___x_4935_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4908_ = lean_array_fset(v_xs_x27_4905_, v_j_4897_, v___y_4907_);
                crate::leanh::lean_dec(v_j_4897_);
                if v_isShared_4902_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4901_, 0, v___x_4908_);
                    v___x_4910_ = v___x_4901_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
                    v___x_4910_ = v_reuseFailAlloc_4911_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4910_;
            }
            4 => {
                v___x_4917_ = lean_name_eq(v_x_4890_, v_key_4912_);
                if v___x_4917_ == 0 {
                    crate::leanh::lean_del_object(v___x_4915_);
                    v___x_4918_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4912_,
                        v_val_4913_,
                        v_x_4890_,
                        v_x_4891_,
                    );
                    v___x_4919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4919_, 0, v___x_4918_);
                    v___y_4907_ = v___x_4919_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_4913_);
                    crate::leanh::lean_dec(v_key_4912_);
                    if v_isShared_4916_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4915_, 1, v_x_4891_);
                        crate::leanh::lean_ctor_set(v___x_4915_, 0, v_x_4890_);
                        v___x_4921_ = v___x_4915_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4922_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_x_4890_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_x_4891_);
                        v___x_4921_ = v_reuseFailAlloc_4922_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4907_ = v___x_4921_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4928_ = lean_usize_shift_right(v_x_4888_, v___x_4893_);
                v___x_4929_ = lean_usize_add(v_x_4889_, v___x_4894_);
                v___x_4930_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_node_4924_, v___x_4928_, v___x_4929_, v_x_4890_, v_x_4891_);
                if v_isShared_4927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4926_, 0, v___x_4930_);
                    v___x_4932_ = v___x_4926_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4933_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4930_);
                    v___x_4932_ = v_reuseFailAlloc_4933_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4907_ = v___x_4932_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4942_ == 0 {
                    v___x_4944_ = v___x_4941_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4958_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_ks_4938_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4958_, 1, v_vs_4939_);
                    v___x_4944_ = v_reuseFailAlloc_4958_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4945_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v___x_4944_, v_x_4890_, v_x_4891_);
                v___x_4953_ = 7usize;
                v___x_4954_ = lean_usize_dec_le(v___x_4953_, v_x_4889_);
                if v___x_4954_ == 0 {
                    v___x_4955_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4945_);
                    v___x_4956_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_4957_ = lean_nat_dec_lt(v___x_4955_, v___x_4956_);
                    crate::leanh::lean_dec(v___x_4955_);
                    v___y_4947_ = v___x_4957_;
                    state = 10;
                    continue;
                } else {
                    v___y_4947_ = v___x_4954_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4947_ == 0 {
                    v_ks_4948_ = crate::leanh::lean_ctor_get(v_newNode_4945_, 0);
                    crate::leanh::lean_inc_ref(v_ks_4948_);
                    v_vs_4949_ = crate::leanh::lean_ctor_get(v_newNode_4945_, 1);
                    crate::leanh::lean_inc_ref(v_vs_4949_);
                    crate::leanh::lean_dec_ref(v_newNode_4945_);
                    v___x_4950_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4951_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2);
                    v___x_4952_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_4889_, v_ks_4948_, v_vs_4949_, v___x_4950_, v___x_4951_);
                    crate::leanh::lean_dec_ref(v_vs_4949_);
                    crate::leanh::lean_dec_ref(v_ks_4948_);
                    return v___x_4952_;
                } else {
                    return v_newNode_4945_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(
    mut v_depth_4960_: usize,
    mut v_keys_4961_: *mut crate::leanh::LeanObject,
    mut v_vals_4962_: *mut crate::leanh::LeanObject,
    mut v_i_4963_: *mut crate::leanh::LeanObject,
    mut v_entries_4964_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: u8 = 0;
    let mut v_k_4967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4970_: u64 = 0;
    let mut v_h_4971_: usize = 0;
    let mut v___x_4972_: usize = 0;
    let mut v___x_4973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: usize = 0;
    let mut v___x_4975_: usize = 0;
    let mut v___x_4976_: usize = 0;
    let mut v_h_4977_: usize = 0;
    let mut v___x_4978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: u64 = 0;
    let mut v_hash_4982_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4965_ = lean_array_get_size(v_keys_4961_);
                v___x_4966_ = lean_nat_dec_lt(v_i_4963_, v___x_4965_);
                if v___x_4966_ == 0 {
                    crate::leanh::lean_dec(v_i_4963_);
                    return v_entries_4964_;
                } else {
                    v_k_4967_ = lean_array_fget_borrowed(v_keys_4961_, v_i_4963_);
                    v_v_4968_ = lean_array_fget_borrowed(v_vals_4962_, v_i_4963_);
                    if crate::leanh::lean_obj_tag(v_k_4967_) == 0 {
                        v___x_4981_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
                        v___y_4970_ = v___x_4981_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4982_ = crate::leanh::lean_ctor_get_uint64(
                            v_k_4967_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4970_ = v_hash_4982_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4971_ = lean_uint64_to_usize(v___y_4970_);
                v___x_4972_ = 5usize;
                v___x_4973_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4974_ = 1usize;
                v___x_4975_ = lean_usize_sub(v_depth_4960_, v___x_4974_);
                v___x_4976_ = lean_usize_mul(v___x_4972_, v___x_4975_);
                v_h_4977_ = lean_usize_shift_right(v_h_4971_, v___x_4976_);
                v___x_4978_ = lean_nat_add(v_i_4963_, v___x_4973_);
                crate::leanh::lean_dec(v_i_4963_);
                crate::leanh::lean_inc(v_v_4968_);
                crate::leanh::lean_inc(v_k_4967_);
                v___x_4979_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_entries_4964_, v_h_4977_, v_depth_4960_, v_k_4967_, v_v_4968_);
                v_i_4963_ = v___x_4978_;
                v_entries_4964_ = v___x_4979_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___boxed(
    mut v_depth_4983_: *mut crate::leanh::LeanObject,
    mut v_keys_4984_: *mut crate::leanh::LeanObject,
    mut v_vals_4985_: *mut crate::leanh::LeanObject,
    mut v_i_4986_: *mut crate::leanh::LeanObject,
    mut v_entries_4987_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_4988_: usize = 0;
    let mut v_res_4989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4988_ = crate::leanh::lean_unbox_usize(v_depth_4983_);
    crate::leanh::lean_dec(v_depth_4983_);
    v_res_4989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_4988_, v_keys_4984_, v_vals_4985_, v_i_4986_, v_entries_4987_);
    crate::leanh::lean_dec_ref(v_vals_4985_);
    crate::leanh::lean_dec_ref(v_keys_4984_);
    return v_res_4989_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(
    mut v_x_4990_: *mut crate::leanh::LeanObject,
    mut v_x_4991_: *mut crate::leanh::LeanObject,
    mut v_x_4992_: *mut crate::leanh::LeanObject,
    mut v_x_4993_: *mut crate::leanh::LeanObject,
    mut v_x_4994_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_47256__boxed_4995_: usize = 0;
    let mut v_x_47257__boxed_4996_: usize = 0;
    let mut v_res_4997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_47256__boxed_4995_ = crate::leanh::lean_unbox_usize(v_x_4991_);
    crate::leanh::lean_dec(v_x_4991_);
    v_x_47257__boxed_4996_ = crate::leanh::lean_unbox_usize(v_x_4992_);
    crate::leanh::lean_dec(v_x_4992_);
    v_res_4997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_4990_, v_x_47256__boxed_4995_, v_x_47257__boxed_4996_, v_x_4993_, v_x_4994_);
    return v_res_4997_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(
    mut v_x_4998_: *mut crate::leanh::LeanObject,
    mut v_x_4999_: *mut crate::leanh::LeanObject,
    mut v_x_5000_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_5002_: u64 = 0;
    let mut v___x_5003_: usize = 0;
    let mut v___x_5004_: usize = 0;
    let mut v___x_5005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: u64 = 0;
    let mut v_hash_5007_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_4999_) == 0 {
                    v___x_5006_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
                    v___y_5002_ = v___x_5006_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5007_ = crate::leanh::lean_ctor_get_uint64(
                        v_x_4999_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5002_ = v_hash_5007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5003_ = lean_uint64_to_usize(v___y_5002_);
                v___x_5004_ = 1usize;
                v___x_5005_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_4998_, v___x_5003_, v___x_5004_, v_x_4999_, v_x_5000_);
                return v___x_5005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(
    mut v_a_5008_: *mut crate::leanh::LeanObject,
    mut v_b_5009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_5010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5015_: u8 = 0;
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5010_ = crate::leanh::lean_ctor_get(v_a_5008_, 0);
                v_start_5011_ = crate::leanh::lean_ctor_get(v_a_5008_, 1);
                v_stop_5012_ = crate::leanh::lean_ctor_get(v_a_5008_, 2);
                v_isSharedCheck_5025_ = (!crate::leanh::lean_is_exclusive(v_a_5008_)) as u8;
                if v_isSharedCheck_5025_ == 0 {
                    v___x_5014_ = v_a_5008_;
                    v_isShared_5015_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_5012_);
                    crate::leanh::lean_inc(v_start_5011_);
                    crate::leanh::lean_inc(v_array_5010_);
                    crate::leanh::lean_dec(v_a_5008_);
                    v___x_5014_ = crate::leanh::lean_box(0);
                    v_isShared_5015_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5016_ = lean_nat_dec_lt(v_start_5011_, v_stop_5012_);
                if v___x_5016_ == 0 {
                    crate::leanh::lean_del_object(v___x_5014_);
                    crate::leanh::lean_dec(v_stop_5012_);
                    crate::leanh::lean_dec(v_start_5011_);
                    crate::leanh::lean_dec_ref(v_array_5010_);
                    return v_b_5009_;
                } else {
                    v___x_5017_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5018_ = lean_nat_add(v_start_5011_, v___x_5017_);
                    crate::leanh::lean_inc_ref(v_array_5010_);
                    if v_isShared_5015_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5014_, 1, v___x_5018_);
                        v___x_5020_ = v___x_5014_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5024_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_array_5010_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5018_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5024_, 2, v_stop_5012_);
                        v___x_5020_ = v_reuseFailAlloc_5024_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5021_ = lean_array_fget(v_array_5010_, v_start_5011_);
                crate::leanh::lean_dec(v_start_5011_);
                crate::leanh::lean_dec_ref(v_array_5010_);
                v___x_5022_ = lean_array_push(v_b_5009_, v___x_5021_);
                v_a_5008_ = v___x_5020_;
                v_b_5009_ = v___x_5022_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(
    mut v_as_5026_: *mut crate::leanh::LeanObject,
    mut v_sz_5027_: usize,
    mut v_i_5028_: usize,
    mut v_b_5029_: *mut crate::leanh::LeanObject,
    mut v___y_5030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5032_: u8 = 0;
    let mut v___x_5033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_5036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5041_: u8 = 0;
    let mut v___x_5042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_5045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_5046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_5047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_5048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_5049_: u8 = 0;
    let mut v_visited_5050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_5051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_5052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: usize = 0;
    let mut v___x_5066_: usize = 0;
    let mut v_reuseFailAlloc_5068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5070_: u8 = 0;
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut v_unused_5072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5032_ = lean_usize_dec_lt(v_i_5028_, v_sz_5027_);
                if v___x_5032_ == 0 {
                    v___x_5033_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5033_, 0, v_b_5029_);
                    return v___x_5033_;
                } else {
                    v_array_5034_ = crate::leanh::lean_ctor_get(v_b_5029_, 0);
                    v_start_5035_ = crate::leanh::lean_ctor_get(v_b_5029_, 1);
                    v_stop_5036_ = crate::leanh::lean_ctor_get(v_b_5029_, 2);
                    v___x_5037_ = lean_nat_dec_lt(v_start_5035_, v_stop_5036_);
                    if v___x_5037_ == 0 {
                        v___x_5038_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5038_, 0, v_b_5029_);
                        return v___x_5038_;
                    } else {
                        crate::leanh::lean_inc(v_stop_5036_);
                        crate::leanh::lean_inc(v_start_5035_);
                        crate::leanh::lean_inc_ref(v_array_5034_);
                        v_isSharedCheck_5071_ = (!crate::leanh::lean_is_exclusive(v_b_5029_)) as u8;
                        if v_isSharedCheck_5071_ == 0 {
                            v_unused_5072_ = crate::leanh::lean_ctor_get(v_b_5029_, 2);
                            crate::leanh::lean_dec(v_unused_5072_);
                            v_unused_5073_ = crate::leanh::lean_ctor_get(v_b_5029_, 1);
                            crate::leanh::lean_dec(v_unused_5073_);
                            v_unused_5074_ = crate::leanh::lean_ctor_get(v_b_5029_, 0);
                            crate::leanh::lean_dec(v_unused_5074_);
                            v___x_5040_ = v_b_5029_;
                            v_isShared_5041_ = v_isSharedCheck_5071_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_5029_);
                            v___x_5040_ = crate::leanh::lean_box(0);
                            v_isShared_5041_ = v_isSharedCheck_5071_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5042_ = lean_st_ref_take(v___y_5030_);
                v_a_5043_ = lean_array_uget_borrowed(v_as_5026_, v_i_5028_);
                v_fvarId_5044_ = crate::leanh::lean_ctor_get(v_a_5043_, 0);
                v_subst_5045_ = crate::leanh::lean_ctor_get(v___x_5042_, 0);
                v_used_5046_ = crate::leanh::lean_ctor_get(v___x_5042_, 1);
                v_binderRenaming_5047_ = crate::leanh::lean_ctor_get(v___x_5042_, 2);
                v_funDeclInfoMap_5048_ = crate::leanh::lean_ctor_get(v___x_5042_, 3);
                v_simplified_5049_ = crate::leanh::lean_ctor_get_uint8(
                    v___x_5042_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_visited_5050_ = crate::leanh::lean_ctor_get(v___x_5042_, 4);
                v_inline_5051_ = crate::leanh::lean_ctor_get(v___x_5042_, 5);
                v_inlineLocal_5052_ = crate::leanh::lean_ctor_get(v___x_5042_, 6);
                v_isSharedCheck_5070_ = (!crate::leanh::lean_is_exclusive(v___x_5042_)) as u8;
                if v_isSharedCheck_5070_ == 0 {
                    v___x_5054_ = v___x_5042_;
                    v_isShared_5055_ = v_isSharedCheck_5070_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_inlineLocal_5052_);
                    crate::leanh::lean_inc(v_inline_5051_);
                    crate::leanh::lean_inc(v_visited_5050_);
                    crate::leanh::lean_inc(v_funDeclInfoMap_5048_);
                    crate::leanh::lean_inc(v_binderRenaming_5047_);
                    crate::leanh::lean_inc(v_used_5046_);
                    crate::leanh::lean_inc(v_subst_5045_);
                    crate::leanh::lean_dec(v___x_5042_);
                    v___x_5054_ = crate::leanh::lean_box(0);
                    v_isShared_5055_ = v_isSharedCheck_5070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5056_ = lean_array_fget_borrowed(v_array_5034_, v_start_5035_);
                crate::leanh::lean_inc(v___x_5056_);
                crate::leanh::lean_inc(v_fvarId_5044_);
                v___x_5057_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_5045_, v_fvarId_5044_, v___x_5056_);
                if v_isShared_5055_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5054_, 0, v___x_5057_);
                    v___x_5059_ = v___x_5054_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5069_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5057_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 1, v_used_5046_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 2, v_binderRenaming_5047_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 3, v_funDeclInfoMap_5048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 4, v_visited_5050_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 5, v_inline_5051_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5069_, 6, v_inlineLocal_5052_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_5069_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_5049_,
                    );
                    v___x_5059_ = v_reuseFailAlloc_5069_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5060_ = lean_st_ref_set(v___y_5030_, v___x_5059_);
                v___x_5061_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_5062_ = lean_nat_add(v_start_5035_, v___x_5061_);
                crate::leanh::lean_dec(v_start_5035_);
                if v_isShared_5041_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5040_, 1, v___x_5062_);
                    v___x_5064_ = v___x_5040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5068_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_array_5034_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 1, v___x_5062_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5068_, 2, v_stop_5036_);
                    v___x_5064_ = v_reuseFailAlloc_5068_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5065_ = 1usize;
                v___x_5066_ = lean_usize_add(v_i_5028_, v___x_5065_);
                v_i_5028_ = v___x_5066_;
                v_b_5029_ = v___x_5064_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg___boxed(
    mut v_as_5075_: *mut crate::leanh::LeanObject,
    mut v_sz_5076_: *mut crate::leanh::LeanObject,
    mut v_i_5077_: *mut crate::leanh::LeanObject,
    mut v_b_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5081_: usize = 0;
    let mut v_i_boxed_5082_: usize = 0;
    let mut v_res_5083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5081_ = crate::leanh::lean_unbox_usize(v_sz_5076_);
    crate::leanh::lean_dec(v_sz_5076_);
    v_i_boxed_5082_ = crate::leanh::lean_unbox_usize(v_i_5077_);
    crate::leanh::lean_dec(v_i_5077_);
    v_res_5083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_5075_, v_sz_boxed_5081_, v_i_boxed_5082_, v_b_5078_, v___y_5079_);
    crate::leanh::lean_dec(v___y_5079_);
    crate::leanh::lean_dec_ref(v_as_5075_);
    return v_res_5083_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(
    mut v_as_5084_: *mut crate::leanh::LeanObject,
    mut v_i_5085_: usize,
    mut v_stop_5086_: usize,
    mut v_b_5087_: *mut crate::leanh::LeanObject,
    mut v___y_5088_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5090_: u8 = 0;
    let mut v___x_5091_: u8 = 0;
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: usize = 0;
    let mut v___x_5096_: usize = 0;
    let mut v___x_5098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5090_ = lean_usize_dec_eq(v_i_5085_, v_stop_5086_);
                if v___x_5090_ == 0 {
                    v___x_5091_ = 0;
                    v___x_5092_ = lean_array_uget_borrowed(v_as_5084_, v_i_5085_);
                    v___x_5093_ = l_Lean_Compiler_LCNF_eraseParam___redArg(
                        v___x_5091_,
                        v___x_5092_,
                        v___y_5088_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5093_) == 0 {
                        v_a_5094_ = crate::leanh::lean_ctor_get(v___x_5093_, 0);
                        crate::leanh::lean_inc(v_a_5094_);
                        crate::leanh::lean_dec_ref_known(v___x_5093_, 1);
                        v___x_5095_ = 1usize;
                        v___x_5096_ = lean_usize_add(v_i_5085_, v___x_5095_);
                        v_i_5085_ = v___x_5096_;
                        v_b_5087_ = v_a_5094_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5093_;
                    }
                } else {
                    v___x_5098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5098_, 0, v_b_5087_);
                    return v___x_5098_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(
    mut v_as_5099_: *mut crate::leanh::LeanObject,
    mut v_i_5100_: *mut crate::leanh::LeanObject,
    mut v_stop_5101_: *mut crate::leanh::LeanObject,
    mut v_b_5102_: *mut crate::leanh::LeanObject,
    mut v___y_5103_: *mut crate::leanh::LeanObject,
    mut v___y_5104_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5105_: usize = 0;
    let mut v_stop_boxed_5106_: usize = 0;
    let mut v_res_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5105_ = crate::leanh::lean_unbox_usize(v_i_5100_);
    crate::leanh::lean_dec(v_i_5100_);
    v_stop_boxed_5106_ = crate::leanh::lean_unbox_usize(v_stop_5101_);
    crate::leanh::lean_dec(v_stop_5101_);
    v_res_5107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_5099_, v_i_boxed_5105_, v_stop_boxed_5106_, v_b_5102_, v___y_5103_);
    crate::leanh::lean_dec(v___y_5103_);
    crate::leanh::lean_dec_ref(v_as_5099_);
    return v_res_5107_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5108_ = 0;
    v___x_5109_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5108_);
    return v___x_5109_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(
    mut v_msg_5110_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5111_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0,
    );
    v___x_5112_ = lean_panic_fn_borrowed(v___x_5111_, v_msg_5110_);
    return v___x_5112_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(
    mut v_as_5113_: *mut crate::leanh::LeanObject,
    mut v_i_5114_: usize,
    mut v_stop_5115_: usize,
    mut v___y_5116_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5118_: u8 = 0;
    let mut v___x_5119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_5120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5127_: usize = 0;
    let mut v___x_5128_: usize = 0;
    let mut v___x_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5118_ = lean_usize_dec_eq(v_i_5114_, v_stop_5115_);
                if v___x_5118_ == 0 {
                    v___x_5119_ = lean_array_uget_borrowed(v_as_5113_, v_i_5114_);
                    v_type_5120_ = crate::leanh::lean_ctor_get(v___x_5119_, 2);
                    v___x_5121_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(
                        v_type_5120_,
                        v___y_5116_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5121_) == 0 {
                        v_a_5122_ = crate::leanh::lean_ctor_get(v___x_5121_, 0);
                        v_isSharedCheck_5133_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5121_)) as u8;
                        if v_isSharedCheck_5133_ == 0 {
                            v___x_5124_ = v___x_5121_;
                            v_isShared_5125_ = v_isSharedCheck_5133_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5122_);
                            crate::leanh::lean_dec(v___x_5121_);
                            v___x_5124_ = crate::leanh::lean_box(0);
                            v_isShared_5125_ = v_isSharedCheck_5133_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_5121_;
                    }
                } else {
                    v___x_5134_ = 0;
                    v___x_5135_ = crate::leanh::lean_box((v___x_5134_) as usize);
                    v___x_5136_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5136_, 0, v___x_5135_);
                    return v___x_5136_;
                }
            }
            1 => {
                v___x_5126_ = (crate::leanh::lean_unbox(v_a_5122_) as u8);
                if v___x_5126_ == 0 {
                    crate::leanh::lean_del_object(v___x_5124_);
                    crate::leanh::lean_dec(v_a_5122_);
                    v___x_5127_ = 1usize;
                    v___x_5128_ = lean_usize_add(v_i_5114_, v___x_5127_);
                    v_i_5114_ = v___x_5128_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5125_ == 0 {
                        v___x_5131_ = v___x_5124_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5132_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5122_);
                        v___x_5131_ = v_reuseFailAlloc_5132_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5131_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg___boxed(
    mut v_as_5137_: *mut crate::leanh::LeanObject,
    mut v_i_5138_: *mut crate::leanh::LeanObject,
    mut v_stop_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5142_: usize = 0;
    let mut v_stop_boxed_5143_: usize = 0;
    let mut v_res_5144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5142_ = crate::leanh::lean_unbox_usize(v_i_5138_);
    crate::leanh::lean_dec(v_i_5138_);
    v_stop_boxed_5143_ = crate::leanh::lean_unbox_usize(v_stop_5139_);
    crate::leanh::lean_dec(v_stop_5139_);
    v_res_5144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_5137_, v_i_boxed_5142_, v_stop_boxed_5143_, v___y_5140_);
    crate::leanh::lean_dec(v___y_5140_);
    crate::leanh::lean_dec_ref(v_as_5137_);
    return v_res_5144_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(
    mut v_as_5145_: *mut crate::leanh::LeanObject,
    mut v_i_5146_: usize,
    mut v_stop_5147_: usize,
    mut v_b_5148_: *mut crate::leanh::LeanObject,
    mut v___y_5149_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5151_: u8 = 0;
    let mut v___x_5152_: u8 = 0;
    let mut v___x_5153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: usize = 0;
    let mut v___x_5157_: usize = 0;
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5151_ = lean_usize_dec_eq(v_i_5146_, v_stop_5147_);
                if v___x_5151_ == 0 {
                    v___x_5152_ = 0;
                    v___x_5153_ = lean_array_uget_borrowed(v_as_5145_, v_i_5146_);
                    v___x_5154_ = l_Lean_Compiler_LCNF_eraseParam___redArg(
                        v___x_5152_,
                        v___x_5153_,
                        v___y_5149_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5154_) == 0 {
                        v_a_5155_ = crate::leanh::lean_ctor_get(v___x_5154_, 0);
                        crate::leanh::lean_inc(v_a_5155_);
                        crate::leanh::lean_dec_ref_known(v___x_5154_, 1);
                        v___x_5156_ = 1usize;
                        v___x_5157_ = lean_usize_add(v_i_5146_, v___x_5156_);
                        v_i_5146_ = v___x_5157_;
                        v_b_5148_ = v_a_5155_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5154_;
                    }
                } else {
                    v___x_5159_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5159_, 0, v_b_5148_);
                    return v___x_5159_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(
    mut v_as_5160_: *mut crate::leanh::LeanObject,
    mut v_i_5161_: *mut crate::leanh::LeanObject,
    mut v_stop_5162_: *mut crate::leanh::LeanObject,
    mut v_b_5163_: *mut crate::leanh::LeanObject,
    mut v___y_5164_: *mut crate::leanh::LeanObject,
    mut v___y_5165_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5166_: usize = 0;
    let mut v_stop_boxed_5167_: usize = 0;
    let mut v_res_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5166_ = crate::leanh::lean_unbox_usize(v_i_5161_);
    crate::leanh::lean_dec(v_i_5161_);
    v_stop_boxed_5167_ = crate::leanh::lean_unbox_usize(v_stop_5162_);
    crate::leanh::lean_dec(v_stop_5162_);
    v_res_5168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_5160_, v_i_boxed_5166_, v_stop_boxed_5167_, v_b_5163_, v___y_5164_);
    crate::leanh::lean_dec(v___y_5164_);
    crate::leanh::lean_dec_ref(v_as_5160_);
    return v_res_5168_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(
    mut v_as_5169_: *mut crate::leanh::LeanObject,
    mut v_i_5170_: usize,
    mut v_stop_5171_: usize,
    mut v_b_5172_: *mut crate::leanh::LeanObject,
    mut v___y_5173_: *mut crate::leanh::LeanObject,
    mut v___y_5174_: *mut crate::leanh::LeanObject,
    mut v___y_5175_: *mut crate::leanh::LeanObject,
    mut v___y_5176_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_5179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: usize = 0;
    let mut v___x_5181_: usize = 0;
    let mut v___y_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: u8 = 0;
    let mut v___x_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: u8 = 0;
    let mut v___x_5193_: u8 = 0;
    let mut v___x_5194_: usize = 0;
    let mut v___x_5195_: usize = 0;
    let mut v___x_5196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: usize = 0;
    let mut v___x_5198_: usize = 0;
    let mut v___x_5199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5186_ = lean_usize_dec_eq(v_i_5170_, v_stop_5171_);
                if v___x_5186_ == 0 {
                    v___x_5187_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_5188_ = lean_array_uget_borrowed(v_as_5169_, v_i_5170_);
                    v___x_5189_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_5188_);
                    v___x_5190_ = lean_array_get_size(v___x_5189_);
                    v___x_5191_ = crate::leanh::lean_box(0);
                    v___x_5192_ = lean_nat_dec_lt(v___x_5187_, v___x_5190_);
                    if v___x_5192_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_5189_);
                        v_a_5179_ = v___x_5191_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5193_ = lean_nat_dec_le(v___x_5190_, v___x_5190_);
                        if v___x_5193_ == 0 {
                            if v___x_5192_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_5189_);
                                v_a_5179_ = v___x_5191_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5194_ = 0usize;
                                v___x_5195_ = lean_usize_of_nat(v___x_5190_);
                                v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_5189_, v___x_5194_, v___x_5195_, v___x_5191_, v___y_5174_);
                                crate::leanh::lean_dec_ref(v___x_5189_);
                                v___y_5184_ = v___x_5196_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_5197_ = 0usize;
                            v___x_5198_ = lean_usize_of_nat(v___x_5190_);
                            v___x_5199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_5189_, v___x_5197_, v___x_5198_, v___x_5191_, v___y_5174_);
                            crate::leanh::lean_dec_ref(v___x_5189_);
                            v___y_5184_ = v___x_5199_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_5200_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5200_, 0, v_b_5172_);
                    return v___x_5200_;
                }
            }
            1 => {
                v___x_5180_ = 1usize;
                v___x_5181_ = lean_usize_add(v_i_5170_, v___x_5180_);
                v_i_5170_ = v___x_5181_;
                v_b_5172_ = v_a_5179_;
                state = 0;
                continue;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_5184_) == 0 {
                    v_a_5185_ = crate::leanh::lean_ctor_get(v___y_5184_, 0);
                    crate::leanh::lean_inc(v_a_5185_);
                    crate::leanh::lean_dec_ref_known(v___y_5184_, 1);
                    v_a_5179_ = v_a_5185_;
                    state = 1;
                    continue;
                } else {
                    return v___y_5184_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg___boxed(
    mut v_as_5201_: *mut crate::leanh::LeanObject,
    mut v_i_5202_: *mut crate::leanh::LeanObject,
    mut v_stop_5203_: *mut crate::leanh::LeanObject,
    mut v_b_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5210_: usize = 0;
    let mut v_stop_boxed_5211_: usize = 0;
    let mut v_res_5212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5210_ = crate::leanh::lean_unbox_usize(v_i_5202_);
    crate::leanh::lean_dec(v_i_5202_);
    v_stop_boxed_5211_ = crate::leanh::lean_unbox_usize(v_stop_5203_);
    crate::leanh::lean_dec(v_stop_5203_);
    v_res_5212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_5201_, v_i_boxed_5210_, v_stop_boxed_5211_, v_b_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
    crate::leanh::lean_dec(v___y_5208_);
    crate::leanh::lean_dec_ref(v___y_5207_);
    crate::leanh::lean_dec(v___y_5206_);
    crate::leanh::lean_dec_ref(v___y_5205_);
    crate::leanh::lean_dec_ref(v_as_5201_);
    return v_res_5212_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(
    mut v_as_5213_: *mut crate::leanh::LeanObject,
    mut v_i_5214_: usize,
    mut v_stop_5215_: usize,
    mut v___y_5216_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5218_: u8 = 0;
    let mut v___x_5219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5226_: u8 = 0;
    let mut v___x_5227_: usize = 0;
    let mut v___x_5228_: usize = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut v___x_5235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5218_ = lean_usize_dec_eq(v_i_5214_, v_stop_5215_);
                if v___x_5218_ == 0 {
                    v___x_5219_ = lean_array_uget_borrowed(v_as_5213_, v_i_5214_);
                    v_fvarId_5220_ = crate::leanh::lean_ctor_get(v___x_5219_, 0);
                    v___x_5221_ =
                        l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_5220_, v___y_5216_);
                    if crate::leanh::lean_obj_tag(v___x_5221_) == 0 {
                        v_a_5222_ = crate::leanh::lean_ctor_get(v___x_5221_, 0);
                        v_isSharedCheck_5233_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5221_)) as u8;
                        if v_isSharedCheck_5233_ == 0 {
                            v___x_5224_ = v___x_5221_;
                            v_isShared_5225_ = v_isSharedCheck_5233_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5222_);
                            crate::leanh::lean_dec(v___x_5221_);
                            v___x_5224_ = crate::leanh::lean_box(0);
                            v_isShared_5225_ = v_isSharedCheck_5233_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_5221_;
                    }
                } else {
                    v___x_5234_ = 0;
                    v___x_5235_ = crate::leanh::lean_box((v___x_5234_) as usize);
                    v___x_5236_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5236_, 0, v___x_5235_);
                    return v___x_5236_;
                }
            }
            1 => {
                v___x_5226_ = (crate::leanh::lean_unbox(v_a_5222_) as u8);
                if v___x_5226_ == 0 {
                    crate::leanh::lean_del_object(v___x_5224_);
                    crate::leanh::lean_dec(v_a_5222_);
                    v___x_5227_ = 1usize;
                    v___x_5228_ = lean_usize_add(v_i_5214_, v___x_5227_);
                    v_i_5214_ = v___x_5228_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5225_ == 0 {
                        v___x_5231_ = v___x_5224_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5232_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5222_);
                        v___x_5231_ = v_reuseFailAlloc_5232_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5231_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg___boxed(
    mut v_as_5237_: *mut crate::leanh::LeanObject,
    mut v_i_5238_: *mut crate::leanh::LeanObject,
    mut v_stop_5239_: *mut crate::leanh::LeanObject,
    mut v___y_5240_: *mut crate::leanh::LeanObject,
    mut v___y_5241_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_5242_: usize = 0;
    let mut v_stop_boxed_5243_: usize = 0;
    let mut v_res_5244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5242_ = crate::leanh::lean_unbox_usize(v_i_5238_);
    crate::leanh::lean_dec(v_i_5238_);
    v_stop_boxed_5243_ = crate::leanh::lean_unbox_usize(v_stop_5239_);
    crate::leanh::lean_dec(v_stop_5239_);
    v_res_5244_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_5237_, v_i_boxed_5242_, v_stop_boxed_5243_, v___y_5240_);
    crate::leanh::lean_dec(v___y_5240_);
    crate::leanh::lean_dec_ref(v_as_5237_);
    return v_res_5244_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3() -> *mut crate::leanh::LeanObject {
    let mut v___x_5248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5248_ = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
    v___x_5249_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_5250_ = crate::leanh::lean_unsigned_to_nat(641);
    v___x_5251_ = l_Lean_Compiler_LCNF_Simp_simp___closed__1;
    v___x_5252_ = l_Lean_Compiler_LCNF_Simp_simp___closed__0;
    v___x_5253_ = l_mkPanicMessageWithDecl(
        v___x_5252_,
        v___x_5251_,
        v___x_5250_,
        v___x_5249_,
        v___x_5248_,
    );
    return v___x_5253_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(
    mut v___x_5257_: *mut crate::leanh::LeanObject,
    mut v___x_5258_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5259_: *mut crate::leanh::LeanObject,
    mut v_k_5260_: *mut crate::leanh::LeanObject,
    mut v_args_5261_: *mut crate::leanh::LeanObject,
    mut v___x_5262_: u8,
    mut v___x_5263_: *mut crate::leanh::LeanObject,
    mut v_result_5264_: *mut crate::leanh::LeanObject,
    mut v___y_5265_: *mut crate::leanh::LeanObject,
    mut v___y_5266_: *mut crate::leanh::LeanObject,
    mut v___y_5267_: *mut crate::leanh::LeanObject,
    mut v___y_5268_: *mut crate::leanh::LeanObject,
    mut v___y_5269_: *mut crate::leanh::LeanObject,
    mut v___y_5270_: *mut crate::leanh::LeanObject,
    mut v___y_5271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_lower_5274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_5275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5293_: u8 = 0;
    let mut v_a_5294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v___x_5299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut v___x_5302_: u8 = 0;
    let mut v___x_5303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5308_: u8 = 0;
    let mut v___x_5310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut v___x_5313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5302_ = lean_nat_dec_lt(v___x_5257_, v___x_5258_);
                if v___x_5302_ == 0 {
                    crate::leanh::lean_dec(v___x_5263_);
                    crate::leanh::lean_dec_ref(v_args_5261_);
                    crate::leanh::lean_dec(v___x_5258_);
                    crate::leanh::lean_dec(v___x_5257_);
                    v___x_5303_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_5259_,
                        v_result_5264_,
                        v___y_5266_,
                        v___y_5268_,
                        v___y_5269_,
                        v___y_5270_,
                        v___y_5271_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5303_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5303_, 1);
                        crate::leanh::lean_inc_ref(v___y_5270_);
                        v___x_5304_ = l_Lean_Compiler_LCNF_Simp_simp(
                            v_k_5260_,
                            v___y_5265_,
                            v___y_5266_,
                            v___y_5267_,
                            v___y_5268_,
                            v___y_5269_,
                            v___y_5270_,
                            v___y_5271_,
                        );
                        return v___x_5304_;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_5260_);
                        v_a_5305_ = crate::leanh::lean_ctor_get(v___x_5303_, 0);
                        v_isSharedCheck_5312_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5303_)) as u8;
                        if v_isSharedCheck_5312_ == 0 {
                            v___x_5307_ = v___x_5303_;
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5305_);
                            crate::leanh::lean_dec(v___x_5303_);
                            v___x_5307_ = crate::leanh::lean_box(0);
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_5313_ = lean_nat_dec_le(v___x_5257_, v___x_5263_);
                    if v___x_5313_ == 0 {
                        crate::leanh::lean_dec(v___x_5263_);
                        v_lower_5274_ = v___x_5257_;
                        v_upper_5275_ = v___x_5258_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5257_);
                        v_lower_5274_ = v___x_5263_;
                        v_upper_5275_ = v___x_5258_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5276_ =
                    l_Array_toSubarray___redArg(v_args_5261_, v_lower_5274_, v_upper_5275_);
                v___x_5277_ = l_Subarray_copy___redArg(v___x_5276_);
                v___x_5278_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5278_, 0, v_result_5264_);
                crate::leanh::lean_ctor_set(v___x_5278_, 1, v___x_5277_);
                v___x_5279_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
                v___x_5280_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
                    v___x_5262_,
                    v___x_5278_,
                    v___x_5279_,
                    v___y_5268_,
                    v___y_5269_,
                    v___y_5270_,
                    v___y_5271_,
                );
                if crate::leanh::lean_obj_tag(v___x_5280_) == 0 {
                    v_a_5281_ = crate::leanh::lean_ctor_get(v___x_5280_, 0);
                    crate::leanh::lean_inc(v_a_5281_);
                    crate::leanh::lean_dec_ref_known(v___x_5280_, 1);
                    v_fvarId_5282_ = crate::leanh::lean_ctor_get(v_a_5281_, 0);
                    crate::leanh::lean_inc(v_fvarId_5282_);
                    v___x_5283_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_5259_,
                        v_fvarId_5282_,
                        v___y_5266_,
                        v___y_5268_,
                        v___y_5269_,
                        v___y_5270_,
                        v___y_5271_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5283_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5283_, 1);
                        v___x_5284_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5284_, 0, v_a_5281_);
                        crate::leanh::lean_ctor_set(v___x_5284_, 1, v_k_5260_);
                        crate::leanh::lean_inc_ref(v___y_5270_);
                        v___x_5285_ = l_Lean_Compiler_LCNF_Simp_simp(
                            v___x_5284_,
                            v___y_5265_,
                            v___y_5266_,
                            v___y_5267_,
                            v___y_5268_,
                            v___y_5269_,
                            v___y_5270_,
                            v___y_5271_,
                        );
                        return v___x_5285_;
                    } else {
                        crate::leanh::lean_dec(v_a_5281_);
                        crate::leanh::lean_dec_ref(v_k_5260_);
                        v_a_5286_ = crate::leanh::lean_ctor_get(v___x_5283_, 0);
                        v_isSharedCheck_5293_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5283_)) as u8;
                        if v_isSharedCheck_5293_ == 0 {
                            v___x_5288_ = v___x_5283_;
                            v_isShared_5289_ = v_isSharedCheck_5293_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5286_);
                            crate::leanh::lean_dec(v___x_5283_);
                            v___x_5288_ = crate::leanh::lean_box(0);
                            v_isShared_5289_ = v_isSharedCheck_5293_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_k_5260_);
                    crate::leanh::lean_dec(v_fvarId_5259_);
                    v_a_5294_ = crate::leanh::lean_ctor_get(v___x_5280_, 0);
                    v_isSharedCheck_5301_ = (!crate::leanh::lean_is_exclusive(v___x_5280_)) as u8;
                    if v_isSharedCheck_5301_ == 0 {
                        v___x_5296_ = v___x_5280_;
                        v_isShared_5297_ = v_isSharedCheck_5301_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5294_);
                        crate::leanh::lean_dec(v___x_5280_);
                        v___x_5296_ = crate::leanh::lean_box(0);
                        v_isShared_5297_ = v_isSharedCheck_5301_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_5289_ == 0 {
                    v___x_5291_ = v___x_5288_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5292_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
                    v___x_5291_ = v_reuseFailAlloc_5292_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_5291_;
            }
            4 => {
                if v_isShared_5297_ == 0 {
                    v___x_5299_ = v___x_5296_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
                    v___x_5299_ = v_reuseFailAlloc_5300_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5299_;
            }
            6 => {
                if v_isShared_5308_ == 0 {
                    v___x_5310_ = v___x_5307_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5311_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
                    v___x_5310_ = v_reuseFailAlloc_5311_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5310_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(
    mut v___x_5314_: *mut crate::leanh::LeanObject,
    mut v___x_5315_: *mut crate::leanh::LeanObject,
    mut v_fvarId_5316_: *mut crate::leanh::LeanObject,
    mut v_k_5317_: *mut crate::leanh::LeanObject,
    mut v_args_5318_: *mut crate::leanh::LeanObject,
    mut v___x_5319_: *mut crate::leanh::LeanObject,
    mut v___x_5320_: *mut crate::leanh::LeanObject,
    mut v_result_5321_: *mut crate::leanh::LeanObject,
    mut v___y_5322_: *mut crate::leanh::LeanObject,
    mut v___y_5323_: *mut crate::leanh::LeanObject,
    mut v___y_5324_: *mut crate::leanh::LeanObject,
    mut v___y_5325_: *mut crate::leanh::LeanObject,
    mut v___y_5326_: *mut crate::leanh::LeanObject,
    mut v___y_5327_: *mut crate::leanh::LeanObject,
    mut v___y_5328_: *mut crate::leanh::LeanObject,
    mut v___y_5329_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_47787__boxed_5330_: u8 = 0;
    let mut v_res_5331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_47787__boxed_5330_ = (crate::leanh::lean_unbox(v___x_5319_) as u8);
    v_res_5331_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(
        v___x_5314_,
        v___x_5315_,
        v_fvarId_5316_,
        v_k_5317_,
        v_args_5318_,
        v___x_47787__boxed_5330_,
        v___x_5320_,
        v_result_5321_,
        v___y_5322_,
        v___y_5323_,
        v___y_5324_,
        v___y_5325_,
        v___y_5326_,
        v___y_5327_,
        v___y_5328_,
    );
    crate::leanh::lean_dec(v___y_5328_);
    crate::leanh::lean_dec_ref(v___y_5327_);
    crate::leanh::lean_dec(v___y_5326_);
    crate::leanh::lean_dec_ref(v___y_5325_);
    crate::leanh::lean_dec_ref(v___y_5324_);
    crate::leanh::lean_dec(v___y_5323_);
    crate::leanh::lean_dec_ref(v___y_5322_);
    return v_res_5331_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(
    mut v_letDecl_5332_: *mut crate::leanh::LeanObject,
    mut v_k_5333_: *mut crate::leanh::LeanObject,
    mut v_a_5334_: *mut crate::leanh::LeanObject,
    mut v_a_5335_: *mut crate::leanh::LeanObject,
    mut v_a_5336_: *mut crate::leanh::LeanObject,
    mut v_a_5337_: *mut crate::leanh::LeanObject,
    mut v_a_5338_: *mut crate::leanh::LeanObject,
    mut v_a_5339_: *mut crate::leanh::LeanObject,
    mut v_a_5340_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_fvarId_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5351_: u8 = 0;
    let mut v_val_5352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v_params_5356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fType_5358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_5360_: u8 = 0;
    let mut v___x_5361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: u8 = 0;
    let mut v___y_5365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5369_: u8 = 0;
    let mut v___y_5370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: u8 = 0;
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_a_5413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v_a_5421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v_a_5429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___x_5434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v_a_5437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5440_: u8 = 0;
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5444_: u8 = 0;
    let mut v___x_5445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5461_: u8 = 0;
    let mut v___x_5463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v_a_5469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5472_: u8 = 0;
    let mut v___x_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_a_5477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5480_: u8 = 0;
    let mut v___x_5482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5484_: u8 = 0;
    let mut v_a_5485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5488_: u8 = 0;
    let mut v___x_5490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5492_: u8 = 0;
    let mut v_a_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5496_: u8 = 0;
    let mut v___x_5498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut v_a_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5504_: u8 = 0;
    let mut v___x_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5508_: u8 = 0;
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut v_a_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_a_5529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_a_5537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5540_: u8 = 0;
    let mut v___x_5542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5544_: u8 = 0;
    let mut v___y_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: u8 = 0;
    let mut v___x_5563_: u8 = 0;
    let mut v___x_5564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5569_: u8 = 0;
    let mut v___x_5570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5574_: u8 = 0;
    let mut v_a_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut v_a_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v___x_5588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5590_: u8 = 0;
    let mut v_a_5591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5598_: u8 = 0;
    let mut v___x_5599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5614_: u8 = 0;
    let mut v_a_5615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5618_: u8 = 0;
    let mut v___x_5620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5622_: u8 = 0;
    let mut v_a_5623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5626_: u8 = 0;
    let mut v___x_5628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5630_: u8 = 0;
    let mut v_a_5631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5634_: u8 = 0;
    let mut v___x_5636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut v_a_5639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v_declName_5647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_config_5651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineStack_5652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineStackOccs_5653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5662_: u8 = 0;
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5666_: u8 = 0;
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5672_: u8 = 0;
    let mut v_a_5673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5676_: u8 = 0;
    let mut v___x_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut v_isSharedCheck_5681_: u8 = 0;
    let mut v_unused_5682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_5342_ = crate::leanh::lean_ctor_get(v_letDecl_5332_, 0);
                v_value_5343_ = crate::leanh::lean_ctor_get(v_letDecl_5332_, 3);
                v_isSharedCheck_5681_ = (!crate::leanh::lean_is_exclusive(v_letDecl_5332_)) as u8;
                if v_isSharedCheck_5681_ == 0 {
                    v_unused_5682_ = crate::leanh::lean_ctor_get(v_letDecl_5332_, 2);
                    crate::leanh::lean_dec(v_unused_5682_);
                    v_unused_5683_ = crate::leanh::lean_ctor_get(v_letDecl_5332_, 1);
                    crate::leanh::lean_dec(v_unused_5683_);
                    v___x_5345_ = v_letDecl_5332_;
                    v_isShared_5346_ = v_isSharedCheck_5681_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_value_5343_);
                    crate::leanh::lean_inc(v_fvarId_5342_);
                    crate::leanh::lean_dec(v_letDecl_5332_);
                    v___x_5345_ = crate::leanh::lean_box(0);
                    v_isShared_5346_ = v_isSharedCheck_5681_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_value_5343_);
                v___x_5347_ = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(
                    v_value_5343_,
                    v_a_5334_,
                    v_a_5335_,
                    v_a_5336_,
                    v_a_5337_,
                    v_a_5338_,
                    v_a_5339_,
                    v_a_5340_,
                );
                if crate::leanh::lean_obj_tag(v___x_5347_) == 0 {
                    v_a_5348_ = crate::leanh::lean_ctor_get(v___x_5347_, 0);
                    v_isSharedCheck_5672_ = (!crate::leanh::lean_is_exclusive(v___x_5347_)) as u8;
                    if v_isSharedCheck_5672_ == 0 {
                        v___x_5350_ = v___x_5347_;
                        v_isShared_5351_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5348_);
                        crate::leanh::lean_dec(v___x_5347_);
                        v___x_5350_ = crate::leanh::lean_box(0);
                        v_isShared_5351_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5345_);
                    crate::leanh::lean_dec(v_value_5343_);
                    crate::leanh::lean_dec(v_fvarId_5342_);
                    crate::leanh::lean_dec_ref(v_k_5333_);
                    v_a_5673_ = crate::leanh::lean_ctor_get(v___x_5347_, 0);
                    v_isSharedCheck_5680_ = (!crate::leanh::lean_is_exclusive(v___x_5347_)) as u8;
                    if v_isSharedCheck_5680_ == 0 {
                        v___x_5675_ = v___x_5347_;
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 61;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5673_);
                        crate::leanh::lean_dec(v___x_5347_);
                        v___x_5675_ = crate::leanh::lean_box(0);
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 61;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5348_) == 1 {
                    crate::leanh::lean_del_object(v___x_5350_);
                    v_val_5352_ = crate::leanh::lean_ctor_get(v_a_5348_, 0);
                    v_isSharedCheck_5667_ = (!crate::leanh::lean_is_exclusive(v_a_5348_)) as u8;
                    if v_isSharedCheck_5667_ == 0 {
                        v___x_5354_ = v_a_5348_;
                        v_isShared_5355_ = v_isSharedCheck_5667_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5352_);
                        crate::leanh::lean_dec(v_a_5348_);
                        v___x_5354_ = crate::leanh::lean_box(0);
                        v_isShared_5355_ = v_isSharedCheck_5667_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5348_);
                    crate::leanh::lean_del_object(v___x_5345_);
                    crate::leanh::lean_dec(v_value_5343_);
                    crate::leanh::lean_dec(v_fvarId_5342_);
                    crate::leanh::lean_dec_ref(v_k_5333_);
                    v___x_5668_ = crate::leanh::lean_box(0);
                    if v_isShared_5351_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5350_, 0, v___x_5668_);
                        v___x_5670_ = v___x_5350_;
                        state = 60;
                        continue;
                    } else {
                        v_reuseFailAlloc_5671_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5671_, 0, v___x_5668_);
                        v___x_5670_ = v_reuseFailAlloc_5671_;
                        state = 60;
                        continue;
                    }
                }
            }
            3 => {
                v_params_5356_ = crate::leanh::lean_ctor_get(v_val_5352_, 0);
                v_value_5357_ = crate::leanh::lean_ctor_get(v_val_5352_, 1);
                v_fType_5358_ = crate::leanh::lean_ctor_get(v_val_5352_, 2);
                v_args_5359_ = crate::leanh::lean_ctor_get(v_val_5352_, 3);
                v_recursive_5360_ = crate::leanh::lean_ctor_get_uint8(
                    v_val_5352_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4 + 2) as u32,
                );
                v___x_5361_ = lean_array_get_size(v_args_5359_);
                v___x_5362_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_5352_);
                v___x_5363_ = lean_nat_dec_lt(v___x_5361_, v___x_5362_);
                if crate::leanh::lean_obj_tag(v_value_5343_) == 3 {
                    v_declName_5647_ = crate::leanh::lean_ctor_get(v_value_5343_, 0);
                    crate::leanh::lean_inc_n(v_declName_5647_, 2);
                    crate::leanh::lean_dec_ref_known(v_value_5343_, 3);
                    v___x_5648_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_5360_, v_declName_5647_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_);
                    if crate::leanh::lean_obj_tag(v___x_5648_) == 0 {
                        v_a_5649_ = crate::leanh::lean_ctor_get(v___x_5648_, 0);
                        crate::leanh::lean_inc(v_a_5649_);
                        crate::leanh::lean_dec_ref_known(v___x_5648_, 1);
                        v_declName_5650_ = crate::leanh::lean_ctor_get(v_a_5334_, 0);
                        v_config_5651_ = crate::leanh::lean_ctor_get(v_a_5334_, 1);
                        v_inlineStack_5652_ = crate::leanh::lean_ctor_get(v_a_5334_, 2);
                        v_inlineStackOccs_5653_ = crate::leanh::lean_ctor_get(v_a_5334_, 3);
                        crate::leanh::lean_inc(v_inlineStack_5652_);
                        crate::leanh::lean_inc(v_declName_5647_);
                        v___x_5654_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_5654_, 0, v_declName_5647_);
                        crate::leanh::lean_ctor_set(v___x_5654_, 1, v_inlineStack_5652_);
                        crate::leanh::lean_inc_ref(v_inlineStackOccs_5653_);
                        v___x_5655_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_5653_, v_declName_5647_, v_a_5649_);
                        crate::leanh::lean_inc_ref(v_config_5651_);
                        crate::leanh::lean_inc(v_declName_5650_);
                        if v_isShared_5346_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_5345_, 3, v___x_5655_);
                            crate::leanh::lean_ctor_set(v___x_5345_, 2, v___x_5654_);
                            crate::leanh::lean_ctor_set(v___x_5345_, 1, v_config_5651_);
                            crate::leanh::lean_ctor_set(v___x_5345_, 0, v_declName_5650_);
                            v___x_5657_ = v___x_5345_;
                            state = 57;
                            continue;
                        } else {
                            v_reuseFailAlloc_5658_ =
                                crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_5658_,
                                0,
                                v_declName_5650_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_config_5651_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 2, v___x_5654_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_5658_, 3, v___x_5655_);
                            v___x_5657_ = v_reuseFailAlloc_5658_;
                            state = 57;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_declName_5647_);
                        crate::leanh::lean_dec(v___x_5362_);
                        crate::leanh::lean_del_object(v___x_5354_);
                        crate::leanh::lean_dec(v_val_5352_);
                        crate::leanh::lean_del_object(v___x_5345_);
                        crate::leanh::lean_dec(v_fvarId_5342_);
                        crate::leanh::lean_dec_ref(v_k_5333_);
                        v_a_5659_ = crate::leanh::lean_ctor_get(v___x_5648_, 0);
                        v_isSharedCheck_5666_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5648_)) as u8;
                        if v_isSharedCheck_5666_ == 0 {
                            v___x_5661_ = v___x_5648_;
                            v_isShared_5662_ = v_isSharedCheck_5666_;
                            state = 58;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5659_);
                            crate::leanh::lean_dec(v___x_5648_);
                            v___x_5661_ = crate::leanh::lean_box(0);
                            v_isShared_5662_ = v_isSharedCheck_5666_;
                            state = 58;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5345_);
                    crate::leanh::lean_dec(v_value_5343_);
                    crate::leanh::lean_inc_ref(v_a_5334_);
                    v___y_5546_ = v_a_5334_;
                    v___y_5547_ = v_a_5335_;
                    v___y_5548_ = v_a_5336_;
                    v___y_5549_ = v_a_5337_;
                    v___y_5550_ = v_a_5338_;
                    v___y_5551_ = v_a_5339_;
                    v___y_5552_ = v_a_5340_;
                    state = 38;
                    continue;
                }
            }
            4 => {
                crate::leanh::lean_inc_ref(v___y_5370_);
                v___x_5378_ = l_Lean_Compiler_LCNF_Simp_simp(
                    v___y_5377_,
                    v___y_5373_,
                    v___y_5374_,
                    v___y_5372_,
                    v___y_5368_,
                    v___y_5371_,
                    v___y_5370_,
                    v___y_5375_,
                );
                if crate::leanh::lean_obj_tag(v___x_5378_) == 0 {
                    v_a_5379_ = crate::leanh::lean_ctor_get(v___x_5378_, 0);
                    crate::leanh::lean_inc(v_a_5379_);
                    crate::leanh::lean_dec_ref_known(v___x_5378_, 1);
                    v___x_5380_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5374_);
                    if crate::leanh::lean_obj_tag(v___x_5380_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5380_, 1);
                        v___x_5381_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_5379_);
                        if v___x_5381_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_5367_);
                            v___x_5382_ = lean_mk_empty_array_with_capacity(v___y_5366_);
                            crate::leanh::lean_dec(v___y_5366_);
                            crate::leanh::lean_inc_ref(v___x_5382_);
                            v___x_5383_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v___y_5365_, v___x_5382_);
                            v___x_5384_ = l_Lean_Compiler_LCNF_inferAppType(
                                v___y_5369_,
                                v_fType_5358_,
                                v___x_5383_,
                                v___y_5368_,
                                v___y_5371_,
                                v___y_5370_,
                                v___y_5375_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5384_) == 0 {
                                v_a_5385_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                                crate::leanh::lean_inc_n(v_a_5385_, 2);
                                crate::leanh::lean_dec_ref_known(v___x_5384_, 1);
                                v___x_5386_ = l_Lean_Expr_headBeta(v_a_5385_);
                                v___x_5387_ = l_Lean_Expr_isForall(v___x_5386_);
                                crate::leanh::lean_dec_ref(v___x_5386_);
                                if v___x_5387_ == 0 {
                                    crate::leanh::lean_dec_ref(v___x_5382_);
                                    v___x_5388_ = l_Lean_Compiler_LCNF_mkAuxParam(
                                        v___y_5369_,
                                        v_a_5385_,
                                        v___x_5363_,
                                        v___y_5368_,
                                        v___y_5371_,
                                        v___y_5370_,
                                        v___y_5375_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5388_) == 0 {
                                        v_a_5389_ = crate::leanh::lean_ctor_get(v___x_5388_, 0);
                                        crate::leanh::lean_inc(v_a_5389_);
                                        crate::leanh::lean_dec_ref_known(v___x_5388_, 1);
                                        v_fvarId_5390_ = crate::leanh::lean_ctor_get(v_a_5389_, 0);
                                        crate::leanh::lean_inc(v___y_5375_);
                                        crate::leanh::lean_inc_ref(v___y_5370_);
                                        crate::leanh::lean_inc(v___y_5371_);
                                        crate::leanh::lean_inc_ref(v___y_5368_);
                                        crate::leanh::lean_inc_ref(v___y_5372_);
                                        crate::leanh::lean_inc(v___y_5374_);
                                        crate::leanh::lean_inc(v_fvarId_5390_);
                                        v___x_5391_ = crate::leanh::lean_apply_9(
                                            v___y_5376_,
                                            v_fvarId_5390_,
                                            v___y_5373_,
                                            v___y_5374_,
                                            v___y_5372_,
                                            v___y_5368_,
                                            v___y_5371_,
                                            v___y_5370_,
                                            v___y_5375_,
                                            crate::leanh::lean_box(0),
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_5391_) == 0 {
                                            v_a_5392_ = crate::leanh::lean_ctor_get(v___x_5391_, 0);
                                            crate::leanh::lean_inc(v_a_5392_);
                                            crate::leanh::lean_dec_ref_known(v___x_5391_, 1);
                                            v___x_5393_ = crate::leanh::lean_unsigned_to_nat(1);
                                            v___x_5394_ =
                                                lean_mk_empty_array_with_capacity(v___x_5393_);
                                            v___x_5395_ = lean_array_push(v___x_5394_, v_a_5389_);
                                            v___x_5396_ =
                                                l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1;
                                            v___x_5397_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(
                                                v___y_5369_,
                                                v___x_5395_,
                                                v_a_5392_,
                                                v___x_5396_,
                                                v___y_5368_,
                                                v___y_5371_,
                                                v___y_5370_,
                                                v___y_5375_,
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_5397_) == 0 {
                                                v_a_5398_ =
                                                    crate::leanh::lean_ctor_get(v___x_5397_, 0);
                                                crate::leanh::lean_inc_n(v_a_5398_, 2);
                                                crate::leanh::lean_dec_ref_known(v___x_5397_, 1);
                                                v___f_5399_ = crate::leanh::lean_alloc_closure(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                                                crate::leanh::lean_closure_set(
                                                    v___f_5399_,
                                                    0,
                                                    v_a_5398_,
                                                );
                                                crate::leanh::lean_closure_set(
                                                    v___f_5399_,
                                                    1,
                                                    v___x_5393_,
                                                );
                                                v___x_5400_ =
                                                    l_Lean_Compiler_LCNF_CompilerM_codeBind(
                                                        v___y_5369_,
                                                        v_a_5379_,
                                                        v___f_5399_,
                                                        v___y_5368_,
                                                        v___y_5371_,
                                                        v___y_5370_,
                                                        v___y_5375_,
                                                    );
                                                if crate::leanh::lean_obj_tag(v___x_5400_) == 0 {
                                                    v_a_5401_ =
                                                        crate::leanh::lean_ctor_get(v___x_5400_, 0);
                                                    v_isSharedCheck_5412_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5400_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5412_ == 0 {
                                                        v___x_5403_ = v___x_5400_;
                                                        v_isShared_5404_ = v_isSharedCheck_5412_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5401_);
                                                        crate::leanh::lean_dec(v___x_5400_);
                                                        v___x_5403_ = crate::leanh::lean_box(0);
                                                        v_isShared_5404_ = v_isSharedCheck_5412_;
                                                        state = 5;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_a_5398_);
                                                    crate::leanh::lean_del_object(v___x_5354_);
                                                    v_a_5413_ =
                                                        crate::leanh::lean_ctor_get(v___x_5400_, 0);
                                                    v_isSharedCheck_5420_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5400_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5420_ == 0 {
                                                        v___x_5415_ = v___x_5400_;
                                                        v_isShared_5416_ = v_isSharedCheck_5420_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5413_);
                                                        crate::leanh::lean_dec(v___x_5400_);
                                                        v___x_5415_ = crate::leanh::lean_box(0);
                                                        v_isShared_5416_ = v_isSharedCheck_5420_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_5379_);
                                                crate::leanh::lean_del_object(v___x_5354_);
                                                v_a_5421_ =
                                                    crate::leanh::lean_ctor_get(v___x_5397_, 0);
                                                v_isSharedCheck_5428_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5397_))
                                                        as u8;
                                                if v_isSharedCheck_5428_ == 0 {
                                                    v___x_5423_ = v___x_5397_;
                                                    v_isShared_5424_ = v_isSharedCheck_5428_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5421_);
                                                    crate::leanh::lean_dec(v___x_5397_);
                                                    v___x_5423_ = crate::leanh::lean_box(0);
                                                    v_isShared_5424_ = v_isSharedCheck_5428_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec(v_a_5389_);
                                            crate::leanh::lean_dec(v_a_5379_);
                                            crate::leanh::lean_del_object(v___x_5354_);
                                            v_a_5429_ = crate::leanh::lean_ctor_get(v___x_5391_, 0);
                                            v_isSharedCheck_5436_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5391_))
                                                    as u8;
                                            if v_isSharedCheck_5436_ == 0 {
                                                v___x_5431_ = v___x_5391_;
                                                v_isShared_5432_ = v_isSharedCheck_5436_;
                                                state = 12;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5429_);
                                                crate::leanh::lean_dec(v___x_5391_);
                                                v___x_5431_ = crate::leanh::lean_box(0);
                                                v_isShared_5432_ = v_isSharedCheck_5436_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_5379_);
                                        crate::leanh::lean_dec_ref(v___y_5376_);
                                        crate::leanh::lean_dec_ref(v___y_5373_);
                                        crate::leanh::lean_del_object(v___x_5354_);
                                        v_a_5437_ = crate::leanh::lean_ctor_get(v___x_5388_, 0);
                                        v_isSharedCheck_5444_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5388_)) as u8;
                                        if v_isSharedCheck_5444_ == 0 {
                                            v___x_5439_ = v___x_5388_;
                                            v_isShared_5440_ = v_isSharedCheck_5444_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5437_);
                                            crate::leanh::lean_dec(v___x_5388_);
                                            v___x_5439_ = crate::leanh::lean_box(0);
                                            v_isShared_5440_ = v_isSharedCheck_5444_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5385_);
                                    v___x_5445_ =
                                        l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4;
                                    v___x_5446_ = l_Lean_Compiler_LCNF_mkAuxFunDecl(
                                        v___x_5382_,
                                        v_a_5379_,
                                        v___x_5445_,
                                        v___y_5368_,
                                        v___y_5371_,
                                        v___y_5370_,
                                        v___y_5375_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_5446_) == 0 {
                                        v_a_5447_ = crate::leanh::lean_ctor_get(v___x_5446_, 0);
                                        crate::leanh::lean_inc(v_a_5447_);
                                        crate::leanh::lean_dec_ref_known(v___x_5446_, 1);
                                        v___x_5448_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(
                                            v_a_5447_,
                                            v___y_5368_,
                                            v___y_5371_,
                                            v___y_5370_,
                                            v___y_5375_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_5448_) == 0 {
                                            v_a_5449_ = crate::leanh::lean_ctor_get(v___x_5448_, 0);
                                            crate::leanh::lean_inc(v_a_5449_);
                                            crate::leanh::lean_dec_ref_known(v___x_5448_, 1);
                                            v_fvarId_5450_ =
                                                crate::leanh::lean_ctor_get(v_a_5449_, 0);
                                            crate::leanh::lean_inc(v___y_5375_);
                                            crate::leanh::lean_inc_ref(v___y_5370_);
                                            crate::leanh::lean_inc(v___y_5371_);
                                            crate::leanh::lean_inc_ref(v___y_5368_);
                                            crate::leanh::lean_inc_ref(v___y_5372_);
                                            crate::leanh::lean_inc(v___y_5374_);
                                            crate::leanh::lean_inc_ref(v___y_5373_);
                                            crate::leanh::lean_inc(v_fvarId_5450_);
                                            v___x_5451_ = crate::leanh::lean_apply_9(
                                                v___y_5376_,
                                                v_fvarId_5450_,
                                                v___y_5373_,
                                                v___y_5374_,
                                                v___y_5372_,
                                                v___y_5368_,
                                                v___y_5371_,
                                                v___y_5370_,
                                                v___y_5375_,
                                                crate::leanh::lean_box(0),
                                            );
                                            if crate::leanh::lean_obj_tag(v___x_5451_) == 0 {
                                                v_a_5452_ =
                                                    crate::leanh::lean_ctor_get(v___x_5451_, 0);
                                                crate::leanh::lean_inc(v_a_5452_);
                                                crate::leanh::lean_dec_ref_known(v___x_5451_, 1);
                                                v___x_5453_ =
                                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                                crate::leanh::lean_ctor_set(
                                                    v___x_5453_,
                                                    0,
                                                    v_a_5449_,
                                                );
                                                v___x_5454_ = crate::leanh::lean_unsigned_to_nat(1);
                                                v___x_5455_ =
                                                    lean_mk_empty_array_with_capacity(v___x_5454_);
                                                v___x_5456_ =
                                                    lean_array_push(v___x_5455_, v___x_5453_);
                                                v___x_5457_ =
                                                    l_Lean_Compiler_LCNF_Simp_attachCodeDecls(
                                                        v___x_5456_,
                                                        v_a_5452_,
                                                        v___y_5373_,
                                                        v___y_5374_,
                                                        v___y_5372_,
                                                        v___y_5368_,
                                                        v___y_5371_,
                                                        v___y_5370_,
                                                        v___y_5375_,
                                                    );
                                                crate::leanh::lean_dec_ref(v___y_5373_);
                                                crate::leanh::lean_dec_ref(v___x_5456_);
                                                if crate::leanh::lean_obj_tag(v___x_5457_) == 0 {
                                                    v_a_5458_ =
                                                        crate::leanh::lean_ctor_get(v___x_5457_, 0);
                                                    v_isSharedCheck_5468_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5457_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5468_ == 0 {
                                                        v___x_5460_ = v___x_5457_;
                                                        v_isShared_5461_ = v_isSharedCheck_5468_;
                                                        state = 16;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5458_);
                                                        crate::leanh::lean_dec(v___x_5457_);
                                                        v___x_5460_ = crate::leanh::lean_box(0);
                                                        v_isShared_5461_ = v_isSharedCheck_5468_;
                                                        state = 16;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_del_object(v___x_5354_);
                                                    v_a_5469_ =
                                                        crate::leanh::lean_ctor_get(v___x_5457_, 0);
                                                    v_isSharedCheck_5476_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_5457_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_5476_ == 0 {
                                                        v___x_5471_ = v___x_5457_;
                                                        v_isShared_5472_ = v_isSharedCheck_5476_;
                                                        state = 19;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_5469_);
                                                        crate::leanh::lean_dec(v___x_5457_);
                                                        v___x_5471_ = crate::leanh::lean_box(0);
                                                        v_isShared_5472_ = v_isSharedCheck_5476_;
                                                        state = 19;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_5449_);
                                                crate::leanh::lean_dec_ref(v___y_5373_);
                                                crate::leanh::lean_del_object(v___x_5354_);
                                                v_a_5477_ =
                                                    crate::leanh::lean_ctor_get(v___x_5451_, 0);
                                                v_isSharedCheck_5484_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_5451_))
                                                        as u8;
                                                if v_isSharedCheck_5484_ == 0 {
                                                    v___x_5479_ = v___x_5451_;
                                                    v_isShared_5480_ = v_isSharedCheck_5484_;
                                                    state = 21;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_5477_);
                                                    crate::leanh::lean_dec(v___x_5451_);
                                                    v___x_5479_ = crate::leanh::lean_box(0);
                                                    v_isShared_5480_ = v_isSharedCheck_5484_;
                                                    state = 21;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___y_5376_);
                                            crate::leanh::lean_dec_ref(v___y_5373_);
                                            crate::leanh::lean_del_object(v___x_5354_);
                                            v_a_5485_ = crate::leanh::lean_ctor_get(v___x_5448_, 0);
                                            v_isSharedCheck_5492_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_5448_))
                                                    as u8;
                                            if v_isSharedCheck_5492_ == 0 {
                                                v___x_5487_ = v___x_5448_;
                                                v_isShared_5488_ = v_isSharedCheck_5492_;
                                                state = 23;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_5485_);
                                                crate::leanh::lean_dec(v___x_5448_);
                                                v___x_5487_ = crate::leanh::lean_box(0);
                                                v_isShared_5488_ = v_isSharedCheck_5492_;
                                                state = 23;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___y_5376_);
                                        crate::leanh::lean_dec_ref(v___y_5373_);
                                        crate::leanh::lean_del_object(v___x_5354_);
                                        v_a_5493_ = crate::leanh::lean_ctor_get(v___x_5446_, 0);
                                        v_isSharedCheck_5500_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5446_)) as u8;
                                        if v_isSharedCheck_5500_ == 0 {
                                            v___x_5495_ = v___x_5446_;
                                            v_isShared_5496_ = v_isSharedCheck_5500_;
                                            state = 25;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5493_);
                                            crate::leanh::lean_dec(v___x_5446_);
                                            v___x_5495_ = crate::leanh::lean_box(0);
                                            v_isShared_5496_ = v_isSharedCheck_5500_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___x_5382_);
                                crate::leanh::lean_dec(v_a_5379_);
                                crate::leanh::lean_dec_ref(v___y_5376_);
                                crate::leanh::lean_dec_ref(v___y_5373_);
                                crate::leanh::lean_del_object(v___x_5354_);
                                v_a_5501_ = crate::leanh::lean_ctor_get(v___x_5384_, 0);
                                v_isSharedCheck_5508_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5384_)) as u8;
                                if v_isSharedCheck_5508_ == 0 {
                                    v___x_5503_ = v___x_5384_;
                                    v_isShared_5504_ = v_isSharedCheck_5508_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5501_);
                                    crate::leanh::lean_dec(v___x_5384_);
                                    v___x_5503_ = crate::leanh::lean_box(0);
                                    v_isShared_5504_ = v_isSharedCheck_5508_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_5376_);
                            crate::leanh::lean_dec_ref(v___y_5373_);
                            crate::leanh::lean_dec(v___y_5366_);
                            crate::leanh::lean_dec_ref(v___y_5365_);
                            crate::leanh::lean_dec_ref(v_fType_5358_);
                            v___x_5509_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(
                                v___y_5369_,
                                v_a_5379_,
                                v___y_5367_,
                                v___y_5368_,
                                v___y_5371_,
                                v___y_5370_,
                                v___y_5375_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5509_) == 0 {
                                v_a_5510_ = crate::leanh::lean_ctor_get(v___x_5509_, 0);
                                v_isSharedCheck_5520_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5509_)) as u8;
                                if v_isSharedCheck_5520_ == 0 {
                                    v___x_5512_ = v___x_5509_;
                                    v_isShared_5513_ = v_isSharedCheck_5520_;
                                    state = 29;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5510_);
                                    crate::leanh::lean_dec(v___x_5509_);
                                    v___x_5512_ = crate::leanh::lean_box(0);
                                    v_isShared_5513_ = v_isSharedCheck_5520_;
                                    state = 29;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_5354_);
                                v_a_5521_ = crate::leanh::lean_ctor_get(v___x_5509_, 0);
                                v_isSharedCheck_5528_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5509_)) as u8;
                                if v_isSharedCheck_5528_ == 0 {
                                    v___x_5523_ = v___x_5509_;
                                    v_isShared_5524_ = v_isSharedCheck_5528_;
                                    state = 32;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5521_);
                                    crate::leanh::lean_dec(v___x_5509_);
                                    v___x_5523_ = crate::leanh::lean_box(0);
                                    v_isShared_5524_ = v_isSharedCheck_5528_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5379_);
                        crate::leanh::lean_dec_ref(v___y_5376_);
                        crate::leanh::lean_dec_ref(v___y_5373_);
                        crate::leanh::lean_dec_ref(v___y_5367_);
                        crate::leanh::lean_dec(v___y_5366_);
                        crate::leanh::lean_dec_ref(v___y_5365_);
                        crate::leanh::lean_dec_ref(v_fType_5358_);
                        crate::leanh::lean_del_object(v___x_5354_);
                        v_a_5529_ = crate::leanh::lean_ctor_get(v___x_5380_, 0);
                        v_isSharedCheck_5536_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5380_)) as u8;
                        if v_isSharedCheck_5536_ == 0 {
                            v___x_5531_ = v___x_5380_;
                            v_isShared_5532_ = v_isSharedCheck_5536_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5529_);
                            crate::leanh::lean_dec(v___x_5380_);
                            v___x_5531_ = crate::leanh::lean_box(0);
                            v_isShared_5532_ = v_isSharedCheck_5536_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_5376_);
                    crate::leanh::lean_dec_ref(v___y_5373_);
                    crate::leanh::lean_dec_ref(v___y_5367_);
                    crate::leanh::lean_dec(v___y_5366_);
                    crate::leanh::lean_dec_ref(v___y_5365_);
                    crate::leanh::lean_dec_ref(v_fType_5358_);
                    crate::leanh::lean_del_object(v___x_5354_);
                    v_a_5537_ = crate::leanh::lean_ctor_get(v___x_5378_, 0);
                    v_isSharedCheck_5544_ = (!crate::leanh::lean_is_exclusive(v___x_5378_)) as u8;
                    if v_isSharedCheck_5544_ == 0 {
                        v___x_5539_ = v___x_5378_;
                        v_isShared_5540_ = v_isSharedCheck_5544_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5537_);
                        crate::leanh::lean_dec(v___x_5378_);
                        v___x_5539_ = crate::leanh::lean_box(0);
                        v_isShared_5540_ = v_isSharedCheck_5544_;
                        state = 36;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5405_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5405_, 0, v_a_5398_);
                crate::leanh::lean_ctor_set(v___x_5405_, 1, v_a_5401_);
                if v_isShared_5355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5354_, 0, v___x_5405_);
                    v___x_5407_ = v___x_5354_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5411_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5411_, 0, v___x_5405_);
                    v___x_5407_ = v_reuseFailAlloc_5411_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5404_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5403_, 0, v___x_5407_);
                    v___x_5409_ = v___x_5403_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5410_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5407_);
                    v___x_5409_ = v_reuseFailAlloc_5410_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5409_;
            }
            8 => {
                if v_isShared_5416_ == 0 {
                    v___x_5418_ = v___x_5415_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5419_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
                    v___x_5418_ = v_reuseFailAlloc_5419_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5418_;
            }
            10 => {
                if v_isShared_5424_ == 0 {
                    v___x_5426_ = v___x_5423_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
                    v___x_5426_ = v_reuseFailAlloc_5427_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_5426_;
            }
            12 => {
                if v_isShared_5432_ == 0 {
                    v___x_5434_ = v___x_5431_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_5435_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
                    v___x_5434_ = v_reuseFailAlloc_5435_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_5434_;
            }
            14 => {
                if v_isShared_5440_ == 0 {
                    v___x_5442_ = v___x_5439_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_5443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
                    v___x_5442_ = v_reuseFailAlloc_5443_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_5442_;
            }
            16 => {
                if v_isShared_5355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5354_, 0, v_a_5458_);
                    v___x_5463_ = v___x_5354_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5458_);
                    v___x_5463_ = v_reuseFailAlloc_5467_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5461_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5460_, 0, v___x_5463_);
                    v___x_5465_ = v___x_5460_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5465_;
            }
            19 => {
                if v_isShared_5472_ == 0 {
                    v___x_5474_ = v___x_5471_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
                    v___x_5474_ = v_reuseFailAlloc_5475_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_5474_;
            }
            21 => {
                if v_isShared_5480_ == 0 {
                    v___x_5482_ = v___x_5479_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5483_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_a_5477_);
                    v___x_5482_ = v_reuseFailAlloc_5483_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5482_;
            }
            23 => {
                if v_isShared_5488_ == 0 {
                    v___x_5490_ = v___x_5487_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5491_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
                    v___x_5490_ = v_reuseFailAlloc_5491_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5490_;
            }
            25 => {
                if v_isShared_5496_ == 0 {
                    v___x_5498_ = v___x_5495_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5499_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
                    v___x_5498_ = v_reuseFailAlloc_5499_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_5498_;
            }
            27 => {
                if v_isShared_5504_ == 0 {
                    v___x_5506_ = v___x_5503_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5507_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
                    v___x_5506_ = v_reuseFailAlloc_5507_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_5506_;
            }
            29 => {
                if v_isShared_5355_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5354_, 0, v_a_5510_);
                    v___x_5515_ = v___x_5354_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5519_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5510_);
                    v___x_5515_ = v_reuseFailAlloc_5519_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_5513_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5512_, 0, v___x_5515_);
                    v___x_5517_ = v___x_5512_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5518_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5515_);
                    v___x_5517_ = v_reuseFailAlloc_5518_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_5517_;
            }
            32 => {
                if v_isShared_5524_ == 0 {
                    v___x_5526_ = v___x_5523_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_5527_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
                    v___x_5526_ = v_reuseFailAlloc_5527_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_5526_;
            }
            34 => {
                if v_isShared_5532_ == 0 {
                    v___x_5534_ = v___x_5531_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_5535_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
                    v___x_5534_ = v_reuseFailAlloc_5535_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_5534_;
            }
            36 => {
                if v_isShared_5540_ == 0 {
                    v___x_5542_ = v___x_5539_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_5543_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_a_5537_);
                    v___x_5542_ = v_reuseFailAlloc_5543_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_5542_;
            }
            38 => {
                if v___x_5363_ == 0 {
                    crate::leanh::lean_inc_ref_n(v_args_5359_, 2);
                    crate::leanh::lean_inc_ref(v_fType_5358_);
                    crate::leanh::lean_inc_ref(v_value_5357_);
                    crate::leanh::lean_inc_ref(v_params_5356_);
                    crate::leanh::lean_dec(v_val_5352_);
                    v___x_5553_ = crate::leanh::lean_unsigned_to_nat(0);
                    crate::leanh::lean_inc(v___x_5362_);
                    v___x_5554_ =
                        l_Array_toSubarray___redArg(v_args_5359_, v___x_5553_, v___x_5362_);
                    crate::leanh::lean_inc_ref(v___x_5554_);
                    v___x_5555_ = l_Subarray_copy___redArg(v___x_5554_);
                    v___x_5556_ = l_Lean_Compiler_LCNF_Simp_betaReduce(
                        v_params_5356_,
                        v_value_5357_,
                        v___x_5555_,
                        v___x_5363_,
                        v___y_5546_,
                        v___y_5547_,
                        v___y_5548_,
                        v___y_5549_,
                        v___y_5550_,
                        v___y_5551_,
                        v___y_5552_,
                    );
                    crate::leanh::lean_dec_ref(v_params_5356_);
                    if crate::leanh::lean_obj_tag(v___x_5556_) == 0 {
                        v_a_5557_ = crate::leanh::lean_ctor_get(v___x_5556_, 0);
                        crate::leanh::lean_inc(v_a_5557_);
                        crate::leanh::lean_dec_ref_known(v___x_5556_, 1);
                        v___x_5558_ = 0;
                        v___x_5559_ = crate::leanh::lean_box((v___x_5558_) as usize);
                        crate::leanh::lean_inc_ref(v_k_5333_);
                        crate::leanh::lean_inc(v_fvarId_5342_);
                        crate::leanh::lean_inc(v___x_5362_);
                        v___f_5560_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed
                                as *mut core::ffi::c_void,
                            16,
                            7,
                        );
                        crate::leanh::lean_closure_set(v___f_5560_, 0, v___x_5362_);
                        crate::leanh::lean_closure_set(v___f_5560_, 1, v___x_5361_);
                        crate::leanh::lean_closure_set(v___f_5560_, 2, v_fvarId_5342_);
                        crate::leanh::lean_closure_set(v___f_5560_, 3, v_k_5333_);
                        crate::leanh::lean_closure_set(v___f_5560_, 4, v_args_5359_);
                        crate::leanh::lean_closure_set(v___f_5560_, 5, v___x_5559_);
                        crate::leanh::lean_closure_set(v___f_5560_, 6, v___x_5553_);
                        crate::leanh::lean_inc_ref(v___y_5548_);
                        crate::leanh::lean_inc_ref(v___y_5546_);
                        crate::leanh::lean_inc_ref(v___f_5560_);
                        crate::leanh::lean_inc(v___y_5547_);
                        v___f_5561_ = crate::leanh::lean_alloc_closure(
                            l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed
                                as *mut core::ffi::c_void,
                            10,
                            4,
                        );
                        crate::leanh::lean_closure_set(v___f_5561_, 0, v___y_5547_);
                        crate::leanh::lean_closure_set(v___f_5561_, 1, v___f_5560_);
                        crate::leanh::lean_closure_set(v___f_5561_, 2, v___y_5546_);
                        crate::leanh::lean_closure_set(v___f_5561_, 3, v___y_5548_);
                        v___x_5562_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(
                            v_k_5333_,
                            v_fvarId_5342_,
                        );
                        crate::leanh::lean_dec(v_fvarId_5342_);
                        crate::leanh::lean_dec_ref(v_k_5333_);
                        if v___x_5562_ == 0 {
                            crate::leanh::lean_dec(v___x_5362_);
                            v___y_5365_ = v___x_5554_;
                            v___y_5366_ = v___x_5553_;
                            v___y_5367_ = v___f_5561_;
                            v___y_5368_ = v___y_5549_;
                            v___y_5369_ = v___x_5558_;
                            v___y_5370_ = v___y_5551_;
                            v___y_5371_ = v___y_5550_;
                            v___y_5372_ = v___y_5548_;
                            v___y_5373_ = v___y_5546_;
                            v___y_5374_ = v___y_5547_;
                            v___y_5375_ = v___y_5552_;
                            v___y_5376_ = v___f_5560_;
                            v___y_5377_ = v_a_5557_;
                            state = 4;
                            continue;
                        } else {
                            v___x_5563_ = lean_nat_dec_eq(v___x_5361_, v___x_5362_);
                            crate::leanh::lean_dec(v___x_5362_);
                            if v___x_5563_ == 0 {
                                v___y_5365_ = v___x_5554_;
                                v___y_5366_ = v___x_5553_;
                                v___y_5367_ = v___f_5561_;
                                v___y_5368_ = v___y_5549_;
                                v___y_5369_ = v___x_5558_;
                                v___y_5370_ = v___y_5551_;
                                v___y_5371_ = v___y_5550_;
                                v___y_5372_ = v___y_5548_;
                                v___y_5373_ = v___y_5546_;
                                v___y_5374_ = v___y_5547_;
                                v___y_5375_ = v___y_5552_;
                                v___y_5376_ = v___f_5560_;
                                v___y_5377_ = v_a_5557_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___f_5561_);
                                crate::leanh::lean_dec_ref(v___f_5560_);
                                crate::leanh::lean_dec_ref(v___x_5554_);
                                crate::leanh::lean_dec_ref(v_fType_5358_);
                                crate::leanh::lean_del_object(v___x_5354_);
                                v___x_5564_ =
                                    l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5547_);
                                if crate::leanh::lean_obj_tag(v___x_5564_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_5564_, 1);
                                    crate::leanh::lean_inc_ref(v___y_5551_);
                                    v___x_5565_ = l_Lean_Compiler_LCNF_Simp_simp(
                                        v_a_5557_,
                                        v___y_5546_,
                                        v___y_5547_,
                                        v___y_5548_,
                                        v___y_5549_,
                                        v___y_5550_,
                                        v___y_5551_,
                                        v___y_5552_,
                                    );
                                    crate::leanh::lean_dec_ref(v___y_5546_);
                                    if crate::leanh::lean_obj_tag(v___x_5565_) == 0 {
                                        v_a_5566_ = crate::leanh::lean_ctor_get(v___x_5565_, 0);
                                        v_isSharedCheck_5574_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5565_)) as u8;
                                        if v_isSharedCheck_5574_ == 0 {
                                            v___x_5568_ = v___x_5565_;
                                            v_isShared_5569_ = v_isSharedCheck_5574_;
                                            state = 39;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5566_);
                                            crate::leanh::lean_dec(v___x_5565_);
                                            v___x_5568_ = crate::leanh::lean_box(0);
                                            v_isShared_5569_ = v_isSharedCheck_5574_;
                                            state = 39;
                                            continue;
                                        }
                                    } else {
                                        v_a_5575_ = crate::leanh::lean_ctor_get(v___x_5565_, 0);
                                        v_isSharedCheck_5582_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_5565_)) as u8;
                                        if v_isSharedCheck_5582_ == 0 {
                                            v___x_5577_ = v___x_5565_;
                                            v_isShared_5578_ = v_isSharedCheck_5582_;
                                            state = 41;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_5575_);
                                            crate::leanh::lean_dec(v___x_5565_);
                                            v___x_5577_ = crate::leanh::lean_box(0);
                                            v_isShared_5578_ = v_isSharedCheck_5582_;
                                            state = 41;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_5557_);
                                    crate::leanh::lean_dec_ref(v___y_5546_);
                                    v_a_5583_ = crate::leanh::lean_ctor_get(v___x_5564_, 0);
                                    v_isSharedCheck_5590_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5564_)) as u8;
                                    if v_isSharedCheck_5590_ == 0 {
                                        v___x_5585_ = v___x_5564_;
                                        v_isShared_5586_ = v_isSharedCheck_5590_;
                                        state = 43;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5583_);
                                        crate::leanh::lean_dec(v___x_5564_);
                                        v___x_5585_ = crate::leanh::lean_box(0);
                                        v_isShared_5586_ = v_isSharedCheck_5590_;
                                        state = 43;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_5554_);
                        crate::leanh::lean_dec_ref(v___y_5546_);
                        crate::leanh::lean_dec(v___x_5362_);
                        crate::leanh::lean_dec_ref(v_args_5359_);
                        crate::leanh::lean_dec_ref(v_fType_5358_);
                        crate::leanh::lean_del_object(v___x_5354_);
                        crate::leanh::lean_dec(v_fvarId_5342_);
                        crate::leanh::lean_dec_ref(v_k_5333_);
                        v_a_5591_ = crate::leanh::lean_ctor_get(v___x_5556_, 0);
                        v_isSharedCheck_5598_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5556_)) as u8;
                        if v_isSharedCheck_5598_ == 0 {
                            v___x_5593_ = v___x_5556_;
                            v_isShared_5594_ = v_isSharedCheck_5598_;
                            state = 45;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5591_);
                            crate::leanh::lean_dec(v___x_5556_);
                            v___x_5593_ = crate::leanh::lean_box(0);
                            v_isShared_5594_ = v_isSharedCheck_5598_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5362_);
                    crate::leanh::lean_del_object(v___x_5354_);
                    v___x_5599_ = l_Lean_Compiler_LCNF_Simp_specializePartialApp(
                        v_val_5352_,
                        v___y_5546_,
                        v___y_5547_,
                        v___y_5548_,
                        v___y_5549_,
                        v___y_5550_,
                        v___y_5551_,
                        v___y_5552_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5599_) == 0 {
                        v_a_5600_ = crate::leanh::lean_ctor_get(v___x_5599_, 0);
                        crate::leanh::lean_inc(v_a_5600_);
                        crate::leanh::lean_dec_ref_known(v___x_5599_, 1);
                        v_fvarId_5601_ = crate::leanh::lean_ctor_get(v_a_5600_, 0);
                        crate::leanh::lean_inc(v_fvarId_5601_);
                        v___x_5602_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                            v_fvarId_5342_,
                            v_fvarId_5601_,
                            v___y_5547_,
                            v___y_5549_,
                            v___y_5550_,
                            v___y_5551_,
                            v___y_5552_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5602_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_5602_, 1);
                            v___x_5603_ =
                                l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5547_);
                            if crate::leanh::lean_obj_tag(v___x_5603_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_5603_, 1);
                                v___x_5604_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_5604_, 0, v_a_5600_);
                                crate::leanh::lean_ctor_set(v___x_5604_, 1, v_k_5333_);
                                crate::leanh::lean_inc_ref(v___y_5551_);
                                v___x_5605_ = l_Lean_Compiler_LCNF_Simp_simp(
                                    v___x_5604_,
                                    v___y_5546_,
                                    v___y_5547_,
                                    v___y_5548_,
                                    v___y_5549_,
                                    v___y_5550_,
                                    v___y_5551_,
                                    v___y_5552_,
                                );
                                crate::leanh::lean_dec_ref(v___y_5546_);
                                if crate::leanh::lean_obj_tag(v___x_5605_) == 0 {
                                    v_a_5606_ = crate::leanh::lean_ctor_get(v___x_5605_, 0);
                                    v_isSharedCheck_5614_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5605_)) as u8;
                                    if v_isSharedCheck_5614_ == 0 {
                                        v___x_5608_ = v___x_5605_;
                                        v_isShared_5609_ = v_isSharedCheck_5614_;
                                        state = 47;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5606_);
                                        crate::leanh::lean_dec(v___x_5605_);
                                        v___x_5608_ = crate::leanh::lean_box(0);
                                        v_isShared_5609_ = v_isSharedCheck_5614_;
                                        state = 47;
                                        continue;
                                    }
                                } else {
                                    v_a_5615_ = crate::leanh::lean_ctor_get(v___x_5605_, 0);
                                    v_isSharedCheck_5622_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_5605_)) as u8;
                                    if v_isSharedCheck_5622_ == 0 {
                                        v___x_5617_ = v___x_5605_;
                                        v_isShared_5618_ = v_isSharedCheck_5622_;
                                        state = 49;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_5615_);
                                        crate::leanh::lean_dec(v___x_5605_);
                                        v___x_5617_ = crate::leanh::lean_box(0);
                                        v_isShared_5618_ = v_isSharedCheck_5622_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5600_);
                                crate::leanh::lean_dec_ref(v___y_5546_);
                                crate::leanh::lean_dec_ref(v_k_5333_);
                                v_a_5623_ = crate::leanh::lean_ctor_get(v___x_5603_, 0);
                                v_isSharedCheck_5630_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5603_)) as u8;
                                if v_isSharedCheck_5630_ == 0 {
                                    v___x_5625_ = v___x_5603_;
                                    v_isShared_5626_ = v_isSharedCheck_5630_;
                                    state = 51;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5623_);
                                    crate::leanh::lean_dec(v___x_5603_);
                                    v___x_5625_ = crate::leanh::lean_box(0);
                                    v_isShared_5626_ = v_isSharedCheck_5630_;
                                    state = 51;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5600_);
                            crate::leanh::lean_dec_ref(v___y_5546_);
                            crate::leanh::lean_dec_ref(v_k_5333_);
                            v_a_5631_ = crate::leanh::lean_ctor_get(v___x_5602_, 0);
                            v_isSharedCheck_5638_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5602_)) as u8;
                            if v_isSharedCheck_5638_ == 0 {
                                v___x_5633_ = v___x_5602_;
                                v_isShared_5634_ = v_isSharedCheck_5638_;
                                state = 53;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5631_);
                                crate::leanh::lean_dec(v___x_5602_);
                                v___x_5633_ = crate::leanh::lean_box(0);
                                v_isShared_5634_ = v_isSharedCheck_5638_;
                                state = 53;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___y_5546_);
                        crate::leanh::lean_dec(v_fvarId_5342_);
                        crate::leanh::lean_dec_ref(v_k_5333_);
                        v_a_5639_ = crate::leanh::lean_ctor_get(v___x_5599_, 0);
                        v_isSharedCheck_5646_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5599_)) as u8;
                        if v_isSharedCheck_5646_ == 0 {
                            v___x_5641_ = v___x_5599_;
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 55;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5639_);
                            crate::leanh::lean_dec(v___x_5599_);
                            v___x_5641_ = crate::leanh::lean_box(0);
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 55;
                            continue;
                        }
                    }
                }
            }
            39 => {
                v___x_5570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5570_, 0, v_a_5566_);
                if v_isShared_5569_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5568_, 0, v___x_5570_);
                    v___x_5572_ = v___x_5568_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5573_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
                    v___x_5572_ = v_reuseFailAlloc_5573_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_5572_;
            }
            41 => {
                if v_isShared_5578_ == 0 {
                    v___x_5580_ = v___x_5577_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_5581_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
                    v___x_5580_ = v_reuseFailAlloc_5581_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_5580_;
            }
            43 => {
                if v_isShared_5586_ == 0 {
                    v___x_5588_ = v___x_5585_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_5589_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
                    v___x_5588_ = v_reuseFailAlloc_5589_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_5588_;
            }
            45 => {
                if v_isShared_5594_ == 0 {
                    v___x_5596_ = v___x_5593_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_5597_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
                    v___x_5596_ = v_reuseFailAlloc_5597_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5596_;
            }
            47 => {
                v___x_5610_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5610_, 0, v_a_5606_);
                if v_isShared_5609_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5608_, 0, v___x_5610_);
                    v___x_5612_ = v___x_5608_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5610_);
                    v___x_5612_ = v_reuseFailAlloc_5613_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_5612_;
            }
            49 => {
                if v_isShared_5618_ == 0 {
                    v___x_5620_ = v___x_5617_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
                    v___x_5620_ = v_reuseFailAlloc_5621_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5620_;
            }
            51 => {
                if v_isShared_5626_ == 0 {
                    v___x_5628_ = v___x_5625_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5629_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
                    v___x_5628_ = v_reuseFailAlloc_5629_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5628_;
            }
            53 => {
                if v_isShared_5634_ == 0 {
                    v___x_5636_ = v___x_5633_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5637_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5631_);
                    v___x_5636_ = v_reuseFailAlloc_5637_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_5636_;
            }
            55 => {
                if v_isShared_5642_ == 0 {
                    v___x_5644_ = v___x_5641_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_5645_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
                    v___x_5644_ = v_reuseFailAlloc_5645_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_5644_;
            }
            57 => {
                v___y_5546_ = v___x_5657_;
                v___y_5547_ = v_a_5335_;
                v___y_5548_ = v_a_5336_;
                v___y_5549_ = v_a_5337_;
                v___y_5550_ = v_a_5338_;
                v___y_5551_ = v_a_5339_;
                v___y_5552_ = v_a_5340_;
                state = 38;
                continue;
            }
            58 => {
                if v_isShared_5662_ == 0 {
                    v___x_5664_ = v___x_5661_;
                    state = 59;
                    continue;
                } else {
                    v_reuseFailAlloc_5665_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
                    v___x_5664_ = v_reuseFailAlloc_5665_;
                    state = 59;
                    continue;
                }
            }
            59 => {
                return v___x_5664_;
            }
            60 => {
                return v___x_5670_;
            }
            61 => {
                if v_isShared_5676_ == 0 {
                    v___x_5678_ = v___x_5675_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_5679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5673_);
                    v___x_5678_ = v_reuseFailAlloc_5679_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                return v___x_5678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5684_: u8 = 0;
    let mut v___x_5685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5684_ = 0;
    v___x_5685_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_5684_);
    return v___x_5685_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(
    mut v_cases_5686_: *mut crate::leanh::LeanObject,
    mut v_a_5687_: *mut crate::leanh::LeanObject,
    mut v_a_5688_: *mut crate::leanh::LeanObject,
    mut v_a_5689_: *mut crate::leanh::LeanObject,
    mut v_a_5690_: *mut crate::leanh::LeanObject,
    mut v_a_5691_: *mut crate::leanh::LeanObject,
    mut v_a_5692_: *mut crate::leanh::LeanObject,
    mut v_a_5693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_5698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_5701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: u8 = 0;
    let mut v___x_5704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5710_: u8 = 0;
    let mut v_val_5711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v___x_5715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5722_: u8 = 0;
    let mut v_val_5723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v_induct_5727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: u8 = 0;
    let mut v___x_5729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5738_: u8 = 0;
    let mut v___x_5740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_5746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_5748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_5749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5751_: usize = 0;
    let mut v___x_5752_: usize = 0;
    let mut v___x_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_unused_5767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5771_: u8 = 0;
    let mut v___x_5773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5775_: u8 = 0;
    let mut v_a_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5779_: u8 = 0;
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5783_: u8 = 0;
    let mut v_a_5784_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut v_numParams_5792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: u8 = 0;
    let mut v_params_5796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5801_: u8 = 0;
    let mut v_zero_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5803_: u8 = 0;
    let mut v___x_5804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5808_: u8 = 0;
    let mut v___x_5810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5815_: u8 = 0;
    let mut v_a_5816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5823_: u8 = 0;
    let mut v_one_5824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5853_: u8 = 0;
    let mut v_unused_5854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5858_: u8 = 0;
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5862_: u8 = 0;
    let mut v_a_5863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5866_: u8 = 0;
    let mut v___x_5868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_a_5871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v___x_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5878_: u8 = 0;
    let mut v_a_5879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5882_: u8 = 0;
    let mut v___x_5884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut v_reuseFailAlloc_5887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v_code_5890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5895_: u8 = 0;
    let mut v___x_5897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut v_a_5903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5906_: u8 = 0;
    let mut v___x_5908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5910_: u8 = 0;
    let mut v_a_5911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5914_: u8 = 0;
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5918_: u8 = 0;
    let mut v_a_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v___x_5924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut v_reuseFailAlloc_5927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut v_isSharedCheck_5929_: u8 = 0;
    let mut v_isSharedCheck_5930_: u8 = 0;
    let mut v_isSharedCheck_5931_: u8 = 0;
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5936_: u8 = 0;
    let mut v_a_5937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5940_: u8 = 0;
    let mut v___x_5942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5944_: u8 = 0;
    let mut v___x_5945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5949_: u8 = 0;
    let mut v___x_5950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5954_: u8 = 0;
    let mut v_a_5955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v___x_5960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_5698_ = crate::leanh::lean_ctor_get(v_cases_5686_, 0);
                v_discr_5699_ = crate::leanh::lean_ctor_get(v_cases_5686_, 2);
                v___x_5700_ = lean_st_ref_get(v_a_5688_);
                v_subst_5701_ = crate::leanh::lean_ctor_get(v___x_5700_, 0);
                crate::leanh::lean_inc_ref(v_subst_5701_);
                crate::leanh::lean_dec(v___x_5700_);
                v___x_5702_ = 0;
                v___x_5703_ = 0;
                crate::leanh::lean_inc(v_discr_5699_);
                v___x_5704_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v_subst_5701_,
                    v_discr_5699_,
                    v___x_5703_,
                );
                crate::leanh::lean_dec_ref(v_subst_5701_);
                if crate::leanh::lean_obj_tag(v___x_5704_) == 0 {
                    v_fvarId_5705_ = crate::leanh::lean_ctor_get(v___x_5704_, 0);
                    crate::leanh::lean_inc(v_fvarId_5705_);
                    crate::leanh::lean_dec_ref_known(v___x_5704_, 1);
                    v___x_5706_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
                        v_fvarId_5705_,
                        v_a_5689_,
                        v_a_5691_,
                        v_a_5693_,
                    );
                    crate::leanh::lean_dec(v_fvarId_5705_);
                    if crate::leanh::lean_obj_tag(v___x_5706_) == 0 {
                        v_a_5707_ = crate::leanh::lean_ctor_get(v___x_5706_, 0);
                        v_isSharedCheck_5936_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5706_)) as u8;
                        if v_isSharedCheck_5936_ == 0 {
                            v___x_5709_ = v___x_5706_;
                            v_isShared_5710_ = v_isSharedCheck_5936_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5707_);
                            crate::leanh::lean_dec(v___x_5706_);
                            v___x_5709_ = crate::leanh::lean_box(0);
                            v_isShared_5710_ = v_isSharedCheck_5936_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_cases_5686_);
                        v_a_5937_ = crate::leanh::lean_ctor_get(v___x_5706_, 0);
                        v_isSharedCheck_5944_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5706_)) as u8;
                        if v_isSharedCheck_5944_ == 0 {
                            v___x_5939_ = v___x_5706_;
                            v_isShared_5940_ = v_isSharedCheck_5944_;
                            state = 49;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5937_);
                            crate::leanh::lean_dec(v___x_5706_);
                            v___x_5939_ = crate::leanh::lean_box(0);
                            v_isShared_5940_ = v_isSharedCheck_5944_;
                            state = 49;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_cases_5686_);
                    v___x_5945_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v___x_5702_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5945_) == 0 {
                        v_a_5946_ = crate::leanh::lean_ctor_get(v___x_5945_, 0);
                        v_isSharedCheck_5954_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5945_)) as u8;
                        if v_isSharedCheck_5954_ == 0 {
                            v___x_5948_ = v___x_5945_;
                            v_isShared_5949_ = v_isSharedCheck_5954_;
                            state = 51;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5946_);
                            crate::leanh::lean_dec(v___x_5945_);
                            v___x_5948_ = crate::leanh::lean_box(0);
                            v_isShared_5949_ = v_isSharedCheck_5954_;
                            state = 51;
                            continue;
                        }
                    } else {
                        v_a_5955_ = crate::leanh::lean_ctor_get(v___x_5945_, 0);
                        v_isSharedCheck_5962_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5945_)) as u8;
                        if v_isSharedCheck_5962_ == 0 {
                            v___x_5957_ = v___x_5945_;
                            v_isShared_5958_ = v_isSharedCheck_5962_;
                            state = 53;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5955_);
                            crate::leanh::lean_dec(v___x_5945_);
                            v___x_5957_ = crate::leanh::lean_box(0);
                            v_isShared_5958_ = v_isSharedCheck_5962_;
                            state = 53;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5696_ = crate::leanh::lean_box(0);
                v___x_5697_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5697_, 0, v___x_5696_);
                return v___x_5697_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5707_) == 1 {
                    v_val_5711_ = crate::leanh::lean_ctor_get(v_a_5707_, 0);
                    v_isSharedCheck_5931_ = (!crate::leanh::lean_is_exclusive(v_a_5707_)) as u8;
                    if v_isSharedCheck_5931_ == 0 {
                        v___x_5713_ = v_a_5707_;
                        v_isShared_5714_ = v_isSharedCheck_5931_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5711_);
                        crate::leanh::lean_dec(v_a_5707_);
                        v___x_5713_ = crate::leanh::lean_box(0);
                        v_isShared_5714_ = v_isSharedCheck_5931_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_5707_);
                    crate::leanh::lean_dec_ref(v_cases_5686_);
                    v___x_5932_ = crate::leanh::lean_box(0);
                    if v_isShared_5710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5709_, 0, v___x_5932_);
                        v___x_5934_ = v___x_5709_;
                        state = 48;
                        continue;
                    } else {
                        v_reuseFailAlloc_5935_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5935_, 0, v___x_5932_);
                        v___x_5934_ = v_reuseFailAlloc_5935_;
                        state = 48;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5715_ = lean_st_ref_get(v_a_5693_);
                v_env_5716_ = crate::leanh::lean_ctor_get(v___x_5715_, 0);
                crate::leanh::lean_inc_ref(v_env_5716_);
                crate::leanh::lean_dec(v___x_5715_);
                v___x_5717_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_5711_);
                crate::leanh::lean_inc(v___x_5717_);
                v___x_5718_ = l_Lean_Environment_find_x3f(v_env_5716_, v___x_5717_, v___x_5703_);
                if crate::leanh::lean_obj_tag(v___x_5718_) == 1 {
                    v_val_5719_ = crate::leanh::lean_ctor_get(v___x_5718_, 0);
                    v_isSharedCheck_5930_ = (!crate::leanh::lean_is_exclusive(v___x_5718_)) as u8;
                    if v_isSharedCheck_5930_ == 0 {
                        v___x_5721_ = v___x_5718_;
                        v_isShared_5722_ = v_isSharedCheck_5930_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5719_);
                        crate::leanh::lean_dec(v___x_5718_);
                        v___x_5721_ = crate::leanh::lean_box(0);
                        v_isShared_5722_ = v_isSharedCheck_5930_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_5718_);
                    crate::leanh::lean_dec(v___x_5717_);
                    crate::leanh::lean_del_object(v___x_5713_);
                    crate::leanh::lean_dec(v_val_5711_);
                    crate::leanh::lean_del_object(v___x_5709_);
                    crate::leanh::lean_dec_ref(v_cases_5686_);
                    state = 1;
                    continue;
                }
            }
            4 => {
                if crate::leanh::lean_obj_tag(v_val_5719_) == 6 {
                    v_val_5723_ = crate::leanh::lean_ctor_get(v_val_5719_, 0);
                    v_isSharedCheck_5929_ = (!crate::leanh::lean_is_exclusive(v_val_5719_)) as u8;
                    if v_isSharedCheck_5929_ == 0 {
                        v___x_5725_ = v_val_5719_;
                        v_isShared_5726_ = v_isSharedCheck_5929_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_5723_);
                        crate::leanh::lean_dec(v_val_5719_);
                        v___x_5725_ = crate::leanh::lean_box(0);
                        v_isShared_5726_ = v_isSharedCheck_5929_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5721_);
                    crate::leanh::lean_dec(v_val_5719_);
                    crate::leanh::lean_dec(v___x_5717_);
                    crate::leanh::lean_del_object(v___x_5713_);
                    crate::leanh::lean_dec(v_val_5711_);
                    crate::leanh::lean_del_object(v___x_5709_);
                    crate::leanh::lean_dec_ref(v_cases_5686_);
                    state = 1;
                    continue;
                }
            }
            5 => {
                v_induct_5727_ = crate::leanh::lean_ctor_get(v_val_5723_, 1);
                crate::leanh::lean_inc(v_induct_5727_);
                crate::leanh::lean_dec_ref(v_val_5723_);
                v___x_5728_ = lean_name_eq(v_typeName_5698_, v_induct_5727_);
                crate::leanh::lean_dec(v_induct_5727_);
                if v___x_5728_ == 0 {
                    crate::leanh::lean_del_object(v___x_5725_);
                    crate::leanh::lean_del_object(v___x_5721_);
                    crate::leanh::lean_dec(v___x_5717_);
                    crate::leanh::lean_del_object(v___x_5713_);
                    crate::leanh::lean_dec(v_val_5711_);
                    crate::leanh::lean_dec_ref(v_cases_5686_);
                    v___x_5729_ = crate::leanh::lean_box(0);
                    if v_isShared_5710_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5709_, 0, v___x_5729_);
                        v___x_5731_ = v___x_5709_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5732_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 0, v___x_5729_);
                        v___x_5731_ = v_reuseFailAlloc_5732_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5709_);
                    v___x_5733_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(
                        v___x_5702_,
                        v_cases_5686_,
                        v___x_5717_,
                    );
                    v_fst_5734_ = crate::leanh::lean_ctor_get(v___x_5733_, 0);
                    v_snd_5735_ = crate::leanh::lean_ctor_get(v___x_5733_, 1);
                    v_isSharedCheck_5928_ = (!crate::leanh::lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5928_ == 0 {
                        v___x_5737_ = v___x_5733_;
                        v_isShared_5738_ = v_isSharedCheck_5928_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5735_);
                        crate::leanh::lean_inc(v_fst_5734_);
                        crate::leanh::lean_dec(v___x_5733_);
                        v___x_5737_ = crate::leanh::lean_box(0);
                        v_isShared_5738_ = v_isSharedCheck_5928_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                return v___x_5731_;
            }
            7 => {
                if v_isShared_5726_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5725_, 4);
                    crate::leanh::lean_ctor_set(v___x_5725_, 0, v_snd_5735_);
                    v___x_5740_ = v___x_5725_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_snd_5735_);
                    v___x_5740_ = v_reuseFailAlloc_5927_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5741_ =
                    l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5702_, v___x_5740_, v_a_5691_);
                crate::leanh::lean_dec_ref(v___x_5740_);
                if crate::leanh::lean_obj_tag(v___x_5741_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5741_, 1);
                    v___x_5742_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_5688_);
                    if crate::leanh::lean_obj_tag(v___x_5742_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5742_, 1);
                        if crate::leanh::lean_obj_tag(v_fst_5734_) == 0 {
                            if crate::leanh::lean_obj_tag(v_val_5711_) == 0 {
                                crate::leanh::lean_del_object(v___x_5737_);
                                crate::leanh::lean_del_object(v___x_5713_);
                                v_params_5743_ = crate::leanh::lean_ctor_get(v_fst_5734_, 1);
                                crate::leanh::lean_inc_ref(v_params_5743_);
                                v_code_5744_ = crate::leanh::lean_ctor_get(v_fst_5734_, 2);
                                crate::leanh::lean_inc_ref(v_code_5744_);
                                crate::leanh::lean_dec_ref_known(v_fst_5734_, 3);
                                v_val_5745_ = crate::leanh::lean_ctor_get(v_val_5711_, 0);
                                crate::leanh::lean_inc_ref(v_val_5745_);
                                v_args_5746_ = crate::leanh::lean_ctor_get(v_val_5711_, 1);
                                crate::leanh::lean_inc_ref(v_args_5746_);
                                crate::leanh::lean_dec_ref_known(v_val_5711_, 2);
                                v_numParams_5792_ = crate::leanh::lean_ctor_get(v_val_5745_, 3);
                                crate::leanh::lean_inc(v_numParams_5792_);
                                crate::leanh::lean_dec_ref(v_val_5745_);
                                v___x_5793_ = crate::leanh::lean_unsigned_to_nat(0);
                                v___x_5794_ = lean_array_get_size(v_args_5746_);
                                v___x_5795_ = lean_nat_dec_le(v_numParams_5792_, v___x_5793_);
                                if v___x_5795_ == 0 {
                                    v_lower_5748_ = v_numParams_5792_;
                                    v_upper_5749_ = v___x_5794_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_numParams_5792_);
                                    v_lower_5748_ = v___x_5793_;
                                    v_upper_5749_ = v___x_5794_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v_params_5796_ = crate::leanh::lean_ctor_get(v_fst_5734_, 1);
                                crate::leanh::lean_inc_ref(v_params_5796_);
                                v_code_5797_ = crate::leanh::lean_ctor_get(v_fst_5734_, 2);
                                crate::leanh::lean_inc_ref(v_code_5797_);
                                crate::leanh::lean_dec_ref_known(v_fst_5734_, 3);
                                v_n_5798_ = crate::leanh::lean_ctor_get(v_val_5711_, 0);
                                v_isSharedCheck_5889_ =
                                    (!crate::leanh::lean_is_exclusive(v_val_5711_)) as u8;
                                if v_isSharedCheck_5889_ == 0 {
                                    v___x_5800_ = v_val_5711_;
                                    v_isShared_5801_ = v_isSharedCheck_5889_;
                                    state = 19;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_n_5798_);
                                    crate::leanh::lean_dec(v_val_5711_);
                                    v___x_5800_ = crate::leanh::lean_box(0);
                                    v_isShared_5801_ = v_isSharedCheck_5889_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_5737_);
                            crate::leanh::lean_del_object(v___x_5713_);
                            crate::leanh::lean_dec(v_val_5711_);
                            v_code_5890_ = crate::leanh::lean_ctor_get(v_fst_5734_, 0);
                            crate::leanh::lean_inc_ref(v_code_5890_);
                            crate::leanh::lean_dec_ref_known(v_fst_5734_, 1);
                            crate::leanh::lean_inc_ref(v_a_5692_);
                            v___x_5891_ = l_Lean_Compiler_LCNF_Simp_simp(
                                v_code_5890_,
                                v_a_5687_,
                                v_a_5688_,
                                v_a_5689_,
                                v_a_5690_,
                                v_a_5691_,
                                v_a_5692_,
                                v_a_5693_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_5891_) == 0 {
                                v_a_5892_ = crate::leanh::lean_ctor_get(v___x_5891_, 0);
                                v_isSharedCheck_5902_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5891_)) as u8;
                                if v_isSharedCheck_5902_ == 0 {
                                    v___x_5894_ = v___x_5891_;
                                    v_isShared_5895_ = v_isSharedCheck_5902_;
                                    state = 39;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5892_);
                                    crate::leanh::lean_dec(v___x_5891_);
                                    v___x_5894_ = crate::leanh::lean_box(0);
                                    v_isShared_5895_ = v_isSharedCheck_5902_;
                                    state = 39;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_5721_);
                                v_a_5903_ = crate::leanh::lean_ctor_get(v___x_5891_, 0);
                                v_isSharedCheck_5910_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5891_)) as u8;
                                if v_isSharedCheck_5910_ == 0 {
                                    v___x_5905_ = v___x_5891_;
                                    v_isShared_5906_ = v_isSharedCheck_5910_;
                                    state = 42;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5903_);
                                    crate::leanh::lean_dec(v___x_5891_);
                                    v___x_5905_ = crate::leanh::lean_box(0);
                                    v_isShared_5906_ = v_isSharedCheck_5910_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5737_);
                        crate::leanh::lean_dec(v_fst_5734_);
                        crate::leanh::lean_del_object(v___x_5721_);
                        crate::leanh::lean_del_object(v___x_5713_);
                        crate::leanh::lean_dec(v_val_5711_);
                        v_a_5911_ = crate::leanh::lean_ctor_get(v___x_5742_, 0);
                        v_isSharedCheck_5918_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5742_)) as u8;
                        if v_isSharedCheck_5918_ == 0 {
                            v___x_5913_ = v___x_5742_;
                            v_isShared_5914_ = v_isSharedCheck_5918_;
                            state = 44;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5911_);
                            crate::leanh::lean_dec(v___x_5742_);
                            v___x_5913_ = crate::leanh::lean_box(0);
                            v_isShared_5914_ = v_isSharedCheck_5918_;
                            state = 44;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5737_);
                    crate::leanh::lean_dec(v_fst_5734_);
                    crate::leanh::lean_del_object(v___x_5721_);
                    crate::leanh::lean_del_object(v___x_5713_);
                    crate::leanh::lean_dec(v_val_5711_);
                    v_a_5919_ = crate::leanh::lean_ctor_get(v___x_5741_, 0);
                    v_isSharedCheck_5926_ = (!crate::leanh::lean_is_exclusive(v___x_5741_)) as u8;
                    if v_isSharedCheck_5926_ == 0 {
                        v___x_5921_ = v___x_5741_;
                        v_isShared_5922_ = v_isSharedCheck_5926_;
                        state = 46;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5919_);
                        crate::leanh::lean_dec(v___x_5741_);
                        v___x_5921_ = crate::leanh::lean_box(0);
                        v_isShared_5922_ = v_isSharedCheck_5926_;
                        state = 46;
                        continue;
                    }
                }
            }
            9 => {
                v___x_5750_ =
                    l_Array_toSubarray___redArg(v_args_5746_, v_lower_5748_, v_upper_5749_);
                v_sz_5751_ = lean_array_size(v_params_5743_);
                v___x_5752_ = 0usize;
                v___x_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_params_5743_, v_sz_5751_, v___x_5752_, v___x_5750_, v_a_5688_);
                if crate::leanh::lean_obj_tag(v___x_5753_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5753_, 1);
                    crate::leanh::lean_inc_ref(v_a_5692_);
                    v___x_5754_ = l_Lean_Compiler_LCNF_Simp_simp(
                        v_code_5744_,
                        v_a_5687_,
                        v_a_5688_,
                        v_a_5689_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5754_) == 0 {
                        v_a_5755_ = crate::leanh::lean_ctor_get(v___x_5754_, 0);
                        crate::leanh::lean_inc(v_a_5755_);
                        crate::leanh::lean_dec_ref_known(v___x_5754_, 1);
                        v___x_5756_ = l_Lean_Compiler_LCNF_eraseParams___redArg(
                            v___x_5702_,
                            v_params_5743_,
                            v_a_5691_,
                        );
                        crate::leanh::lean_dec_ref(v_params_5743_);
                        if crate::leanh::lean_obj_tag(v___x_5756_) == 0 {
                            v_isSharedCheck_5766_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5766_ == 0 {
                                v_unused_5767_ = crate::leanh::lean_ctor_get(v___x_5756_, 0);
                                crate::leanh::lean_dec(v_unused_5767_);
                                v___x_5758_ = v___x_5756_;
                                v_isShared_5759_ = v_isSharedCheck_5766_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_5756_);
                                v___x_5758_ = crate::leanh::lean_box(0);
                                v_isShared_5759_ = v_isSharedCheck_5766_;
                                state = 10;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5755_);
                            crate::leanh::lean_del_object(v___x_5721_);
                            v_a_5768_ = crate::leanh::lean_ctor_get(v___x_5756_, 0);
                            v_isSharedCheck_5775_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5775_ == 0 {
                                v___x_5770_ = v___x_5756_;
                                v_isShared_5771_ = v_isSharedCheck_5775_;
                                state = 13;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5768_);
                                crate::leanh::lean_dec(v___x_5756_);
                                v___x_5770_ = crate::leanh::lean_box(0);
                                v_isShared_5771_ = v_isSharedCheck_5775_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_params_5743_);
                        crate::leanh::lean_del_object(v___x_5721_);
                        v_a_5776_ = crate::leanh::lean_ctor_get(v___x_5754_, 0);
                        v_isSharedCheck_5783_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5754_)) as u8;
                        if v_isSharedCheck_5783_ == 0 {
                            v___x_5778_ = v___x_5754_;
                            v_isShared_5779_ = v_isSharedCheck_5783_;
                            state = 15;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5776_);
                            crate::leanh::lean_dec(v___x_5754_);
                            v___x_5778_ = crate::leanh::lean_box(0);
                            v_isShared_5779_ = v_isSharedCheck_5783_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_code_5744_);
                    crate::leanh::lean_dec_ref(v_params_5743_);
                    crate::leanh::lean_del_object(v___x_5721_);
                    v_a_5784_ = crate::leanh::lean_ctor_get(v___x_5753_, 0);
                    v_isSharedCheck_5791_ = (!crate::leanh::lean_is_exclusive(v___x_5753_)) as u8;
                    if v_isSharedCheck_5791_ == 0 {
                        v___x_5786_ = v___x_5753_;
                        v_isShared_5787_ = v_isSharedCheck_5791_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5784_);
                        crate::leanh::lean_dec(v___x_5753_);
                        v___x_5786_ = crate::leanh::lean_box(0);
                        v_isShared_5787_ = v_isSharedCheck_5791_;
                        state = 17;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_5722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5721_, 0, v_a_5755_);
                    v___x_5761_ = v___x_5721_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5755_);
                    v___x_5761_ = v_reuseFailAlloc_5765_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5759_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5758_, 0, v___x_5761_);
                    v___x_5763_ = v___x_5758_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5764_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5761_);
                    v___x_5763_ = v_reuseFailAlloc_5764_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_5763_;
            }
            13 => {
                if v_isShared_5771_ == 0 {
                    v___x_5773_ = v___x_5770_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5774_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_a_5768_);
                    v___x_5773_ = v_reuseFailAlloc_5774_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5773_;
            }
            15 => {
                if v_isShared_5779_ == 0 {
                    v___x_5781_ = v___x_5778_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_5782_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_a_5776_);
                    v___x_5781_ = v_reuseFailAlloc_5782_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_5781_;
            }
            17 => {
                if v_isShared_5787_ == 0 {
                    v___x_5789_ = v___x_5786_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5790_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
                    v___x_5789_ = v_reuseFailAlloc_5790_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5789_;
            }
            19 => {
                v_zero_5802_ = crate::leanh::lean_unsigned_to_nat(0);
                v_isZero_5803_ = lean_nat_dec_eq(v_n_5798_, v_zero_5802_);
                if v_isZero_5803_ == 1 {
                    crate::leanh::lean_del_object(v___x_5800_);
                    crate::leanh::lean_dec(v_n_5798_);
                    crate::leanh::lean_dec_ref(v_params_5796_);
                    crate::leanh::lean_del_object(v___x_5737_);
                    crate::leanh::lean_del_object(v___x_5713_);
                    crate::leanh::lean_inc_ref(v_a_5692_);
                    v___x_5804_ = l_Lean_Compiler_LCNF_Simp_simp(
                        v_code_5797_,
                        v_a_5687_,
                        v_a_5688_,
                        v_a_5689_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5804_) == 0 {
                        v_a_5805_ = crate::leanh::lean_ctor_get(v___x_5804_, 0);
                        v_isSharedCheck_5815_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5804_)) as u8;
                        if v_isSharedCheck_5815_ == 0 {
                            v___x_5807_ = v___x_5804_;
                            v_isShared_5808_ = v_isSharedCheck_5815_;
                            state = 20;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5805_);
                            crate::leanh::lean_dec(v___x_5804_);
                            v___x_5807_ = crate::leanh::lean_box(0);
                            v_isShared_5808_ = v_isSharedCheck_5815_;
                            state = 20;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_5721_);
                        v_a_5816_ = crate::leanh::lean_ctor_get(v___x_5804_, 0);
                        v_isSharedCheck_5823_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5804_)) as u8;
                        if v_isSharedCheck_5823_ == 0 {
                            v___x_5818_ = v___x_5804_;
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5816_);
                            crate::leanh::lean_dec(v___x_5804_);
                            v___x_5818_ = crate::leanh::lean_box(0);
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    v_one_5824_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_n_5825_ = lean_nat_sub(v_n_5798_, v_one_5824_);
                    crate::leanh::lean_dec(v_n_5798_);
                    if v_isShared_5801_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_5800_, 0);
                        crate::leanh::lean_ctor_set(v___x_5800_, 0, v_n_5825_);
                        v___x_5827_ = v___x_5800_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_5888_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_n_5825_);
                        v___x_5827_ = v_reuseFailAlloc_5888_;
                        state = 25;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_5722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5721_, 0, v_a_5805_);
                    v___x_5810_ = v___x_5721_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5814_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_a_5805_);
                    v___x_5810_ = v_reuseFailAlloc_5814_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_5808_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5807_, 0, v___x_5810_);
                    v___x_5812_ = v___x_5807_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5810_);
                    v___x_5812_ = v_reuseFailAlloc_5813_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_5812_;
            }
            23 => {
                if v_isShared_5819_ == 0 {
                    v___x_5821_ = v___x_5818_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_5822_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_a_5816_);
                    v___x_5821_ = v_reuseFailAlloc_5822_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_5821_;
            }
            25 => {
                if v_isShared_5714_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_5713_, 0);
                    crate::leanh::lean_ctor_set(v___x_5713_, 0, v___x_5827_);
                    v___x_5829_ = v___x_5713_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5887_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5887_, 0, v___x_5827_);
                    v___x_5829_ = v_reuseFailAlloc_5887_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                v___x_5830_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1;
                v___x_5831_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
                    v___x_5702_,
                    v___x_5829_,
                    v___x_5830_,
                    v_a_5690_,
                    v_a_5691_,
                    v_a_5692_,
                    v_a_5693_,
                );
                if crate::leanh::lean_obj_tag(v___x_5831_) == 0 {
                    v_a_5832_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                    crate::leanh::lean_inc(v_a_5832_);
                    crate::leanh::lean_dec_ref_known(v___x_5831_, 1);
                    v___x_5833_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0,
                    );
                    v___x_5834_ =
                        lean_array_get_borrowed(v___x_5833_, v_params_5796_, v_zero_5802_);
                    v_fvarId_5835_ = crate::leanh::lean_ctor_get(v___x_5834_, 0);
                    v_fvarId_5836_ = crate::leanh::lean_ctor_get(v_a_5832_, 0);
                    crate::leanh::lean_inc(v_fvarId_5836_);
                    crate::leanh::lean_inc(v_fvarId_5835_);
                    v___x_5837_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_5835_,
                        v_fvarId_5836_,
                        v_a_5688_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_5837_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5837_, 1);
                        crate::leanh::lean_inc_ref(v_a_5692_);
                        v___x_5838_ = l_Lean_Compiler_LCNF_Simp_simp(
                            v_code_5797_,
                            v_a_5687_,
                            v_a_5688_,
                            v_a_5689_,
                            v_a_5690_,
                            v_a_5691_,
                            v_a_5692_,
                            v_a_5693_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_5838_) == 0 {
                            v_a_5839_ = crate::leanh::lean_ctor_get(v___x_5838_, 0);
                            crate::leanh::lean_inc(v_a_5839_);
                            crate::leanh::lean_dec_ref_known(v___x_5838_, 1);
                            v___x_5840_ = l_Lean_Compiler_LCNF_eraseParams___redArg(
                                v___x_5702_,
                                v_params_5796_,
                                v_a_5691_,
                            );
                            crate::leanh::lean_dec_ref(v_params_5796_);
                            if crate::leanh::lean_obj_tag(v___x_5840_) == 0 {
                                v_isSharedCheck_5853_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5840_)) as u8;
                                if v_isSharedCheck_5853_ == 0 {
                                    v_unused_5854_ = crate::leanh::lean_ctor_get(v___x_5840_, 0);
                                    crate::leanh::lean_dec(v_unused_5854_);
                                    v___x_5842_ = v___x_5840_;
                                    v_isShared_5843_ = v_isSharedCheck_5853_;
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_5840_);
                                    v___x_5842_ = crate::leanh::lean_box(0);
                                    v_isShared_5843_ = v_isSharedCheck_5853_;
                                    state = 27;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_5839_);
                                crate::leanh::lean_dec(v_a_5832_);
                                crate::leanh::lean_del_object(v___x_5737_);
                                crate::leanh::lean_del_object(v___x_5721_);
                                v_a_5855_ = crate::leanh::lean_ctor_get(v___x_5840_, 0);
                                v_isSharedCheck_5862_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_5840_)) as u8;
                                if v_isSharedCheck_5862_ == 0 {
                                    v___x_5857_ = v___x_5840_;
                                    v_isShared_5858_ = v_isSharedCheck_5862_;
                                    state = 31;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_5855_);
                                    crate::leanh::lean_dec(v___x_5840_);
                                    v___x_5857_ = crate::leanh::lean_box(0);
                                    v_isShared_5858_ = v_isSharedCheck_5862_;
                                    state = 31;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_5832_);
                            crate::leanh::lean_dec_ref(v_params_5796_);
                            crate::leanh::lean_del_object(v___x_5737_);
                            crate::leanh::lean_del_object(v___x_5721_);
                            v_a_5863_ = crate::leanh::lean_ctor_get(v___x_5838_, 0);
                            v_isSharedCheck_5870_ =
                                (!crate::leanh::lean_is_exclusive(v___x_5838_)) as u8;
                            if v_isSharedCheck_5870_ == 0 {
                                v___x_5865_ = v___x_5838_;
                                v_isShared_5866_ = v_isSharedCheck_5870_;
                                state = 33;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_5863_);
                                crate::leanh::lean_dec(v___x_5838_);
                                v___x_5865_ = crate::leanh::lean_box(0);
                                v_isShared_5866_ = v_isSharedCheck_5870_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_5832_);
                        crate::leanh::lean_dec_ref(v_code_5797_);
                        crate::leanh::lean_dec_ref(v_params_5796_);
                        crate::leanh::lean_del_object(v___x_5737_);
                        crate::leanh::lean_del_object(v___x_5721_);
                        v_a_5871_ = crate::leanh::lean_ctor_get(v___x_5837_, 0);
                        v_isSharedCheck_5878_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5837_)) as u8;
                        if v_isSharedCheck_5878_ == 0 {
                            v___x_5873_ = v___x_5837_;
                            v_isShared_5874_ = v_isSharedCheck_5878_;
                            state = 35;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5871_);
                            crate::leanh::lean_dec(v___x_5837_);
                            v___x_5873_ = crate::leanh::lean_box(0);
                            v_isShared_5874_ = v_isSharedCheck_5878_;
                            state = 35;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_code_5797_);
                    crate::leanh::lean_dec_ref(v_params_5796_);
                    crate::leanh::lean_del_object(v___x_5737_);
                    crate::leanh::lean_del_object(v___x_5721_);
                    v_a_5879_ = crate::leanh::lean_ctor_get(v___x_5831_, 0);
                    v_isSharedCheck_5886_ = (!crate::leanh::lean_is_exclusive(v___x_5831_)) as u8;
                    if v_isSharedCheck_5886_ == 0 {
                        v___x_5881_ = v___x_5831_;
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 37;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5879_);
                        crate::leanh::lean_dec(v___x_5831_);
                        v___x_5881_ = crate::leanh::lean_box(0);
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 37;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_5738_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5737_, 1, v_a_5839_);
                    crate::leanh::lean_ctor_set(v___x_5737_, 0, v_a_5832_);
                    v___x_5845_ = v___x_5737_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_a_5832_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5852_, 1, v_a_5839_);
                    v___x_5845_ = v_reuseFailAlloc_5852_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_5722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5721_, 0, v___x_5845_);
                    v___x_5847_ = v___x_5721_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5851_, 0, v___x_5845_);
                    v___x_5847_ = v_reuseFailAlloc_5851_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_5843_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5842_, 0, v___x_5847_);
                    v___x_5849_ = v___x_5842_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5850_, 0, v___x_5847_);
                    v___x_5849_ = v_reuseFailAlloc_5850_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_5849_;
            }
            31 => {
                if v_isShared_5858_ == 0 {
                    v___x_5860_ = v___x_5857_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_5861_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5855_);
                    v___x_5860_ = v_reuseFailAlloc_5861_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_5860_;
            }
            33 => {
                if v_isShared_5866_ == 0 {
                    v___x_5868_ = v___x_5865_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_5869_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
                    v___x_5868_ = v_reuseFailAlloc_5869_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_5868_;
            }
            35 => {
                if v_isShared_5874_ == 0 {
                    v___x_5876_ = v___x_5873_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_5877_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
                    v___x_5876_ = v_reuseFailAlloc_5877_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_5876_;
            }
            37 => {
                if v_isShared_5882_ == 0 {
                    v___x_5884_ = v___x_5881_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_5885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
                    v___x_5884_ = v_reuseFailAlloc_5885_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_5884_;
            }
            39 => {
                if v_isShared_5722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5721_, 0, v_a_5892_);
                    v___x_5897_ = v___x_5721_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5892_);
                    v___x_5897_ = v_reuseFailAlloc_5901_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_5895_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5894_, 0, v___x_5897_);
                    v___x_5899_ = v___x_5894_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5900_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5897_);
                    v___x_5899_ = v_reuseFailAlloc_5900_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_5899_;
            }
            42 => {
                if v_isShared_5906_ == 0 {
                    v___x_5908_ = v___x_5905_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_5909_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_a_5903_);
                    v___x_5908_ = v_reuseFailAlloc_5909_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_5908_;
            }
            44 => {
                if v_isShared_5914_ == 0 {
                    v___x_5916_ = v___x_5913_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_5917_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
                    v___x_5916_ = v_reuseFailAlloc_5917_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_5916_;
            }
            46 => {
                if v_isShared_5922_ == 0 {
                    v___x_5924_ = v___x_5921_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_5925_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5919_);
                    v___x_5924_ = v_reuseFailAlloc_5925_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_5924_;
            }
            48 => {
                return v___x_5934_;
            }
            49 => {
                if v_isShared_5940_ == 0 {
                    v___x_5942_ = v___x_5939_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_5943_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5943_, 0, v_a_5937_);
                    v___x_5942_ = v_reuseFailAlloc_5943_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5942_;
            }
            51 => {
                v___x_5950_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_5950_, 0, v_a_5946_);
                if v_isShared_5949_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5948_, 0, v___x_5950_);
                    v___x_5952_ = v___x_5948_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5953_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5950_);
                    v___x_5952_ = v_reuseFailAlloc_5953_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_5952_;
            }
            53 => {
                if v_isShared_5958_ == 0 {
                    v___x_5960_ = v___x_5957_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_5961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_a_5955_);
                    v___x_5960_ = v_reuseFailAlloc_5961_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_5960_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(
    mut v_fvarId_5963_: *mut crate::leanh::LeanObject,
    mut v_i_5964_: *mut crate::leanh::LeanObject,
    mut v_as_5965_: *mut crate::leanh::LeanObject,
    mut v___y_5966_: *mut crate::leanh::LeanObject,
    mut v___y_5967_: *mut crate::leanh::LeanObject,
    mut v___y_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
    mut v___y_5970_: *mut crate::leanh::LeanObject,
    mut v___y_5971_: *mut crate::leanh::LeanObject,
    mut v___y_5972_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: u8 = 0;
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: usize = 0;
    let mut v___x_5981_: usize = 0;
    let mut v___x_5982_: u8 = 0;
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_5991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6002_: u8 = 0;
    let mut v___x_6004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6006_: u8 = 0;
    let mut v_a_6007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6010_: u8 = 0;
    let mut v___x_6012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6014_: u8 = 0;
    let mut v___x_6015_: u8 = 0;
    let mut v_a_6017_: u8 = 0;
    let mut v___x_6018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6027_: u8 = 0;
    let mut v___x_6029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut v_a_6032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6035_: u8 = 0;
    let mut v___x_6037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6039_: u8 = 0;
    let mut v_a_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6047_: u8 = 0;
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: u8 = 0;
    let mut v___x_6051_: usize = 0;
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: u8 = 0;
    let mut v_a_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v_code_6064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6071_: u8 = 0;
    let mut v___x_6073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5974_ = lean_array_get_size(v_as_5965_);
                v___x_5975_ = lean_nat_dec_lt(v_i_5964_, v___x_5974_);
                if v___x_5975_ == 0 {
                    crate::leanh::lean_dec(v_i_5964_);
                    crate::leanh::lean_dec(v_fvarId_5963_);
                    v___x_5976_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5976_, 0, v_as_5965_);
                    return v___x_5976_;
                } else {
                    v_a_5977_ = lean_array_fget_borrowed(v_as_5965_, v_i_5964_);
                    if crate::leanh::lean_obj_tag(v_a_5977_) == 0 {
                        v_ctorName_5990_ = crate::leanh::lean_ctor_get(v_a_5977_, 0);
                        v_params_5991_ = crate::leanh::lean_ctor_get(v_a_5977_, 1);
                        v_code_5992_ = crate::leanh::lean_ctor_get(v_a_5977_, 2);
                        v___x_6015_ = 0;
                        v___x_6048_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6049_ = lean_array_get_size(v_params_5991_);
                        v___x_6050_ = lean_nat_dec_lt(v___x_6048_, v___x_6049_);
                        if v___x_6050_ == 0 {
                            v_a_6017_ = v___x_6050_;
                            state = 7;
                            continue;
                        } else {
                            if v___x_6050_ == 0 {
                                v_a_6017_ = v___x_6050_;
                                state = 7;
                                continue;
                            } else {
                                v___x_6051_ = 0usize;
                                v___x_6052_ = lean_usize_of_nat(v___x_6049_);
                                v___x_6053_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_params_5991_, v___x_6051_, v___x_6052_, v___y_5972_);
                                if crate::leanh::lean_obj_tag(v___x_6053_) == 0 {
                                    v_a_6054_ = crate::leanh::lean_ctor_get(v___x_6053_, 0);
                                    crate::leanh::lean_inc(v_a_6054_);
                                    crate::leanh::lean_dec_ref_known(v___x_6053_, 1);
                                    v___x_6055_ = (crate::leanh::lean_unbox(v_a_6054_) as u8);
                                    crate::leanh::lean_dec(v_a_6054_);
                                    v_a_6017_ = v___x_6055_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec_ref(v_as_5965_);
                                    crate::leanh::lean_dec(v_i_5964_);
                                    crate::leanh::lean_dec(v_fvarId_5963_);
                                    v_a_6056_ = crate::leanh::lean_ctor_get(v___x_6053_, 0);
                                    v_isSharedCheck_6063_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6053_)) as u8;
                                    if v_isSharedCheck_6063_ == 0 {
                                        v___x_6058_ = v___x_6053_;
                                        v_isShared_6059_ = v_isSharedCheck_6063_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6056_);
                                        crate::leanh::lean_dec(v___x_6053_);
                                        v___x_6058_ = crate::leanh::lean_box(0);
                                        v_isShared_6059_ = v_isSharedCheck_6063_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v_code_6064_ = crate::leanh::lean_ctor_get(v_a_5977_, 0);
                        crate::leanh::lean_inc_ref(v___y_5971_);
                        crate::leanh::lean_inc_ref(v_code_6064_);
                        v___x_6065_ = l_Lean_Compiler_LCNF_Simp_simp(
                            v_code_6064_,
                            v___y_5966_,
                            v___y_5967_,
                            v___y_5968_,
                            v___y_5969_,
                            v___y_5970_,
                            v___y_5971_,
                            v___y_5972_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6065_) == 0 {
                            v_a_6066_ = crate::leanh::lean_ctor_get(v___x_6065_, 0);
                            crate::leanh::lean_inc(v_a_6066_);
                            crate::leanh::lean_dec_ref_known(v___x_6065_, 1);
                            crate::leanh::lean_inc_ref(v_a_5977_);
                            v___x_6067_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5977_, v_a_6066_);
                            v_a_5979_ = v___x_6067_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v_as_5965_);
                            crate::leanh::lean_dec(v_i_5964_);
                            crate::leanh::lean_dec(v_fvarId_5963_);
                            v_a_6068_ = crate::leanh::lean_ctor_get(v___x_6065_, 0);
                            v_isSharedCheck_6075_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6065_)) as u8;
                            if v_isSharedCheck_6075_ == 0 {
                                v___x_6070_ = v___x_6065_;
                                v_isShared_6071_ = v_isSharedCheck_6075_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6068_);
                                crate::leanh::lean_dec(v___x_6065_);
                                v___x_6070_ = crate::leanh::lean_box(0);
                                v_isShared_6071_ = v_isSharedCheck_6075_;
                                state = 16;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5980_ = lean_ptr_addr(v_a_5977_);
                v___x_5981_ = lean_ptr_addr(v_a_5979_);
                v___x_5982_ = lean_usize_dec_eq(v___x_5980_, v___x_5981_);
                if v___x_5982_ == 0 {
                    v___x_5983_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5984_ = lean_nat_add(v_i_5964_, v___x_5983_);
                    v___x_5985_ = lean_array_fset(v_as_5965_, v_i_5964_, v_a_5979_);
                    crate::leanh::lean_dec(v_i_5964_);
                    v_i_5964_ = v___x_5984_;
                    v_as_5965_ = v___x_5985_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_a_5979_);
                    v___x_5987_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5988_ = lean_nat_add(v_i_5964_, v___x_5987_);
                    crate::leanh::lean_dec(v_i_5964_);
                    v_i_5964_ = v___x_5988_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_params_5991_);
                crate::leanh::lean_inc(v_ctorName_5990_);
                crate::leanh::lean_inc(v_fvarId_5963_);
                v___x_5994_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_5963_, v_ctorName_5990_, v_params_5991_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
                if crate::leanh::lean_obj_tag(v___x_5994_) == 0 {
                    v_a_5995_ = crate::leanh::lean_ctor_get(v___x_5994_, 0);
                    crate::leanh::lean_inc(v_a_5995_);
                    crate::leanh::lean_dec_ref_known(v___x_5994_, 1);
                    crate::leanh::lean_inc_ref(v___y_5971_);
                    crate::leanh::lean_inc_ref(v_code_5992_);
                    v___x_5996_ = l_Lean_Compiler_LCNF_Simp_simp(
                        v_code_5992_,
                        v___y_5966_,
                        v___y_5967_,
                        v_a_5995_,
                        v___y_5969_,
                        v___y_5970_,
                        v___y_5971_,
                        v___y_5972_,
                    );
                    crate::leanh::lean_dec(v_a_5995_);
                    if crate::leanh::lean_obj_tag(v___x_5996_) == 0 {
                        v_a_5997_ = crate::leanh::lean_ctor_get(v___x_5996_, 0);
                        crate::leanh::lean_inc(v_a_5997_);
                        crate::leanh::lean_dec_ref_known(v___x_5996_, 1);
                        crate::leanh::lean_inc_ref(v_a_5977_);
                        v___x_5998_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5977_, v_a_5997_);
                        v_a_5979_ = v___x_5998_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_as_5965_);
                        crate::leanh::lean_dec(v_i_5964_);
                        crate::leanh::lean_dec(v_fvarId_5963_);
                        v_a_5999_ = crate::leanh::lean_ctor_get(v___x_5996_, 0);
                        v_isSharedCheck_6006_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5996_)) as u8;
                        if v_isSharedCheck_6006_ == 0 {
                            v___x_6001_ = v___x_5996_;
                            v_isShared_6002_ = v_isSharedCheck_6006_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5999_);
                            crate::leanh::lean_dec(v___x_5996_);
                            v___x_6001_ = crate::leanh::lean_box(0);
                            v_isShared_6002_ = v_isSharedCheck_6006_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_as_5965_);
                    crate::leanh::lean_dec(v_i_5964_);
                    crate::leanh::lean_dec(v_fvarId_5963_);
                    v_a_6007_ = crate::leanh::lean_ctor_get(v___x_5994_, 0);
                    v_isSharedCheck_6014_ = (!crate::leanh::lean_is_exclusive(v___x_5994_)) as u8;
                    if v_isSharedCheck_6014_ == 0 {
                        v___x_6009_ = v___x_5994_;
                        v_isShared_6010_ = v_isSharedCheck_6014_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6007_);
                        crate::leanh::lean_dec(v___x_5994_);
                        v___x_6009_ = crate::leanh::lean_box(0);
                        v_isShared_6010_ = v_isSharedCheck_6014_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6002_ == 0 {
                    v___x_6004_ = v___x_6001_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6005_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6005_, 0, v_a_5999_);
                    v___x_6004_ = v_reuseFailAlloc_6005_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6004_;
            }
            5 => {
                if v_isShared_6010_ == 0 {
                    v___x_6012_ = v___x_6009_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6013_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
                    v___x_6012_ = v_reuseFailAlloc_6013_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6012_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_code_5992_) == 6 {
                    state = 2;
                    continue;
                } else {
                    if v_a_6017_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc_ref(v_code_5992_);
                        v___x_6018_ = l_Lean_Compiler_LCNF_Code_inferType(
                            v___x_6015_,
                            v_code_5992_,
                            v___y_5969_,
                            v___y_5970_,
                            v___y_5971_,
                            v___y_5972_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6018_) == 0 {
                            v_a_6019_ = crate::leanh::lean_ctor_get(v___x_6018_, 0);
                            crate::leanh::lean_inc(v_a_6019_);
                            crate::leanh::lean_dec_ref_known(v___x_6018_, 1);
                            v___x_6020_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                                v___x_6015_,
                                v_code_5992_,
                                v___y_5970_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6020_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6020_, 1);
                                v___x_6021_ =
                                    l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5967_);
                                if crate::leanh::lean_obj_tag(v___x_6021_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6021_, 1);
                                    v___x_6022_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_6022_, 0, v_a_6019_);
                                    crate::leanh::lean_inc_ref(v_a_5977_);
                                    v___x_6023_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5977_, v___x_6022_);
                                    v_a_5979_ = v___x_6023_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_6019_);
                                    crate::leanh::lean_dec_ref(v_as_5965_);
                                    crate::leanh::lean_dec(v_i_5964_);
                                    crate::leanh::lean_dec(v_fvarId_5963_);
                                    v_a_6024_ = crate::leanh::lean_ctor_get(v___x_6021_, 0);
                                    v_isSharedCheck_6031_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6021_)) as u8;
                                    if v_isSharedCheck_6031_ == 0 {
                                        v___x_6026_ = v___x_6021_;
                                        v_isShared_6027_ = v_isSharedCheck_6031_;
                                        state = 8;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6024_);
                                        crate::leanh::lean_dec(v___x_6021_);
                                        v___x_6026_ = crate::leanh::lean_box(0);
                                        v_isShared_6027_ = v_isSharedCheck_6031_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6019_);
                                crate::leanh::lean_dec_ref(v_as_5965_);
                                crate::leanh::lean_dec(v_i_5964_);
                                crate::leanh::lean_dec(v_fvarId_5963_);
                                v_a_6032_ = crate::leanh::lean_ctor_get(v___x_6020_, 0);
                                v_isSharedCheck_6039_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6020_)) as u8;
                                if v_isSharedCheck_6039_ == 0 {
                                    v___x_6034_ = v___x_6020_;
                                    v_isShared_6035_ = v_isSharedCheck_6039_;
                                    state = 10;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6032_);
                                    crate::leanh::lean_dec(v___x_6020_);
                                    v___x_6034_ = crate::leanh::lean_box(0);
                                    v_isShared_6035_ = v_isSharedCheck_6039_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_as_5965_);
                            crate::leanh::lean_dec(v_i_5964_);
                            crate::leanh::lean_dec(v_fvarId_5963_);
                            v_a_6040_ = crate::leanh::lean_ctor_get(v___x_6018_, 0);
                            v_isSharedCheck_6047_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6018_)) as u8;
                            if v_isSharedCheck_6047_ == 0 {
                                v___x_6042_ = v___x_6018_;
                                v_isShared_6043_ = v_isSharedCheck_6047_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6040_);
                                crate::leanh::lean_dec(v___x_6018_);
                                v___x_6042_ = crate::leanh::lean_box(0);
                                v_isShared_6043_ = v_isSharedCheck_6047_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                }
            }
            8 => {
                if v_isShared_6027_ == 0 {
                    v___x_6029_ = v___x_6026_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6030_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
                    v___x_6029_ = v_reuseFailAlloc_6030_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6029_;
            }
            10 => {
                if v_isShared_6035_ == 0 {
                    v___x_6037_ = v___x_6034_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6038_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_a_6032_);
                    v___x_6037_ = v_reuseFailAlloc_6038_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6037_;
            }
            12 => {
                if v_isShared_6043_ == 0 {
                    v___x_6045_ = v___x_6042_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_6046_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_a_6040_);
                    v___x_6045_ = v_reuseFailAlloc_6046_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_6045_;
            }
            14 => {
                if v_isShared_6059_ == 0 {
                    v___x_6061_ = v___x_6058_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
                    v___x_6061_ = v_reuseFailAlloc_6062_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6061_;
            }
            16 => {
                if v_isShared_6071_ == 0 {
                    v___x_6073_ = v___x_6070_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_6074_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_a_6068_);
                    v___x_6073_ = v_reuseFailAlloc_6074_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_6073_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simp(
    mut v_code_6077_: *mut crate::leanh::LeanObject,
    mut v_a_6078_: *mut crate::leanh::LeanObject,
    mut v_a_6079_: *mut crate::leanh::LeanObject,
    mut v_a_6080_: *mut crate::leanh::LeanObject,
    mut v_a_6081_: *mut crate::leanh::LeanObject,
    mut v_a_6082_: *mut crate::leanh::LeanObject,
    mut v_a_6083_: *mut crate::leanh::LeanObject,
    mut v_a_6084_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_6087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6089_: u8 = 0;
    let mut v___x_6090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6096_: u8 = 0;
    let mut v___x_6097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: usize = 0;
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: u8 = 0;
    let mut v___x_6108_: usize = 0;
    let mut v___x_6109_: usize = 0;
    let mut v___x_6110_: u8 = 0;
    let mut v_decl_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: usize = 0;
    let mut v___x_6114_: usize = 0;
    let mut v___x_6115_: u8 = 0;
    let mut v___x_6116_: usize = 0;
    let mut v___x_6117_: usize = 0;
    let mut v___x_6118_: u8 = 0;
    let mut v___x_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6123_: u8 = 0;
    let mut v___y_6124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: u8 = 0;
    let mut v___x_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6142_: u8 = 0;
    let mut v___x_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6146_: u8 = 0;
    let mut v_unused_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6151_: u8 = 0;
    let mut v___x_6153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6155_: u8 = 0;
    let mut v___x_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6160_: u8 = 0;
    let mut v___x_6162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6164_: u8 = 0;
    let mut v_a_6165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6168_: u8 = 0;
    let mut v___x_6170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6172_: u8 = 0;
    let mut v___y_6174_: u8 = 0;
    let mut v___y_6175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6189_: u8 = 0;
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6193_: u8 = 0;
    let mut v_decl_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: u8 = 0;
    let mut v___x_6210_: u8 = 0;
    let mut v___x_6211_: u8 = 0;
    let mut v___x_6212_: u8 = 0;
    let mut v___x_6213_: u8 = 0;
    let mut v___x_6214_: u8 = 0;
    let mut v___x_6215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_6216_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: u8 = 0;
    let mut v___x_6218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: u8 = 0;
    let mut v_a_6224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6227_: u8 = 0;
    let mut v___x_6229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_a_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut v_a_6240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6243_: u8 = 0;
    let mut v___x_6245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6247_: u8 = 0;
    let mut v___x_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_6249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: u8 = 0;
    let mut v___x_6251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: u8 = 0;
    let mut v_a_6254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6261_: u8 = 0;
    let mut v_a_6262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v___x_6267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v___y_6271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: u8 = 0;
    let mut v___x_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6298_: u8 = 0;
    let mut v___x_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v___x_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6319_: u8 = 0;
    let mut v___x_6321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6323_: u8 = 0;
    let mut v_a_6324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6327_: u8 = 0;
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6331_: u8 = 0;
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6338_: u8 = 0;
    let mut v___x_6340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6342_: u8 = 0;
    let mut v_unused_6343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6347_: u8 = 0;
    let mut v___x_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6351_: u8 = 0;
    let mut v___x_6352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6369_: u8 = 0;
    let mut v_a_6370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6373_: u8 = 0;
    let mut v___x_6375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6377_: u8 = 0;
    let mut v___x_6378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: u8 = 0;
    let mut v___x_6383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6386_: u8 = 0;
    let mut v___x_6388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6390_: u8 = 0;
    let mut v_unused_6391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6399_: u8 = 0;
    let mut v___x_6400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: usize = 0;
    let mut v___x_6402_: usize = 0;
    let mut v___x_6403_: u8 = 0;
    let mut v___x_6404_: usize = 0;
    let mut v___x_6405_: usize = 0;
    let mut v___x_6406_: u8 = 0;
    let mut v_a_6407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6410_: u8 = 0;
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6414_: u8 = 0;
    let mut v_a_6415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6418_: u8 = 0;
    let mut v___x_6420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6422_: u8 = 0;
    let mut v_a_6423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6426_: u8 = 0;
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6430_: u8 = 0;
    let mut v_a_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6434_: u8 = 0;
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6438_: u8 = 0;
    let mut v_a_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6442_: u8 = 0;
    let mut v___x_6444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6446_: u8 = 0;
    let mut v_a_6447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6454_: u8 = 0;
    let mut v_a_6455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6458_: u8 = 0;
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6462_: u8 = 0;
    let mut v___y_6464_: u8 = 0;
    let mut v___y_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: u8 = 0;
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: u8 = 0;
    let mut v___x_6481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_6482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_used_6483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_6484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_6485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_6486_: u8 = 0;
    let mut v_visited_6487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_6488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_6489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6492_: u8 = 0;
    let mut v___x_6493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6503_: u8 = 0;
    let mut v___x_6505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut v_reuseFailAlloc_6508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6509_: u8 = 0;
    let mut v___y_6511_: u8 = 0;
    let mut v___y_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v_a_6542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6545_: u8 = 0;
    let mut v___x_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6549_: u8 = 0;
    let mut v_a_6550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6553_: u8 = 0;
    let mut v___x_6555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6557_: u8 = 0;
    let mut v___y_6559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6561_: u8 = 0;
    let mut v___x_6562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: u8 = 0;
    let mut v___x_6571_: usize = 0;
    let mut v___x_6572_: usize = 0;
    let mut v___x_6573_: u8 = 0;
    let mut v___y_6575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6583_: u8 = 0;
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6587_: u8 = 0;
    let mut v___y_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6594_: u8 = 0;
    let mut v___x_6595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_unused_6600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6604_: u8 = 0;
    let mut v___x_6606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6608_: u8 = 0;
    let mut v___y_6610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6616_: u8 = 0;
    let mut v___x_6618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6620_: u8 = 0;
    let mut v___y_6622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: u8 = 0;
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: u8 = 0;
    let mut v___x_6634_: usize = 0;
    let mut v___x_6635_: usize = 0;
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: usize = 0;
    let mut v___x_6638_: usize = 0;
    let mut v___x_6639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6654_: u8 = 0;
    let mut v___x_6655_: u8 = 0;
    let mut v___x_6656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: u8 = 0;
    let mut v___x_6673_: usize = 0;
    let mut v___x_6674_: usize = 0;
    let mut v___x_6675_: u8 = 0;
    let mut v___x_6676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: usize = 0;
    let mut v___x_6678_: usize = 0;
    let mut v___x_6679_: u8 = 0;
    let mut v___x_6680_: usize = 0;
    let mut v___x_6681_: usize = 0;
    let mut v___x_6682_: u8 = 0;
    let mut v_a_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6690_: u8 = 0;
    let mut v___y_6692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6697_: u8 = 0;
    let mut v___x_6699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6701_: u8 = 0;
    let mut v_unused_6702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6706_: u8 = 0;
    let mut v___x_6708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6710_: u8 = 0;
    let mut v___y_6712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6722_: u8 = 0;
    let mut v___y_6724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: u8 = 0;
    let mut v___x_6731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: u8 = 0;
    let mut v___x_6733_: usize = 0;
    let mut v___x_6734_: usize = 0;
    let mut v___x_6735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: usize = 0;
    let mut v___x_6737_: usize = 0;
    let mut v___x_6738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: u8 = 0;
    let mut v___x_6750_: u8 = 0;
    let mut v___x_6751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: u8 = 0;
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6758_: u8 = 0;
    let mut v___x_6760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6762_: u8 = 0;
    let mut v_a_6763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6766_: u8 = 0;
    let mut v___x_6768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6770_: u8 = 0;
    let mut v_fvarId_6771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_6774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: u8 = 0;
    let mut v___x_6776_: u8 = 0;
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: u8 = 0;
    let mut v___x_6789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: u8 = 0;
    let mut v___x_6791_: usize = 0;
    let mut v___x_6792_: usize = 0;
    let mut v___x_6793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: usize = 0;
    let mut v___x_6795_: usize = 0;
    let mut v___x_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6800_: u8 = 0;
    let mut v___x_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6804_: u8 = 0;
    let mut v_a_6805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6808_: u8 = 0;
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6812_: u8 = 0;
    let mut v_a_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6816_: u8 = 0;
    let mut v___x_6818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6820_: u8 = 0;
    let mut v___x_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_6822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6827_: u8 = 0;
    let mut v_val_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_6832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_6833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_6834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_6835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_6837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: u8 = 0;
    let mut v___x_6839_: u8 = 0;
    let mut v___x_6840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6850_: u8 = 0;
    let mut v_subst_6851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: u8 = 0;
    let mut v___x_6856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_6857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_6858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: u8 = 0;
    let mut v___x_6861_: usize = 0;
    let mut v___x_6862_: usize = 0;
    let mut v___x_6863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: u8 = 0;
    let mut v_a_6866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6869_: u8 = 0;
    let mut v___x_6871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6873_: u8 = 0;
    let mut v_code_6874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6878_: u8 = 0;
    let mut v_a_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6882_: u8 = 0;
    let mut v___x_6884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6886_: u8 = 0;
    let mut v_a_6887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6890_: u8 = 0;
    let mut v___x_6892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6894_: u8 = 0;
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6896_: u8 = 0;
    let mut v_a_6897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6900_: u8 = 0;
    let mut v___x_6902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v_fvarId_6905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_6907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: u8 = 0;
    let mut v___x_6909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6914_: u8 = 0;
    let mut v___x_6915_: u8 = 0;
    let mut v___x_6917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6918_: u8 = 0;
    let mut v___x_6920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_unused_6926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6930_: u8 = 0;
    let mut v_unused_6931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6935_: u8 = 0;
    let mut v___x_6937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6939_: u8 = 0;
    let mut v___x_6940_: u8 = 0;
    let mut v___x_6941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_6942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_6944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: u8 = 0;
    let mut v___x_6946_: u8 = 0;
    let mut v___x_6947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: usize = 0;
    let mut v___x_6949_: usize = 0;
    let mut v___x_6950_: u8 = 0;
    let mut v___x_6952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6953_: u8 = 0;
    let mut v___x_6955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6958_: u8 = 0;
    let mut v_unused_6959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_6961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6975_: u8 = 0;
    let mut v_cancelTk_x3f_6976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6977_: u8 = 0;
    let mut v_inheritedTraceOptions_6978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_6982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: u8 = 0;
    let mut v___x_6990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6995_: u8 = 0;
    let mut v___x_6997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut v_a_7000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v___x_7008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: u8 = 0;
    let mut v___x_7010_: u8 = 0;
    let mut v___x_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6963_ = crate::leanh::lean_ctor_get(v_a_6083_, 0);
                v_fileMap_6964_ = crate::leanh::lean_ctor_get(v_a_6083_, 1);
                v_options_6965_ = crate::leanh::lean_ctor_get(v_a_6083_, 2);
                v_currRecDepth_6966_ = crate::leanh::lean_ctor_get(v_a_6083_, 3);
                v_maxRecDepth_6967_ = crate::leanh::lean_ctor_get(v_a_6083_, 4);
                v_ref_6968_ = crate::leanh::lean_ctor_get(v_a_6083_, 5);
                v_currNamespace_6969_ = crate::leanh::lean_ctor_get(v_a_6083_, 6);
                v_openDecls_6970_ = crate::leanh::lean_ctor_get(v_a_6083_, 7);
                v_initHeartbeats_6971_ = crate::leanh::lean_ctor_get(v_a_6083_, 8);
                v_maxHeartbeats_6972_ = crate::leanh::lean_ctor_get(v_a_6083_, 9);
                v_quotContext_6973_ = crate::leanh::lean_ctor_get(v_a_6083_, 10);
                v_currMacroScope_6974_ = crate::leanh::lean_ctor_get(v_a_6083_, 11);
                v_diag_6975_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6083_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6976_ = crate::leanh::lean_ctor_get(v_a_6083_, 12);
                v_suppressElabErrors_6977_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_6083_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6978_ = crate::leanh::lean_ctor_get(v_a_6083_, 13);
                v___x_7008_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_7009_ = lean_nat_dec_eq(v_maxRecDepth_6967_, v___x_7008_);
                if v___x_7009_ == 0 {
                    v___x_7010_ = lean_nat_dec_eq(v_currRecDepth_6966_, v_maxRecDepth_6967_);
                    if v___x_7010_ == 0 {
                        crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6978_);
                        crate::leanh::lean_inc(v_cancelTk_x3f_6976_);
                        crate::leanh::lean_inc(v_currMacroScope_6974_);
                        crate::leanh::lean_inc(v_quotContext_6973_);
                        crate::leanh::lean_inc(v_maxHeartbeats_6972_);
                        crate::leanh::lean_inc(v_initHeartbeats_6971_);
                        crate::leanh::lean_inc(v_openDecls_6970_);
                        crate::leanh::lean_inc(v_currNamespace_6969_);
                        crate::leanh::lean_inc(v_ref_6968_);
                        crate::leanh::lean_inc(v_maxRecDepth_6967_);
                        crate::leanh::lean_inc(v_currRecDepth_6966_);
                        crate::leanh::lean_inc_ref(v_options_6965_);
                        crate::leanh::lean_inc_ref(v_fileMap_6964_);
                        crate::leanh::lean_inc_ref(v_fileName_6963_);
                        crate::leanh::lean_dec_ref(v_a_6083_);
                        state = 133;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_code_6077_);
                        v___x_7011_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(crate::leanh::lean_box(0), v_a_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_);
                        crate::leanh::lean_dec_ref(v_a_6083_);
                        return v___x_7011_;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_inheritedTraceOptions_6978_);
                    crate::leanh::lean_inc(v_cancelTk_x3f_6976_);
                    crate::leanh::lean_inc(v_currMacroScope_6974_);
                    crate::leanh::lean_inc(v_quotContext_6973_);
                    crate::leanh::lean_inc(v_maxHeartbeats_6972_);
                    crate::leanh::lean_inc(v_initHeartbeats_6971_);
                    crate::leanh::lean_inc(v_openDecls_6970_);
                    crate::leanh::lean_inc(v_currNamespace_6969_);
                    crate::leanh::lean_inc(v_ref_6968_);
                    crate::leanh::lean_inc(v_maxRecDepth_6967_);
                    crate::leanh::lean_inc(v_currRecDepth_6966_);
                    crate::leanh::lean_inc_ref(v_options_6965_);
                    crate::leanh::lean_inc_ref(v_fileMap_6964_);
                    crate::leanh::lean_inc_ref(v_fileName_6963_);
                    crate::leanh::lean_dec_ref(v_a_6083_);
                    state = 133;
                    continue;
                }
            }
            1 => {
                if v___y_6089_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v___x_6090_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6090_, 0, v___y_6087_);
                    crate::leanh::lean_ctor_set(v___x_6090_, 1, v___y_6088_);
                    v___x_6091_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6091_, 0, v___x_6090_);
                    return v___x_6091_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6088_);
                    crate::leanh::lean_dec_ref(v___y_6087_);
                    v___x_6092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6092_, 0, v_code_6077_);
                    return v___x_6092_;
                }
            }
            2 => {
                if v___y_6096_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v___x_6097_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6097_, 0, v___y_6094_);
                    crate::leanh::lean_ctor_set(v___x_6097_, 1, v___y_6095_);
                    v___x_6098_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6098_, 0, v___x_6097_);
                    return v___x_6098_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6095_);
                    crate::leanh::lean_dec_ref(v___y_6094_);
                    v___x_6099_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6099_, 0, v_code_6077_);
                    return v___x_6099_;
                }
            }
            3 => match crate::leanh::lean_obj_tag(v_code_6077_) {
                1 => {
                    v_decl_6103_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    v_k_6104_ = crate::leanh::lean_ctor_get(v_code_6077_, 1);
                    v___x_6105_ = lean_ptr_addr(v_k_6104_);
                    v___x_6106_ = lean_ptr_addr(v___y_6102_);
                    v___x_6107_ = lean_usize_dec_eq(v___x_6105_, v___x_6106_);
                    if v___x_6107_ == 0 {
                        v___y_6087_ = v___y_6101_;
                        v___y_6088_ = v___y_6102_;
                        v___y_6089_ = v___x_6107_;
                        state = 1;
                        continue;
                    } else {
                        v___x_6108_ = lean_ptr_addr(v_decl_6103_);
                        v___x_6109_ = lean_ptr_addr(v___y_6101_);
                        v___x_6110_ = lean_usize_dec_eq(v___x_6108_, v___x_6109_);
                        v___y_6087_ = v___y_6101_;
                        v___y_6088_ = v___y_6102_;
                        v___y_6089_ = v___x_6110_;
                        state = 1;
                        continue;
                    }
                }
                2 => {
                    v_decl_6111_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    v_k_6112_ = crate::leanh::lean_ctor_get(v_code_6077_, 1);
                    v___x_6113_ = lean_ptr_addr(v_k_6112_);
                    v___x_6114_ = lean_ptr_addr(v___y_6102_);
                    v___x_6115_ = lean_usize_dec_eq(v___x_6113_, v___x_6114_);
                    if v___x_6115_ == 0 {
                        v___y_6094_ = v___y_6101_;
                        v___y_6095_ = v___y_6102_;
                        v___y_6096_ = v___x_6115_;
                        state = 2;
                        continue;
                    } else {
                        v___x_6116_ = lean_ptr_addr(v_decl_6111_);
                        v___x_6117_ = lean_ptr_addr(v___y_6101_);
                        v___x_6118_ = lean_usize_dec_eq(v___x_6116_, v___x_6117_);
                        v___y_6094_ = v___y_6101_;
                        v___y_6095_ = v___y_6102_;
                        v___y_6096_ = v___x_6118_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    crate::leanh::lean_dec_ref(v___y_6102_);
                    crate::leanh::lean_dec_ref(v___y_6101_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v___x_6119_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_simp___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_simp___closed__3_once),
                        _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3,
                    );
                    v___x_6120_ =
                        l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_6119_);
                    v___x_6121_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6121_, 0, v___x_6120_);
                    return v___x_6121_;
                }
            },
            4 => {
                crate::leanh::lean_inc_ref(v___y_6131_);
                v___x_6133_ = l_Lean_Compiler_LCNF_Simp_simp(
                    v___y_6124_,
                    v___y_6126_,
                    v___y_6127_,
                    v___y_6128_,
                    v___y_6129_,
                    v___y_6130_,
                    v___y_6131_,
                    v___y_6132_,
                );
                if crate::leanh::lean_obj_tag(v___x_6133_) == 0 {
                    v_a_6134_ = crate::leanh::lean_ctor_get(v___x_6133_, 0);
                    crate::leanh::lean_inc(v_a_6134_);
                    crate::leanh::lean_dec_ref_known(v___x_6133_, 1);
                    v_fvarId_6135_ = crate::leanh::lean_ctor_get(v_decl_6125_, 0);
                    v___x_6136_ =
                        l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_6135_, v___y_6127_);
                    if crate::leanh::lean_obj_tag(v___x_6136_) == 0 {
                        v_a_6137_ = crate::leanh::lean_ctor_get(v___x_6136_, 0);
                        crate::leanh::lean_inc(v_a_6137_);
                        crate::leanh::lean_dec_ref_known(v___x_6136_, 1);
                        v___x_6138_ = (crate::leanh::lean_unbox(v_a_6137_) as u8);
                        crate::leanh::lean_dec(v_a_6137_);
                        if v___x_6138_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_6131_);
                            crate::leanh::lean_dec_ref(v_code_6077_);
                            v___x_6139_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(
                                v_decl_6125_,
                                v___y_6127_,
                                v___y_6130_,
                            );
                            crate::leanh::lean_dec_ref(v_decl_6125_);
                            if crate::leanh::lean_obj_tag(v___x_6139_) == 0 {
                                v_isSharedCheck_6146_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6139_)) as u8;
                                if v_isSharedCheck_6146_ == 0 {
                                    v_unused_6147_ = crate::leanh::lean_ctor_get(v___x_6139_, 0);
                                    crate::leanh::lean_dec(v_unused_6147_);
                                    v___x_6141_ = v___x_6139_;
                                    v_isShared_6142_ = v_isSharedCheck_6146_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_6139_);
                                    v___x_6141_ = crate::leanh::lean_box(0);
                                    v_isShared_6142_ = v_isSharedCheck_6146_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6134_);
                                v_a_6148_ = crate::leanh::lean_ctor_get(v___x_6139_, 0);
                                v_isSharedCheck_6155_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6139_)) as u8;
                                if v_isSharedCheck_6155_ == 0 {
                                    v___x_6150_ = v___x_6139_;
                                    v_isShared_6151_ = v_isSharedCheck_6155_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6148_);
                                    crate::leanh::lean_dec(v___x_6139_);
                                    v___x_6150_ = crate::leanh::lean_box(0);
                                    v_isShared_6151_ = v_isSharedCheck_6155_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            if v___y_6123_ == 0 {
                                crate::leanh::lean_dec_ref(v___y_6131_);
                                v___y_6101_ = v_decl_6125_;
                                v___y_6102_ = v_a_6134_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc_ref(v_decl_6125_);
                                v___x_6156_ = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(
                                    v_decl_6125_,
                                    v___y_6126_,
                                    v___y_6127_,
                                    v___y_6128_,
                                    v___y_6129_,
                                    v___y_6130_,
                                    v___y_6131_,
                                    v___y_6132_,
                                );
                                crate::leanh::lean_dec_ref(v___y_6131_);
                                if crate::leanh::lean_obj_tag(v___x_6156_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_6156_, 1);
                                    v___y_6101_ = v_decl_6125_;
                                    v___y_6102_ = v_a_6134_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_6134_);
                                    crate::leanh::lean_dec_ref(v_decl_6125_);
                                    crate::leanh::lean_dec_ref(v_code_6077_);
                                    v_a_6157_ = crate::leanh::lean_ctor_get(v___x_6156_, 0);
                                    v_isSharedCheck_6164_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6156_)) as u8;
                                    if v_isSharedCheck_6164_ == 0 {
                                        v___x_6159_ = v___x_6156_;
                                        v_isShared_6160_ = v_isSharedCheck_6164_;
                                        state = 9;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6157_);
                                        crate::leanh::lean_dec(v___x_6156_);
                                        v___x_6159_ = crate::leanh::lean_box(0);
                                        v_isShared_6160_ = v_isSharedCheck_6164_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6134_);
                        crate::leanh::lean_dec_ref(v___y_6131_);
                        crate::leanh::lean_dec_ref(v_decl_6125_);
                        crate::leanh::lean_dec_ref(v_code_6077_);
                        v_a_6165_ = crate::leanh::lean_ctor_get(v___x_6136_, 0);
                        v_isSharedCheck_6172_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6136_)) as u8;
                        if v_isSharedCheck_6172_ == 0 {
                            v___x_6167_ = v___x_6136_;
                            v_isShared_6168_ = v_isSharedCheck_6172_;
                            state = 11;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6165_);
                            crate::leanh::lean_dec(v___x_6136_);
                            v___x_6167_ = crate::leanh::lean_box(0);
                            v_isShared_6168_ = v_isSharedCheck_6172_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6131_);
                    crate::leanh::lean_dec_ref(v_decl_6125_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    return v___x_6133_;
                }
            }
            5 => {
                if v_isShared_6142_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6141_, 0, v_a_6134_);
                    v___x_6144_ = v___x_6141_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6145_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_a_6134_);
                    v___x_6144_ = v_reuseFailAlloc_6145_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6144_;
            }
            7 => {
                if v_isShared_6151_ == 0 {
                    v___x_6153_ = v___x_6150_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
                    v___x_6153_ = v_reuseFailAlloc_6154_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6153_;
            }
            9 => {
                if v_isShared_6160_ == 0 {
                    v___x_6162_ = v___x_6159_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6163_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_a_6157_);
                    v___x_6162_ = v_reuseFailAlloc_6163_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6162_;
            }
            11 => {
                if v_isShared_6168_ == 0 {
                    v___x_6170_ = v___x_6167_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_6171_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_a_6165_);
                    v___x_6170_ = v_reuseFailAlloc_6171_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_6170_;
            }
            13 => {
                v___x_6184_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(
                    v_decl_6176_,
                    v___y_6177_,
                    v___y_6178_,
                    v___y_6179_,
                    v___y_6180_,
                    v___y_6181_,
                    v___y_6182_,
                    v___y_6183_,
                );
                if crate::leanh::lean_obj_tag(v___x_6184_) == 0 {
                    v_a_6185_ = crate::leanh::lean_ctor_get(v___x_6184_, 0);
                    crate::leanh::lean_inc(v_a_6185_);
                    crate::leanh::lean_dec_ref_known(v___x_6184_, 1);
                    v___y_6123_ = v___y_6174_;
                    v___y_6124_ = v___y_6175_;
                    v_decl_6125_ = v_a_6185_;
                    v___y_6126_ = v___y_6177_;
                    v___y_6127_ = v___y_6178_;
                    v___y_6128_ = v___y_6179_;
                    v___y_6129_ = v___y_6180_;
                    v___y_6130_ = v___y_6181_;
                    v___y_6131_ = v___y_6182_;
                    v___y_6132_ = v___y_6183_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6182_);
                    crate::leanh::lean_dec_ref(v___y_6175_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v_a_6186_ = crate::leanh::lean_ctor_get(v___x_6184_, 0);
                    v_isSharedCheck_6193_ = (!crate::leanh::lean_is_exclusive(v___x_6184_)) as u8;
                    if v_isSharedCheck_6193_ == 0 {
                        v___x_6188_ = v___x_6184_;
                        v_isShared_6189_ = v_isSharedCheck_6193_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6186_);
                        crate::leanh::lean_dec(v___x_6184_);
                        v___x_6188_ = crate::leanh::lean_box(0);
                        v_isShared_6189_ = v_isSharedCheck_6193_;
                        state = 14;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_6189_ == 0 {
                    v___x_6191_ = v___x_6188_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_6192_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_a_6186_);
                    v___x_6191_ = v_reuseFailAlloc_6192_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6191_;
            }
            16 => {
                v_fvarId_6204_ = crate::leanh::lean_ctor_get(v_decl_6195_, 0);
                v_params_6205_ = crate::leanh::lean_ctor_get(v_decl_6195_, 2);
                v_type_6206_ = crate::leanh::lean_ctor_get(v_decl_6195_, 3);
                v___x_6207_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(
                    v_fvarId_6204_,
                    v___y_6198_,
                );
                if crate::leanh::lean_obj_tag(v___x_6207_) == 0 {
                    v_a_6208_ = crate::leanh::lean_ctor_get(v___x_6207_, 0);
                    crate::leanh::lean_inc(v_a_6208_);
                    crate::leanh::lean_dec_ref_known(v___x_6207_, 1);
                    v___x_6209_ = 0;
                    v___x_6210_ = (crate::leanh::lean_unbox(v_a_6208_) as u8);
                    if v___x_6210_ == 0 {
                        v___x_6211_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_6077_);
                        if v___x_6211_ == 0 {
                            v___x_6212_ = (crate::leanh::lean_unbox(v_a_6208_) as u8);
                            crate::leanh::lean_dec(v_a_6208_);
                            v___y_6174_ = v___x_6212_;
                            v___y_6175_ = v_k_6196_;
                            v_decl_6176_ = v_decl_6195_;
                            v___y_6177_ = v___y_6197_;
                            v___y_6178_ = v___y_6198_;
                            v___y_6179_ = v___y_6199_;
                            v___y_6180_ = v___y_6200_;
                            v___y_6181_ = v___y_6201_;
                            v___y_6182_ = v___y_6202_;
                            v___y_6183_ = v___y_6203_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc_ref(v_type_6206_);
                            v___x_6213_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(
                                v_type_6206_,
                                v_params_6205_,
                            );
                            if v___x_6213_ == 0 {
                                v___x_6214_ = (crate::leanh::lean_unbox(v_a_6208_) as u8);
                                crate::leanh::lean_dec(v_a_6208_);
                                v___y_6174_ = v___x_6214_;
                                v___y_6175_ = v_k_6196_;
                                v_decl_6176_ = v_decl_6195_;
                                v___y_6177_ = v___y_6197_;
                                v___y_6178_ = v___y_6198_;
                                v___y_6179_ = v___y_6199_;
                                v___y_6180_ = v___y_6200_;
                                v___y_6181_ = v___y_6201_;
                                v___y_6182_ = v___y_6202_;
                                v___y_6183_ = v___y_6203_;
                                state = 13;
                                continue;
                            } else {
                                v___x_6215_ = lean_st_ref_get(v___y_6198_);
                                v_subst_6216_ = crate::leanh::lean_ctor_get(v___x_6215_, 0);
                                crate::leanh::lean_inc_ref(v_subst_6216_);
                                crate::leanh::lean_dec(v___x_6215_);
                                v___x_6217_ = (crate::leanh::lean_unbox(v_a_6208_) as u8);
                                v___x_6218_ = l_Lean_Compiler_LCNF_normFunDeclImp(
                                    v___x_6209_,
                                    v___x_6217_,
                                    v_decl_6195_,
                                    v_subst_6216_,
                                    v___y_6200_,
                                    v___y_6201_,
                                    v___y_6202_,
                                    v___y_6203_,
                                );
                                crate::leanh::lean_dec_ref(v_subst_6216_);
                                if crate::leanh::lean_obj_tag(v___x_6218_) == 0 {
                                    v_a_6219_ = crate::leanh::lean_ctor_get(v___x_6218_, 0);
                                    crate::leanh::lean_inc(v_a_6219_);
                                    crate::leanh::lean_dec_ref_known(v___x_6218_, 1);
                                    v___x_6220_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(
                                        v_a_6219_,
                                        v___y_6200_,
                                        v___y_6201_,
                                        v___y_6202_,
                                        v___y_6203_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_6220_) == 0 {
                                        v_a_6221_ = crate::leanh::lean_ctor_get(v___x_6220_, 0);
                                        crate::leanh::lean_inc(v_a_6221_);
                                        crate::leanh::lean_dec_ref_known(v___x_6220_, 1);
                                        v___x_6222_ =
                                            l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(
                                                v___y_6198_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_6222_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_6222_, 1);
                                            v___x_6223_ =
                                                (crate::leanh::lean_unbox(v_a_6208_) as u8);
                                            crate::leanh::lean_dec(v_a_6208_);
                                            v___y_6174_ = v___x_6223_;
                                            v___y_6175_ = v_k_6196_;
                                            v_decl_6176_ = v_a_6221_;
                                            v___y_6177_ = v___y_6197_;
                                            v___y_6178_ = v___y_6198_;
                                            v___y_6179_ = v___y_6199_;
                                            v___y_6180_ = v___y_6200_;
                                            v___y_6181_ = v___y_6201_;
                                            v___y_6182_ = v___y_6202_;
                                            v___y_6183_ = v___y_6203_;
                                            state = 13;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v_a_6221_);
                                            crate::leanh::lean_dec(v_a_6208_);
                                            crate::leanh::lean_dec_ref(v___y_6202_);
                                            crate::leanh::lean_dec_ref(v_k_6196_);
                                            crate::leanh::lean_dec_ref(v_code_6077_);
                                            v_a_6224_ = crate::leanh::lean_ctor_get(v___x_6222_, 0);
                                            v_isSharedCheck_6231_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6222_))
                                                    as u8;
                                            if v_isSharedCheck_6231_ == 0 {
                                                v___x_6226_ = v___x_6222_;
                                                v_isShared_6227_ = v_isSharedCheck_6231_;
                                                state = 17;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6224_);
                                                crate::leanh::lean_dec(v___x_6222_);
                                                v___x_6226_ = crate::leanh::lean_box(0);
                                                v_isShared_6227_ = v_isSharedCheck_6231_;
                                                state = 17;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6208_);
                                        crate::leanh::lean_dec_ref(v___y_6202_);
                                        crate::leanh::lean_dec_ref(v_k_6196_);
                                        crate::leanh::lean_dec_ref(v_code_6077_);
                                        v_a_6232_ = crate::leanh::lean_ctor_get(v___x_6220_, 0);
                                        v_isSharedCheck_6239_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6220_)) as u8;
                                        if v_isSharedCheck_6239_ == 0 {
                                            v___x_6234_ = v___x_6220_;
                                            v_isShared_6235_ = v_isSharedCheck_6239_;
                                            state = 19;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6232_);
                                            crate::leanh::lean_dec(v___x_6220_);
                                            v___x_6234_ = crate::leanh::lean_box(0);
                                            v_isShared_6235_ = v_isSharedCheck_6239_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v_a_6208_);
                                    crate::leanh::lean_dec_ref(v___y_6202_);
                                    crate::leanh::lean_dec_ref(v_k_6196_);
                                    crate::leanh::lean_dec_ref(v_code_6077_);
                                    v_a_6240_ = crate::leanh::lean_ctor_get(v___x_6218_, 0);
                                    v_isSharedCheck_6247_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6218_)) as u8;
                                    if v_isSharedCheck_6247_ == 0 {
                                        v___x_6242_ = v___x_6218_;
                                        v_isShared_6243_ = v_isSharedCheck_6247_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6240_);
                                        crate::leanh::lean_dec(v___x_6218_);
                                        v___x_6242_ = crate::leanh::lean_box(0);
                                        v_isShared_6243_ = v_isSharedCheck_6247_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v___x_6248_ = lean_st_ref_get(v___y_6198_);
                        v_subst_6249_ = crate::leanh::lean_ctor_get(v___x_6248_, 0);
                        crate::leanh::lean_inc_ref(v_subst_6249_);
                        crate::leanh::lean_dec(v___x_6248_);
                        v___x_6250_ = 0;
                        v___x_6251_ = l_Lean_Compiler_LCNF_normFunDeclImp(
                            v___x_6209_,
                            v___x_6250_,
                            v_decl_6195_,
                            v_subst_6249_,
                            v___y_6200_,
                            v___y_6201_,
                            v___y_6202_,
                            v___y_6203_,
                        );
                        crate::leanh::lean_dec_ref(v_subst_6249_);
                        if crate::leanh::lean_obj_tag(v___x_6251_) == 0 {
                            v_a_6252_ = crate::leanh::lean_ctor_get(v___x_6251_, 0);
                            crate::leanh::lean_inc(v_a_6252_);
                            crate::leanh::lean_dec_ref_known(v___x_6251_, 1);
                            v___x_6253_ = (crate::leanh::lean_unbox(v_a_6208_) as u8);
                            crate::leanh::lean_dec(v_a_6208_);
                            v___y_6123_ = v___x_6253_;
                            v___y_6124_ = v_k_6196_;
                            v_decl_6125_ = v_a_6252_;
                            v___y_6126_ = v___y_6197_;
                            v___y_6127_ = v___y_6198_;
                            v___y_6128_ = v___y_6199_;
                            v___y_6129_ = v___y_6200_;
                            v___y_6130_ = v___y_6201_;
                            v___y_6131_ = v___y_6202_;
                            v___y_6132_ = v___y_6203_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_6208_);
                            crate::leanh::lean_dec_ref(v___y_6202_);
                            crate::leanh::lean_dec_ref(v_k_6196_);
                            crate::leanh::lean_dec_ref(v_code_6077_);
                            v_a_6254_ = crate::leanh::lean_ctor_get(v___x_6251_, 0);
                            v_isSharedCheck_6261_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6251_)) as u8;
                            if v_isSharedCheck_6261_ == 0 {
                                v___x_6256_ = v___x_6251_;
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 23;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6254_);
                                crate::leanh::lean_dec(v___x_6251_);
                                v___x_6256_ = crate::leanh::lean_box(0);
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6202_);
                    crate::leanh::lean_dec_ref(v_k_6196_);
                    crate::leanh::lean_dec_ref(v_decl_6195_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v_a_6262_ = crate::leanh::lean_ctor_get(v___x_6207_, 0);
                    v_isSharedCheck_6269_ = (!crate::leanh::lean_is_exclusive(v___x_6207_)) as u8;
                    if v_isSharedCheck_6269_ == 0 {
                        v___x_6264_ = v___x_6207_;
                        v_isShared_6265_ = v_isSharedCheck_6269_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6262_);
                        crate::leanh::lean_dec(v___x_6207_);
                        v___x_6264_ = crate::leanh::lean_box(0);
                        v_isShared_6265_ = v_isSharedCheck_6269_;
                        state = 25;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_6227_ == 0 {
                    v___x_6229_ = v___x_6226_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_6230_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_a_6224_);
                    v___x_6229_ = v_reuseFailAlloc_6230_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_6229_;
            }
            19 => {
                if v_isShared_6235_ == 0 {
                    v___x_6237_ = v___x_6234_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_6238_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
                    v___x_6237_ = v_reuseFailAlloc_6238_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_6237_;
            }
            21 => {
                if v_isShared_6243_ == 0 {
                    v___x_6245_ = v___x_6242_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_6246_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6246_, 0, v_a_6240_);
                    v___x_6245_ = v_reuseFailAlloc_6246_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_6245_;
            }
            23 => {
                if v_isShared_6257_ == 0 {
                    v___x_6259_ = v___x_6256_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_6260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6254_);
                    v___x_6259_ = v_reuseFailAlloc_6260_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_6259_;
            }
            25 => {
                if v_isShared_6265_ == 0 {
                    v___x_6267_ = v___x_6264_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_6268_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
                    v___x_6267_ = v_reuseFailAlloc_6268_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_6267_;
            }
            27 => {
                if v___y_6273_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v___x_6274_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6274_, 0, v___y_6271_);
                    crate::leanh::lean_ctor_set(v___x_6274_, 1, v___y_6272_);
                    v___x_6275_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6275_, 0, v___x_6274_);
                    return v___x_6275_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6272_);
                    crate::leanh::lean_dec_ref(v___y_6271_);
                    v___x_6276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6276_, 0, v_code_6077_);
                    return v___x_6276_;
                }
            }
            28 => {
                crate::leanh::lean_inc_ref(v___y_6279_);
                v___x_6288_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(
                    v___y_6279_,
                    v___y_6285_,
                    v___y_6278_,
                    v___y_6280_,
                    v___y_6283_,
                );
                if crate::leanh::lean_obj_tag(v___x_6288_) == 0 {
                    v_a_6289_ = crate::leanh::lean_ctor_get(v___x_6288_, 0);
                    crate::leanh::lean_inc(v_a_6289_);
                    crate::leanh::lean_dec_ref_known(v___x_6288_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6289_) == 1 {
                        crate::leanh::lean_dec_ref(v___y_6286_);
                        crate::leanh::lean_dec_ref(v___y_6279_);
                        crate::leanh::lean_dec_ref(v_code_6077_);
                        v_val_6290_ = crate::leanh::lean_ctor_get(v_a_6289_, 0);
                        crate::leanh::lean_inc(v_val_6290_);
                        crate::leanh::lean_dec_ref_known(v_a_6289_, 1);
                        v___x_6291_ =
                            l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6281_);
                        if crate::leanh::lean_obj_tag(v___x_6291_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6291_, 1);
                            crate::leanh::lean_inc_ref(v___y_6280_);
                            v___x_6292_ = l_Lean_Compiler_LCNF_Simp_simp(
                                v___y_6287_,
                                v___y_6282_,
                                v___y_6281_,
                                v___y_6284_,
                                v___y_6285_,
                                v___y_6278_,
                                v___y_6280_,
                                v___y_6283_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6292_) == 0 {
                                v_a_6293_ = crate::leanh::lean_ctor_get(v___x_6292_, 0);
                                crate::leanh::lean_inc(v_a_6293_);
                                crate::leanh::lean_dec_ref_known(v___x_6292_, 1);
                                v___x_6294_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(
                                    v_val_6290_,
                                    v_a_6293_,
                                    v___y_6282_,
                                    v___y_6281_,
                                    v___y_6284_,
                                    v___y_6285_,
                                    v___y_6278_,
                                    v___y_6280_,
                                    v___y_6283_,
                                );
                                crate::leanh::lean_dec_ref(v___y_6280_);
                                crate::leanh::lean_dec(v_val_6290_);
                                return v___x_6294_;
                            } else {
                                crate::leanh::lean_dec(v_val_6290_);
                                crate::leanh::lean_dec_ref(v___y_6280_);
                                return v___x_6292_;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_6290_);
                            crate::leanh::lean_dec_ref(v___y_6287_);
                            crate::leanh::lean_dec_ref(v___y_6280_);
                            v_a_6295_ = crate::leanh::lean_ctor_get(v___x_6291_, 0);
                            v_isSharedCheck_6302_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6291_)) as u8;
                            if v_isSharedCheck_6302_ == 0 {
                                v___x_6297_ = v___x_6291_;
                                v_isShared_6298_ = v_isSharedCheck_6302_;
                                state = 29;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6295_);
                                crate::leanh::lean_dec(v___x_6291_);
                                v___x_6297_ = crate::leanh::lean_box(0);
                                v_isShared_6298_ = v_isSharedCheck_6302_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_6289_);
                        crate::leanh::lean_inc_ref(v___y_6279_);
                        v___x_6303_ = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(
                            v___y_6279_,
                            v___y_6282_,
                            v___y_6281_,
                            v___y_6284_,
                            v___y_6285_,
                            v___y_6278_,
                            v___y_6280_,
                            v___y_6283_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6303_) == 0 {
                            v_a_6304_ = crate::leanh::lean_ctor_get(v___x_6303_, 0);
                            crate::leanh::lean_inc(v_a_6304_);
                            crate::leanh::lean_dec_ref_known(v___x_6303_, 1);
                            if crate::leanh::lean_obj_tag(v_a_6304_) == 1 {
                                crate::leanh::lean_dec_ref(v___y_6286_);
                                crate::leanh::lean_dec_ref(v___y_6279_);
                                crate::leanh::lean_dec_ref(v_code_6077_);
                                v_val_6305_ = crate::leanh::lean_ctor_get(v_a_6304_, 0);
                                crate::leanh::lean_inc(v_val_6305_);
                                crate::leanh::lean_dec_ref_known(v_a_6304_, 1);
                                v___x_6306_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_6306_, 0, v_val_6305_);
                                crate::leanh::lean_ctor_set(v___x_6306_, 1, v___y_6287_);
                                v_code_6077_ = v___x_6306_;
                                v_a_6078_ = v___y_6282_;
                                v_a_6079_ = v___y_6281_;
                                v_a_6080_ = v___y_6284_;
                                v_a_6081_ = v___y_6285_;
                                v_a_6082_ = v___y_6278_;
                                v_a_6083_ = v___y_6280_;
                                v_a_6084_ = v___y_6283_;
                                state = 0;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6304_);
                                v_fvarId_6308_ = crate::leanh::lean_ctor_get(v___y_6279_, 0);
                                v_value_6309_ = crate::leanh::lean_ctor_get(v___y_6279_, 3);
                                v___x_6310_ =
                                    l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_6309_);
                                if crate::leanh::lean_obj_tag(v___x_6310_) == 0 {
                                    v_a_6311_ = crate::leanh::lean_ctor_get(v___x_6310_, 0);
                                    crate::leanh::lean_inc(v_a_6311_);
                                    crate::leanh::lean_dec_ref_known(v___x_6310_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_6311_) == 1 {
                                        crate::leanh::lean_dec_ref(v___y_6286_);
                                        crate::leanh::lean_dec_ref(v_code_6077_);
                                        v_val_6312_ = crate::leanh::lean_ctor_get(v_a_6311_, 0);
                                        crate::leanh::lean_inc(v_val_6312_);
                                        crate::leanh::lean_dec_ref_known(v_a_6311_, 1);
                                        crate::leanh::lean_inc(v_fvarId_6308_);
                                        v___x_6313_ =
                                            l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                                                v_fvarId_6308_,
                                                v_val_6312_,
                                                v___y_6281_,
                                                v___y_6285_,
                                                v___y_6278_,
                                                v___y_6280_,
                                                v___y_6283_,
                                            );
                                        if crate::leanh::lean_obj_tag(v___x_6313_) == 0 {
                                            crate::leanh::lean_dec_ref_known(v___x_6313_, 1);
                                            v___x_6314_ =
                                                l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
                                                    v___y_6279_,
                                                    v___y_6281_,
                                                    v___y_6278_,
                                                );
                                            crate::leanh::lean_dec_ref(v___y_6279_);
                                            if crate::leanh::lean_obj_tag(v___x_6314_) == 0 {
                                                crate::leanh::lean_dec_ref_known(v___x_6314_, 1);
                                                v_code_6077_ = v___y_6287_;
                                                v_a_6078_ = v___y_6282_;
                                                v_a_6079_ = v___y_6281_;
                                                v_a_6080_ = v___y_6284_;
                                                v_a_6081_ = v___y_6285_;
                                                v_a_6082_ = v___y_6278_;
                                                v_a_6083_ = v___y_6280_;
                                                v_a_6084_ = v___y_6283_;
                                                state = 0;
                                                continue;
                                            } else {
                                                crate::leanh::lean_dec_ref(v___y_6287_);
                                                crate::leanh::lean_dec_ref(v___y_6280_);
                                                v_a_6316_ =
                                                    crate::leanh::lean_ctor_get(v___x_6314_, 0);
                                                v_isSharedCheck_6323_ =
                                                    (!crate::leanh::lean_is_exclusive(v___x_6314_))
                                                        as u8;
                                                if v_isSharedCheck_6323_ == 0 {
                                                    v___x_6318_ = v___x_6314_;
                                                    v_isShared_6319_ = v_isSharedCheck_6323_;
                                                    state = 31;
                                                    continue;
                                                } else {
                                                    crate::leanh::lean_inc(v_a_6316_);
                                                    crate::leanh::lean_dec(v___x_6314_);
                                                    v___x_6318_ = crate::leanh::lean_box(0);
                                                    v_isShared_6319_ = v_isSharedCheck_6323_;
                                                    state = 31;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___y_6287_);
                                            crate::leanh::lean_dec_ref(v___y_6280_);
                                            crate::leanh::lean_dec_ref(v___y_6279_);
                                            v_a_6324_ = crate::leanh::lean_ctor_get(v___x_6313_, 0);
                                            v_isSharedCheck_6331_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6313_))
                                                    as u8;
                                            if v_isSharedCheck_6331_ == 0 {
                                                v___x_6326_ = v___x_6313_;
                                                v_isShared_6327_ = v_isSharedCheck_6331_;
                                                state = 33;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6324_);
                                                crate::leanh::lean_dec(v___x_6313_);
                                                v___x_6326_ = crate::leanh::lean_box(0);
                                                v_isShared_6327_ = v_isSharedCheck_6331_;
                                                state = 33;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6311_);
                                        crate::leanh::lean_inc_ref(v___y_6287_);
                                        crate::leanh::lean_inc_ref(v___y_6279_);
                                        v___x_6332_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(
                                            v___y_6279_,
                                            v___y_6287_,
                                            v___y_6282_,
                                            v___y_6281_,
                                            v___y_6284_,
                                            v___y_6285_,
                                            v___y_6278_,
                                            v___y_6280_,
                                            v___y_6283_,
                                        );
                                        if crate::leanh::lean_obj_tag(v___x_6332_) == 0 {
                                            v_a_6333_ = crate::leanh::lean_ctor_get(v___x_6332_, 0);
                                            crate::leanh::lean_inc(v_a_6333_);
                                            crate::leanh::lean_dec_ref_known(v___x_6332_, 1);
                                            if crate::leanh::lean_obj_tag(v_a_6333_) == 1 {
                                                crate::leanh::lean_dec_ref(v___y_6287_);
                                                crate::leanh::lean_dec_ref(v___y_6286_);
                                                crate::leanh::lean_dec_ref(v___y_6280_);
                                                crate::leanh::lean_dec_ref(v_code_6077_);
                                                v_val_6334_ =
                                                    crate::leanh::lean_ctor_get(v_a_6333_, 0);
                                                crate::leanh::lean_inc(v_val_6334_);
                                                crate::leanh::lean_dec_ref_known(v_a_6333_, 1);
                                                v___x_6335_ =
                                                    l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
                                                        v___y_6279_,
                                                        v___y_6281_,
                                                        v___y_6278_,
                                                    );
                                                crate::leanh::lean_dec_ref(v___y_6279_);
                                                if crate::leanh::lean_obj_tag(v___x_6335_) == 0 {
                                                    v_isSharedCheck_6342_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_6335_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_6342_ == 0 {
                                                        v_unused_6343_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___x_6335_,
                                                                0,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_6343_);
                                                        v___x_6337_ = v___x_6335_;
                                                        v_isShared_6338_ = v_isSharedCheck_6342_;
                                                        state = 35;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_6335_);
                                                        v___x_6337_ = crate::leanh::lean_box(0);
                                                        v_isShared_6338_ = v_isSharedCheck_6342_;
                                                        state = 35;
                                                        continue;
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec(v_val_6334_);
                                                    v_a_6344_ =
                                                        crate::leanh::lean_ctor_get(v___x_6335_, 0);
                                                    v_isSharedCheck_6351_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_6335_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_6351_ == 0 {
                                                        v___x_6346_ = v___x_6335_;
                                                        v_isShared_6347_ = v_isSharedCheck_6351_;
                                                        state = 37;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_6344_);
                                                        crate::leanh::lean_dec(v___x_6335_);
                                                        v___x_6346_ = crate::leanh::lean_box(0);
                                                        v_isShared_6347_ = v_isSharedCheck_6351_;
                                                        state = 37;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                crate::leanh::lean_dec(v_a_6333_);
                                                crate::leanh::lean_inc(v_value_6309_);
                                                v___x_6352_ =
                                                    l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(
                                                        v_value_6309_,
                                                        v___y_6282_,
                                                        v___y_6281_,
                                                        v___y_6284_,
                                                        v___y_6285_,
                                                        v___y_6278_,
                                                        v___y_6280_,
                                                        v___y_6283_,
                                                    );
                                                if crate::leanh::lean_obj_tag(v___x_6352_) == 0 {
                                                    v_a_6353_ =
                                                        crate::leanh::lean_ctor_get(v___x_6352_, 0);
                                                    crate::leanh::lean_inc(v_a_6353_);
                                                    crate::leanh::lean_dec_ref_known(
                                                        v___x_6352_,
                                                        1,
                                                    );
                                                    if crate::leanh::lean_obj_tag(v_a_6353_) == 1 {
                                                        crate::leanh::lean_dec_ref(v___y_6286_);
                                                        crate::leanh::lean_dec_ref(v_code_6077_);
                                                        v_val_6354_ = crate::leanh::lean_ctor_get(
                                                            v_a_6353_, 0,
                                                        );
                                                        crate::leanh::lean_inc(v_val_6354_);
                                                        crate::leanh::lean_dec_ref_known(
                                                            v_a_6353_, 1,
                                                        );
                                                        v_fst_6355_ = crate::leanh::lean_ctor_get(
                                                            v_val_6354_,
                                                            0,
                                                        );
                                                        crate::leanh::lean_inc(v_fst_6355_);
                                                        v_snd_6356_ = crate::leanh::lean_ctor_get(
                                                            v_val_6354_,
                                                            1,
                                                        );
                                                        crate::leanh::lean_inc(v_snd_6356_);
                                                        crate::leanh::lean_dec(v_val_6354_);
                                                        crate::leanh::lean_inc(v_fvarId_6308_);
                                                        v___x_6357_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_6308_, v_snd_6356_, v___y_6281_, v___y_6285_, v___y_6278_, v___y_6280_, v___y_6283_);
                                                        if crate::leanh::lean_obj_tag(v___x_6357_)
                                                            == 0
                                                        {
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_6357_,
                                                                1,
                                                            );
                                                            v___x_6358_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_6279_, v___y_6281_, v___y_6278_);
                                                            crate::leanh::lean_dec_ref(v___y_6279_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_6358_,
                                                            ) == 0
                                                            {
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_6358_,
                                                                    1,
                                                                );
                                                                crate::leanh::lean_inc_ref(
                                                                    v___y_6280_,
                                                                );
                                                                v___x_6359_ =
                                                                    l_Lean_Compiler_LCNF_Simp_simp(
                                                                        v___y_6287_,
                                                                        v___y_6282_,
                                                                        v___y_6281_,
                                                                        v___y_6284_,
                                                                        v___y_6285_,
                                                                        v___y_6278_,
                                                                        v___y_6280_,
                                                                        v___y_6283_,
                                                                    );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_6359_,
                                                                ) == 0
                                                                {
                                                                    v_a_6360_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_6359_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_6360_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref_known(v___x_6359_, 1);
                                                                    v___x_6361_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_6355_, v_a_6360_, v___y_6282_, v___y_6281_, v___y_6284_, v___y_6285_, v___y_6278_, v___y_6280_, v___y_6283_);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_6280_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_fst_6355_,
                                                                    );
                                                                    return v___x_6361_;
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_fst_6355_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_6280_,
                                                                    );
                                                                    return v___x_6359_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_fst_6355_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v___y_6287_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___y_6280_,
                                                                );
                                                                v_a_6362_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_6358_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_6369_ = (!crate::leanh::lean_is_exclusive(v___x_6358_)) as u8;
                                                                if v_isSharedCheck_6369_ == 0 {
                                                                    v___x_6364_ = v___x_6358_;
                                                                    v_isShared_6365_ =
                                                                        v_isSharedCheck_6369_;
                                                                    state = 39;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_6362_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_6358_,
                                                                    );
                                                                    v___x_6364_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_6365_ =
                                                                        v_isSharedCheck_6369_;
                                                                    state = 39;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec(v_fst_6355_);
                                                            crate::leanh::lean_dec_ref(v___y_6287_);
                                                            crate::leanh::lean_dec_ref(v___y_6280_);
                                                            crate::leanh::lean_dec_ref(v___y_6279_);
                                                            v_a_6370_ = crate::leanh::lean_ctor_get(
                                                                v___x_6357_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_6377_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_6357_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_6377_ == 0 {
                                                                v___x_6372_ = v___x_6357_;
                                                                v_isShared_6373_ =
                                                                    v_isSharedCheck_6377_;
                                                                state = 41;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_6370_);
                                                                crate::leanh::lean_dec(v___x_6357_);
                                                                v___x_6372_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_6373_ =
                                                                    v_isSharedCheck_6377_;
                                                                state = 41;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec(v_a_6353_);
                                                        crate::leanh::lean_inc_ref(v___y_6280_);
                                                        crate::leanh::lean_inc_ref(v___y_6287_);
                                                        v___x_6378_ =
                                                            l_Lean_Compiler_LCNF_Simp_simp(
                                                                v___y_6287_,
                                                                v___y_6282_,
                                                                v___y_6281_,
                                                                v___y_6284_,
                                                                v___y_6285_,
                                                                v___y_6278_,
                                                                v___y_6280_,
                                                                v___y_6283_,
                                                            );
                                                        if crate::leanh::lean_obj_tag(v___x_6378_)
                                                            == 0
                                                        {
                                                            v_a_6379_ = crate::leanh::lean_ctor_get(
                                                                v___x_6378_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_6379_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_6378_,
                                                                1,
                                                            );
                                                            v___x_6380_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_6308_, v___y_6281_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_6380_,
                                                            ) == 0
                                                            {
                                                                v_a_6381_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_6380_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_6381_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_6380_,
                                                                    1,
                                                                );
                                                                v___x_6382_ =
                                                                    (crate::leanh::lean_unbox(
                                                                        v_a_6381_,
                                                                    )
                                                                        as u8);
                                                                crate::leanh::lean_dec(v_a_6381_);
                                                                if v___x_6382_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_6287_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_6286_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_6280_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_code_6077_,
                                                                    );
                                                                    v___x_6383_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_6279_, v___y_6281_, v___y_6278_);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_6279_,
                                                                    );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_6383_,
                                                                    ) == 0
                                                                    {
                                                                        v_isSharedCheck_6390_ = (!crate::leanh::lean_is_exclusive(v___x_6383_)) as u8;
                                                                        if v_isSharedCheck_6390_
                                                                            == 0
                                                                        {
                                                                            v_unused_6391_ = crate::leanh::lean_ctor_get(v___x_6383_, 0);
                                                                            crate::leanh::lean_dec(
                                                                                v_unused_6391_,
                                                                            );
                                                                            v___x_6385_ =
                                                                                v___x_6383_;
                                                                            v_isShared_6386_ = v_isSharedCheck_6390_;
                                                                            state = 43;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_dec(
                                                                                v___x_6383_,
                                                                            );
                                                                            v___x_6385_ = crate::leanh::lean_box(0);
                                                                            v_isShared_6386_ = v_isSharedCheck_6390_;
                                                                            state = 43;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_6379_,
                                                                        );
                                                                        v_a_6392_ = crate::leanh::lean_ctor_get(v___x_6383_, 0);
                                                                        v_isSharedCheck_6399_ = (!crate::leanh::lean_is_exclusive(v___x_6383_)) as u8;
                                                                        if v_isSharedCheck_6399_
                                                                            == 0
                                                                        {
                                                                            v___x_6394_ =
                                                                                v___x_6383_;
                                                                            v_isShared_6395_ = v_isSharedCheck_6399_;
                                                                            state = 45;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_6392_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_6383_,
                                                                            );
                                                                            v___x_6394_ = crate::leanh::lean_box(0);
                                                                            v_isShared_6395_ = v_isSharedCheck_6399_;
                                                                            state = 45;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_inc_ref(
                                                                        v___y_6279_,
                                                                    );
                                                                    v___x_6400_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_6279_, v___y_6282_, v___y_6281_, v___y_6284_, v___y_6285_, v___y_6278_, v___y_6280_, v___y_6283_);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v___y_6280_,
                                                                    );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_6400_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec_ref_known(v___x_6400_, 1);
                                                                        v___x_6401_ = lean_ptr_addr(
                                                                            v___y_6287_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___y_6287_,
                                                                        );
                                                                        v___x_6402_ = lean_ptr_addr(
                                                                            v_a_6379_,
                                                                        );
                                                                        v___x_6403_ =
                                                                            lean_usize_dec_eq(
                                                                                v___x_6401_,
                                                                                v___x_6402_,
                                                                            );
                                                                        if v___x_6403_ == 0 {
                                                                            crate::leanh::lean_dec_ref(v___y_6286_);
                                                                            v___y_6271_ =
                                                                                v___y_6279_;
                                                                            v___y_6272_ = v_a_6379_;
                                                                            v___y_6273_ =
                                                                                v___x_6403_;
                                                                            state = 27;
                                                                            continue;
                                                                        } else {
                                                                            v___x_6404_ =
                                                                                lean_ptr_addr(
                                                                                    v___y_6286_,
                                                                                );
                                                                            crate::leanh::lean_dec_ref(v___y_6286_);
                                                                            v___x_6405_ =
                                                                                lean_ptr_addr(
                                                                                    v___y_6279_,
                                                                                );
                                                                            v___x_6406_ =
                                                                                lean_usize_dec_eq(
                                                                                    v___x_6404_,
                                                                                    v___x_6405_,
                                                                                );
                                                                            v___y_6271_ =
                                                                                v___y_6279_;
                                                                            v___y_6272_ = v_a_6379_;
                                                                            v___y_6273_ =
                                                                                v___x_6406_;
                                                                            state = 27;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        crate::leanh::lean_dec(
                                                                            v_a_6379_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___y_6287_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___y_6286_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v___y_6279_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_code_6077_,
                                                                        );
                                                                        v_a_6407_ = crate::leanh::lean_ctor_get(v___x_6400_, 0);
                                                                        v_isSharedCheck_6414_ = (!crate::leanh::lean_is_exclusive(v___x_6400_)) as u8;
                                                                        if v_isSharedCheck_6414_
                                                                            == 0
                                                                        {
                                                                            v___x_6409_ =
                                                                                v___x_6400_;
                                                                            v_isShared_6410_ = v_isSharedCheck_6414_;
                                                                            state = 47;
                                                                            continue;
                                                                        } else {
                                                                            crate::leanh::lean_inc(
                                                                                v_a_6407_,
                                                                            );
                                                                            crate::leanh::lean_dec(
                                                                                v___x_6400_,
                                                                            );
                                                                            v___x_6409_ = crate::leanh::lean_box(0);
                                                                            v_isShared_6410_ = v_isSharedCheck_6414_;
                                                                            state = 47;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_6379_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v___y_6287_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___y_6286_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___y_6280_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___y_6279_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_code_6077_,
                                                                );
                                                                v_a_6415_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_6380_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_6422_ = (!crate::leanh::lean_is_exclusive(v___x_6380_)) as u8;
                                                                if v_isSharedCheck_6422_ == 0 {
                                                                    v___x_6417_ = v___x_6380_;
                                                                    v_isShared_6418_ =
                                                                        v_isSharedCheck_6422_;
                                                                    state = 49;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_6415_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_6380_,
                                                                    );
                                                                    v___x_6417_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_6418_ =
                                                                        v_isSharedCheck_6422_;
                                                                    state = 49;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___y_6287_);
                                                            crate::leanh::lean_dec_ref(v___y_6286_);
                                                            crate::leanh::lean_dec_ref(v___y_6280_);
                                                            crate::leanh::lean_dec_ref(v___y_6279_);
                                                            crate::leanh::lean_dec_ref(
                                                                v_code_6077_,
                                                            );
                                                            return v___x_6378_;
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___y_6287_);
                                                    crate::leanh::lean_dec_ref(v___y_6286_);
                                                    crate::leanh::lean_dec_ref(v___y_6280_);
                                                    crate::leanh::lean_dec_ref(v___y_6279_);
                                                    crate::leanh::lean_dec_ref(v_code_6077_);
                                                    v_a_6423_ =
                                                        crate::leanh::lean_ctor_get(v___x_6352_, 0);
                                                    v_isSharedCheck_6430_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_6352_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_6430_ == 0 {
                                                        v___x_6425_ = v___x_6352_;
                                                        v_isShared_6426_ = v_isSharedCheck_6430_;
                                                        state = 51;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_inc(v_a_6423_);
                                                        crate::leanh::lean_dec(v___x_6352_);
                                                        v___x_6425_ = crate::leanh::lean_box(0);
                                                        v_isShared_6426_ = v_isSharedCheck_6430_;
                                                        state = 51;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            crate::leanh::lean_dec_ref(v___y_6287_);
                                            crate::leanh::lean_dec_ref(v___y_6286_);
                                            crate::leanh::lean_dec_ref(v___y_6280_);
                                            crate::leanh::lean_dec_ref(v___y_6279_);
                                            crate::leanh::lean_dec_ref(v_code_6077_);
                                            v_a_6431_ = crate::leanh::lean_ctor_get(v___x_6332_, 0);
                                            v_isSharedCheck_6438_ =
                                                (!crate::leanh::lean_is_exclusive(v___x_6332_))
                                                    as u8;
                                            if v_isSharedCheck_6438_ == 0 {
                                                v___x_6433_ = v___x_6332_;
                                                v_isShared_6434_ = v_isSharedCheck_6438_;
                                                state = 53;
                                                continue;
                                            } else {
                                                crate::leanh::lean_inc(v_a_6431_);
                                                crate::leanh::lean_dec(v___x_6332_);
                                                v___x_6433_ = crate::leanh::lean_box(0);
                                                v_isShared_6434_ = v_isSharedCheck_6438_;
                                                state = 53;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___y_6287_);
                                    crate::leanh::lean_dec_ref(v___y_6286_);
                                    crate::leanh::lean_dec_ref(v___y_6280_);
                                    crate::leanh::lean_dec_ref(v___y_6279_);
                                    crate::leanh::lean_dec_ref(v_code_6077_);
                                    v_a_6439_ = crate::leanh::lean_ctor_get(v___x_6310_, 0);
                                    v_isSharedCheck_6446_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6310_)) as u8;
                                    if v_isSharedCheck_6446_ == 0 {
                                        v___x_6441_ = v___x_6310_;
                                        v_isShared_6442_ = v_isSharedCheck_6446_;
                                        state = 55;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6439_);
                                        crate::leanh::lean_dec(v___x_6310_);
                                        v___x_6441_ = crate::leanh::lean_box(0);
                                        v_isShared_6442_ = v_isSharedCheck_6446_;
                                        state = 55;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___y_6287_);
                            crate::leanh::lean_dec_ref(v___y_6286_);
                            crate::leanh::lean_dec_ref(v___y_6280_);
                            crate::leanh::lean_dec_ref(v___y_6279_);
                            crate::leanh::lean_dec_ref(v_code_6077_);
                            v_a_6447_ = crate::leanh::lean_ctor_get(v___x_6303_, 0);
                            v_isSharedCheck_6454_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6303_)) as u8;
                            if v_isSharedCheck_6454_ == 0 {
                                v___x_6449_ = v___x_6303_;
                                v_isShared_6450_ = v_isSharedCheck_6454_;
                                state = 57;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6447_);
                                crate::leanh::lean_dec(v___x_6303_);
                                v___x_6449_ = crate::leanh::lean_box(0);
                                v_isShared_6450_ = v_isSharedCheck_6454_;
                                state = 57;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6287_);
                    crate::leanh::lean_dec_ref(v___y_6286_);
                    crate::leanh::lean_dec_ref(v___y_6280_);
                    crate::leanh::lean_dec_ref(v___y_6279_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v_a_6455_ = crate::leanh::lean_ctor_get(v___x_6288_, 0);
                    v_isSharedCheck_6462_ = (!crate::leanh::lean_is_exclusive(v___x_6288_)) as u8;
                    if v_isSharedCheck_6462_ == 0 {
                        v___x_6457_ = v___x_6288_;
                        v_isShared_6458_ = v_isSharedCheck_6462_;
                        state = 59;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6455_);
                        crate::leanh::lean_dec(v___x_6288_);
                        v___x_6457_ = crate::leanh::lean_box(0);
                        v_isShared_6458_ = v_isSharedCheck_6462_;
                        state = 59;
                        continue;
                    }
                }
            }
            29 => {
                if v_isShared_6298_ == 0 {
                    v___x_6300_ = v___x_6297_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_6301_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_a_6295_);
                    v___x_6300_ = v_reuseFailAlloc_6301_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_6300_;
            }
            31 => {
                if v_isShared_6319_ == 0 {
                    v___x_6321_ = v___x_6318_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_6322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6322_, 0, v_a_6316_);
                    v___x_6321_ = v_reuseFailAlloc_6322_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_6321_;
            }
            33 => {
                if v_isShared_6327_ == 0 {
                    v___x_6329_ = v___x_6326_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_6330_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6330_, 0, v_a_6324_);
                    v___x_6329_ = v_reuseFailAlloc_6330_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_6329_;
            }
            35 => {
                if v_isShared_6338_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6337_, 0, v_val_6334_);
                    v___x_6340_ = v___x_6337_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6341_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6341_, 0, v_val_6334_);
                    v___x_6340_ = v_reuseFailAlloc_6341_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                return v___x_6340_;
            }
            37 => {
                if v_isShared_6347_ == 0 {
                    v___x_6349_ = v___x_6346_;
                    state = 38;
                    continue;
                } else {
                    v_reuseFailAlloc_6350_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_a_6344_);
                    v___x_6349_ = v_reuseFailAlloc_6350_;
                    state = 38;
                    continue;
                }
            }
            38 => {
                return v___x_6349_;
            }
            39 => {
                if v_isShared_6365_ == 0 {
                    v___x_6367_ = v___x_6364_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_6368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6368_, 0, v_a_6362_);
                    v___x_6367_ = v_reuseFailAlloc_6368_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_6367_;
            }
            41 => {
                if v_isShared_6373_ == 0 {
                    v___x_6375_ = v___x_6372_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_6376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6376_, 0, v_a_6370_);
                    v___x_6375_ = v_reuseFailAlloc_6376_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_6375_;
            }
            43 => {
                if v_isShared_6386_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6385_, 0, v_a_6379_);
                    v___x_6388_ = v___x_6385_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6389_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6389_, 0, v_a_6379_);
                    v___x_6388_ = v_reuseFailAlloc_6389_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_6388_;
            }
            45 => {
                if v_isShared_6395_ == 0 {
                    v___x_6397_ = v___x_6394_;
                    state = 46;
                    continue;
                } else {
                    v_reuseFailAlloc_6398_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6398_, 0, v_a_6392_);
                    v___x_6397_ = v_reuseFailAlloc_6398_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_6397_;
            }
            47 => {
                if v_isShared_6410_ == 0 {
                    v___x_6412_ = v___x_6409_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_6413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_a_6407_);
                    v___x_6412_ = v_reuseFailAlloc_6413_;
                    state = 48;
                    continue;
                }
            }
            48 => {
                return v___x_6412_;
            }
            49 => {
                if v_isShared_6418_ == 0 {
                    v___x_6420_ = v___x_6417_;
                    state = 50;
                    continue;
                } else {
                    v_reuseFailAlloc_6421_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6421_, 0, v_a_6415_);
                    v___x_6420_ = v_reuseFailAlloc_6421_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_6420_;
            }
            51 => {
                if v_isShared_6426_ == 0 {
                    v___x_6428_ = v___x_6425_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_6429_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6429_, 0, v_a_6423_);
                    v___x_6428_ = v_reuseFailAlloc_6429_;
                    state = 52;
                    continue;
                }
            }
            52 => {
                return v___x_6428_;
            }
            53 => {
                if v_isShared_6434_ == 0 {
                    v___x_6436_ = v___x_6433_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_6437_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6437_, 0, v_a_6431_);
                    v___x_6436_ = v_reuseFailAlloc_6437_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_6436_;
            }
            55 => {
                if v_isShared_6442_ == 0 {
                    v___x_6444_ = v___x_6441_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_6445_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_a_6439_);
                    v___x_6444_ = v_reuseFailAlloc_6445_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_6444_;
            }
            57 => {
                if v_isShared_6450_ == 0 {
                    v___x_6452_ = v___x_6449_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_6453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6453_, 0, v_a_6447_);
                    v___x_6452_ = v_reuseFailAlloc_6453_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_6452_;
            }
            59 => {
                if v_isShared_6458_ == 0 {
                    v___x_6460_ = v___x_6457_;
                    state = 60;
                    continue;
                } else {
                    v_reuseFailAlloc_6461_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6455_);
                    v___x_6460_ = v_reuseFailAlloc_6461_;
                    state = 60;
                    continue;
                }
            }
            60 => {
                return v___x_6460_;
            }
            61 => {
                v___x_6478_ = l_Lean_Expr_isErased(v_type_6469_);
                crate::leanh::lean_dec_ref(v_type_6469_);
                if v___x_6478_ == 0 {
                    crate::leanh::lean_dec(v_value_6470_);
                    crate::leanh::lean_dec(v_fvarId_6468_);
                    v___y_6278_ = v___y_6475_;
                    v___y_6279_ = v_decl_6467_;
                    v___y_6280_ = v___y_6476_;
                    v___y_6281_ = v___y_6472_;
                    v___y_6282_ = v___y_6471_;
                    v___y_6283_ = v___y_6477_;
                    v___y_6284_ = v___y_6473_;
                    v___y_6285_ = v___y_6474_;
                    v___y_6286_ = v___y_6466_;
                    v___y_6287_ = v___y_6465_;
                    state = 28;
                    continue;
                } else {
                    v___x_6479_ = crate::leanh::lean_box(1);
                    v___x_6480_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(
                        v___y_6464_,
                        v_value_6470_,
                        v___x_6479_,
                    );
                    crate::leanh::lean_dec(v_value_6470_);
                    if v___x_6480_ == 0 {
                        if v___x_6478_ == 0 {
                            crate::leanh::lean_dec(v_fvarId_6468_);
                            v___y_6278_ = v___y_6475_;
                            v___y_6279_ = v_decl_6467_;
                            v___y_6280_ = v___y_6476_;
                            v___y_6281_ = v___y_6472_;
                            v___y_6282_ = v___y_6471_;
                            v___y_6283_ = v___y_6477_;
                            v___y_6284_ = v___y_6473_;
                            v___y_6285_ = v___y_6474_;
                            v___y_6286_ = v___y_6466_;
                            v___y_6287_ = v___y_6465_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_6466_);
                            crate::leanh::lean_dec_ref(v_code_6077_);
                            v___x_6481_ = lean_st_ref_take(v___y_6472_);
                            v_subst_6482_ = crate::leanh::lean_ctor_get(v___x_6481_, 0);
                            v_used_6483_ = crate::leanh::lean_ctor_get(v___x_6481_, 1);
                            v_binderRenaming_6484_ = crate::leanh::lean_ctor_get(v___x_6481_, 2);
                            v_funDeclInfoMap_6485_ = crate::leanh::lean_ctor_get(v___x_6481_, 3);
                            v_simplified_6486_ = crate::leanh::lean_ctor_get_uint8(
                                v___x_6481_,
                                (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                            );
                            v_visited_6487_ = crate::leanh::lean_ctor_get(v___x_6481_, 4);
                            v_inline_6488_ = crate::leanh::lean_ctor_get(v___x_6481_, 5);
                            v_inlineLocal_6489_ = crate::leanh::lean_ctor_get(v___x_6481_, 6);
                            v_isSharedCheck_6509_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6481_)) as u8;
                            if v_isSharedCheck_6509_ == 0 {
                                v___x_6491_ = v___x_6481_;
                                v_isShared_6492_ = v_isSharedCheck_6509_;
                                state = 62;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_inlineLocal_6489_);
                                crate::leanh::lean_inc(v_inline_6488_);
                                crate::leanh::lean_inc(v_visited_6487_);
                                crate::leanh::lean_inc(v_funDeclInfoMap_6485_);
                                crate::leanh::lean_inc(v_binderRenaming_6484_);
                                crate::leanh::lean_inc(v_used_6483_);
                                crate::leanh::lean_inc(v_subst_6482_);
                                crate::leanh::lean_dec(v___x_6481_);
                                v___x_6491_ = crate::leanh::lean_box(0);
                                v_isShared_6492_ = v_isSharedCheck_6509_;
                                state = 62;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_6468_);
                        v___y_6278_ = v___y_6475_;
                        v___y_6279_ = v_decl_6467_;
                        v___y_6280_ = v___y_6476_;
                        v___y_6281_ = v___y_6472_;
                        v___y_6282_ = v___y_6471_;
                        v___y_6283_ = v___y_6477_;
                        v___y_6284_ = v___y_6473_;
                        v___y_6285_ = v___y_6474_;
                        v___y_6286_ = v___y_6466_;
                        v___y_6287_ = v___y_6465_;
                        state = 28;
                        continue;
                    }
                }
            }
            62 => {
                v___x_6493_ = crate::leanh::lean_box(0);
                v___x_6494_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_6482_, v_fvarId_6468_, v___x_6493_);
                if v_isShared_6492_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6491_, 0, v___x_6494_);
                    v___x_6496_ = v___x_6491_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_6508_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 0, v___x_6494_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 1, v_used_6483_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 2, v_binderRenaming_6484_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 3, v_funDeclInfoMap_6485_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 4, v_visited_6487_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 5, v_inline_6488_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6508_, 6, v_inlineLocal_6489_);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_6508_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                        v_simplified_6486_,
                    );
                    v___x_6496_ = v_reuseFailAlloc_6508_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                v___x_6497_ = lean_st_ref_set(v___y_6472_, v___x_6496_);
                v___x_6498_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
                    v_decl_6467_,
                    v___y_6472_,
                    v___y_6475_,
                );
                crate::leanh::lean_dec_ref(v_decl_6467_);
                if crate::leanh::lean_obj_tag(v___x_6498_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6498_, 1);
                    v_code_6077_ = v___y_6465_;
                    v_a_6078_ = v___y_6471_;
                    v_a_6079_ = v___y_6472_;
                    v_a_6080_ = v___y_6473_;
                    v_a_6081_ = v___y_6474_;
                    v_a_6082_ = v___y_6475_;
                    v_a_6083_ = v___y_6476_;
                    v_a_6084_ = v___y_6477_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6476_);
                    crate::leanh::lean_dec_ref(v___y_6465_);
                    v_a_6500_ = crate::leanh::lean_ctor_get(v___x_6498_, 0);
                    v_isSharedCheck_6507_ = (!crate::leanh::lean_is_exclusive(v___x_6498_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6502_ = v___x_6498_;
                        v_isShared_6503_ = v_isSharedCheck_6507_;
                        state = 64;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6500_);
                        crate::leanh::lean_dec(v___x_6498_);
                        v___x_6502_ = crate::leanh::lean_box(0);
                        v_isShared_6503_ = v_isSharedCheck_6507_;
                        state = 64;
                        continue;
                    }
                }
            }
            64 => {
                if v_isShared_6503_ == 0 {
                    v___x_6505_ = v___x_6502_;
                    state = 65;
                    continue;
                } else {
                    v_reuseFailAlloc_6506_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6500_);
                    v___x_6505_ = v_reuseFailAlloc_6506_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_6505_;
            }
            66 => {
                v_fvarId_6522_ = crate::leanh::lean_ctor_get(v___y_6514_, 0);
                v_type_6523_ = crate::leanh::lean_ctor_get(v___y_6514_, 2);
                v_value_6524_ = crate::leanh::lean_ctor_get(v___y_6514_, 3);
                crate::leanh::lean_inc(v_value_6524_);
                v___x_6525_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
                    v_value_6524_,
                    v___y_6515_,
                    v___y_6517_,
                    v___y_6518_,
                    v___y_6519_,
                    v___y_6520_,
                    v___y_6521_,
                );
                if crate::leanh::lean_obj_tag(v___x_6525_) == 0 {
                    v_a_6526_ = crate::leanh::lean_ctor_get(v___x_6525_, 0);
                    crate::leanh::lean_inc(v_a_6526_);
                    crate::leanh::lean_dec_ref_known(v___x_6525_, 1);
                    if crate::leanh::lean_obj_tag(v_a_6526_) == 1 {
                        v_val_6527_ = crate::leanh::lean_ctor_get(v_a_6526_, 0);
                        crate::leanh::lean_inc(v_val_6527_);
                        crate::leanh::lean_dec_ref_known(v_a_6526_, 1);
                        v___x_6528_ =
                            l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6516_);
                        if crate::leanh::lean_obj_tag(v___x_6528_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6528_, 1);
                            v___x_6529_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                v___y_6511_,
                                v___y_6514_,
                                v_val_6527_,
                                v___y_6519_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6529_) == 0 {
                                v_a_6530_ = crate::leanh::lean_ctor_get(v___x_6529_, 0);
                                crate::leanh::lean_inc(v_a_6530_);
                                crate::leanh::lean_dec_ref_known(v___x_6529_, 1);
                                v_fvarId_6531_ = crate::leanh::lean_ctor_get(v_a_6530_, 0);
                                crate::leanh::lean_inc(v_fvarId_6531_);
                                v_type_6532_ = crate::leanh::lean_ctor_get(v_a_6530_, 2);
                                crate::leanh::lean_inc_ref(v_type_6532_);
                                v_value_6533_ = crate::leanh::lean_ctor_get(v_a_6530_, 3);
                                crate::leanh::lean_inc(v_value_6533_);
                                v___y_6464_ = v___y_6511_;
                                v___y_6465_ = v___y_6513_;
                                v___y_6466_ = v___y_6512_;
                                v_decl_6467_ = v_a_6530_;
                                v_fvarId_6468_ = v_fvarId_6531_;
                                v_type_6469_ = v_type_6532_;
                                v_value_6470_ = v_value_6533_;
                                v___y_6471_ = v___y_6515_;
                                v___y_6472_ = v___y_6516_;
                                v___y_6473_ = v___y_6517_;
                                v___y_6474_ = v___y_6518_;
                                v___y_6475_ = v___y_6519_;
                                v___y_6476_ = v___y_6520_;
                                v___y_6477_ = v___y_6521_;
                                state = 61;
                                continue;
                            } else {
                                crate::leanh::lean_dec_ref(v___y_6520_);
                                crate::leanh::lean_dec_ref(v___y_6513_);
                                crate::leanh::lean_dec_ref(v___y_6512_);
                                crate::leanh::lean_dec_ref(v_code_6077_);
                                v_a_6534_ = crate::leanh::lean_ctor_get(v___x_6529_, 0);
                                v_isSharedCheck_6541_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6529_)) as u8;
                                if v_isSharedCheck_6541_ == 0 {
                                    v___x_6536_ = v___x_6529_;
                                    v_isShared_6537_ = v_isSharedCheck_6541_;
                                    state = 67;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6534_);
                                    crate::leanh::lean_dec(v___x_6529_);
                                    v___x_6536_ = crate::leanh::lean_box(0);
                                    v_isShared_6537_ = v_isSharedCheck_6541_;
                                    state = 67;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_6527_);
                            crate::leanh::lean_dec_ref(v___y_6520_);
                            crate::leanh::lean_dec_ref(v___y_6514_);
                            crate::leanh::lean_dec_ref(v___y_6513_);
                            crate::leanh::lean_dec_ref(v___y_6512_);
                            crate::leanh::lean_dec_ref(v_code_6077_);
                            v_a_6542_ = crate::leanh::lean_ctor_get(v___x_6528_, 0);
                            v_isSharedCheck_6549_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6528_)) as u8;
                            if v_isSharedCheck_6549_ == 0 {
                                v___x_6544_ = v___x_6528_;
                                v_isShared_6545_ = v_isSharedCheck_6549_;
                                state = 69;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6542_);
                                crate::leanh::lean_dec(v___x_6528_);
                                v___x_6544_ = crate::leanh::lean_box(0);
                                v_isShared_6545_ = v_isSharedCheck_6549_;
                                state = 69;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_inc(v_value_6524_);
                        crate::leanh::lean_inc_ref(v_type_6523_);
                        crate::leanh::lean_inc(v_fvarId_6522_);
                        crate::leanh::lean_dec(v_a_6526_);
                        v___y_6464_ = v___y_6511_;
                        v___y_6465_ = v___y_6513_;
                        v___y_6466_ = v___y_6512_;
                        v_decl_6467_ = v___y_6514_;
                        v_fvarId_6468_ = v_fvarId_6522_;
                        v_type_6469_ = v_type_6523_;
                        v_value_6470_ = v_value_6524_;
                        v___y_6471_ = v___y_6515_;
                        v___y_6472_ = v___y_6516_;
                        v___y_6473_ = v___y_6517_;
                        v___y_6474_ = v___y_6518_;
                        v___y_6475_ = v___y_6519_;
                        v___y_6476_ = v___y_6520_;
                        v___y_6477_ = v___y_6521_;
                        state = 61;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6520_);
                    crate::leanh::lean_dec_ref(v___y_6514_);
                    crate::leanh::lean_dec_ref(v___y_6513_);
                    crate::leanh::lean_dec_ref(v___y_6512_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v_a_6550_ = crate::leanh::lean_ctor_get(v___x_6525_, 0);
                    v_isSharedCheck_6557_ = (!crate::leanh::lean_is_exclusive(v___x_6525_)) as u8;
                    if v_isSharedCheck_6557_ == 0 {
                        v___x_6552_ = v___x_6525_;
                        v_isShared_6553_ = v_isSharedCheck_6557_;
                        state = 71;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6550_);
                        crate::leanh::lean_dec(v___x_6525_);
                        v___x_6552_ = crate::leanh::lean_box(0);
                        v_isShared_6553_ = v_isSharedCheck_6557_;
                        state = 71;
                        continue;
                    }
                }
            }
            67 => {
                if v_isShared_6537_ == 0 {
                    v___x_6539_ = v___x_6536_;
                    state = 68;
                    continue;
                } else {
                    v_reuseFailAlloc_6540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
                    v___x_6539_ = v_reuseFailAlloc_6540_;
                    state = 68;
                    continue;
                }
            }
            68 => {
                return v___x_6539_;
            }
            69 => {
                if v_isShared_6545_ == 0 {
                    v___x_6547_ = v___x_6544_;
                    state = 70;
                    continue;
                } else {
                    v_reuseFailAlloc_6548_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6548_, 0, v_a_6542_);
                    v___x_6547_ = v_reuseFailAlloc_6548_;
                    state = 70;
                    continue;
                }
            }
            70 => {
                return v___x_6547_;
            }
            71 => {
                if v_isShared_6553_ == 0 {
                    v___x_6555_ = v___x_6552_;
                    state = 72;
                    continue;
                } else {
                    v_reuseFailAlloc_6556_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6556_, 0, v_a_6550_);
                    v___x_6555_ = v_reuseFailAlloc_6556_;
                    state = 72;
                    continue;
                }
            }
            72 => {
                return v___x_6555_;
            }
            73 => {
                if v___y_6561_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v___x_6562_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6562_, 0, v___y_6559_);
                    crate::leanh::lean_ctor_set(v___x_6562_, 1, v___y_6560_);
                    v___x_6563_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6563_, 0, v___x_6562_);
                    return v___x_6563_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6560_);
                    crate::leanh::lean_dec(v___y_6559_);
                    v___x_6564_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6564_, 0, v_code_6077_);
                    return v___x_6564_;
                }
            }
            74 => {
                v___x_6570_ = l_Lean_instBEqFVarId_beq(v___y_6566_, v___y_6568_);
                crate::leanh::lean_dec(v___y_6566_);
                if v___x_6570_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6567_);
                    v___y_6559_ = v___y_6568_;
                    v___y_6560_ = v___y_6569_;
                    v___y_6561_ = v___x_6570_;
                    state = 73;
                    continue;
                } else {
                    v___x_6571_ = lean_ptr_addr(v___y_6567_);
                    crate::leanh::lean_dec_ref(v___y_6567_);
                    v___x_6572_ = lean_ptr_addr(v___y_6569_);
                    v___x_6573_ = lean_usize_dec_eq(v___x_6571_, v___x_6572_);
                    v___y_6559_ = v___y_6568_;
                    v___y_6560_ = v___y_6569_;
                    v___y_6561_ = v___x_6573_;
                    state = 73;
                    continue;
                }
            }
            75 => {
                if crate::leanh::lean_obj_tag(v___y_6579_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_6579_, 1);
                    v___y_6566_ = v___y_6575_;
                    v___y_6567_ = v___y_6576_;
                    v___y_6568_ = v___y_6577_;
                    v___y_6569_ = v___y_6578_;
                    state = 74;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6578_);
                    crate::leanh::lean_dec(v___y_6577_);
                    crate::leanh::lean_dec_ref(v___y_6576_);
                    crate::leanh::lean_dec(v___y_6575_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v_a_6580_ = crate::leanh::lean_ctor_get(v___y_6579_, 0);
                    v_isSharedCheck_6587_ = (!crate::leanh::lean_is_exclusive(v___y_6579_)) as u8;
                    if v_isSharedCheck_6587_ == 0 {
                        v___x_6582_ = v___y_6579_;
                        v_isShared_6583_ = v_isSharedCheck_6587_;
                        state = 76;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6580_);
                        crate::leanh::lean_dec(v___y_6579_);
                        v___x_6582_ = crate::leanh::lean_box(0);
                        v_isShared_6583_ = v_isSharedCheck_6587_;
                        state = 76;
                        continue;
                    }
                }
            }
            76 => {
                if v_isShared_6583_ == 0 {
                    v___x_6585_ = v___x_6582_;
                    state = 77;
                    continue;
                } else {
                    v_reuseFailAlloc_6586_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6586_, 0, v_a_6580_);
                    v___x_6585_ = v_reuseFailAlloc_6586_;
                    state = 77;
                    continue;
                }
            }
            77 => {
                return v___x_6585_;
            }
            78 => {
                v___x_6591_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6589_);
                if crate::leanh::lean_obj_tag(v___x_6591_) == 0 {
                    v_isSharedCheck_6599_ = (!crate::leanh::lean_is_exclusive(v___x_6591_)) as u8;
                    if v_isSharedCheck_6599_ == 0 {
                        v_unused_6600_ = crate::leanh::lean_ctor_get(v___x_6591_, 0);
                        crate::leanh::lean_dec(v_unused_6600_);
                        v___x_6593_ = v___x_6591_;
                        v_isShared_6594_ = v_isSharedCheck_6599_;
                        state = 79;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6591_);
                        v___x_6593_ = crate::leanh::lean_box(0);
                        v_isShared_6594_ = v_isSharedCheck_6599_;
                        state = 79;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6590_);
                    v_a_6601_ = crate::leanh::lean_ctor_get(v___x_6591_, 0);
                    v_isSharedCheck_6608_ = (!crate::leanh::lean_is_exclusive(v___x_6591_)) as u8;
                    if v_isSharedCheck_6608_ == 0 {
                        v___x_6603_ = v___x_6591_;
                        v_isShared_6604_ = v_isSharedCheck_6608_;
                        state = 81;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6601_);
                        crate::leanh::lean_dec(v___x_6591_);
                        v___x_6603_ = crate::leanh::lean_box(0);
                        v_isShared_6604_ = v_isSharedCheck_6608_;
                        state = 81;
                        continue;
                    }
                }
            }
            79 => {
                v___x_6595_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6595_, 0, v___y_6590_);
                if v_isShared_6594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6593_, 0, v___x_6595_);
                    v___x_6597_ = v___x_6593_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6595_);
                    v___x_6597_ = v_reuseFailAlloc_6598_;
                    state = 80;
                    continue;
                }
            }
            80 => {
                return v___x_6597_;
            }
            81 => {
                if v_isShared_6604_ == 0 {
                    v___x_6606_ = v___x_6603_;
                    state = 82;
                    continue;
                } else {
                    v_reuseFailAlloc_6607_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6607_, 0, v_a_6601_);
                    v___x_6606_ = v_reuseFailAlloc_6607_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_6606_;
            }
            83 => {
                if crate::leanh::lean_obj_tag(v___y_6612_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_6612_, 1);
                    v___y_6589_ = v___y_6610_;
                    v___y_6590_ = v___y_6611_;
                    state = 78;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6611_);
                    v_a_6613_ = crate::leanh::lean_ctor_get(v___y_6612_, 0);
                    v_isSharedCheck_6620_ = (!crate::leanh::lean_is_exclusive(v___y_6612_)) as u8;
                    if v_isSharedCheck_6620_ == 0 {
                        v___x_6615_ = v___y_6612_;
                        v_isShared_6616_ = v_isSharedCheck_6620_;
                        state = 84;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6613_);
                        crate::leanh::lean_dec(v___y_6612_);
                        v___x_6615_ = crate::leanh::lean_box(0);
                        v_isShared_6616_ = v_isSharedCheck_6620_;
                        state = 84;
                        continue;
                    }
                }
            }
            84 => {
                if v_isShared_6616_ == 0 {
                    v___x_6618_ = v___x_6615_;
                    state = 85;
                    continue;
                } else {
                    v_reuseFailAlloc_6619_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6619_, 0, v_a_6613_);
                    v___x_6618_ = v_reuseFailAlloc_6619_;
                    state = 85;
                    continue;
                }
            }
            85 => {
                return v___x_6618_;
            }
            86 => {
                v___x_6631_ = lean_nat_dec_lt(v___y_6628_, v___y_6622_);
                crate::leanh::lean_dec(v___y_6628_);
                if v___x_6631_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6630_);
                    crate::leanh::lean_dec_ref(v___y_6624_);
                    crate::leanh::lean_dec(v___y_6622_);
                    v___y_6589_ = v___y_6623_;
                    v___y_6590_ = v___y_6626_;
                    state = 78;
                    continue;
                } else {
                    v___x_6632_ = crate::leanh::lean_box(0);
                    v___x_6633_ = lean_nat_dec_le(v___y_6622_, v___y_6622_);
                    if v___x_6633_ == 0 {
                        if v___x_6631_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_6630_);
                            crate::leanh::lean_dec_ref(v___y_6624_);
                            crate::leanh::lean_dec(v___y_6622_);
                            v___y_6589_ = v___y_6623_;
                            v___y_6590_ = v___y_6626_;
                            state = 78;
                            continue;
                        } else {
                            v___x_6634_ = 0usize;
                            v___x_6635_ = lean_usize_of_nat(v___y_6622_);
                            crate::leanh::lean_dec(v___y_6622_);
                            v___x_6636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_6624_, v___x_6634_, v___x_6635_, v___x_6632_, v___y_6627_, v___y_6625_, v___y_6630_, v___y_6629_);
                            crate::leanh::lean_dec_ref(v___y_6630_);
                            crate::leanh::lean_dec_ref(v___y_6624_);
                            v___y_6610_ = v___y_6623_;
                            v___y_6611_ = v___y_6626_;
                            v___y_6612_ = v___x_6636_;
                            state = 83;
                            continue;
                        }
                    } else {
                        v___x_6637_ = 0usize;
                        v___x_6638_ = lean_usize_of_nat(v___y_6622_);
                        crate::leanh::lean_dec(v___y_6622_);
                        v___x_6639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_6624_, v___x_6637_, v___x_6638_, v___x_6632_, v___y_6627_, v___y_6625_, v___y_6630_, v___y_6629_);
                        crate::leanh::lean_dec_ref(v___y_6630_);
                        crate::leanh::lean_dec_ref(v___y_6624_);
                        v___y_6610_ = v___y_6623_;
                        v___y_6611_ = v___y_6626_;
                        v___y_6612_ = v___x_6639_;
                        state = 83;
                        continue;
                    }
                }
            }
            87 => {
                v___x_6645_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6645_, 0, v___y_6643_);
                crate::leanh::lean_ctor_set(v___x_6645_, 1, v___y_6644_);
                crate::leanh::lean_ctor_set(v___x_6645_, 2, v___y_6641_);
                crate::leanh::lean_ctor_set(v___x_6645_, 3, v___y_6642_);
                v___x_6646_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6646_, 0, v___x_6645_);
                v___x_6647_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6647_, 0, v___x_6646_);
                return v___x_6647_;
            }
            88 => {
                if v___y_6654_ == 0 {
                    crate::leanh::lean_dec(v___y_6649_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v___y_6641_ = v___y_6650_;
                    v___y_6642_ = v___y_6651_;
                    v___y_6643_ = v___y_6652_;
                    v___y_6644_ = v___y_6653_;
                    state = 87;
                    continue;
                } else {
                    v___x_6655_ = l_Lean_instBEqFVarId_beq(v___y_6649_, v___y_6650_);
                    crate::leanh::lean_dec(v___y_6649_);
                    if v___x_6655_ == 0 {
                        crate::leanh::lean_dec_ref(v_code_6077_);
                        v___y_6641_ = v___y_6650_;
                        v___y_6642_ = v___y_6651_;
                        v___y_6643_ = v___y_6652_;
                        v___y_6644_ = v___y_6653_;
                        state = 87;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___y_6653_);
                        crate::leanh::lean_dec(v___y_6652_);
                        crate::leanh::lean_dec_ref(v___y_6651_);
                        crate::leanh::lean_dec(v___y_6650_);
                        v___x_6656_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6656_, 0, v_code_6077_);
                        return v___x_6656_;
                    }
                }
            }
            89 => {
                v___x_6671_ = lean_array_get_size(v___y_6660_);
                v___x_6672_ = lean_nat_dec_lt(v___y_6665_, v___x_6671_);
                if v___x_6672_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6664_);
                    crate::leanh::lean_dec(v___y_6662_);
                    crate::leanh::lean_dec_ref(v___y_6661_);
                    crate::leanh::lean_dec(v___y_6659_);
                    crate::leanh::lean_dec(v___y_6658_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v___y_6622_ = v___x_6671_;
                    v___y_6623_ = v___y_6666_;
                    v___y_6624_ = v___y_6660_;
                    v___y_6625_ = v___y_6668_;
                    v___y_6626_ = v___y_6663_;
                    v___y_6627_ = v___y_6667_;
                    v___y_6628_ = v___y_6665_;
                    v___y_6629_ = v___y_6670_;
                    v___y_6630_ = v___y_6669_;
                    state = 86;
                    continue;
                } else {
                    if v___x_6672_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_6664_);
                        crate::leanh::lean_dec(v___y_6662_);
                        crate::leanh::lean_dec_ref(v___y_6661_);
                        crate::leanh::lean_dec(v___y_6659_);
                        crate::leanh::lean_dec(v___y_6658_);
                        crate::leanh::lean_dec_ref(v_code_6077_);
                        v___y_6622_ = v___x_6671_;
                        v___y_6623_ = v___y_6666_;
                        v___y_6624_ = v___y_6660_;
                        v___y_6625_ = v___y_6668_;
                        v___y_6626_ = v___y_6663_;
                        v___y_6627_ = v___y_6667_;
                        v___y_6628_ = v___y_6665_;
                        v___y_6629_ = v___y_6670_;
                        v___y_6630_ = v___y_6669_;
                        state = 86;
                        continue;
                    } else {
                        v___x_6673_ = 0usize;
                        v___x_6674_ = lean_usize_of_nat(v___x_6671_);
                        v___x_6675_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v___y_6660_, v___x_6673_, v___x_6674_);
                        if v___x_6675_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_6664_);
                            crate::leanh::lean_dec(v___y_6662_);
                            crate::leanh::lean_dec_ref(v___y_6661_);
                            crate::leanh::lean_dec(v___y_6659_);
                            crate::leanh::lean_dec(v___y_6658_);
                            crate::leanh::lean_dec_ref(v_code_6077_);
                            v___y_6622_ = v___x_6671_;
                            v___y_6623_ = v___y_6666_;
                            v___y_6624_ = v___y_6660_;
                            v___y_6625_ = v___y_6668_;
                            v___y_6626_ = v___y_6663_;
                            v___y_6627_ = v___y_6667_;
                            v___y_6628_ = v___y_6665_;
                            v___y_6629_ = v___y_6670_;
                            v___y_6630_ = v___y_6669_;
                            state = 86;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___y_6669_);
                            crate::leanh::lean_dec(v___y_6665_);
                            crate::leanh::lean_inc(v___y_6659_);
                            v___x_6676_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(
                                v___y_6659_,
                                v___y_6666_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6676_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6676_, 1);
                                v___x_6677_ = lean_ptr_addr(v___y_6664_);
                                crate::leanh::lean_dec_ref(v___y_6664_);
                                v___x_6678_ = lean_ptr_addr(v___y_6660_);
                                v___x_6679_ = lean_usize_dec_eq(v___x_6677_, v___x_6678_);
                                if v___x_6679_ == 0 {
                                    crate::leanh::lean_dec_ref(v___y_6661_);
                                    v___y_6649_ = v___y_6658_;
                                    v___y_6650_ = v___y_6659_;
                                    v___y_6651_ = v___y_6660_;
                                    v___y_6652_ = v___y_6662_;
                                    v___y_6653_ = v___y_6663_;
                                    v___y_6654_ = v___x_6679_;
                                    state = 88;
                                    continue;
                                } else {
                                    v___x_6680_ = lean_ptr_addr(v___y_6661_);
                                    crate::leanh::lean_dec_ref(v___y_6661_);
                                    v___x_6681_ = lean_ptr_addr(v___y_6663_);
                                    v___x_6682_ = lean_usize_dec_eq(v___x_6680_, v___x_6681_);
                                    v___y_6649_ = v___y_6658_;
                                    v___y_6650_ = v___y_6659_;
                                    v___y_6651_ = v___y_6660_;
                                    v___y_6652_ = v___y_6662_;
                                    v___y_6653_ = v___y_6663_;
                                    v___y_6654_ = v___x_6682_;
                                    state = 88;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v___y_6664_);
                                crate::leanh::lean_dec_ref(v___y_6663_);
                                crate::leanh::lean_dec(v___y_6662_);
                                crate::leanh::lean_dec_ref(v___y_6661_);
                                crate::leanh::lean_dec_ref(v___y_6660_);
                                crate::leanh::lean_dec(v___y_6659_);
                                crate::leanh::lean_dec(v___y_6658_);
                                crate::leanh::lean_dec_ref(v_code_6077_);
                                v_a_6683_ = crate::leanh::lean_ctor_get(v___x_6676_, 0);
                                v_isSharedCheck_6690_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6676_)) as u8;
                                if v_isSharedCheck_6690_ == 0 {
                                    v___x_6685_ = v___x_6676_;
                                    v_isShared_6686_ = v_isSharedCheck_6690_;
                                    state = 90;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6683_);
                                    crate::leanh::lean_dec(v___x_6676_);
                                    v___x_6685_ = crate::leanh::lean_box(0);
                                    v_isShared_6686_ = v_isSharedCheck_6690_;
                                    state = 90;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            90 => {
                if v_isShared_6686_ == 0 {
                    v___x_6688_ = v___x_6685_;
                    state = 91;
                    continue;
                } else {
                    v_reuseFailAlloc_6689_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6689_, 0, v_a_6683_);
                    v___x_6688_ = v_reuseFailAlloc_6689_;
                    state = 91;
                    continue;
                }
            }
            91 => {
                return v___x_6688_;
            }
            92 => {
                v___x_6694_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6692_);
                if crate::leanh::lean_obj_tag(v___x_6694_) == 0 {
                    v_isSharedCheck_6701_ = (!crate::leanh::lean_is_exclusive(v___x_6694_)) as u8;
                    if v_isSharedCheck_6701_ == 0 {
                        v_unused_6702_ = crate::leanh::lean_ctor_get(v___x_6694_, 0);
                        crate::leanh::lean_dec(v_unused_6702_);
                        v___x_6696_ = v___x_6694_;
                        v_isShared_6697_ = v_isSharedCheck_6701_;
                        state = 93;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_6694_);
                        v___x_6696_ = crate::leanh::lean_box(0);
                        v_isShared_6697_ = v_isSharedCheck_6701_;
                        state = 93;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_6693_);
                    v_a_6703_ = crate::leanh::lean_ctor_get(v___x_6694_, 0);
                    v_isSharedCheck_6710_ = (!crate::leanh::lean_is_exclusive(v___x_6694_)) as u8;
                    if v_isSharedCheck_6710_ == 0 {
                        v___x_6705_ = v___x_6694_;
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 95;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6703_);
                        crate::leanh::lean_dec(v___x_6694_);
                        v___x_6705_ = crate::leanh::lean_box(0);
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 95;
                        continue;
                    }
                }
            }
            93 => {
                if v_isShared_6697_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6696_, 0, v___y_6693_);
                    v___x_6699_ = v___x_6696_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_6700_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6700_, 0, v___y_6693_);
                    v___x_6699_ = v_reuseFailAlloc_6700_;
                    state = 94;
                    continue;
                }
            }
            94 => {
                return v___x_6699_;
            }
            95 => {
                if v_isShared_6706_ == 0 {
                    v___x_6708_ = v___x_6705_;
                    state = 96;
                    continue;
                } else {
                    v_reuseFailAlloc_6709_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6709_, 0, v_a_6703_);
                    v___x_6708_ = v_reuseFailAlloc_6709_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_6708_;
            }
            97 => {
                if crate::leanh::lean_obj_tag(v___y_6714_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_6714_, 1);
                    v___y_6692_ = v___y_6712_;
                    v___y_6693_ = v___y_6713_;
                    state = 92;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_6713_);
                    v_a_6715_ = crate::leanh::lean_ctor_get(v___y_6714_, 0);
                    v_isSharedCheck_6722_ = (!crate::leanh::lean_is_exclusive(v___y_6714_)) as u8;
                    if v_isSharedCheck_6722_ == 0 {
                        v___x_6717_ = v___y_6714_;
                        v_isShared_6718_ = v_isSharedCheck_6722_;
                        state = 98;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6715_);
                        crate::leanh::lean_dec(v___y_6714_);
                        v___x_6717_ = crate::leanh::lean_box(0);
                        v_isShared_6718_ = v_isSharedCheck_6722_;
                        state = 98;
                        continue;
                    }
                }
            }
            98 => {
                if v_isShared_6718_ == 0 {
                    v___x_6720_ = v___x_6717_;
                    state = 99;
                    continue;
                } else {
                    v_reuseFailAlloc_6721_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6721_, 0, v_a_6715_);
                    v___x_6720_ = v_reuseFailAlloc_6721_;
                    state = 99;
                    continue;
                }
            }
            99 => {
                return v___x_6720_;
            }
            100 => {
                v___x_6730_ = lean_nat_dec_lt(v___y_6729_, v___y_6725_);
                crate::leanh::lean_dec(v___y_6729_);
                if v___x_6730_ == 0 {
                    crate::leanh::lean_dec_ref(v___y_6726_);
                    crate::leanh::lean_dec(v___y_6725_);
                    v___y_6692_ = v___y_6724_;
                    v___y_6693_ = v___y_6727_;
                    state = 92;
                    continue;
                } else {
                    v___x_6731_ = crate::leanh::lean_box(0);
                    v___x_6732_ = lean_nat_dec_le(v___y_6725_, v___y_6725_);
                    if v___x_6732_ == 0 {
                        if v___x_6730_ == 0 {
                            crate::leanh::lean_dec_ref(v___y_6726_);
                            crate::leanh::lean_dec(v___y_6725_);
                            v___y_6692_ = v___y_6724_;
                            v___y_6693_ = v___y_6727_;
                            state = 92;
                            continue;
                        } else {
                            v___x_6733_ = 0usize;
                            v___x_6734_ = lean_usize_of_nat(v___y_6725_);
                            crate::leanh::lean_dec(v___y_6725_);
                            v___x_6735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_6726_, v___x_6733_, v___x_6734_, v___x_6731_, v___y_6728_);
                            crate::leanh::lean_dec_ref(v___y_6726_);
                            v___y_6712_ = v___y_6724_;
                            v___y_6713_ = v___y_6727_;
                            v___y_6714_ = v___x_6735_;
                            state = 97;
                            continue;
                        }
                    } else {
                        v___x_6736_ = 0usize;
                        v___x_6737_ = lean_usize_of_nat(v___y_6725_);
                        crate::leanh::lean_dec(v___y_6725_);
                        v___x_6738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_6726_, v___x_6736_, v___x_6737_, v___x_6731_, v___y_6728_);
                        crate::leanh::lean_dec_ref(v___y_6726_);
                        v___y_6712_ = v___y_6724_;
                        v___y_6713_ = v___y_6727_;
                        v___y_6714_ = v___x_6738_;
                        state = 97;
                        continue;
                    }
                }
            }
            101 => match crate::leanh::lean_obj_tag(v_code_6077_) {
                0 => {
                    v_decl_6747_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    v_k_6748_ = crate::leanh::lean_ctor_get(v_code_6077_, 1);
                    v___x_6749_ = 0;
                    v___x_6750_ = 0;
                    crate::leanh::lean_inc_ref(v_decl_6747_);
                    v___x_6751_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_6749_, v___x_6750_, v_decl_6747_, v___y_6741_, v___y_6744_);
                    if crate::leanh::lean_obj_tag(v___x_6751_) == 0 {
                        v_a_6752_ = crate::leanh::lean_ctor_get(v___x_6751_, 0);
                        crate::leanh::lean_inc(v_a_6752_);
                        crate::leanh::lean_dec_ref_known(v___x_6751_, 1);
                        v___x_6753_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(
                            v___x_6749_,
                            v_decl_6747_,
                            v_a_6752_,
                        );
                        if v___x_6753_ == 0 {
                            v___x_6754_ =
                                l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6741_);
                            if crate::leanh::lean_obj_tag(v___x_6754_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_6754_, 1);
                                crate::leanh::lean_inc_ref(v_k_6748_);
                                crate::leanh::lean_inc_ref(v_decl_6747_);
                                v___y_6511_ = v___x_6749_;
                                v___y_6512_ = v_decl_6747_;
                                v___y_6513_ = v_k_6748_;
                                v___y_6514_ = v_a_6752_;
                                v___y_6515_ = v___y_6740_;
                                v___y_6516_ = v___y_6741_;
                                v___y_6517_ = v___y_6742_;
                                v___y_6518_ = v___y_6743_;
                                v___y_6519_ = v___y_6744_;
                                v___y_6520_ = v___y_6745_;
                                v___y_6521_ = v___y_6746_;
                                state = 66;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v_a_6752_);
                                crate::leanh::lean_dec_ref_known(v_code_6077_, 2);
                                crate::leanh::lean_dec_ref(v___y_6745_);
                                v_a_6755_ = crate::leanh::lean_ctor_get(v___x_6754_, 0);
                                v_isSharedCheck_6762_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6754_)) as u8;
                                if v_isSharedCheck_6762_ == 0 {
                                    v___x_6757_ = v___x_6754_;
                                    v_isShared_6758_ = v_isSharedCheck_6762_;
                                    state = 102;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6755_);
                                    crate::leanh::lean_dec(v___x_6754_);
                                    v___x_6757_ = crate::leanh::lean_box(0);
                                    v_isShared_6758_ = v_isSharedCheck_6762_;
                                    state = 102;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_inc_ref(v_k_6748_);
                            crate::leanh::lean_inc_ref(v_decl_6747_);
                            v___y_6511_ = v___x_6749_;
                            v___y_6512_ = v_decl_6747_;
                            v___y_6513_ = v_k_6748_;
                            v___y_6514_ = v_a_6752_;
                            v___y_6515_ = v___y_6740_;
                            v___y_6516_ = v___y_6741_;
                            v___y_6517_ = v___y_6742_;
                            v___y_6518_ = v___y_6743_;
                            v___y_6519_ = v___y_6744_;
                            v___y_6520_ = v___y_6745_;
                            v___y_6521_ = v___y_6746_;
                            state = 66;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_6077_, 2);
                        crate::leanh::lean_dec_ref(v___y_6745_);
                        v_a_6763_ = crate::leanh::lean_ctor_get(v___x_6751_, 0);
                        v_isSharedCheck_6770_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6751_)) as u8;
                        if v_isSharedCheck_6770_ == 0 {
                            v___x_6765_ = v___x_6751_;
                            v_isShared_6766_ = v_isSharedCheck_6770_;
                            state = 104;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6763_);
                            crate::leanh::lean_dec(v___x_6751_);
                            v___x_6765_ = crate::leanh::lean_box(0);
                            v_isShared_6766_ = v_isSharedCheck_6770_;
                            state = 104;
                            continue;
                        }
                    }
                }
                3 => {
                    v_fvarId_6771_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    v_args_6772_ = crate::leanh::lean_ctor_get(v_code_6077_, 1);
                    v___x_6773_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6774_ = crate::leanh::lean_ctor_get(v___x_6773_, 0);
                    crate::leanh::lean_inc_ref(v_subst_6774_);
                    crate::leanh::lean_dec(v___x_6773_);
                    v___x_6775_ = 0;
                    v___x_6776_ = 0;
                    crate::leanh::lean_inc(v_fvarId_6771_);
                    v___x_6777_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_subst_6774_,
                        v_fvarId_6771_,
                        v___x_6776_,
                    );
                    crate::leanh::lean_dec_ref(v_subst_6774_);
                    if crate::leanh::lean_obj_tag(v___x_6777_) == 0 {
                        v_fvarId_6778_ = crate::leanh::lean_ctor_get(v___x_6777_, 0);
                        crate::leanh::lean_inc(v_fvarId_6778_);
                        crate::leanh::lean_dec_ref_known(v___x_6777_, 1);
                        crate::leanh::lean_inc_ref(v_args_6772_);
                        v___x_6779_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_6775_, v___x_6776_, v_args_6772_, v___y_6741_);
                        if crate::leanh::lean_obj_tag(v___x_6779_) == 0 {
                            v_a_6780_ = crate::leanh::lean_ctor_get(v___x_6779_, 0);
                            crate::leanh::lean_inc_n(v_a_6780_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_6779_, 1);
                            v___x_6781_ = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(
                                v_fvarId_6778_,
                                v_a_6780_,
                                v___y_6740_,
                                v___y_6741_,
                                v___y_6742_,
                                v___y_6743_,
                                v___y_6744_,
                                v___y_6745_,
                                v___y_6746_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6781_) == 0 {
                                v_a_6782_ = crate::leanh::lean_ctor_get(v___x_6781_, 0);
                                crate::leanh::lean_inc(v_a_6782_);
                                crate::leanh::lean_dec_ref_known(v___x_6781_, 1);
                                if crate::leanh::lean_obj_tag(v_a_6782_) == 1 {
                                    crate::leanh::lean_dec(v_a_6780_);
                                    crate::leanh::lean_dec(v_fvarId_6778_);
                                    crate::leanh::lean_dec_ref_known(v_code_6077_, 2);
                                    v_val_6783_ = crate::leanh::lean_ctor_get(v_a_6782_, 0);
                                    crate::leanh::lean_inc(v_val_6783_);
                                    crate::leanh::lean_dec_ref_known(v_a_6782_, 1);
                                    v_code_6077_ = v_val_6783_;
                                    v_a_6078_ = v___y_6740_;
                                    v_a_6079_ = v___y_6741_;
                                    v_a_6080_ = v___y_6742_;
                                    v_a_6081_ = v___y_6743_;
                                    v_a_6082_ = v___y_6744_;
                                    v_a_6083_ = v___y_6745_;
                                    v_a_6084_ = v___y_6746_;
                                    state = 0;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v_a_6782_);
                                    crate::leanh::lean_dec_ref(v___y_6745_);
                                    crate::leanh::lean_inc(v_fvarId_6778_);
                                    v___x_6785_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(
                                        v_fvarId_6778_,
                                        v___y_6741_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_6785_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_6785_, 1);
                                        v___x_6786_ = crate::leanh::lean_unsigned_to_nat(0);
                                        v___x_6787_ = lean_array_get_size(v_a_6780_);
                                        v___x_6788_ = lean_nat_dec_lt(v___x_6786_, v___x_6787_);
                                        if v___x_6788_ == 0 {
                                            crate::leanh::lean_inc_ref(v_args_6772_);
                                            crate::leanh::lean_inc(v_fvarId_6771_);
                                            v___y_6566_ = v_fvarId_6771_;
                                            v___y_6567_ = v_args_6772_;
                                            v___y_6568_ = v_fvarId_6778_;
                                            v___y_6569_ = v_a_6780_;
                                            state = 74;
                                            continue;
                                        } else {
                                            v___x_6789_ = crate::leanh::lean_box(0);
                                            v___x_6790_ = lean_nat_dec_le(v___x_6787_, v___x_6787_);
                                            if v___x_6790_ == 0 {
                                                if v___x_6788_ == 0 {
                                                    crate::leanh::lean_inc_ref(v_args_6772_);
                                                    crate::leanh::lean_inc(v_fvarId_6771_);
                                                    v___y_6566_ = v_fvarId_6771_;
                                                    v___y_6567_ = v_args_6772_;
                                                    v___y_6568_ = v_fvarId_6778_;
                                                    v___y_6569_ = v_a_6780_;
                                                    state = 74;
                                                    continue;
                                                } else {
                                                    v___x_6791_ = 0usize;
                                                    v___x_6792_ = lean_usize_of_nat(v___x_6787_);
                                                    v___x_6793_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_6780_, v___x_6791_, v___x_6792_, v___x_6789_, v___y_6741_);
                                                    crate::leanh::lean_inc_ref(v_args_6772_);
                                                    crate::leanh::lean_inc(v_fvarId_6771_);
                                                    v___y_6575_ = v_fvarId_6771_;
                                                    v___y_6576_ = v_args_6772_;
                                                    v___y_6577_ = v_fvarId_6778_;
                                                    v___y_6578_ = v_a_6780_;
                                                    v___y_6579_ = v___x_6793_;
                                                    state = 75;
                                                    continue;
                                                }
                                            } else {
                                                v___x_6794_ = 0usize;
                                                v___x_6795_ = lean_usize_of_nat(v___x_6787_);
                                                v___x_6796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_a_6780_, v___x_6794_, v___x_6795_, v___x_6789_, v___y_6741_);
                                                crate::leanh::lean_inc_ref(v_args_6772_);
                                                crate::leanh::lean_inc(v_fvarId_6771_);
                                                v___y_6575_ = v_fvarId_6771_;
                                                v___y_6576_ = v_args_6772_;
                                                v___y_6577_ = v_fvarId_6778_;
                                                v___y_6578_ = v_a_6780_;
                                                v___y_6579_ = v___x_6796_;
                                                state = 75;
                                                continue;
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_6780_);
                                        crate::leanh::lean_dec(v_fvarId_6778_);
                                        crate::leanh::lean_dec_ref_known(v_code_6077_, 2);
                                        v_a_6797_ = crate::leanh::lean_ctor_get(v___x_6785_, 0);
                                        v_isSharedCheck_6804_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_6785_)) as u8;
                                        if v_isSharedCheck_6804_ == 0 {
                                            v___x_6799_ = v___x_6785_;
                                            v_isShared_6800_ = v_isSharedCheck_6804_;
                                            state = 106;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_6797_);
                                            crate::leanh::lean_dec(v___x_6785_);
                                            v___x_6799_ = crate::leanh::lean_box(0);
                                            v_isShared_6800_ = v_isSharedCheck_6804_;
                                            state = 106;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_6780_);
                                crate::leanh::lean_dec(v_fvarId_6778_);
                                crate::leanh::lean_dec_ref_known(v_code_6077_, 2);
                                crate::leanh::lean_dec_ref(v___y_6745_);
                                v_a_6805_ = crate::leanh::lean_ctor_get(v___x_6781_, 0);
                                v_isSharedCheck_6812_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6781_)) as u8;
                                if v_isSharedCheck_6812_ == 0 {
                                    v___x_6807_ = v___x_6781_;
                                    v_isShared_6808_ = v_isSharedCheck_6812_;
                                    state = 108;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6805_);
                                    crate::leanh::lean_dec(v___x_6781_);
                                    v___x_6807_ = crate::leanh::lean_box(0);
                                    v_isShared_6808_ = v_isSharedCheck_6812_;
                                    state = 108;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_6778_);
                            crate::leanh::lean_dec_ref_known(v_code_6077_, 2);
                            crate::leanh::lean_dec_ref(v___y_6745_);
                            v_a_6813_ = crate::leanh::lean_ctor_get(v___x_6779_, 0);
                            v_isSharedCheck_6820_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6779_)) as u8;
                            if v_isSharedCheck_6820_ == 0 {
                                v___x_6815_ = v___x_6779_;
                                v_isShared_6816_ = v_isSharedCheck_6820_;
                                state = 110;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6813_);
                                crate::leanh::lean_dec(v___x_6779_);
                                v___x_6815_ = crate::leanh::lean_box(0);
                                v_isShared_6816_ = v_isSharedCheck_6820_;
                                state = 110;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_6077_, 2);
                        v___x_6821_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v___x_6775_,
                            v___y_6743_,
                            v___y_6744_,
                            v___y_6745_,
                            v___y_6746_,
                        );
                        crate::leanh::lean_dec_ref(v___y_6745_);
                        return v___x_6821_;
                    }
                }
                4 => {
                    v_cases_6822_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    crate::leanh::lean_inc_ref(v_cases_6822_);
                    v___x_6823_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(
                        v_cases_6822_,
                        v___y_6740_,
                        v___y_6741_,
                        v___y_6742_,
                        v___y_6743_,
                        v___y_6744_,
                        v___y_6745_,
                        v___y_6746_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_6823_) == 0 {
                        v_a_6824_ = crate::leanh::lean_ctor_get(v___x_6823_, 0);
                        v_isSharedCheck_6896_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6823_)) as u8;
                        if v_isSharedCheck_6896_ == 0 {
                            v___x_6826_ = v___x_6823_;
                            v_isShared_6827_ = v_isSharedCheck_6896_;
                            state = 112;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6824_);
                            crate::leanh::lean_dec(v___x_6823_);
                            v___x_6826_ = crate::leanh::lean_box(0);
                            v_isShared_6827_ = v_isSharedCheck_6896_;
                            state = 112;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                        crate::leanh::lean_dec_ref(v___y_6745_);
                        v_a_6897_ = crate::leanh::lean_ctor_get(v___x_6823_, 0);
                        v_isSharedCheck_6904_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6823_)) as u8;
                        if v_isSharedCheck_6904_ == 0 {
                            v___x_6899_ = v___x_6823_;
                            v_isShared_6900_ = v_isSharedCheck_6904_;
                            state = 122;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6897_);
                            crate::leanh::lean_dec(v___x_6823_);
                            v___x_6899_ = crate::leanh::lean_box(0);
                            v_isShared_6900_ = v_isSharedCheck_6904_;
                            state = 122;
                            continue;
                        }
                    }
                }
                5 => {
                    v_fvarId_6905_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    v___x_6906_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6907_ = crate::leanh::lean_ctor_get(v___x_6906_, 0);
                    crate::leanh::lean_inc_ref(v_subst_6907_);
                    crate::leanh::lean_dec(v___x_6906_);
                    v___x_6908_ = 0;
                    crate::leanh::lean_inc(v_fvarId_6905_);
                    v___x_6909_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_subst_6907_,
                        v_fvarId_6905_,
                        v___x_6908_,
                    );
                    crate::leanh::lean_dec_ref(v_subst_6907_);
                    if crate::leanh::lean_obj_tag(v___x_6909_) == 0 {
                        crate::leanh::lean_dec_ref(v___y_6745_);
                        v_fvarId_6910_ = crate::leanh::lean_ctor_get(v___x_6909_, 0);
                        crate::leanh::lean_inc_n(v_fvarId_6910_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_6909_, 1);
                        v___x_6911_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(
                            v_fvarId_6910_,
                            v___y_6741_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_6911_) == 0 {
                            v_isSharedCheck_6930_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6911_)) as u8;
                            if v_isSharedCheck_6930_ == 0 {
                                v_unused_6931_ = crate::leanh::lean_ctor_get(v___x_6911_, 0);
                                crate::leanh::lean_dec(v_unused_6931_);
                                v___x_6913_ = v___x_6911_;
                                v_isShared_6914_ = v_isSharedCheck_6930_;
                                state = 124;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6911_);
                                v___x_6913_ = crate::leanh::lean_box(0);
                                v_isShared_6914_ = v_isSharedCheck_6930_;
                                state = 124;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_fvarId_6910_);
                            crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                            v_a_6932_ = crate::leanh::lean_ctor_get(v___x_6911_, 0);
                            v_isSharedCheck_6939_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6911_)) as u8;
                            if v_isSharedCheck_6939_ == 0 {
                                v___x_6934_ = v___x_6911_;
                                v_isShared_6935_ = v_isSharedCheck_6939_;
                                state = 129;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6932_);
                                crate::leanh::lean_dec(v___x_6911_);
                                v___x_6934_ = crate::leanh::lean_box(0);
                                v_isShared_6935_ = v_isSharedCheck_6939_;
                                state = 129;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                        v___x_6940_ = 0;
                        v___x_6941_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v___x_6940_,
                            v___y_6743_,
                            v___y_6744_,
                            v___y_6745_,
                            v___y_6746_,
                        );
                        crate::leanh::lean_dec_ref(v___y_6745_);
                        return v___x_6941_;
                    }
                }
                6 => {
                    crate::leanh::lean_dec_ref(v___y_6745_);
                    v_type_6942_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    v___x_6943_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6944_ = crate::leanh::lean_ctor_get(v___x_6943_, 0);
                    crate::leanh::lean_inc_ref(v_subst_6944_);
                    crate::leanh::lean_dec(v___x_6943_);
                    v___x_6945_ = 0;
                    v___x_6946_ = 0;
                    crate::leanh::lean_inc_ref(v_type_6942_);
                    v___x_6947_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_6945_, v_subst_6944_, v___x_6946_, v_type_6942_);
                    crate::leanh::lean_dec_ref(v_subst_6944_);
                    v___x_6948_ = lean_ptr_addr(v_type_6942_);
                    v___x_6949_ = lean_ptr_addr(v___x_6947_);
                    v___x_6950_ = lean_usize_dec_eq(v___x_6948_, v___x_6949_);
                    if v___x_6950_ == 0 {
                        v_isSharedCheck_6958_ =
                            (!crate::leanh::lean_is_exclusive(v_code_6077_)) as u8;
                        if v_isSharedCheck_6958_ == 0 {
                            v_unused_6959_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                            crate::leanh::lean_dec(v_unused_6959_);
                            v___x_6952_ = v_code_6077_;
                            v_isShared_6953_ = v_isSharedCheck_6958_;
                            state = 131;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_code_6077_);
                            v___x_6952_ = crate::leanh::lean_box(0);
                            v_isShared_6953_ = v_isSharedCheck_6958_;
                            state = 131;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v___x_6947_);
                        v___x_6960_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_6960_, 0, v_code_6077_);
                        return v___x_6960_;
                    }
                }
                _ => {
                    v_decl_6961_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                    v_k_6962_ = crate::leanh::lean_ctor_get(v_code_6077_, 1);
                    crate::leanh::lean_inc_ref(v_k_6962_);
                    crate::leanh::lean_inc_ref(v_decl_6961_);
                    v_decl_6195_ = v_decl_6961_;
                    v_k_6196_ = v_k_6962_;
                    v___y_6197_ = v___y_6740_;
                    v___y_6198_ = v___y_6741_;
                    v___y_6199_ = v___y_6742_;
                    v___y_6200_ = v___y_6743_;
                    v___y_6201_ = v___y_6744_;
                    v___y_6202_ = v___y_6745_;
                    v___y_6203_ = v___y_6746_;
                    state = 16;
                    continue;
                }
            },
            102 => {
                if v_isShared_6758_ == 0 {
                    v___x_6760_ = v___x_6757_;
                    state = 103;
                    continue;
                } else {
                    v_reuseFailAlloc_6761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6761_, 0, v_a_6755_);
                    v___x_6760_ = v_reuseFailAlloc_6761_;
                    state = 103;
                    continue;
                }
            }
            103 => {
                return v___x_6760_;
            }
            104 => {
                if v_isShared_6766_ == 0 {
                    v___x_6768_ = v___x_6765_;
                    state = 105;
                    continue;
                } else {
                    v_reuseFailAlloc_6769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6769_, 0, v_a_6763_);
                    v___x_6768_ = v_reuseFailAlloc_6769_;
                    state = 105;
                    continue;
                }
            }
            105 => {
                return v___x_6768_;
            }
            106 => {
                if v_isShared_6800_ == 0 {
                    v___x_6802_ = v___x_6799_;
                    state = 107;
                    continue;
                } else {
                    v_reuseFailAlloc_6803_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6803_, 0, v_a_6797_);
                    v___x_6802_ = v_reuseFailAlloc_6803_;
                    state = 107;
                    continue;
                }
            }
            107 => {
                return v___x_6802_;
            }
            108 => {
                if v_isShared_6808_ == 0 {
                    v___x_6810_ = v___x_6807_;
                    state = 109;
                    continue;
                } else {
                    v_reuseFailAlloc_6811_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6811_, 0, v_a_6805_);
                    v___x_6810_ = v_reuseFailAlloc_6811_;
                    state = 109;
                    continue;
                }
            }
            109 => {
                return v___x_6810_;
            }
            110 => {
                if v_isShared_6816_ == 0 {
                    v___x_6818_ = v___x_6815_;
                    state = 111;
                    continue;
                } else {
                    v_reuseFailAlloc_6819_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6819_, 0, v_a_6813_);
                    v___x_6818_ = v_reuseFailAlloc_6819_;
                    state = 111;
                    continue;
                }
            }
            111 => {
                return v___x_6818_;
            }
            112 => {
                if crate::leanh::lean_obj_tag(v_a_6824_) == 1 {
                    crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                    crate::leanh::lean_dec_ref(v___y_6745_);
                    v_val_6828_ = crate::leanh::lean_ctor_get(v_a_6824_, 0);
                    crate::leanh::lean_inc(v_val_6828_);
                    crate::leanh::lean_dec_ref_known(v_a_6824_, 1);
                    if v_isShared_6827_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6826_, 0, v_val_6828_);
                        v___x_6830_ = v___x_6826_;
                        state = 113;
                        continue;
                    } else {
                        v_reuseFailAlloc_6831_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6831_, 0, v_val_6828_);
                        v___x_6830_ = v_reuseFailAlloc_6831_;
                        state = 113;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6826_);
                    crate::leanh::lean_dec(v_a_6824_);
                    v_typeName_6832_ = crate::leanh::lean_ctor_get(v_cases_6822_, 0);
                    v_resultType_6833_ = crate::leanh::lean_ctor_get(v_cases_6822_, 1);
                    v_discr_6834_ = crate::leanh::lean_ctor_get(v_cases_6822_, 2);
                    v_alts_6835_ = crate::leanh::lean_ctor_get(v_cases_6822_, 3);
                    v___x_6836_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6837_ = crate::leanh::lean_ctor_get(v___x_6836_, 0);
                    crate::leanh::lean_inc_ref(v_subst_6837_);
                    crate::leanh::lean_dec(v___x_6836_);
                    v___x_6838_ = 0;
                    v___x_6839_ = 0;
                    crate::leanh::lean_inc(v_discr_6834_);
                    v___x_6840_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_subst_6837_,
                        v_discr_6834_,
                        v___x_6839_,
                    );
                    crate::leanh::lean_dec_ref(v_subst_6837_);
                    if crate::leanh::lean_obj_tag(v___x_6840_) == 0 {
                        v_fvarId_6841_ = crate::leanh::lean_ctor_get(v___x_6840_, 0);
                        crate::leanh::lean_inc_n(v_fvarId_6841_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_6840_, 1);
                        v___x_6842_ = lean_st_ref_get(v___y_6741_);
                        v___x_6843_ = crate::leanh::lean_unsigned_to_nat(0);
                        crate::leanh::lean_inc_ref(v_alts_6835_);
                        v___x_6844_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_6841_, v___x_6843_, v_alts_6835_, v___y_6740_, v___y_6741_, v___y_6742_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
                        if crate::leanh::lean_obj_tag(v___x_6844_) == 0 {
                            v_a_6845_ = crate::leanh::lean_ctor_get(v___x_6844_, 0);
                            crate::leanh::lean_inc(v_a_6845_);
                            crate::leanh::lean_dec_ref_known(v___x_6844_, 1);
                            v___x_6846_ = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(
                                v_a_6845_,
                                v___y_6740_,
                                v___y_6741_,
                                v___y_6742_,
                                v___y_6743_,
                                v___y_6744_,
                                v___y_6745_,
                                v___y_6746_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_6846_) == 0 {
                                v_a_6847_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                                v_isSharedCheck_6878_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6846_)) as u8;
                                if v_isSharedCheck_6878_ == 0 {
                                    v___x_6849_ = v___x_6846_;
                                    v_isShared_6850_ = v_isSharedCheck_6878_;
                                    state = 114;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6847_);
                                    crate::leanh::lean_dec(v___x_6846_);
                                    v___x_6849_ = crate::leanh::lean_box(0);
                                    v_isShared_6850_ = v_isSharedCheck_6878_;
                                    state = 114;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_6842_);
                                crate::leanh::lean_dec(v_fvarId_6841_);
                                crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                                crate::leanh::lean_dec_ref(v___y_6745_);
                                v_a_6879_ = crate::leanh::lean_ctor_get(v___x_6846_, 0);
                                v_isSharedCheck_6886_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_6846_)) as u8;
                                if v_isSharedCheck_6886_ == 0 {
                                    v___x_6881_ = v___x_6846_;
                                    v_isShared_6882_ = v_isSharedCheck_6886_;
                                    state = 118;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_6879_);
                                    crate::leanh::lean_dec(v___x_6846_);
                                    v___x_6881_ = crate::leanh::lean_box(0);
                                    v_isShared_6882_ = v_isSharedCheck_6886_;
                                    state = 118;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_6842_);
                            crate::leanh::lean_dec(v_fvarId_6841_);
                            crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                            crate::leanh::lean_dec_ref(v___y_6745_);
                            v_a_6887_ = crate::leanh::lean_ctor_get(v___x_6844_, 0);
                            v_isSharedCheck_6894_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6844_)) as u8;
                            if v_isSharedCheck_6894_ == 0 {
                                v___x_6889_ = v___x_6844_;
                                v_isShared_6890_ = v_isSharedCheck_6894_;
                                state = 120;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6887_);
                                crate::leanh::lean_dec(v___x_6844_);
                                v___x_6889_ = crate::leanh::lean_box(0);
                                v_isShared_6890_ = v_isSharedCheck_6894_;
                                state = 120;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                        v___x_6895_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v___x_6838_,
                            v___y_6743_,
                            v___y_6744_,
                            v___y_6745_,
                            v___y_6746_,
                        );
                        crate::leanh::lean_dec_ref(v___y_6745_);
                        return v___x_6895_;
                    }
                }
            }
            113 => {
                return v___x_6830_;
            }
            114 => {
                v_subst_6851_ = crate::leanh::lean_ctor_get(v___x_6842_, 0);
                crate::leanh::lean_inc_ref(v_subst_6851_);
                crate::leanh::lean_dec(v___x_6842_);
                crate::leanh::lean_inc_ref(v_resultType_6833_);
                v___x_6852_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v___x_6838_,
                        v_subst_6851_,
                        v___x_6839_,
                        v_resultType_6833_,
                    );
                crate::leanh::lean_dec_ref(v_subst_6851_);
                v___x_6853_ = lean_array_get_size(v_a_6847_);
                v___x_6854_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6855_ = lean_nat_dec_eq(v___x_6853_, v___x_6854_);
                if v___x_6855_ == 0 {
                    crate::leanh::lean_del_object(v___x_6849_);
                    crate::leanh::lean_inc_ref(v_alts_6835_);
                    crate::leanh::lean_inc(v_typeName_6832_);
                    crate::leanh::lean_inc_ref(v_resultType_6833_);
                    crate::leanh::lean_inc(v_discr_6834_);
                    v___y_6658_ = v_discr_6834_;
                    v___y_6659_ = v_fvarId_6841_;
                    v___y_6660_ = v_a_6847_;
                    v___y_6661_ = v_resultType_6833_;
                    v___y_6662_ = v_typeName_6832_;
                    v___y_6663_ = v___x_6852_;
                    v___y_6664_ = v_alts_6835_;
                    v___y_6665_ = v___x_6843_;
                    v___y_6666_ = v___y_6741_;
                    v___y_6667_ = v___y_6743_;
                    v___y_6668_ = v___y_6744_;
                    v___y_6669_ = v___y_6745_;
                    v___y_6670_ = v___y_6746_;
                    state = 89;
                    continue;
                } else {
                    v___x_6856_ = lean_array_fget_borrowed(v_a_6847_, v___x_6843_);
                    if crate::leanh::lean_obj_tag(v___x_6856_) == 0 {
                        crate::leanh::lean_del_object(v___x_6849_);
                        v_params_6857_ = crate::leanh::lean_ctor_get(v___x_6856_, 1);
                        v_code_6858_ = crate::leanh::lean_ctor_get(v___x_6856_, 2);
                        v___x_6859_ = lean_array_get_size(v_params_6857_);
                        v___x_6860_ = lean_nat_dec_lt(v___x_6843_, v___x_6859_);
                        if v___x_6860_ == 0 {
                            crate::leanh::lean_inc_ref(v_code_6858_);
                            crate::leanh::lean_inc_ref(v_params_6857_);
                            crate::leanh::lean_dec_ref(v___x_6852_);
                            crate::leanh::lean_dec(v_a_6847_);
                            crate::leanh::lean_dec(v_fvarId_6841_);
                            crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                            crate::leanh::lean_dec_ref(v___y_6745_);
                            v___y_6724_ = v___y_6741_;
                            v___y_6725_ = v___x_6859_;
                            v___y_6726_ = v_params_6857_;
                            v___y_6727_ = v_code_6858_;
                            v___y_6728_ = v___y_6744_;
                            v___y_6729_ = v___x_6843_;
                            state = 100;
                            continue;
                        } else {
                            if v___x_6860_ == 0 {
                                crate::leanh::lean_inc_ref(v_code_6858_);
                                crate::leanh::lean_inc_ref(v_params_6857_);
                                crate::leanh::lean_dec_ref(v___x_6852_);
                                crate::leanh::lean_dec(v_a_6847_);
                                crate::leanh::lean_dec(v_fvarId_6841_);
                                crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                                crate::leanh::lean_dec_ref(v___y_6745_);
                                v___y_6724_ = v___y_6741_;
                                v___y_6725_ = v___x_6859_;
                                v___y_6726_ = v_params_6857_;
                                v___y_6727_ = v_code_6858_;
                                v___y_6728_ = v___y_6744_;
                                v___y_6729_ = v___x_6843_;
                                state = 100;
                                continue;
                            } else {
                                v___x_6861_ = 0usize;
                                v___x_6862_ = lean_usize_of_nat(v___x_6859_);
                                v___x_6863_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_params_6857_, v___x_6861_, v___x_6862_, v___y_6741_);
                                if crate::leanh::lean_obj_tag(v___x_6863_) == 0 {
                                    v_a_6864_ = crate::leanh::lean_ctor_get(v___x_6863_, 0);
                                    crate::leanh::lean_inc(v_a_6864_);
                                    crate::leanh::lean_dec_ref_known(v___x_6863_, 1);
                                    v___x_6865_ = (crate::leanh::lean_unbox(v_a_6864_) as u8);
                                    crate::leanh::lean_dec(v_a_6864_);
                                    if v___x_6865_ == 0 {
                                        crate::leanh::lean_inc_ref(v_code_6858_);
                                        crate::leanh::lean_inc_ref(v_params_6857_);
                                        crate::leanh::lean_dec_ref(v___x_6852_);
                                        crate::leanh::lean_dec(v_a_6847_);
                                        crate::leanh::lean_dec(v_fvarId_6841_);
                                        crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                                        crate::leanh::lean_dec_ref(v___y_6745_);
                                        v___y_6724_ = v___y_6741_;
                                        v___y_6725_ = v___x_6859_;
                                        v___y_6726_ = v_params_6857_;
                                        v___y_6727_ = v_code_6858_;
                                        v___y_6728_ = v___y_6744_;
                                        v___y_6729_ = v___x_6843_;
                                        state = 100;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc_ref(v_alts_6835_);
                                        crate::leanh::lean_inc(v_typeName_6832_);
                                        crate::leanh::lean_inc_ref(v_resultType_6833_);
                                        crate::leanh::lean_inc(v_discr_6834_);
                                        v___y_6658_ = v_discr_6834_;
                                        v___y_6659_ = v_fvarId_6841_;
                                        v___y_6660_ = v_a_6847_;
                                        v___y_6661_ = v_resultType_6833_;
                                        v___y_6662_ = v_typeName_6832_;
                                        v___y_6663_ = v___x_6852_;
                                        v___y_6664_ = v_alts_6835_;
                                        v___y_6665_ = v___x_6843_;
                                        v___y_6666_ = v___y_6741_;
                                        v___y_6667_ = v___y_6743_;
                                        v___y_6668_ = v___y_6744_;
                                        v___y_6669_ = v___y_6745_;
                                        v___y_6670_ = v___y_6746_;
                                        state = 89;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_6852_);
                                    crate::leanh::lean_dec(v_a_6847_);
                                    crate::leanh::lean_dec(v_fvarId_6841_);
                                    crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                                    crate::leanh::lean_dec_ref(v___y_6745_);
                                    v_a_6866_ = crate::leanh::lean_ctor_get(v___x_6863_, 0);
                                    v_isSharedCheck_6873_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_6863_)) as u8;
                                    if v_isSharedCheck_6873_ == 0 {
                                        v___x_6868_ = v___x_6863_;
                                        v_isShared_6869_ = v_isSharedCheck_6873_;
                                        state = 115;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_6866_);
                                        crate::leanh::lean_dec(v___x_6863_);
                                        v___x_6868_ = crate::leanh::lean_box(0);
                                        v_isShared_6869_ = v_isSharedCheck_6873_;
                                        state = 115;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_inc_ref(v___x_6856_);
                        crate::leanh::lean_dec_ref(v___x_6852_);
                        crate::leanh::lean_dec(v_a_6847_);
                        crate::leanh::lean_dec(v_fvarId_6841_);
                        crate::leanh::lean_dec_ref_known(v_code_6077_, 1);
                        crate::leanh::lean_dec_ref(v___y_6745_);
                        v_code_6874_ = crate::leanh::lean_ctor_get(v___x_6856_, 0);
                        crate::leanh::lean_inc_ref(v_code_6874_);
                        crate::leanh::lean_dec_ref_known(v___x_6856_, 1);
                        if v_isShared_6850_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_6849_, 0, v_code_6874_);
                            v___x_6876_ = v___x_6849_;
                            state = 117;
                            continue;
                        } else {
                            v_reuseFailAlloc_6877_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_6877_, 0, v_code_6874_);
                            v___x_6876_ = v_reuseFailAlloc_6877_;
                            state = 117;
                            continue;
                        }
                    }
                }
            }
            115 => {
                if v_isShared_6869_ == 0 {
                    v___x_6871_ = v___x_6868_;
                    state = 116;
                    continue;
                } else {
                    v_reuseFailAlloc_6872_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6872_, 0, v_a_6866_);
                    v___x_6871_ = v_reuseFailAlloc_6872_;
                    state = 116;
                    continue;
                }
            }
            116 => {
                return v___x_6871_;
            }
            117 => {
                return v___x_6876_;
            }
            118 => {
                if v_isShared_6882_ == 0 {
                    v___x_6884_ = v___x_6881_;
                    state = 119;
                    continue;
                } else {
                    v_reuseFailAlloc_6885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6885_, 0, v_a_6879_);
                    v___x_6884_ = v_reuseFailAlloc_6885_;
                    state = 119;
                    continue;
                }
            }
            119 => {
                return v___x_6884_;
            }
            120 => {
                if v_isShared_6890_ == 0 {
                    v___x_6892_ = v___x_6889_;
                    state = 121;
                    continue;
                } else {
                    v_reuseFailAlloc_6893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_a_6887_);
                    v___x_6892_ = v_reuseFailAlloc_6893_;
                    state = 121;
                    continue;
                }
            }
            121 => {
                return v___x_6892_;
            }
            122 => {
                if v_isShared_6900_ == 0 {
                    v___x_6902_ = v___x_6899_;
                    state = 123;
                    continue;
                } else {
                    v_reuseFailAlloc_6903_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_a_6897_);
                    v___x_6902_ = v_reuseFailAlloc_6903_;
                    state = 123;
                    continue;
                }
            }
            123 => {
                return v___x_6902_;
            }
            124 => {
                v___x_6915_ = l_Lean_instBEqFVarId_beq(v_fvarId_6905_, v_fvarId_6910_);
                if v___x_6915_ == 0 {
                    v_isSharedCheck_6925_ = (!crate::leanh::lean_is_exclusive(v_code_6077_)) as u8;
                    if v_isSharedCheck_6925_ == 0 {
                        v_unused_6926_ = crate::leanh::lean_ctor_get(v_code_6077_, 0);
                        crate::leanh::lean_dec(v_unused_6926_);
                        v___x_6917_ = v_code_6077_;
                        v_isShared_6918_ = v_isSharedCheck_6925_;
                        state = 125;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_6077_);
                        v___x_6917_ = crate::leanh::lean_box(0);
                        v_isShared_6918_ = v_isSharedCheck_6925_;
                        state = 125;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_fvarId_6910_);
                    if v_isShared_6914_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6913_, 0, v_code_6077_);
                        v___x_6928_ = v___x_6913_;
                        state = 128;
                        continue;
                    } else {
                        v_reuseFailAlloc_6929_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6929_, 0, v_code_6077_);
                        v___x_6928_ = v_reuseFailAlloc_6929_;
                        state = 128;
                        continue;
                    }
                }
            }
            125 => {
                if v_isShared_6918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6917_, 0, v_fvarId_6910_);
                    v___x_6920_ = v___x_6917_;
                    state = 126;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_fvarId_6910_);
                    v___x_6920_ = v_reuseFailAlloc_6924_;
                    state = 126;
                    continue;
                }
            }
            126 => {
                if v_isShared_6914_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6913_, 0, v___x_6920_);
                    v___x_6922_ = v___x_6913_;
                    state = 127;
                    continue;
                } else {
                    v_reuseFailAlloc_6923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6923_, 0, v___x_6920_);
                    v___x_6922_ = v_reuseFailAlloc_6923_;
                    state = 127;
                    continue;
                }
            }
            127 => {
                return v___x_6922_;
            }
            128 => {
                return v___x_6928_;
            }
            129 => {
                if v_isShared_6935_ == 0 {
                    v___x_6937_ = v___x_6934_;
                    state = 130;
                    continue;
                } else {
                    v_reuseFailAlloc_6938_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6938_, 0, v_a_6932_);
                    v___x_6937_ = v_reuseFailAlloc_6938_;
                    state = 130;
                    continue;
                }
            }
            130 => {
                return v___x_6937_;
            }
            131 => {
                if v_isShared_6953_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6952_, 0, v___x_6947_);
                    v___x_6955_ = v___x_6952_;
                    state = 132;
                    continue;
                } else {
                    v_reuseFailAlloc_6957_ = crate::leanh::lean_alloc_ctor(6, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6957_, 0, v___x_6947_);
                    v___x_6955_ = v_reuseFailAlloc_6957_;
                    state = 132;
                    continue;
                }
            }
            132 => {
                v___x_6956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6956_, 0, v___x_6955_);
                return v___x_6956_;
            }
            133 => {
                v___x_6980_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_6079_);
                if crate::leanh::lean_obj_tag(v___x_6980_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6980_, 1);
                    v___x_6981_ = lean_st_ref_get(v_a_6079_);
                    v_visited_6982_ = crate::leanh::lean_ctor_get(v___x_6981_, 4);
                    crate::leanh::lean_inc(v_visited_6982_);
                    crate::leanh::lean_dec(v___x_6981_);
                    v___x_6983_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6984_ = lean_nat_add(v_currRecDepth_6966_, v___x_6983_);
                    crate::leanh::lean_dec(v_currRecDepth_6966_);
                    v___x_6985_ = crate::leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    crate::leanh::lean_ctor_set(v___x_6985_, 0, v_fileName_6963_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 1, v_fileMap_6964_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 2, v_options_6965_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 3, v___x_6984_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 4, v_maxRecDepth_6967_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 5, v_ref_6968_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 6, v_currNamespace_6969_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 7, v_openDecls_6970_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 8, v_initHeartbeats_6971_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 9, v_maxHeartbeats_6972_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 10, v_quotContext_6973_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 11, v_currMacroScope_6974_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 12, v_cancelTk_x3f_6976_);
                    crate::leanh::lean_ctor_set(v___x_6985_, 13, v_inheritedTraceOptions_6978_);
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6985_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14) as u32,
                        v_diag_6975_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v___x_6985_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_6977_,
                    );
                    v___x_6986_ = crate::leanh::lean_unsigned_to_nat(128);
                    v___x_6987_ = lean_nat_mod(v_visited_6982_, v___x_6986_);
                    crate::leanh::lean_dec(v_visited_6982_);
                    v___x_6988_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6989_ = lean_nat_dec_eq(v___x_6987_, v___x_6988_);
                    crate::leanh::lean_dec(v___x_6987_);
                    if v___x_6989_ == 0 {
                        v___y_6740_ = v_a_6078_;
                        v___y_6741_ = v_a_6079_;
                        v___y_6742_ = v_a_6080_;
                        v___y_6743_ = v_a_6081_;
                        v___y_6744_ = v_a_6082_;
                        v___y_6745_ = v___x_6985_;
                        v___y_6746_ = v_a_6084_;
                        state = 101;
                        continue;
                    } else {
                        v___x_6990_ = l_Lean_Compiler_LCNF_Simp_simp___closed__4;
                        v___x_6991_ = l_Lean_Core_checkSystem(v___x_6990_, v___x_6985_, v_a_6084_);
                        if crate::leanh::lean_obj_tag(v___x_6991_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_6991_, 1);
                            v___y_6740_ = v_a_6078_;
                            v___y_6741_ = v_a_6079_;
                            v___y_6742_ = v_a_6080_;
                            v___y_6743_ = v_a_6081_;
                            v___y_6744_ = v_a_6082_;
                            v___y_6745_ = v___x_6985_;
                            v___y_6746_ = v_a_6084_;
                            state = 101;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_6985_, 14);
                            crate::leanh::lean_dec_ref(v_code_6077_);
                            v_a_6992_ = crate::leanh::lean_ctor_get(v___x_6991_, 0);
                            v_isSharedCheck_6999_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6991_)) as u8;
                            if v_isSharedCheck_6999_ == 0 {
                                v___x_6994_ = v___x_6991_;
                                v_isShared_6995_ = v_isSharedCheck_6999_;
                                state = 134;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6992_);
                                crate::leanh::lean_dec(v___x_6991_);
                                v___x_6994_ = crate::leanh::lean_box(0);
                                v_isShared_6995_ = v_isSharedCheck_6999_;
                                state = 134;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_inheritedTraceOptions_6978_);
                    crate::leanh::lean_dec(v_cancelTk_x3f_6976_);
                    crate::leanh::lean_dec(v_currMacroScope_6974_);
                    crate::leanh::lean_dec(v_quotContext_6973_);
                    crate::leanh::lean_dec(v_maxHeartbeats_6972_);
                    crate::leanh::lean_dec(v_initHeartbeats_6971_);
                    crate::leanh::lean_dec(v_openDecls_6970_);
                    crate::leanh::lean_dec(v_currNamespace_6969_);
                    crate::leanh::lean_dec(v_ref_6968_);
                    crate::leanh::lean_dec(v_maxRecDepth_6967_);
                    crate::leanh::lean_dec(v_currRecDepth_6966_);
                    crate::leanh::lean_dec_ref(v_options_6965_);
                    crate::leanh::lean_dec_ref(v_fileMap_6964_);
                    crate::leanh::lean_dec_ref(v_fileName_6963_);
                    crate::leanh::lean_dec_ref(v_code_6077_);
                    v_a_7000_ = crate::leanh::lean_ctor_get(v___x_6980_, 0);
                    v_isSharedCheck_7007_ = (!crate::leanh::lean_is_exclusive(v___x_6980_)) as u8;
                    if v_isSharedCheck_7007_ == 0 {
                        v___x_7002_ = v___x_6980_;
                        v_isShared_7003_ = v_isSharedCheck_7007_;
                        state = 136;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7000_);
                        crate::leanh::lean_dec(v___x_6980_);
                        v___x_7002_ = crate::leanh::lean_box(0);
                        v_isShared_7003_ = v_isSharedCheck_7007_;
                        state = 136;
                        continue;
                    }
                }
            }
            134 => {
                if v_isShared_6995_ == 0 {
                    v___x_6997_ = v___x_6994_;
                    state = 135;
                    continue;
                } else {
                    v_reuseFailAlloc_6998_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6998_, 0, v_a_6992_);
                    v___x_6997_ = v_reuseFailAlloc_6998_;
                    state = 135;
                    continue;
                }
            }
            135 => {
                return v___x_6997_;
            }
            136 => {
                if v_isShared_7003_ == 0 {
                    v___x_7005_ = v___x_7002_;
                    state = 137;
                    continue;
                } else {
                    v_reuseFailAlloc_7006_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_a_7000_);
                    v___x_7005_ = v_reuseFailAlloc_7006_;
                    state = 137;
                    continue;
                }
            }
            137 => {
                return v___x_7005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpFunDecl(
    mut v_decl_7012_: *mut crate::leanh::LeanObject,
    mut v_a_7013_: *mut crate::leanh::LeanObject,
    mut v_a_7014_: *mut crate::leanh::LeanObject,
    mut v_a_7015_: *mut crate::leanh::LeanObject,
    mut v_a_7016_: *mut crate::leanh::LeanObject,
    mut v_a_7017_: *mut crate::leanh::LeanObject,
    mut v_a_7018_: *mut crate::leanh::LeanObject,
    mut v_a_7019_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_7021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_7022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_7023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_subst_7025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: u8 = 0;
    let mut v___x_7027_: u8 = 0;
    let mut v___x_7028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7037_: u8 = 0;
    let mut v___x_7039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7041_: u8 = 0;
    let mut v_a_7042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7045_: u8 = 0;
    let mut v___x_7047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_7021_ = crate::leanh::lean_ctor_get(v_decl_7012_, 2);
                v_type_7022_ = crate::leanh::lean_ctor_get(v_decl_7012_, 3);
                v_value_7023_ = crate::leanh::lean_ctor_get(v_decl_7012_, 4);
                v___x_7024_ = lean_st_ref_get(v_a_7014_);
                v_subst_7025_ = crate::leanh::lean_ctor_get(v___x_7024_, 0);
                crate::leanh::lean_inc_ref(v_subst_7025_);
                crate::leanh::lean_dec(v___x_7024_);
                v___x_7026_ = 0;
                v___x_7027_ = 0;
                crate::leanh::lean_inc_ref(v_type_7022_);
                v___x_7028_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v___x_7026_,
                        v_subst_7025_,
                        v___x_7027_,
                        v_type_7022_,
                    );
                crate::leanh::lean_dec_ref(v_subst_7025_);
                crate::leanh::lean_inc_ref(v_params_7021_);
                v___x_7029_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_7026_, v___x_7027_, v_params_7021_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_, v_a_7017_, v_a_7018_, v_a_7019_);
                if crate::leanh::lean_obj_tag(v___x_7029_) == 0 {
                    v_a_7030_ = crate::leanh::lean_ctor_get(v___x_7029_, 0);
                    crate::leanh::lean_inc(v_a_7030_);
                    crate::leanh::lean_dec_ref_known(v___x_7029_, 1);
                    crate::leanh::lean_inc_ref(v_a_7018_);
                    crate::leanh::lean_inc_ref(v_value_7023_);
                    v___x_7031_ = l_Lean_Compiler_LCNF_Simp_simp(
                        v_value_7023_,
                        v_a_7013_,
                        v_a_7014_,
                        v_a_7015_,
                        v_a_7016_,
                        v_a_7017_,
                        v_a_7018_,
                        v_a_7019_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_7031_) == 0 {
                        v_a_7032_ = crate::leanh::lean_ctor_get(v___x_7031_, 0);
                        crate::leanh::lean_inc(v_a_7032_);
                        crate::leanh::lean_dec_ref_known(v___x_7031_, 1);
                        v___x_7033_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_7026_, v_decl_7012_, v___x_7028_, v_a_7030_, v_a_7032_, v_a_7017_);
                        return v___x_7033_;
                    } else {
                        crate::leanh::lean_dec(v_a_7030_);
                        crate::leanh::lean_dec_ref(v___x_7028_);
                        crate::leanh::lean_dec_ref(v_decl_7012_);
                        v_a_7034_ = crate::leanh::lean_ctor_get(v___x_7031_, 0);
                        v_isSharedCheck_7041_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7031_)) as u8;
                        if v_isSharedCheck_7041_ == 0 {
                            v___x_7036_ = v___x_7031_;
                            v_isShared_7037_ = v_isSharedCheck_7041_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7034_);
                            crate::leanh::lean_dec(v___x_7031_);
                            v___x_7036_ = crate::leanh::lean_box(0);
                            v_isShared_7037_ = v_isSharedCheck_7041_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_7028_);
                    crate::leanh::lean_dec_ref(v_decl_7012_);
                    v_a_7042_ = crate::leanh::lean_ctor_get(v___x_7029_, 0);
                    v_isSharedCheck_7049_ = (!crate::leanh::lean_is_exclusive(v___x_7029_)) as u8;
                    if v_isSharedCheck_7049_ == 0 {
                        v___x_7044_ = v___x_7029_;
                        v_isShared_7045_ = v_isSharedCheck_7049_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_7042_);
                        crate::leanh::lean_dec(v___x_7029_);
                        v___x_7044_ = crate::leanh::lean_box(0);
                        v_isShared_7045_ = v_isSharedCheck_7049_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7037_ == 0 {
                    v___x_7039_ = v___x_7036_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7040_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7040_, 0, v_a_7034_);
                    v___x_7039_ = v_reuseFailAlloc_7040_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7039_;
            }
            3 => {
                if v_isShared_7045_ == 0 {
                    v___x_7047_ = v___x_7044_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7048_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7048_, 0, v_a_7042_);
                    v___x_7047_ = v_reuseFailAlloc_7048_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7047_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpFunDecl___boxed(
    mut v_decl_7050_: *mut crate::leanh::LeanObject,
    mut v_a_7051_: *mut crate::leanh::LeanObject,
    mut v_a_7052_: *mut crate::leanh::LeanObject,
    mut v_a_7053_: *mut crate::leanh::LeanObject,
    mut v_a_7054_: *mut crate::leanh::LeanObject,
    mut v_a_7055_: *mut crate::leanh::LeanObject,
    mut v_a_7056_: *mut crate::leanh::LeanObject,
    mut v_a_7057_: *mut crate::leanh::LeanObject,
    mut v_a_7058_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7059_ = l_Lean_Compiler_LCNF_Simp_simpFunDecl(
        v_decl_7050_,
        v_a_7051_,
        v_a_7052_,
        v_a_7053_,
        v_a_7054_,
        v_a_7055_,
        v_a_7056_,
        v_a_7057_,
    );
    crate::leanh::lean_dec(v_a_7057_);
    crate::leanh::lean_dec_ref(v_a_7056_);
    crate::leanh::lean_dec(v_a_7055_);
    crate::leanh::lean_dec_ref(v_a_7054_);
    crate::leanh::lean_dec_ref(v_a_7053_);
    crate::leanh::lean_dec(v_a_7052_);
    crate::leanh::lean_dec_ref(v_a_7051_);
    return v_res_7059_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(
    mut v_fvarId_7060_: *mut crate::leanh::LeanObject,
    mut v_i_7061_: *mut crate::leanh::LeanObject,
    mut v_as_7062_: *mut crate::leanh::LeanObject,
    mut v___y_7063_: *mut crate::leanh::LeanObject,
    mut v___y_7064_: *mut crate::leanh::LeanObject,
    mut v___y_7065_: *mut crate::leanh::LeanObject,
    mut v___y_7066_: *mut crate::leanh::LeanObject,
    mut v___y_7067_: *mut crate::leanh::LeanObject,
    mut v___y_7068_: *mut crate::leanh::LeanObject,
    mut v___y_7069_: *mut crate::leanh::LeanObject,
    mut v___y_7070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7071_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_7060_, v_i_7061_, v_as_7062_, v___y_7063_, v___y_7064_, v___y_7065_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_);
    crate::leanh::lean_dec(v___y_7069_);
    crate::leanh::lean_dec_ref(v___y_7068_);
    crate::leanh::lean_dec(v___y_7067_);
    crate::leanh::lean_dec_ref(v___y_7066_);
    crate::leanh::lean_dec_ref(v___y_7065_);
    crate::leanh::lean_dec(v___y_7064_);
    crate::leanh::lean_dec_ref(v___y_7063_);
    return v_res_7071_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(
    mut v_cases_7072_: *mut crate::leanh::LeanObject,
    mut v_a_7073_: *mut crate::leanh::LeanObject,
    mut v_a_7074_: *mut crate::leanh::LeanObject,
    mut v_a_7075_: *mut crate::leanh::LeanObject,
    mut v_a_7076_: *mut crate::leanh::LeanObject,
    mut v_a_7077_: *mut crate::leanh::LeanObject,
    mut v_a_7078_: *mut crate::leanh::LeanObject,
    mut v_a_7079_: *mut crate::leanh::LeanObject,
    mut v_a_7080_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7081_ = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(
        v_cases_7072_,
        v_a_7073_,
        v_a_7074_,
        v_a_7075_,
        v_a_7076_,
        v_a_7077_,
        v_a_7078_,
        v_a_7079_,
    );
    crate::leanh::lean_dec(v_a_7079_);
    crate::leanh::lean_dec_ref(v_a_7078_);
    crate::leanh::lean_dec(v_a_7077_);
    crate::leanh::lean_dec_ref(v_a_7076_);
    crate::leanh::lean_dec_ref(v_a_7075_);
    crate::leanh::lean_dec(v_a_7074_);
    crate::leanh::lean_dec_ref(v_a_7073_);
    return v_res_7081_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(
    mut v_letDecl_7082_: *mut crate::leanh::LeanObject,
    mut v_k_7083_: *mut crate::leanh::LeanObject,
    mut v_a_7084_: *mut crate::leanh::LeanObject,
    mut v_a_7085_: *mut crate::leanh::LeanObject,
    mut v_a_7086_: *mut crate::leanh::LeanObject,
    mut v_a_7087_: *mut crate::leanh::LeanObject,
    mut v_a_7088_: *mut crate::leanh::LeanObject,
    mut v_a_7089_: *mut crate::leanh::LeanObject,
    mut v_a_7090_: *mut crate::leanh::LeanObject,
    mut v_a_7091_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7092_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(
        v_letDecl_7082_,
        v_k_7083_,
        v_a_7084_,
        v_a_7085_,
        v_a_7086_,
        v_a_7087_,
        v_a_7088_,
        v_a_7089_,
        v_a_7090_,
    );
    crate::leanh::lean_dec(v_a_7090_);
    crate::leanh::lean_dec_ref(v_a_7089_);
    crate::leanh::lean_dec(v_a_7088_);
    crate::leanh::lean_dec_ref(v_a_7087_);
    crate::leanh::lean_dec_ref(v_a_7086_);
    crate::leanh::lean_dec(v_a_7085_);
    crate::leanh::lean_dec_ref(v_a_7084_);
    return v_res_7092_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simp___boxed(
    mut v_code_7093_: *mut crate::leanh::LeanObject,
    mut v_a_7094_: *mut crate::leanh::LeanObject,
    mut v_a_7095_: *mut crate::leanh::LeanObject,
    mut v_a_7096_: *mut crate::leanh::LeanObject,
    mut v_a_7097_: *mut crate::leanh::LeanObject,
    mut v_a_7098_: *mut crate::leanh::LeanObject,
    mut v_a_7099_: *mut crate::leanh::LeanObject,
    mut v_a_7100_: *mut crate::leanh::LeanObject,
    mut v_a_7101_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7102_ = l_Lean_Compiler_LCNF_Simp_simp(
        v_code_7093_,
        v_a_7094_,
        v_a_7095_,
        v_a_7096_,
        v_a_7097_,
        v_a_7098_,
        v_a_7099_,
        v_a_7100_,
    );
    crate::leanh::lean_dec(v_a_7100_);
    crate::leanh::lean_dec(v_a_7098_);
    crate::leanh::lean_dec_ref(v_a_7097_);
    crate::leanh::lean_dec_ref(v_a_7096_);
    crate::leanh::lean_dec(v_a_7095_);
    crate::leanh::lean_dec_ref(v_a_7094_);
    return v_res_7102_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(
    mut v_pu_7103_: u8,
    mut v_t_7104_: u8,
    mut v_decl_7105_: *mut crate::leanh::LeanObject,
    mut v___y_7106_: *mut crate::leanh::LeanObject,
    mut v___y_7107_: *mut crate::leanh::LeanObject,
    mut v___y_7108_: *mut crate::leanh::LeanObject,
    mut v___y_7109_: *mut crate::leanh::LeanObject,
    mut v___y_7110_: *mut crate::leanh::LeanObject,
    mut v___y_7111_: *mut crate::leanh::LeanObject,
    mut v___y_7112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7114_ =
        l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(
            v_pu_7103_,
            v_t_7104_,
            v_decl_7105_,
            v___y_7107_,
            v___y_7110_,
        );
    return v___x_7114_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___boxed(
    mut v_pu_7115_: *mut crate::leanh::LeanObject,
    mut v_t_7116_: *mut crate::leanh::LeanObject,
    mut v_decl_7117_: *mut crate::leanh::LeanObject,
    mut v___y_7118_: *mut crate::leanh::LeanObject,
    mut v___y_7119_: *mut crate::leanh::LeanObject,
    mut v___y_7120_: *mut crate::leanh::LeanObject,
    mut v___y_7121_: *mut crate::leanh::LeanObject,
    mut v___y_7122_: *mut crate::leanh::LeanObject,
    mut v___y_7123_: *mut crate::leanh::LeanObject,
    mut v___y_7124_: *mut crate::leanh::LeanObject,
    mut v___y_7125_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7126_: u8 = 0;
    let mut v_t_boxed_7127_: u8 = 0;
    let mut v_res_7128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7126_ = (crate::leanh::lean_unbox(v_pu_7115_) as u8);
    v_t_boxed_7127_ = (crate::leanh::lean_unbox(v_t_7116_) as u8);
    v_res_7128_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(
        v_pu_boxed_7126_,
        v_t_boxed_7127_,
        v_decl_7117_,
        v___y_7118_,
        v___y_7119_,
        v___y_7120_,
        v___y_7121_,
        v___y_7122_,
        v___y_7123_,
        v___y_7124_,
    );
    crate::leanh::lean_dec(v___y_7124_);
    crate::leanh::lean_dec_ref(v___y_7123_);
    crate::leanh::lean_dec(v___y_7122_);
    crate::leanh::lean_dec_ref(v___y_7121_);
    crate::leanh::lean_dec_ref(v___y_7120_);
    crate::leanh::lean_dec(v___y_7119_);
    crate::leanh::lean_dec_ref(v___y_7118_);
    return v_res_7128_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(
    mut v_pu_7129_: u8,
    mut v_t_7130_: u8,
    mut v_args_7131_: *mut crate::leanh::LeanObject,
    mut v___y_7132_: *mut crate::leanh::LeanObject,
    mut v___y_7133_: *mut crate::leanh::LeanObject,
    mut v___y_7134_: *mut crate::leanh::LeanObject,
    mut v___y_7135_: *mut crate::leanh::LeanObject,
    mut v___y_7136_: *mut crate::leanh::LeanObject,
    mut v___y_7137_: *mut crate::leanh::LeanObject,
    mut v___y_7138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7140_ =
        l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(
            v_pu_7129_,
            v_t_7130_,
            v_args_7131_,
            v___y_7133_,
        );
    return v___x_7140_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___boxed(
    mut v_pu_7141_: *mut crate::leanh::LeanObject,
    mut v_t_7142_: *mut crate::leanh::LeanObject,
    mut v_args_7143_: *mut crate::leanh::LeanObject,
    mut v___y_7144_: *mut crate::leanh::LeanObject,
    mut v___y_7145_: *mut crate::leanh::LeanObject,
    mut v___y_7146_: *mut crate::leanh::LeanObject,
    mut v___y_7147_: *mut crate::leanh::LeanObject,
    mut v___y_7148_: *mut crate::leanh::LeanObject,
    mut v___y_7149_: *mut crate::leanh::LeanObject,
    mut v___y_7150_: *mut crate::leanh::LeanObject,
    mut v___y_7151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7152_: u8 = 0;
    let mut v_t_boxed_7153_: u8 = 0;
    let mut v_res_7154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7152_ = (crate::leanh::lean_unbox(v_pu_7141_) as u8);
    v_t_boxed_7153_ = (crate::leanh::lean_unbox(v_t_7142_) as u8);
    v_res_7154_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(
        v_pu_boxed_7152_,
        v_t_boxed_7153_,
        v_args_7143_,
        v___y_7144_,
        v___y_7145_,
        v___y_7146_,
        v___y_7147_,
        v___y_7148_,
        v___y_7149_,
        v___y_7150_,
    );
    crate::leanh::lean_dec(v___y_7150_);
    crate::leanh::lean_dec_ref(v___y_7149_);
    crate::leanh::lean_dec(v___y_7148_);
    crate::leanh::lean_dec_ref(v___y_7147_);
    crate::leanh::lean_dec_ref(v___y_7146_);
    crate::leanh::lean_dec(v___y_7145_);
    crate::leanh::lean_dec_ref(v___y_7144_);
    return v_res_7154_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(
    mut v_inst_7155_: *mut crate::leanh::LeanObject,
    mut v_R_7156_: *mut crate::leanh::LeanObject,
    mut v_a_7157_: *mut crate::leanh::LeanObject,
    mut v_b_7158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7159_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_7157_, v_b_7158_);
    return v___x_7159_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(
    mut v_00_u03b2_7160_: *mut crate::leanh::LeanObject,
    mut v_x_7161_: *mut crate::leanh::LeanObject,
    mut v_x_7162_: *mut crate::leanh::LeanObject,
    mut v_x_7163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7164_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_7161_, v_x_7162_, v_x_7163_);
    return v___x_7164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(
    mut v_as_7165_: *mut crate::leanh::LeanObject,
    mut v_i_7166_: usize,
    mut v_stop_7167_: usize,
    mut v_b_7168_: *mut crate::leanh::LeanObject,
    mut v___y_7169_: *mut crate::leanh::LeanObject,
    mut v___y_7170_: *mut crate::leanh::LeanObject,
    mut v___y_7171_: *mut crate::leanh::LeanObject,
    mut v___y_7172_: *mut crate::leanh::LeanObject,
    mut v___y_7173_: *mut crate::leanh::LeanObject,
    mut v___y_7174_: *mut crate::leanh::LeanObject,
    mut v___y_7175_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_7165_, v_i_7166_, v_stop_7167_, v_b_7168_, v___y_7170_);
    return v___x_7177_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(
    mut v_as_7178_: *mut crate::leanh::LeanObject,
    mut v_i_7179_: *mut crate::leanh::LeanObject,
    mut v_stop_7180_: *mut crate::leanh::LeanObject,
    mut v_b_7181_: *mut crate::leanh::LeanObject,
    mut v___y_7182_: *mut crate::leanh::LeanObject,
    mut v___y_7183_: *mut crate::leanh::LeanObject,
    mut v___y_7184_: *mut crate::leanh::LeanObject,
    mut v___y_7185_: *mut crate::leanh::LeanObject,
    mut v___y_7186_: *mut crate::leanh::LeanObject,
    mut v___y_7187_: *mut crate::leanh::LeanObject,
    mut v___y_7188_: *mut crate::leanh::LeanObject,
    mut v___y_7189_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7190_: usize = 0;
    let mut v_stop_boxed_7191_: usize = 0;
    let mut v_res_7192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7190_ = crate::leanh::lean_unbox_usize(v_i_7179_);
    crate::leanh::lean_dec(v_i_7179_);
    v_stop_boxed_7191_ = crate::leanh::lean_unbox_usize(v_stop_7180_);
    crate::leanh::lean_dec(v_stop_7180_);
    v_res_7192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_7178_, v_i_boxed_7190_, v_stop_boxed_7191_, v_b_7181_, v___y_7182_, v___y_7183_, v___y_7184_, v___y_7185_, v___y_7186_, v___y_7187_, v___y_7188_);
    crate::leanh::lean_dec(v___y_7188_);
    crate::leanh::lean_dec_ref(v___y_7187_);
    crate::leanh::lean_dec(v___y_7186_);
    crate::leanh::lean_dec_ref(v___y_7185_);
    crate::leanh::lean_dec_ref(v___y_7184_);
    crate::leanh::lean_dec(v___y_7183_);
    crate::leanh::lean_dec_ref(v___y_7182_);
    crate::leanh::lean_dec_ref(v_as_7178_);
    return v_res_7192_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(
    mut v_as_7193_: *mut crate::leanh::LeanObject,
    mut v_i_7194_: usize,
    mut v_stop_7195_: usize,
    mut v___y_7196_: *mut crate::leanh::LeanObject,
    mut v___y_7197_: *mut crate::leanh::LeanObject,
    mut v___y_7198_: *mut crate::leanh::LeanObject,
    mut v___y_7199_: *mut crate::leanh::LeanObject,
    mut v___y_7200_: *mut crate::leanh::LeanObject,
    mut v___y_7201_: *mut crate::leanh::LeanObject,
    mut v___y_7202_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_7193_, v_i_7194_, v_stop_7195_, v___y_7202_);
    return v___x_7204_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(
    mut v_as_7205_: *mut crate::leanh::LeanObject,
    mut v_i_7206_: *mut crate::leanh::LeanObject,
    mut v_stop_7207_: *mut crate::leanh::LeanObject,
    mut v___y_7208_: *mut crate::leanh::LeanObject,
    mut v___y_7209_: *mut crate::leanh::LeanObject,
    mut v___y_7210_: *mut crate::leanh::LeanObject,
    mut v___y_7211_: *mut crate::leanh::LeanObject,
    mut v___y_7212_: *mut crate::leanh::LeanObject,
    mut v___y_7213_: *mut crate::leanh::LeanObject,
    mut v___y_7214_: *mut crate::leanh::LeanObject,
    mut v___y_7215_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7216_: usize = 0;
    let mut v_stop_boxed_7217_: usize = 0;
    let mut v_res_7218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7216_ = crate::leanh::lean_unbox_usize(v_i_7206_);
    crate::leanh::lean_dec(v_i_7206_);
    v_stop_boxed_7217_ = crate::leanh::lean_unbox_usize(v_stop_7207_);
    crate::leanh::lean_dec(v_stop_7207_);
    v_res_7218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_7205_, v_i_boxed_7216_, v_stop_boxed_7217_, v___y_7208_, v___y_7209_, v___y_7210_, v___y_7211_, v___y_7212_, v___y_7213_, v___y_7214_);
    crate::leanh::lean_dec(v___y_7214_);
    crate::leanh::lean_dec_ref(v___y_7213_);
    crate::leanh::lean_dec(v___y_7212_);
    crate::leanh::lean_dec_ref(v___y_7211_);
    crate::leanh::lean_dec_ref(v___y_7210_);
    crate::leanh::lean_dec(v___y_7209_);
    crate::leanh::lean_dec_ref(v___y_7208_);
    crate::leanh::lean_dec_ref(v_as_7205_);
    return v_res_7218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(
    mut v_as_7219_: *mut crate::leanh::LeanObject,
    mut v_i_7220_: usize,
    mut v_stop_7221_: usize,
    mut v_b_7222_: *mut crate::leanh::LeanObject,
    mut v___y_7223_: *mut crate::leanh::LeanObject,
    mut v___y_7224_: *mut crate::leanh::LeanObject,
    mut v___y_7225_: *mut crate::leanh::LeanObject,
    mut v___y_7226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_7219_, v_i_7220_, v_stop_7221_, v_b_7222_, v___y_7224_);
    return v___x_7228_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(
    mut v_as_7229_: *mut crate::leanh::LeanObject,
    mut v_i_7230_: *mut crate::leanh::LeanObject,
    mut v_stop_7231_: *mut crate::leanh::LeanObject,
    mut v_b_7232_: *mut crate::leanh::LeanObject,
    mut v___y_7233_: *mut crate::leanh::LeanObject,
    mut v___y_7234_: *mut crate::leanh::LeanObject,
    mut v___y_7235_: *mut crate::leanh::LeanObject,
    mut v___y_7236_: *mut crate::leanh::LeanObject,
    mut v___y_7237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7238_: usize = 0;
    let mut v_stop_boxed_7239_: usize = 0;
    let mut v_res_7240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7238_ = crate::leanh::lean_unbox_usize(v_i_7230_);
    crate::leanh::lean_dec(v_i_7230_);
    v_stop_boxed_7239_ = crate::leanh::lean_unbox_usize(v_stop_7231_);
    crate::leanh::lean_dec(v_stop_7231_);
    v_res_7240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_7229_, v_i_boxed_7238_, v_stop_boxed_7239_, v_b_7232_, v___y_7233_, v___y_7234_, v___y_7235_, v___y_7236_);
    crate::leanh::lean_dec(v___y_7236_);
    crate::leanh::lean_dec_ref(v___y_7235_);
    crate::leanh::lean_dec(v___y_7234_);
    crate::leanh::lean_dec_ref(v___y_7233_);
    crate::leanh::lean_dec_ref(v_as_7229_);
    return v_res_7240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(
    mut v_as_7241_: *mut crate::leanh::LeanObject,
    mut v_i_7242_: usize,
    mut v_stop_7243_: usize,
    mut v_b_7244_: *mut crate::leanh::LeanObject,
    mut v___y_7245_: *mut crate::leanh::LeanObject,
    mut v___y_7246_: *mut crate::leanh::LeanObject,
    mut v___y_7247_: *mut crate::leanh::LeanObject,
    mut v___y_7248_: *mut crate::leanh::LeanObject,
    mut v___y_7249_: *mut crate::leanh::LeanObject,
    mut v___y_7250_: *mut crate::leanh::LeanObject,
    mut v___y_7251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_7241_, v_i_7242_, v_stop_7243_, v_b_7244_, v___y_7248_, v___y_7249_, v___y_7250_, v___y_7251_);
    return v___x_7253_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(
    mut v_as_7254_: *mut crate::leanh::LeanObject,
    mut v_i_7255_: *mut crate::leanh::LeanObject,
    mut v_stop_7256_: *mut crate::leanh::LeanObject,
    mut v_b_7257_: *mut crate::leanh::LeanObject,
    mut v___y_7258_: *mut crate::leanh::LeanObject,
    mut v___y_7259_: *mut crate::leanh::LeanObject,
    mut v___y_7260_: *mut crate::leanh::LeanObject,
    mut v___y_7261_: *mut crate::leanh::LeanObject,
    mut v___y_7262_: *mut crate::leanh::LeanObject,
    mut v___y_7263_: *mut crate::leanh::LeanObject,
    mut v___y_7264_: *mut crate::leanh::LeanObject,
    mut v___y_7265_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7266_: usize = 0;
    let mut v_stop_boxed_7267_: usize = 0;
    let mut v_res_7268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7266_ = crate::leanh::lean_unbox_usize(v_i_7255_);
    crate::leanh::lean_dec(v_i_7255_);
    v_stop_boxed_7267_ = crate::leanh::lean_unbox_usize(v_stop_7256_);
    crate::leanh::lean_dec(v_stop_7256_);
    v_res_7268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_7254_, v_i_boxed_7266_, v_stop_boxed_7267_, v_b_7257_, v___y_7258_, v___y_7259_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_);
    crate::leanh::lean_dec(v___y_7264_);
    crate::leanh::lean_dec_ref(v___y_7263_);
    crate::leanh::lean_dec(v___y_7262_);
    crate::leanh::lean_dec_ref(v___y_7261_);
    crate::leanh::lean_dec_ref(v___y_7260_);
    crate::leanh::lean_dec(v___y_7259_);
    crate::leanh::lean_dec_ref(v___y_7258_);
    crate::leanh::lean_dec_ref(v_as_7254_);
    return v_res_7268_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(
    mut v_as_7269_: *mut crate::leanh::LeanObject,
    mut v_i_7270_: usize,
    mut v_stop_7271_: usize,
    mut v_b_7272_: *mut crate::leanh::LeanObject,
    mut v___y_7273_: *mut crate::leanh::LeanObject,
    mut v___y_7274_: *mut crate::leanh::LeanObject,
    mut v___y_7275_: *mut crate::leanh::LeanObject,
    mut v___y_7276_: *mut crate::leanh::LeanObject,
    mut v___y_7277_: *mut crate::leanh::LeanObject,
    mut v___y_7278_: *mut crate::leanh::LeanObject,
    mut v___y_7279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_7269_, v_i_7270_, v_stop_7271_, v_b_7272_, v___y_7277_);
    return v___x_7281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(
    mut v_as_7282_: *mut crate::leanh::LeanObject,
    mut v_i_7283_: *mut crate::leanh::LeanObject,
    mut v_stop_7284_: *mut crate::leanh::LeanObject,
    mut v_b_7285_: *mut crate::leanh::LeanObject,
    mut v___y_7286_: *mut crate::leanh::LeanObject,
    mut v___y_7287_: *mut crate::leanh::LeanObject,
    mut v___y_7288_: *mut crate::leanh::LeanObject,
    mut v___y_7289_: *mut crate::leanh::LeanObject,
    mut v___y_7290_: *mut crate::leanh::LeanObject,
    mut v___y_7291_: *mut crate::leanh::LeanObject,
    mut v___y_7292_: *mut crate::leanh::LeanObject,
    mut v___y_7293_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7294_: usize = 0;
    let mut v_stop_boxed_7295_: usize = 0;
    let mut v_res_7296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7294_ = crate::leanh::lean_unbox_usize(v_i_7283_);
    crate::leanh::lean_dec(v_i_7283_);
    v_stop_boxed_7295_ = crate::leanh::lean_unbox_usize(v_stop_7284_);
    crate::leanh::lean_dec(v_stop_7284_);
    v_res_7296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_7282_, v_i_boxed_7294_, v_stop_boxed_7295_, v_b_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_);
    crate::leanh::lean_dec(v___y_7292_);
    crate::leanh::lean_dec_ref(v___y_7291_);
    crate::leanh::lean_dec(v___y_7290_);
    crate::leanh::lean_dec_ref(v___y_7289_);
    crate::leanh::lean_dec_ref(v___y_7288_);
    crate::leanh::lean_dec(v___y_7287_);
    crate::leanh::lean_dec_ref(v___y_7286_);
    crate::leanh::lean_dec_ref(v_as_7282_);
    return v_res_7296_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(
    mut v_as_7297_: *mut crate::leanh::LeanObject,
    mut v_i_7298_: usize,
    mut v_stop_7299_: usize,
    mut v___y_7300_: *mut crate::leanh::LeanObject,
    mut v___y_7301_: *mut crate::leanh::LeanObject,
    mut v___y_7302_: *mut crate::leanh::LeanObject,
    mut v___y_7303_: *mut crate::leanh::LeanObject,
    mut v___y_7304_: *mut crate::leanh::LeanObject,
    mut v___y_7305_: *mut crate::leanh::LeanObject,
    mut v___y_7306_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7308_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_7297_, v_i_7298_, v_stop_7299_, v___y_7301_);
    return v___x_7308_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(
    mut v_as_7309_: *mut crate::leanh::LeanObject,
    mut v_i_7310_: *mut crate::leanh::LeanObject,
    mut v_stop_7311_: *mut crate::leanh::LeanObject,
    mut v___y_7312_: *mut crate::leanh::LeanObject,
    mut v___y_7313_: *mut crate::leanh::LeanObject,
    mut v___y_7314_: *mut crate::leanh::LeanObject,
    mut v___y_7315_: *mut crate::leanh::LeanObject,
    mut v___y_7316_: *mut crate::leanh::LeanObject,
    mut v___y_7317_: *mut crate::leanh::LeanObject,
    mut v___y_7318_: *mut crate::leanh::LeanObject,
    mut v___y_7319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_7320_: usize = 0;
    let mut v_stop_boxed_7321_: usize = 0;
    let mut v_res_7322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7320_ = crate::leanh::lean_unbox_usize(v_i_7310_);
    crate::leanh::lean_dec(v_i_7310_);
    v_stop_boxed_7321_ = crate::leanh::lean_unbox_usize(v_stop_7311_);
    crate::leanh::lean_dec(v_stop_7311_);
    v_res_7322_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_7309_, v_i_boxed_7320_, v_stop_boxed_7321_, v___y_7312_, v___y_7313_, v___y_7314_, v___y_7315_, v___y_7316_, v___y_7317_, v___y_7318_);
    crate::leanh::lean_dec(v___y_7318_);
    crate::leanh::lean_dec_ref(v___y_7317_);
    crate::leanh::lean_dec(v___y_7316_);
    crate::leanh::lean_dec_ref(v___y_7315_);
    crate::leanh::lean_dec_ref(v___y_7314_);
    crate::leanh::lean_dec(v___y_7313_);
    crate::leanh::lean_dec_ref(v___y_7312_);
    crate::leanh::lean_dec_ref(v_as_7309_);
    return v_res_7322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(
    mut v_as_7323_: *mut crate::leanh::LeanObject,
    mut v_sz_7324_: usize,
    mut v_i_7325_: usize,
    mut v_b_7326_: *mut crate::leanh::LeanObject,
    mut v___y_7327_: *mut crate::leanh::LeanObject,
    mut v___y_7328_: *mut crate::leanh::LeanObject,
    mut v___y_7329_: *mut crate::leanh::LeanObject,
    mut v___y_7330_: *mut crate::leanh::LeanObject,
    mut v___y_7331_: *mut crate::leanh::LeanObject,
    mut v___y_7332_: *mut crate::leanh::LeanObject,
    mut v___y_7333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_7323_, v_sz_7324_, v_i_7325_, v_b_7326_, v___y_7328_);
    return v___x_7335_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(
    mut v_as_7336_: *mut crate::leanh::LeanObject,
    mut v_sz_7337_: *mut crate::leanh::LeanObject,
    mut v_i_7338_: *mut crate::leanh::LeanObject,
    mut v_b_7339_: *mut crate::leanh::LeanObject,
    mut v___y_7340_: *mut crate::leanh::LeanObject,
    mut v___y_7341_: *mut crate::leanh::LeanObject,
    mut v___y_7342_: *mut crate::leanh::LeanObject,
    mut v___y_7343_: *mut crate::leanh::LeanObject,
    mut v___y_7344_: *mut crate::leanh::LeanObject,
    mut v___y_7345_: *mut crate::leanh::LeanObject,
    mut v___y_7346_: *mut crate::leanh::LeanObject,
    mut v___y_7347_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_7348_: usize = 0;
    let mut v_i_boxed_7349_: usize = 0;
    let mut v_res_7350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7348_ = crate::leanh::lean_unbox_usize(v_sz_7337_);
    crate::leanh::lean_dec(v_sz_7337_);
    v_i_boxed_7349_ = crate::leanh::lean_unbox_usize(v_i_7338_);
    crate::leanh::lean_dec(v_i_7338_);
    v_res_7350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_7336_, v_sz_boxed_7348_, v_i_boxed_7349_, v_b_7339_, v___y_7340_, v___y_7341_, v___y_7342_, v___y_7343_, v___y_7344_, v___y_7345_, v___y_7346_);
    crate::leanh::lean_dec(v___y_7346_);
    crate::leanh::lean_dec_ref(v___y_7345_);
    crate::leanh::lean_dec(v___y_7344_);
    crate::leanh::lean_dec_ref(v___y_7343_);
    crate::leanh::lean_dec_ref(v___y_7342_);
    crate::leanh::lean_dec(v___y_7341_);
    crate::leanh::lean_dec_ref(v___y_7340_);
    crate::leanh::lean_dec_ref(v_as_7336_);
    return v_res_7350_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(
    mut v_00_u03b2_7351_: *mut crate::leanh::LeanObject,
    mut v_x_7352_: *mut crate::leanh::LeanObject,
    mut v_x_7353_: usize,
    mut v_x_7354_: usize,
    mut v_x_7355_: *mut crate::leanh::LeanObject,
    mut v_x_7356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_7352_, v_x_7353_, v_x_7354_, v_x_7355_, v_x_7356_);
    return v___x_7357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_7358_: *mut crate::leanh::LeanObject,
    mut v_x_7359_: *mut crate::leanh::LeanObject,
    mut v_x_7360_: *mut crate::leanh::LeanObject,
    mut v_x_7361_: *mut crate::leanh::LeanObject,
    mut v_x_7362_: *mut crate::leanh::LeanObject,
    mut v_x_7363_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_51443__boxed_7364_: usize = 0;
    let mut v_x_51444__boxed_7365_: usize = 0;
    let mut v_res_7366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_51443__boxed_7364_ = crate::leanh::lean_unbox_usize(v_x_7360_);
    crate::leanh::lean_dec(v_x_7360_);
    v_x_51444__boxed_7365_ = crate::leanh::lean_unbox_usize(v_x_7361_);
    crate::leanh::lean_dec(v_x_7361_);
    v_res_7366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_7358_, v_x_7359_, v_x_51443__boxed_7364_, v_x_51444__boxed_7365_, v_x_7362_, v_x_7363_);
    return v_res_7366_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(
    mut v_pu_7367_: u8,
    mut v_t_7368_: u8,
    mut v_i_7369_: *mut crate::leanh::LeanObject,
    mut v_as_7370_: *mut crate::leanh::LeanObject,
    mut v___y_7371_: *mut crate::leanh::LeanObject,
    mut v___y_7372_: *mut crate::leanh::LeanObject,
    mut v___y_7373_: *mut crate::leanh::LeanObject,
    mut v___y_7374_: *mut crate::leanh::LeanObject,
    mut v___y_7375_: *mut crate::leanh::LeanObject,
    mut v___y_7376_: *mut crate::leanh::LeanObject,
    mut v___y_7377_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7379_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_7367_, v_t_7368_, v_i_7369_, v_as_7370_, v___y_7372_, v___y_7375_);
    return v___x_7379_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(
    mut v_pu_7380_: *mut crate::leanh::LeanObject,
    mut v_t_7381_: *mut crate::leanh::LeanObject,
    mut v_i_7382_: *mut crate::leanh::LeanObject,
    mut v_as_7383_: *mut crate::leanh::LeanObject,
    mut v___y_7384_: *mut crate::leanh::LeanObject,
    mut v___y_7385_: *mut crate::leanh::LeanObject,
    mut v___y_7386_: *mut crate::leanh::LeanObject,
    mut v___y_7387_: *mut crate::leanh::LeanObject,
    mut v___y_7388_: *mut crate::leanh::LeanObject,
    mut v___y_7389_: *mut crate::leanh::LeanObject,
    mut v___y_7390_: *mut crate::leanh::LeanObject,
    mut v___y_7391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_7392_: u8 = 0;
    let mut v_t_boxed_7393_: u8 = 0;
    let mut v_res_7394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_7392_ = (crate::leanh::lean_unbox(v_pu_7380_) as u8);
    v_t_boxed_7393_ = (crate::leanh::lean_unbox(v_t_7381_) as u8);
    v_res_7394_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_7392_, v_t_boxed_7393_, v_i_7382_, v_as_7383_, v___y_7384_, v___y_7385_, v___y_7386_, v___y_7387_, v___y_7388_, v___y_7389_, v___y_7390_);
    crate::leanh::lean_dec(v___y_7390_);
    crate::leanh::lean_dec_ref(v___y_7389_);
    crate::leanh::lean_dec(v___y_7388_);
    crate::leanh::lean_dec_ref(v___y_7387_);
    crate::leanh::lean_dec_ref(v___y_7386_);
    crate::leanh::lean_dec(v___y_7385_);
    crate::leanh::lean_dec_ref(v___y_7384_);
    return v_res_7394_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(
    mut v_00_u03b2_7395_: *mut crate::leanh::LeanObject,
    mut v_n_7396_: *mut crate::leanh::LeanObject,
    mut v_k_7397_: *mut crate::leanh::LeanObject,
    mut v_v_7398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7399_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_7396_, v_k_7397_, v_v_7398_);
    return v___x_7399_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(
    mut v_00_u03b2_7400_: *mut crate::leanh::LeanObject,
    mut v_depth_7401_: usize,
    mut v_keys_7402_: *mut crate::leanh::LeanObject,
    mut v_vals_7403_: *mut crate::leanh::LeanObject,
    mut v_heq_7404_: *mut crate::leanh::LeanObject,
    mut v_i_7405_: *mut crate::leanh::LeanObject,
    mut v_entries_7406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_7401_, v_keys_7402_, v_vals_7403_, v_i_7405_, v_entries_7406_);
    return v___x_7407_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(
    mut v_00_u03b2_7408_: *mut crate::leanh::LeanObject,
    mut v_depth_7409_: *mut crate::leanh::LeanObject,
    mut v_keys_7410_: *mut crate::leanh::LeanObject,
    mut v_vals_7411_: *mut crate::leanh::LeanObject,
    mut v_heq_7412_: *mut crate::leanh::LeanObject,
    mut v_i_7413_: *mut crate::leanh::LeanObject,
    mut v_entries_7414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_7415_: usize = 0;
    let mut v_res_7416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_7415_ = crate::leanh::lean_unbox_usize(v_depth_7409_);
    crate::leanh::lean_dec(v_depth_7409_);
    v_res_7416_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_7408_, v_depth_boxed_7415_, v_keys_7410_, v_vals_7411_, v_heq_7412_, v_i_7413_, v_entries_7414_);
    crate::leanh::lean_dec_ref(v_vals_7411_);
    crate::leanh::lean_dec_ref(v_keys_7410_);
    return v_res_7416_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(
    mut v_00_u03b2_7417_: *mut crate::leanh::LeanObject,
    mut v_x_7418_: *mut crate::leanh::LeanObject,
    mut v_x_7419_: *mut crate::leanh::LeanObject,
    mut v_x_7420_: *mut crate::leanh::LeanObject,
    mut v_x_7421_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7422_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_7418_, v_x_7419_, v_x_7420_, v_x_7421_);
    return v___x_7422_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_Main(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_Main(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
}
