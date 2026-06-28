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
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_9, lean_box,
    lean_closure_set, lean_ctor_get, lean_ctor_get_uint8, lean_ctor_get_uint64, lean_ctor_set,
    lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_inc, lean_inc_n, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_uint64_once,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat, lean_usize_once,
};
static mut l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__3_value)
                as *mut LeanObject,
            12317437071847932413 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value: LeanStringObject<3> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__0_value)
                as *mut LeanObject,
            7699194985028780469 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___closed__1_value)
        as *mut LeanObject;
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__2_value: LeanStringObject<34> =
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
            117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97,
            115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__1_value: LeanStringObject<68> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__0_value: LeanStringObject<25> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__0_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__3_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value: LeanStringObject<4> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__0_value)
                as *mut LeanObject,
            12958253247387092313 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_simp___closed__4_value: LeanStringObject<10> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_simp___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simp___closed__4_value) as *mut LeanObject;
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0()
-> *mut LeanObject {
    let mut v___x_3712_: u8 = 0;
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    v___x_3712_ = 0;
    v___x_3713_ = l_Lean_Compiler_LCNF_instInhabitedAlt_default__1(v___x_3712_);
    return v___x_3713_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(
    mut v_c_3714_: *mut LeanObject,
) -> u8 {
    let mut v_k_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3723_: u8 = 0;
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3727_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_c_3714_) {
                0 => {
                    v_k_3715_ = lean_ctor_get(v_c_3714_, 1);
                    v_c_3714_ = v_k_3715_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_k_3717_ = lean_ctor_get(v_c_3714_, 1);
                    v_c_3714_ = v_k_3717_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_3719_ = lean_ctor_get(v_c_3714_, 0);
                    v_alts_3720_ = lean_ctor_get(v_cases_3719_, 3);
                    v___x_3721_ = lean_array_get_size(v_alts_3720_);
                    v___x_3722_ = lean_unsigned_to_nat(1);
                    v___x_3723_ = lean_nat_dec_eq(v___x_3721_, v___x_3722_);
                    if v___x_3723_ == 0 {
                        return v___x_3723_;
                    } else {
                        v___x_3724_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___closed__0);
                        v___x_3725_ = lean_unsigned_to_nat(0);
                        v___x_3726_ =
                            lean_array_get_borrowed(v___x_3724_, v_alts_3720_, v___x_3725_);
                        match lean_obj_tag(v___x_3726_) {
                            0 => {
                                v_code_3727_ = lean_ctor_get(v___x_3726_, 2);
                                v_c_3714_ = v_code_3727_;
                                state = 0;
                                continue;
                            }
                            1 => {
                                v_code_3729_ = lean_ctor_get(v___x_3726_, 1);
                                v_c_3714_ = v_code_3729_;
                                state = 0;
                                continue;
                            }
                            _ => {
                                v_code_3731_ = lean_ctor_get(v___x_3726_, 0);
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
    mut v_c_3735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3736_: u8 = 0;
    let mut v_r_3737_: *mut LeanObject = core::ptr::null_mut();
    v_res_3736_ =
        l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(
            v_c_3735_,
        );
    lean_dec_ref(v_c_3735_);
    v_r_3737_ = lean_box((v_res_3736_) as usize);
    return v_r_3737_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(
    mut v_c_3738_: *mut LeanObject,
) -> u8 {
    let mut v___x_3739_: u8 = 0;
    v___x_3739_ =
        l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(
            v_c_3738_,
        );
    return v___x_3739_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(
    mut v_c_3740_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3741_: u8 = 0;
    let mut v_r_3742_: *mut LeanObject = core::ptr::null_mut();
    v_res_3741_ =
        l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(
            v_c_3740_,
        );
    lean_dec_ref(v_c_3740_);
    v_r_3742_ = lean_box((v_res_3741_) as usize);
    return v_r_3742_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(
    mut v_a_3743_: *mut LeanObject,
    mut v_x_3744_: *mut LeanObject,
) -> u8 {
    let mut v___x_3745_: u8 = 0;
    let mut v_key_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3744_) == 0 {
                    v___x_3745_ = 0;
                    return v___x_3745_;
                } else {
                    v_key_3746_ = lean_ctor_get(v_x_3744_, 0);
                    v_tail_3747_ = lean_ctor_get(v_x_3744_, 2);
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
    mut v_a_3750_: *mut LeanObject,
    mut v_x_3751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3752_: u8 = 0;
    let mut v_r_3753_: *mut LeanObject = core::ptr::null_mut();
    v_res_3752_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_3750_, v_x_3751_);
    lean_dec(v_x_3751_);
    lean_dec(v_a_3750_);
    v_r_3753_ = lean_box((v_res_3752_) as usize);
    return v_r_3753_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(
    mut v_x_3754_: *mut LeanObject,
    mut v_x_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3761_: u8 = 0;
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3781_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3755_) == 0 {
                    return v_x_3754_;
                } else {
                    v_key_3756_ = lean_ctor_get(v_x_3755_, 0);
                    v_value_3757_ = lean_ctor_get(v_x_3755_, 1);
                    v_tail_3758_ = lean_ctor_get(v_x_3755_, 2);
                    v_isSharedCheck_3781_ = (!lean_is_exclusive(v_x_3755_)) as u8;
                    if v_isSharedCheck_3781_ == 0 {
                        v___x_3760_ = v_x_3755_;
                        v_isShared_3761_ = v_isSharedCheck_3781_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3758_);
                        lean_inc(v_value_3757_);
                        lean_inc(v_key_3756_);
                        lean_dec(v_x_3755_);
                        v___x_3760_ = lean_box(0);
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
                lean_inc(v___x_3775_);
                if v_isShared_3761_ == 0 {
                    lean_ctor_set(v___x_3760_, 2, v___x_3775_);
                    v___x_3777_ = v___x_3760_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3780_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 0, v_key_3756_);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 1, v_value_3757_);
                    lean_ctor_set(v_reuseFailAlloc_3780_, 2, v___x_3775_);
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
    mut v_i_3782_: *mut LeanObject,
    mut v_source_3783_: *mut LeanObject,
    mut v_target_3784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3786_: u8 = 0;
    let mut v_es_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3785_ = lean_array_get_size(v_source_3783_);
                v___x_3786_ = lean_nat_dec_lt(v_i_3782_, v___x_3785_);
                if v___x_3786_ == 0 {
                    lean_dec_ref(v_source_3783_);
                    lean_dec(v_i_3782_);
                    return v_target_3784_;
                } else {
                    v_es_3787_ = lean_array_fget(v_source_3783_, v_i_3782_);
                    v___x_3788_ = lean_box(0);
                    v_source_3789_ = lean_array_fset(v_source_3783_, v_i_3782_, v___x_3788_);
                    v_target_3790_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_target_3784_, v_es_3787_);
                    v___x_3791_ = lean_unsigned_to_nat(1);
                    v___x_3792_ = lean_nat_add(v_i_3782_, v___x_3791_);
                    lean_dec(v_i_3782_);
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
    mut v_data_3794_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    v___x_3795_ = lean_array_get_size(v_data_3794_);
    v___x_3796_ = lean_unsigned_to_nat(2);
    v_nbuckets_3797_ = lean_nat_mul(v___x_3795_, v___x_3796_);
    v___x_3798_ = lean_unsigned_to_nat(0);
    v___x_3799_ = lean_box(0);
    v___x_3800_ = lean_mk_array(v_nbuckets_3797_, v___x_3799_);
    v___x_3801_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v___x_3798_, v_data_3794_, v___x_3800_);
    return v___x_3801_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(
    mut v_a_3802_: *mut LeanObject,
    mut v_b_3803_: *mut LeanObject,
    mut v_x_3804_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3810_: u8 = 0;
    let mut v___x_3811_: u8 = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3819_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3804_) == 0 {
                    lean_dec(v_b_3803_);
                    lean_dec(v_a_3802_);
                    return v_x_3804_;
                } else {
                    v_key_3805_ = lean_ctor_get(v_x_3804_, 0);
                    v_value_3806_ = lean_ctor_get(v_x_3804_, 1);
                    v_tail_3807_ = lean_ctor_get(v_x_3804_, 2);
                    v_isSharedCheck_3819_ = (!lean_is_exclusive(v_x_3804_)) as u8;
                    if v_isSharedCheck_3819_ == 0 {
                        v___x_3809_ = v_x_3804_;
                        v_isShared_3810_ = v_isSharedCheck_3819_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3807_);
                        lean_inc(v_value_3806_);
                        lean_inc(v_key_3805_);
                        lean_dec(v_x_3804_);
                        v___x_3809_ = lean_box(0);
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
                        lean_ctor_set(v___x_3809_, 2, v___x_3812_);
                        v___x_3814_ = v___x_3809_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3815_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_key_3805_);
                        lean_ctor_set(v_reuseFailAlloc_3815_, 1, v_value_3806_);
                        lean_ctor_set(v_reuseFailAlloc_3815_, 2, v___x_3812_);
                        v___x_3814_ = v_reuseFailAlloc_3815_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3806_);
                    lean_dec(v_key_3805_);
                    if v_isShared_3810_ == 0 {
                        lean_ctor_set(v___x_3809_, 1, v_b_3803_);
                        lean_ctor_set(v___x_3809_, 0, v_a_3802_);
                        v___x_3817_ = v___x_3809_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3818_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3818_, 0, v_a_3802_);
                        lean_ctor_set(v_reuseFailAlloc_3818_, 1, v_b_3803_);
                        lean_ctor_set(v_reuseFailAlloc_3818_, 2, v_tail_3807_);
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
    mut v_m_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_b_3822_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3827_: u8 = 0;
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: u8 = 0;
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: u8 = 0;
    let mut v_val_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3867_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3823_ = lean_ctor_get(v_m_3820_, 0);
                v_buckets_3824_ = lean_ctor_get(v_m_3820_, 1);
                v_isSharedCheck_3867_ = (!lean_is_exclusive(v_m_3820_)) as u8;
                if v_isSharedCheck_3867_ == 0 {
                    v___x_3826_ = v_m_3820_;
                    v_isShared_3827_ = v_isSharedCheck_3867_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3824_);
                    lean_inc(v_size_3823_);
                    lean_dec(v_m_3820_);
                    v___x_3826_ = lean_box(0);
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
                    v___x_3843_ = lean_unsigned_to_nat(1);
                    v_size_x27_3844_ = lean_nat_add(v_size_3823_, v___x_3843_);
                    lean_dec(v_size_3823_);
                    lean_inc(v_bkt_3841_);
                    v___x_3845_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3845_, 0, v_a_3821_);
                    lean_ctor_set(v___x_3845_, 1, v_b_3822_);
                    lean_ctor_set(v___x_3845_, 2, v_bkt_3841_);
                    v_buckets_x27_3846_ =
                        lean_array_uset(v_buckets_3824_, v___x_3840_, v___x_3845_);
                    v___x_3847_ = lean_unsigned_to_nat(4);
                    v___x_3848_ = lean_nat_mul(v_size_x27_3844_, v___x_3847_);
                    v___x_3849_ = lean_unsigned_to_nat(3);
                    v___x_3850_ = lean_nat_div(v___x_3848_, v___x_3849_);
                    lean_dec(v___x_3848_);
                    v___x_3851_ = lean_array_get_size(v_buckets_x27_3846_);
                    v___x_3852_ = lean_nat_dec_le(v___x_3850_, v___x_3851_);
                    lean_dec(v___x_3850_);
                    if v___x_3852_ == 0 {
                        v_val_3853_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_buckets_x27_3846_);
                        if v_isShared_3827_ == 0 {
                            lean_ctor_set(v___x_3826_, 1, v_val_3853_);
                            lean_ctor_set(v___x_3826_, 0, v_size_x27_3844_);
                            v___x_3855_ = v___x_3826_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3856_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3856_, 0, v_size_x27_3844_);
                            lean_ctor_set(v_reuseFailAlloc_3856_, 1, v_val_3853_);
                            v___x_3855_ = v_reuseFailAlloc_3856_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3827_ == 0 {
                            lean_ctor_set(v___x_3826_, 1, v_buckets_x27_3846_);
                            lean_ctor_set(v___x_3826_, 0, v_size_x27_3844_);
                            v___x_3858_ = v___x_3826_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3859_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_size_x27_3844_);
                            lean_ctor_set(v_reuseFailAlloc_3859_, 1, v_buckets_x27_3846_);
                            v___x_3858_ = v_reuseFailAlloc_3859_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3841_);
                    v___x_3860_ = lean_box(0);
                    v_buckets_x27_3861_ =
                        lean_array_uset(v_buckets_3824_, v___x_3840_, v___x_3860_);
                    v___x_3862_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_3821_, v_b_3822_, v_bkt_3841_);
                    v___x_3863_ = lean_array_uset(v_buckets_x27_3861_, v___x_3840_, v___x_3862_);
                    if v_isShared_3827_ == 0 {
                        lean_ctor_set(v___x_3826_, 1, v___x_3863_);
                        v___x_3865_ = v___x_3826_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3866_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3866_, 0, v_size_3823_);
                        lean_ctor_set(v_reuseFailAlloc_3866_, 1, v___x_3863_);
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
    mut v_as_3868_: *mut LeanObject,
    mut v_sz_3869_: usize,
    mut v_i_3870_: usize,
    mut v_b_3871_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3873_: u8 = 0;
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3879_: u8 = 0;
    let mut v_array_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: u8 = 0;
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3890_: u8 = 0;
    let mut v_a_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: usize = 0;
    let mut v___x_3902_: usize = 0;
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v_unused_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3873_ = lean_usize_dec_lt(v_i_3870_, v_sz_3869_);
                if v___x_3873_ == 0 {
                    v___x_3874_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3874_, 0, v_b_3871_);
                    return v___x_3874_;
                } else {
                    v_snd_3875_ = lean_ctor_get(v_b_3871_, 1);
                    v_fst_3876_ = lean_ctor_get(v_b_3871_, 0);
                    v_isSharedCheck_3910_ = (!lean_is_exclusive(v_b_3871_)) as u8;
                    if v_isSharedCheck_3910_ == 0 {
                        v___x_3878_ = v_b_3871_;
                        v_isShared_3879_ = v_isSharedCheck_3910_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_3875_);
                        lean_inc(v_fst_3876_);
                        lean_dec(v_b_3871_);
                        v___x_3878_ = lean_box(0);
                        v_isShared_3879_ = v_isSharedCheck_3910_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_3880_ = lean_ctor_get(v_snd_3875_, 0);
                v_start_3881_ = lean_ctor_get(v_snd_3875_, 1);
                v_stop_3882_ = lean_ctor_get(v_snd_3875_, 2);
                v___x_3883_ = lean_nat_dec_lt(v_start_3881_, v_stop_3882_);
                if v___x_3883_ == 0 {
                    if v_isShared_3879_ == 0 {
                        v___x_3885_ = v___x_3878_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3887_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3887_, 0, v_fst_3876_);
                        lean_ctor_set(v_reuseFailAlloc_3887_, 1, v_snd_3875_);
                        v___x_3885_ = v_reuseFailAlloc_3887_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc(v_stop_3882_);
                    lean_inc(v_start_3881_);
                    lean_inc_ref(v_array_3880_);
                    v_isSharedCheck_3906_ = (!lean_is_exclusive(v_snd_3875_)) as u8;
                    if v_isSharedCheck_3906_ == 0 {
                        v_unused_3907_ = lean_ctor_get(v_snd_3875_, 2);
                        lean_dec(v_unused_3907_);
                        v_unused_3908_ = lean_ctor_get(v_snd_3875_, 1);
                        lean_dec(v_unused_3908_);
                        v_unused_3909_ = lean_ctor_get(v_snd_3875_, 0);
                        lean_dec(v_unused_3909_);
                        v___x_3889_ = v_snd_3875_;
                        v_isShared_3890_ = v_isSharedCheck_3906_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_snd_3875_);
                        v___x_3889_ = lean_box(0);
                        v_isShared_3890_ = v_isSharedCheck_3906_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3886_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3886_, 0, v___x_3885_);
                return v___x_3886_;
            }
            3 => {
                v_a_3891_ = lean_array_uget_borrowed(v_as_3868_, v_i_3870_);
                v_fvarId_3892_ = lean_ctor_get(v_a_3891_, 0);
                v___x_3893_ = lean_array_fget(v_array_3880_, v_start_3881_);
                v___x_3894_ = lean_unsigned_to_nat(1);
                v___x_3895_ = lean_nat_add(v_start_3881_, v___x_3894_);
                lean_dec(v_start_3881_);
                if v_isShared_3890_ == 0 {
                    lean_ctor_set(v___x_3889_, 1, v___x_3895_);
                    v___x_3897_ = v___x_3889_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3905_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3905_, 0, v_array_3880_);
                    lean_ctor_set(v_reuseFailAlloc_3905_, 1, v___x_3895_);
                    lean_ctor_set(v_reuseFailAlloc_3905_, 2, v_stop_3882_);
                    v___x_3897_ = v_reuseFailAlloc_3905_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_fvarId_3892_);
                v___x_3898_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_3876_, v_fvarId_3892_, v___x_3893_);
                if v_isShared_3879_ == 0 {
                    lean_ctor_set(v___x_3878_, 1, v___x_3897_);
                    lean_ctor_set(v___x_3878_, 0, v___x_3898_);
                    v___x_3900_ = v___x_3878_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v___x_3898_);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 1, v___x_3897_);
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
    mut v_as_3911_: *mut LeanObject,
    mut v_sz_3912_: *mut LeanObject,
    mut v_i_3913_: *mut LeanObject,
    mut v_b_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3916_: usize = 0;
    let mut v_i_boxed_3917_: usize = 0;
    let mut v_res_3918_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3916_ = lean_unbox_usize(v_sz_3912_);
    lean_dec(v_sz_3912_);
    v_i_boxed_3917_ = lean_unbox_usize(v_i_3913_);
    lean_dec(v_i_3913_);
    v_res_3918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_3911_, v_sz_boxed_3916_, v_i_boxed_3917_, v_b_3914_);
    lean_dec_ref(v_as_3911_);
    return v_res_3918_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(
    mut v_a_3919_: *mut LeanObject,
    mut v_b_3920_: *mut LeanObject,
    mut v___y_3921_: *mut LeanObject,
    mut v___y_3922_: *mut LeanObject,
    mut v___y_3923_: *mut LeanObject,
    mut v___y_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_3927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: u8 = 0;
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: u8 = 0;
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3964_: u8 = 0;
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3968_: u8 = 0;
    let mut v_a_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3972_: u8 = 0;
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut v_isSharedCheck_3977_: u8 = 0;
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_3926_ = lean_ctor_get(v_a_3919_, 0);
                v_start_3927_ = lean_ctor_get(v_a_3919_, 1);
                v_stop_3928_ = lean_ctor_get(v_a_3919_, 2);
                v_isSharedCheck_3978_ = (!lean_is_exclusive(v_a_3919_)) as u8;
                if v_isSharedCheck_3978_ == 0 {
                    v___x_3930_ = v_a_3919_;
                    v_isShared_3931_ = v_isSharedCheck_3978_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_3928_);
                    lean_inc(v_start_3927_);
                    lean_inc(v_array_3926_);
                    lean_dec(v_a_3919_);
                    v___x_3930_ = lean_box(0);
                    v_isShared_3931_ = v_isSharedCheck_3978_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3932_ = lean_nat_dec_lt(v_start_3927_, v_stop_3928_);
                if v___x_3932_ == 0 {
                    lean_del_object(v___x_3930_);
                    lean_dec(v_stop_3928_);
                    lean_dec(v_start_3927_);
                    lean_dec_ref(v_array_3926_);
                    v___x_3933_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3933_, 0, v_b_3920_);
                    return v___x_3933_;
                } else {
                    v_fst_3934_ = lean_ctor_get(v_b_3920_, 0);
                    v_snd_3935_ = lean_ctor_get(v_b_3920_, 1);
                    v_isSharedCheck_3977_ = (!lean_is_exclusive(v_b_3920_)) as u8;
                    if v_isSharedCheck_3977_ == 0 {
                        v___x_3937_ = v_b_3920_;
                        v_isShared_3938_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3935_);
                        lean_inc(v_fst_3934_);
                        lean_dec(v_b_3920_);
                        v___x_3937_ = lean_box(0);
                        v_isShared_3938_ = v_isSharedCheck_3977_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_3939_ = lean_array_fget_borrowed(v_array_3926_, v_start_3927_);
                v_fvarId_3940_ = lean_ctor_get(v___x_3939_, 0);
                lean_inc(v_fvarId_3940_);
                v_type_3941_ = lean_ctor_get(v___x_3939_, 2);
                v___x_3942_ = 0;
                lean_inc_ref(v_type_3941_);
                v___x_3943_ = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(
                    v___x_3942_,
                    v_type_3941_,
                    v_fst_3934_,
                    v___x_3932_,
                );
                if lean_obj_tag(v___x_3943_) == 0 {
                    v_a_3944_ = lean_ctor_get(v___x_3943_, 0);
                    lean_inc(v_a_3944_);
                    lean_dec_ref_known(v___x_3943_, 1);
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
                    if lean_obj_tag(v___x_3946_) == 0 {
                        v_a_3947_ = lean_ctor_get(v___x_3946_, 0);
                        lean_inc(v_a_3947_);
                        lean_dec_ref_known(v___x_3946_, 1);
                        v_fvarId_3948_ = lean_ctor_get(v_a_3947_, 0);
                        lean_inc(v_fvarId_3948_);
                        v___x_3949_ = lean_unsigned_to_nat(1);
                        v___x_3950_ = lean_nat_add(v_start_3927_, v___x_3949_);
                        lean_dec(v_start_3927_);
                        if v_isShared_3931_ == 0 {
                            lean_ctor_set(v___x_3930_, 1, v___x_3950_);
                            v___x_3952_ = v___x_3930_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3960_ = lean_alloc_ctor(0, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3960_, 0, v_array_3926_);
                            lean_ctor_set(v_reuseFailAlloc_3960_, 1, v___x_3950_);
                            lean_ctor_set(v_reuseFailAlloc_3960_, 2, v_stop_3928_);
                            v___x_3952_ = v_reuseFailAlloc_3960_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_fvarId_3940_);
                        lean_del_object(v___x_3937_);
                        lean_dec(v_snd_3935_);
                        lean_dec(v_fst_3934_);
                        lean_del_object(v___x_3930_);
                        lean_dec(v_stop_3928_);
                        lean_dec(v_start_3927_);
                        lean_dec_ref(v_array_3926_);
                        v_a_3961_ = lean_ctor_get(v___x_3946_, 0);
                        v_isSharedCheck_3968_ = (!lean_is_exclusive(v___x_3946_)) as u8;
                        if v_isSharedCheck_3968_ == 0 {
                            v___x_3963_ = v___x_3946_;
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3961_);
                            lean_dec(v___x_3946_);
                            v___x_3963_ = lean_box(0);
                            v_isShared_3964_ = v_isSharedCheck_3968_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_fvarId_3940_);
                    lean_del_object(v___x_3937_);
                    lean_dec(v_snd_3935_);
                    lean_dec(v_fst_3934_);
                    lean_del_object(v___x_3930_);
                    lean_dec(v_stop_3928_);
                    lean_dec(v_start_3927_);
                    lean_dec_ref(v_array_3926_);
                    v_a_3969_ = lean_ctor_get(v___x_3943_, 0);
                    v_isSharedCheck_3976_ = (!lean_is_exclusive(v___x_3943_)) as u8;
                    if v_isSharedCheck_3976_ == 0 {
                        v___x_3971_ = v___x_3943_;
                        v_isShared_3972_ = v_isSharedCheck_3976_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_3969_);
                        lean_dec(v___x_3943_);
                        v___x_3971_ = lean_box(0);
                        v_isShared_3972_ = v_isSharedCheck_3976_;
                        state = 7;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3953_ = lean_array_push(v_snd_3935_, v_a_3947_);
                v___x_3954_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3954_, 0, v_fvarId_3948_);
                v___x_3955_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_fst_3934_, v_fvarId_3940_, v___x_3954_);
                if v_isShared_3938_ == 0 {
                    lean_ctor_set(v___x_3937_, 1, v___x_3953_);
                    lean_ctor_set(v___x_3937_, 0, v___x_3955_);
                    v___x_3957_ = v___x_3937_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3959_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 0, v___x_3955_);
                    lean_ctor_set(v_reuseFailAlloc_3959_, 1, v___x_3953_);
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
                    v_reuseFailAlloc_3967_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3967_, 0, v_a_3961_);
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
                    v_reuseFailAlloc_3975_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3975_, 0, v_a_3969_);
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
    mut v_a_3979_: *mut LeanObject,
    mut v_b_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3986_: *mut LeanObject = core::ptr::null_mut();
    v_res_3986_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_3979_, v_b_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
    lean_dec(v___y_3984_);
    lean_dec_ref(v___y_3983_);
    lean_dec(v___y_3982_);
    lean_dec_ref(v___y_3981_);
    return v_res_3986_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0() -> *mut LeanObject
{
    let mut v___x_3987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    v___x_3987_ = lean_box(0);
    v___x_3988_ = lean_unsigned_to_nat(16);
    v___x_3989_ = lean_mk_array(v___x_3988_, v___x_3987_);
    return v___x_3989_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__1() -> *mut LeanObject
{
    let mut v___x_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_3992_: *mut LeanObject = core::ptr::null_mut();
    v___x_3990_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Simp_specializePartialApp___closed__0,
    );
    v___x_3991_ = lean_unsigned_to_nat(0);
    v_subst_3992_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v_subst_3992_, 0, v___x_3991_);
    lean_ctor_set(v_subst_3992_, 1, v___x_3990_);
    return v_subst_3992_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_specializePartialApp(
    mut v_info_3998_: *mut LeanObject,
    mut v_a_3999_: *mut LeanObject,
    mut v_a_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
    mut v_a_4003_: *mut LeanObject,
    mut v_a_4004_: *mut LeanObject,
    mut v_a_4005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_4007_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4015_: usize = 0;
    let mut v___x_4016_: usize = 0;
    let mut v___x_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4022_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_4025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4034_: u8 = 0;
    let mut v___x_4035_: u8 = 0;
    let mut v___x_4036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4044_: u8 = 0;
    let mut v___x_4046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4048_: u8 = 0;
    let mut v_a_4049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4052_: u8 = 0;
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4056_: u8 = 0;
    let mut v_a_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_reuseFailAlloc_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: u8 = 0;
    let mut v_isSharedCheck_4068_: u8 = 0;
    let mut v_unused_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4073_: u8 = 0;
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_4007_ = lean_ctor_get(v_info_3998_, 0);
                lean_inc_ref(v_params_4007_);
                v_value_4008_ = lean_ctor_get(v_info_3998_, 1);
                lean_inc_ref(v_value_4008_);
                v_args_4009_ = lean_ctor_get(v_info_3998_, 3);
                lean_inc_ref(v_args_4009_);
                lean_dec_ref(v_info_3998_);
                v___x_4010_ = lean_unsigned_to_nat(0);
                v_subst_4011_ = lean_obj_once(
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
                v___x_4014_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4014_, 0, v_subst_4011_);
                lean_ctor_set(v___x_4014_, 1, v___x_4013_);
                v_sz_4015_ = lean_array_size(v_params_4007_);
                v___x_4016_ = 0usize;
                v___x_4017_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_params_4007_, v_sz_4015_, v___x_4016_, v___x_4014_);
                if lean_obj_tag(v___x_4017_) == 0 {
                    v_a_4018_ = lean_ctor_get(v___x_4017_, 0);
                    lean_inc(v_a_4018_);
                    lean_dec_ref_known(v___x_4017_, 1);
                    v_fst_4019_ = lean_ctor_get(v_a_4018_, 0);
                    v_isSharedCheck_4068_ = (!lean_is_exclusive(v_a_4018_)) as u8;
                    if v_isSharedCheck_4068_ == 0 {
                        v_unused_4069_ = lean_ctor_get(v_a_4018_, 1);
                        lean_dec(v_unused_4069_);
                        v___x_4021_ = v_a_4018_;
                        v_isShared_4022_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fst_4019_);
                        lean_dec(v_a_4018_);
                        v___x_4021_ = lean_box(0);
                        v_isShared_4022_ = v_isSharedCheck_4068_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_value_4008_);
                    lean_dec_ref(v_params_4007_);
                    v_a_4070_ = lean_ctor_get(v___x_4017_, 0);
                    v_isSharedCheck_4077_ = (!lean_is_exclusive(v___x_4017_)) as u8;
                    if v_isSharedCheck_4077_ == 0 {
                        v___x_4072_ = v___x_4017_;
                        v_isShared_4073_ = v_isSharedCheck_4077_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4070_);
                        lean_dec(v___x_4017_);
                        v___x_4072_ = lean_box(0);
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
                    lean_ctor_set(v___x_4021_, 1, v___x_4023_);
                    v___x_4029_ = v___x_4021_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4065_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4065_, 0, v_fst_4019_);
                    lean_ctor_set(v_reuseFailAlloc_4065_, 1, v___x_4023_);
                    v___x_4029_ = v_reuseFailAlloc_4065_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4030_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v___x_4027_, v___x_4029_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_);
                if lean_obj_tag(v___x_4030_) == 0 {
                    v_a_4031_ = lean_ctor_get(v___x_4030_, 0);
                    lean_inc(v_a_4031_);
                    lean_dec_ref_known(v___x_4030_, 1);
                    v_fst_4032_ = lean_ctor_get(v_a_4031_, 0);
                    lean_inc(v_fst_4032_);
                    v_snd_4033_ = lean_ctor_get(v_a_4031_, 1);
                    lean_inc(v_snd_4033_);
                    lean_dec(v_a_4031_);
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
                    if lean_obj_tag(v___x_4036_) == 0 {
                        v_a_4037_ = lean_ctor_get(v___x_4036_, 0);
                        lean_inc_n(v_a_4037_, 2);
                        lean_dec_ref_known(v___x_4036_, 1);
                        v___x_4038_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(
                            v_a_4037_,
                            v___x_4035_,
                            v_a_4000_,
                            v_a_4002_,
                            v_a_4003_,
                            v_a_4004_,
                            v_a_4005_,
                        );
                        if lean_obj_tag(v___x_4038_) == 0 {
                            lean_dec_ref_known(v___x_4038_, 1);
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
                            lean_dec(v_a_4037_);
                            lean_dec(v_snd_4033_);
                            v_a_4041_ = lean_ctor_get(v___x_4038_, 0);
                            v_isSharedCheck_4048_ = (!lean_is_exclusive(v___x_4038_)) as u8;
                            if v_isSharedCheck_4048_ == 0 {
                                v___x_4043_ = v___x_4038_;
                                v_isShared_4044_ = v_isSharedCheck_4048_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_4041_);
                                lean_dec(v___x_4038_);
                                v___x_4043_ = lean_box(0);
                                v_isShared_4044_ = v_isSharedCheck_4048_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_4033_);
                        v_a_4049_ = lean_ctor_get(v___x_4036_, 0);
                        v_isSharedCheck_4056_ = (!lean_is_exclusive(v___x_4036_)) as u8;
                        if v_isSharedCheck_4056_ == 0 {
                            v___x_4051_ = v___x_4036_;
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4049_);
                            lean_dec(v___x_4036_);
                            v___x_4051_ = lean_box(0);
                            v_isShared_4052_ = v_isSharedCheck_4056_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_value_4008_);
                    v_a_4057_ = lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4064_ = (!lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4064_ == 0 {
                        v___x_4059_ = v___x_4030_;
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4057_);
                        lean_dec(v___x_4030_);
                        v___x_4059_ = lean_box(0);
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
                    v_reuseFailAlloc_4047_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4047_, 0, v_a_4041_);
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
                    v_reuseFailAlloc_4055_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4055_, 0, v_a_4049_);
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
                    v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
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
                    v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
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
    mut v_info_4078_: *mut LeanObject,
    mut v_a_4079_: *mut LeanObject,
    mut v_a_4080_: *mut LeanObject,
    mut v_a_4081_: *mut LeanObject,
    mut v_a_4082_: *mut LeanObject,
    mut v_a_4083_: *mut LeanObject,
    mut v_a_4084_: *mut LeanObject,
    mut v_a_4085_: *mut LeanObject,
    mut v_a_4086_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4087_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4085_);
    lean_dec_ref(v_a_4084_);
    lean_dec(v_a_4083_);
    lean_dec_ref(v_a_4082_);
    lean_dec_ref(v_a_4081_);
    lean_dec(v_a_4080_);
    lean_dec_ref(v_a_4079_);
    return v_res_4087_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(
    mut v_00_u03b2_4088_: *mut LeanObject,
    mut v_m_4089_: *mut LeanObject,
    mut v_a_4090_: *mut LeanObject,
    mut v_b_4091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4092_: *mut LeanObject = core::ptr::null_mut();
    v___x_4092_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_m_4089_, v_a_4090_, v_b_4091_);
    return v___x_4092_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(
    mut v_as_4093_: *mut LeanObject,
    mut v_sz_4094_: usize,
    mut v_i_4095_: usize,
    mut v_b_4096_: *mut LeanObject,
    mut v___y_4097_: *mut LeanObject,
    mut v___y_4098_: *mut LeanObject,
    mut v___y_4099_: *mut LeanObject,
    mut v___y_4100_: *mut LeanObject,
    mut v___y_4101_: *mut LeanObject,
    mut v___y_4102_: *mut LeanObject,
    mut v___y_4103_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    v___x_4105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___redArg(v_as_4093_, v_sz_4094_, v_i_4095_, v_b_4096_);
    return v___x_4105_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1___boxed(
    mut v_as_4106_: *mut LeanObject,
    mut v_sz_4107_: *mut LeanObject,
    mut v_i_4108_: *mut LeanObject,
    mut v_b_4109_: *mut LeanObject,
    mut v___y_4110_: *mut LeanObject,
    mut v___y_4111_: *mut LeanObject,
    mut v___y_4112_: *mut LeanObject,
    mut v___y_4113_: *mut LeanObject,
    mut v___y_4114_: *mut LeanObject,
    mut v___y_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4118_: usize = 0;
    let mut v_i_boxed_4119_: usize = 0;
    let mut v_res_4120_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4118_ = lean_unbox_usize(v_sz_4107_);
    lean_dec(v_sz_4107_);
    v_i_boxed_4119_ = lean_unbox_usize(v_i_4108_);
    lean_dec(v_i_4108_);
    v_res_4120_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__1(v_as_4106_, v_sz_boxed_4118_, v_i_boxed_4119_, v_b_4109_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_, v___y_4114_, v___y_4115_, v___y_4116_);
    lean_dec(v___y_4116_);
    lean_dec_ref(v___y_4115_);
    lean_dec(v___y_4114_);
    lean_dec_ref(v___y_4113_);
    lean_dec_ref(v___y_4112_);
    lean_dec(v___y_4111_);
    lean_dec_ref(v___y_4110_);
    lean_dec_ref(v_as_4106_);
    return v_res_4120_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2(
    mut v_inst_4121_: *mut LeanObject,
    mut v_R_4122_: *mut LeanObject,
    mut v_a_4123_: *mut LeanObject,
    mut v_b_4124_: *mut LeanObject,
    mut v_c_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
    mut v___y_4127_: *mut LeanObject,
    mut v___y_4128_: *mut LeanObject,
    mut v___y_4129_: *mut LeanObject,
    mut v___y_4130_: *mut LeanObject,
    mut v___y_4131_: *mut LeanObject,
    mut v___y_4132_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    v___x_4134_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___redArg(v_a_4123_, v_b_4124_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_);
    return v___x_4134_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__2___boxed(
    mut v_inst_4135_: *mut LeanObject,
    mut v_R_4136_: *mut LeanObject,
    mut v_a_4137_: *mut LeanObject,
    mut v_b_4138_: *mut LeanObject,
    mut v_c_4139_: *mut LeanObject,
    mut v___y_4140_: *mut LeanObject,
    mut v___y_4141_: *mut LeanObject,
    mut v___y_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4148_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4146_);
    lean_dec_ref(v___y_4145_);
    lean_dec(v___y_4144_);
    lean_dec_ref(v___y_4143_);
    lean_dec_ref(v___y_4142_);
    lean_dec(v___y_4141_);
    lean_dec_ref(v___y_4140_);
    return v_res_4148_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(
    mut v_00_u03b2_4149_: *mut LeanObject,
    mut v_a_4150_: *mut LeanObject,
    mut v_x_4151_: *mut LeanObject,
) -> u8 {
    let mut v___x_4152_: u8 = 0;
    v___x_4152_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___redArg(v_a_4150_, v_x_4151_);
    return v___x_4152_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0___boxed(
    mut v_00_u03b2_4153_: *mut LeanObject,
    mut v_a_4154_: *mut LeanObject,
    mut v_x_4155_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4156_: u8 = 0;
    let mut v_r_4157_: *mut LeanObject = core::ptr::null_mut();
    v_res_4156_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__0(v_00_u03b2_4153_, v_a_4154_, v_x_4155_);
    lean_dec(v_x_4155_);
    lean_dec(v_a_4154_);
    v_r_4157_ = lean_box((v_res_4156_) as usize);
    return v_r_4157_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1(
    mut v_00_u03b2_4158_: *mut LeanObject,
    mut v_data_4159_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4160_: *mut LeanObject = core::ptr::null_mut();
    v___x_4160_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1___redArg(v_data_4159_);
    return v___x_4160_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2(
    mut v_00_u03b2_4161_: *mut LeanObject,
    mut v_a_4162_: *mut LeanObject,
    mut v_b_4163_: *mut LeanObject,
    mut v_x_4164_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4165_: *mut LeanObject = core::ptr::null_mut();
    v___x_4165_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__2___redArg(v_a_4162_, v_b_4163_, v_x_4164_);
    return v___x_4165_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2(
    mut v_00_u03b2_4166_: *mut LeanObject,
    mut v_i_4167_: *mut LeanObject,
    mut v_source_4168_: *mut LeanObject,
    mut v_target_4169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    v___x_4170_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2___redArg(v_i_4167_, v_source_4168_, v_target_4169_);
    return v___x_4170_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5(
    mut v_00_u03b2_4171_: *mut LeanObject,
    mut v_x_4172_: *mut LeanObject,
    mut v_x_4173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    v___x_4174_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0_spec__1_spec__2_spec__5___redArg(v_x_4172_, v_x_4173_);
    return v___x_4174_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(
    mut v_fvarId_4175_: *mut LeanObject,
    mut v_args_4176_: *mut LeanObject,
    mut v_a_4177_: *mut LeanObject,
    mut v_a_4178_: *mut LeanObject,
    mut v_a_4179_: *mut LeanObject,
    mut v_a_4180_: *mut LeanObject,
    mut v_a_4181_: *mut LeanObject,
    mut v_a_4182_: *mut LeanObject,
    mut v_a_4183_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4185_: u8 = 0;
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4190_: u8 = 0;
    let mut v_val_4191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4194_: u8 = 0;
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4199_: u8 = 0;
    let mut v___x_4200_: u8 = 0;
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: u8 = 0;
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4213_: u8 = 0;
    let mut v___x_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4220_: u8 = 0;
    let mut v_a_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4224_: u8 = 0;
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4228_: u8 = 0;
    let mut v_a_4229_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4232_: u8 = 0;
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4236_: u8 = 0;
    let mut v_isSharedCheck_4237_: u8 = 0;
    let mut v_a_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4241_: u8 = 0;
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4245_: u8 = 0;
    let mut v_isSharedCheck_4246_: u8 = 0;
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4251_: u8 = 0;
    let mut v_a_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4255_: u8 = 0;
    let mut v___x_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4258_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4186_) == 0 {
                    v_a_4187_ = lean_ctor_get(v___x_4186_, 0);
                    v_isSharedCheck_4251_ = (!lean_is_exclusive(v___x_4186_)) as u8;
                    if v_isSharedCheck_4251_ == 0 {
                        v___x_4189_ = v___x_4186_;
                        v_isShared_4190_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4187_);
                        lean_dec(v___x_4186_);
                        v___x_4189_ = lean_box(0);
                        v_isShared_4190_ = v_isSharedCheck_4251_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_4176_);
                    v_a_4252_ = lean_ctor_get(v___x_4186_, 0);
                    v_isSharedCheck_4259_ = (!lean_is_exclusive(v___x_4186_)) as u8;
                    if v_isSharedCheck_4259_ == 0 {
                        v___x_4254_ = v___x_4186_;
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4252_);
                        lean_dec(v___x_4186_);
                        v___x_4254_ = lean_box(0);
                        v_isShared_4255_ = v_isSharedCheck_4259_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4187_) == 1 {
                    lean_del_object(v___x_4189_);
                    v_val_4191_ = lean_ctor_get(v_a_4187_, 0);
                    v_isSharedCheck_4246_ = (!lean_is_exclusive(v_a_4187_)) as u8;
                    if v_isSharedCheck_4246_ == 0 {
                        v___x_4193_ = v_a_4187_;
                        v_isShared_4194_ = v_isSharedCheck_4246_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_4191_);
                        lean_dec(v_a_4187_);
                        v___x_4193_ = lean_box(0);
                        v_isShared_4194_ = v_isSharedCheck_4246_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4187_);
                    lean_dec_ref(v_args_4176_);
                    v___x_4247_ = lean_box(0);
                    if v_isShared_4190_ == 0 {
                        lean_ctor_set(v___x_4189_, 0, v___x_4247_);
                        v___x_4249_ = v___x_4189_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_4250_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4250_, 0, v___x_4247_);
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
                if lean_obj_tag(v___x_4195_) == 0 {
                    v_a_4196_ = lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4237_ = (!lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4237_ == 0 {
                        v___x_4198_ = v___x_4195_;
                        v_isShared_4199_ = v_isSharedCheck_4237_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4196_);
                        lean_dec(v___x_4195_);
                        v___x_4198_ = lean_box(0);
                        v_isShared_4199_ = v_isSharedCheck_4237_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4193_);
                    lean_dec(v_val_4191_);
                    lean_dec_ref(v_args_4176_);
                    v_a_4238_ = lean_ctor_get(v___x_4195_, 0);
                    v_isSharedCheck_4245_ = (!lean_is_exclusive(v___x_4195_)) as u8;
                    if v_isSharedCheck_4245_ == 0 {
                        v___x_4240_ = v___x_4195_;
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_4238_);
                        lean_dec(v___x_4195_);
                        v___x_4240_ = lean_box(0);
                        v_isShared_4241_ = v_isSharedCheck_4245_;
                        state = 12;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4200_ = (lean_unbox(v_a_4196_) as u8);
                lean_dec(v_a_4196_);
                if v___x_4200_ == 0 {
                    lean_del_object(v___x_4193_);
                    lean_dec(v_val_4191_);
                    lean_dec_ref(v_args_4176_);
                    v___x_4201_ = lean_box(0);
                    if v_isShared_4199_ == 0 {
                        lean_ctor_set(v___x_4198_, 0, v___x_4201_);
                        v___x_4203_ = v___x_4198_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4204_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4204_, 0, v___x_4201_);
                        v___x_4203_ = v_reuseFailAlloc_4204_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4198_);
                    v___x_4205_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_4178_);
                    if lean_obj_tag(v___x_4205_) == 0 {
                        lean_dec_ref_known(v___x_4205_, 1);
                        v_params_4206_ = lean_ctor_get(v_val_4191_, 2);
                        lean_inc_ref(v_params_4206_);
                        v_value_4207_ = lean_ctor_get(v_val_4191_, 4);
                        lean_inc_ref(v_value_4207_);
                        lean_dec(v_val_4191_);
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
                        lean_dec_ref(v_params_4206_);
                        if lean_obj_tag(v___x_4209_) == 0 {
                            v_a_4210_ = lean_ctor_get(v___x_4209_, 0);
                            v_isSharedCheck_4220_ = (!lean_is_exclusive(v___x_4209_)) as u8;
                            if v_isSharedCheck_4220_ == 0 {
                                v___x_4212_ = v___x_4209_;
                                v_isShared_4213_ = v_isSharedCheck_4220_;
                                state = 5;
                                continue;
                            } else {
                                lean_inc(v_a_4210_);
                                lean_dec(v___x_4209_);
                                v___x_4212_ = lean_box(0);
                                v_isShared_4213_ = v_isSharedCheck_4220_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4193_);
                            v_a_4221_ = lean_ctor_get(v___x_4209_, 0);
                            v_isSharedCheck_4228_ = (!lean_is_exclusive(v___x_4209_)) as u8;
                            if v_isSharedCheck_4228_ == 0 {
                                v___x_4223_ = v___x_4209_;
                                v_isShared_4224_ = v_isSharedCheck_4228_;
                                state = 8;
                                continue;
                            } else {
                                lean_inc(v_a_4221_);
                                lean_dec(v___x_4209_);
                                v___x_4223_ = lean_box(0);
                                v_isShared_4224_ = v_isSharedCheck_4228_;
                                state = 8;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_4193_);
                        lean_dec(v_val_4191_);
                        lean_dec_ref(v_args_4176_);
                        v_a_4229_ = lean_ctor_get(v___x_4205_, 0);
                        v_isSharedCheck_4236_ = (!lean_is_exclusive(v___x_4205_)) as u8;
                        if v_isSharedCheck_4236_ == 0 {
                            v___x_4231_ = v___x_4205_;
                            v_isShared_4232_ = v_isSharedCheck_4236_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_a_4229_);
                            lean_dec(v___x_4205_);
                            v___x_4231_ = lean_box(0);
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
                    lean_ctor_set(v___x_4193_, 0, v_a_4210_);
                    v___x_4215_ = v___x_4193_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4219_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4219_, 0, v_a_4210_);
                    v___x_4215_ = v_reuseFailAlloc_4219_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4213_ == 0 {
                    lean_ctor_set(v___x_4212_, 0, v___x_4215_);
                    v___x_4217_ = v___x_4212_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4218_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4218_, 0, v___x_4215_);
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
                    v_reuseFailAlloc_4227_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4227_, 0, v_a_4221_);
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
                    v_reuseFailAlloc_4235_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4235_, 0, v_a_4229_);
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
                    v_reuseFailAlloc_4244_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4238_);
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
                    v_reuseFailAlloc_4258_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_a_4252_);
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
    mut v_fvarId_4260_: *mut LeanObject,
    mut v_args_4261_: *mut LeanObject,
    mut v_a_4262_: *mut LeanObject,
    mut v_a_4263_: *mut LeanObject,
    mut v_a_4264_: *mut LeanObject,
    mut v_a_4265_: *mut LeanObject,
    mut v_a_4266_: *mut LeanObject,
    mut v_a_4267_: *mut LeanObject,
    mut v_a_4268_: *mut LeanObject,
    mut v_a_4269_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4270_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4268_);
    lean_dec_ref(v_a_4267_);
    lean_dec(v_a_4266_);
    lean_dec_ref(v_a_4265_);
    lean_dec_ref(v_a_4264_);
    lean_dec(v_a_4263_);
    lean_dec_ref(v_a_4262_);
    lean_dec(v_fvarId_4260_);
    return v_res_4270_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(
    mut v_declName_4271_: *mut LeanObject,
    mut v___y_4272_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: u8 = 0;
    let mut v___x_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    v___x_4274_ = lean_st_ref_get(v___y_4272_);
    v_env_4275_ = lean_ctor_get(v___x_4274_, 0);
    lean_inc_ref(v_env_4275_);
    lean_dec(v___x_4274_);
    v___x_4276_ = l_Lean_isImplicitReducibleCore(v_env_4275_, v_declName_4271_);
    v___x_4277_ = lean_box((v___x_4276_) as usize);
    v___x_4278_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4278_, 0, v___x_4277_);
    v___x_4279_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4279_, 0, v___x_4278_);
    return v___x_4279_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg___boxed(
    mut v_declName_4280_: *mut LeanObject,
    mut v___y_4281_: *mut LeanObject,
    mut v___y_4282_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4283_: *mut LeanObject = core::ptr::null_mut();
    v_res_4283_ =
        l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(
            v_declName_4280_,
            v___y_4281_,
        );
    lean_dec(v___y_4281_);
    return v_res_4283_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0(
    mut v_declName_4284_: *mut LeanObject,
    mut v___y_4285_: *mut LeanObject,
    mut v___y_4286_: *mut LeanObject,
    mut v___y_4287_: *mut LeanObject,
    mut v___y_4288_: *mut LeanObject,
    mut v___y_4289_: *mut LeanObject,
    mut v___y_4290_: *mut LeanObject,
    mut v___y_4291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    v___x_4293_ =
        l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(
            v_declName_4284_,
            v___y_4291_,
        );
    return v___x_4293_;
}
pub unsafe fn l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___boxed(
    mut v_declName_4294_: *mut LeanObject,
    mut v___y_4295_: *mut LeanObject,
    mut v___y_4296_: *mut LeanObject,
    mut v___y_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4303_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4301_);
    lean_dec_ref(v___y_4300_);
    lean_dec(v___y_4299_);
    lean_dec_ref(v___y_4298_);
    lean_dec_ref(v___y_4297_);
    lean_dec(v___y_4296_);
    lean_dec_ref(v___y_4295_);
    return v_res_4303_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(
    mut v_sz_4304_: usize,
    mut v_i_4305_: usize,
    mut v_bs_4306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4307_: u8 = 0;
    let mut v_v_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4313_: usize = 0;
    let mut v___x_4314_: usize = 0;
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4307_ = lean_usize_dec_lt(v_i_4305_, v_sz_4304_);
                if v___x_4307_ == 0 {
                    return v_bs_4306_;
                } else {
                    v_v_4308_ = lean_array_uget_borrowed(v_bs_4306_, v_i_4305_);
                    v_fvarId_4309_ = lean_ctor_get(v_v_4308_, 0);
                    lean_inc(v_fvarId_4309_);
                    v___x_4310_ = lean_unsigned_to_nat(0);
                    v_bs_x27_4311_ = lean_array_uset(v_bs_4306_, v_i_4305_, v___x_4310_);
                    v___x_4312_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4312_, 0, v_fvarId_4309_);
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
    mut v_sz_4317_: *mut LeanObject,
    mut v_i_4318_: *mut LeanObject,
    mut v_bs_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_4320_: usize = 0;
    let mut v_i_boxed_4321_: usize = 0;
    let mut v_res_4322_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4320_ = lean_unbox_usize(v_sz_4317_);
    lean_dec(v_sz_4317_);
    v_i_boxed_4321_ = lean_unbox_usize(v_i_4318_);
    lean_dec(v_i_4318_);
    v_res_4322_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_boxed_4320_, v_i_boxed_4321_, v_bs_4319_);
    return v_res_4322_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(
    mut v_letDecl_4326_: *mut LeanObject,
    mut v_a_4327_: *mut LeanObject,
    mut v_a_4328_: *mut LeanObject,
    mut v_a_4329_: *mut LeanObject,
    mut v_a_4330_: *mut LeanObject,
    mut v_a_4331_: *mut LeanObject,
    mut v_a_4332_: *mut LeanObject,
    mut v_a_4333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_config_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_etaPoly_4336_: u8 = 0;
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_us_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4347_: u8 = 0;
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: u8 = 0;
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4358_: u8 = 0;
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4368_: u8 = 0;
    let mut v_val_4369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4372_: u8 = 0;
    let mut v___x_4373_: u8 = 0;
    let mut v___x_4374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4378_: u8 = 0;
    let mut v___x_4379_: u8 = 0;
    let mut v___x_4380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4384_: u8 = 0;
    let mut v___x_4386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4393_: u8 = 0;
    let mut v___x_4394_: u8 = 0;
    let mut v___x_4395_: u8 = 0;
    let mut v___x_4396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4398_: u8 = 0;
    let mut v___x_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4405_: usize = 0;
    let mut v___x_4406_: usize = 0;
    let mut v___x_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4408_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4426_: u8 = 0;
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4430_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4433_: u8 = 0;
    let mut v_unused_4434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4438_: u8 = 0;
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4442_: u8 = 0;
    let mut v_a_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4446_: u8 = 0;
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4450_: u8 = 0;
    let mut v_a_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4454_: u8 = 0;
    let mut v___x_4456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4458_: u8 = 0;
    let mut v_reuseFailAlloc_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4463_: u8 = 0;
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4467_: u8 = 0;
    let mut v_reuseFailAlloc_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4472_: u8 = 0;
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4476_: u8 = 0;
    let mut v_isSharedCheck_4477_: u8 = 0;
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_a_4479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4482_: u8 = 0;
    let mut v___x_4484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4486_: u8 = 0;
    let mut v_isSharedCheck_4487_: u8 = 0;
    let mut v_a_4488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4491_: u8 = 0;
    let mut v___x_4493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4495_: u8 = 0;
    let mut v___x_4496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4500_: u8 = 0;
    let mut v_isSharedCheck_4501_: u8 = 0;
    let mut v_isSharedCheck_4502_: u8 = 0;
    let mut v_a_4503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4506_: u8 = 0;
    let mut v___x_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4510_: u8 = 0;
    let mut v___x_4511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4513_: u8 = 0;
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_config_4335_ = lean_ctor_get(v_a_4327_, 1);
                v_etaPoly_4336_ = lean_ctor_get_uint8(v_config_4335_, 0 as u32);
                if v_etaPoly_4336_ == 0 {
                    lean_dec_ref(v_letDecl_4326_);
                    v___x_4337_ = lean_box(0);
                    v___x_4338_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4338_, 0, v___x_4337_);
                    return v___x_4338_;
                } else {
                    v_value_4339_ = lean_ctor_get(v_letDecl_4326_, 3);
                    lean_inc(v_value_4339_);
                    if lean_obj_tag(v_value_4339_) == 3 {
                        v_fvarId_4340_ = lean_ctor_get(v_letDecl_4326_, 0);
                        v_type_4341_ = lean_ctor_get(v_letDecl_4326_, 2);
                        v_declName_4342_ = lean_ctor_get(v_value_4339_, 0);
                        v_us_4343_ = lean_ctor_get(v_value_4339_, 1);
                        v_args_4344_ = lean_ctor_get(v_value_4339_, 2);
                        v_isSharedCheck_4513_ = (!lean_is_exclusive(v_value_4339_)) as u8;
                        if v_isSharedCheck_4513_ == 0 {
                            v___x_4346_ = v_value_4339_;
                            v_isShared_4347_ = v_isSharedCheck_4513_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_args_4344_);
                            lean_inc(v_us_4343_);
                            lean_inc(v_declName_4342_);
                            lean_dec(v_value_4339_);
                            v___x_4346_ = lean_box(0);
                            v_isShared_4347_ = v_isSharedCheck_4513_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_value_4339_);
                        lean_dec_ref(v_letDecl_4326_);
                        v___x_4514_ = lean_box(0);
                        v___x_4515_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4515_, 0, v___x_4514_);
                        return v___x_4515_;
                    }
                }
            }
            1 => {
                v___x_4348_ = lean_st_ref_get(v_a_4333_);
                v_env_4349_ = lean_ctor_get(v___x_4348_, 0);
                lean_inc_ref(v_env_4349_);
                lean_dec(v___x_4348_);
                v___x_4350_ = 0;
                lean_inc(v_declName_4342_);
                v___x_4351_ =
                    l_Lean_Environment_find_x3f(v_env_4349_, v_declName_4342_, v___x_4350_);
                if lean_obj_tag(v___x_4351_) == 1 {
                    v_val_4352_ = lean_ctor_get(v___x_4351_, 0);
                    lean_inc(v_val_4352_);
                    lean_dec_ref_known(v___x_4351_, 1);
                    v___x_4353_ = l_Lean_ConstantInfo_type(v_val_4352_);
                    lean_dec(v_val_4352_);
                    v___x_4354_ =
                        l_Lean_Compiler_LCNF_hasLocalInst___redArg(v___x_4353_, v_a_4333_);
                    if lean_obj_tag(v___x_4354_) == 0 {
                        v_a_4355_ = lean_ctor_get(v___x_4354_, 0);
                        v_isSharedCheck_4502_ = (!lean_is_exclusive(v___x_4354_)) as u8;
                        if v_isSharedCheck_4502_ == 0 {
                            v___x_4357_ = v___x_4354_;
                            v_isShared_4358_ = v_isSharedCheck_4502_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_4355_);
                            lean_dec(v___x_4354_);
                            v___x_4357_ = lean_box(0);
                            v_isShared_4358_ = v_isSharedCheck_4502_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4346_);
                        lean_dec_ref(v_args_4344_);
                        lean_dec(v_us_4343_);
                        lean_dec(v_declName_4342_);
                        lean_dec_ref(v_letDecl_4326_);
                        v_a_4503_ = lean_ctor_get(v___x_4354_, 0);
                        v_isSharedCheck_4510_ = (!lean_is_exclusive(v___x_4354_)) as u8;
                        if v_isSharedCheck_4510_ == 0 {
                            v___x_4505_ = v___x_4354_;
                            v_isShared_4506_ = v_isSharedCheck_4510_;
                            state = 32;
                            continue;
                        } else {
                            lean_inc(v_a_4503_);
                            lean_dec(v___x_4354_);
                            v___x_4505_ = lean_box(0);
                            v_isShared_4506_ = v_isSharedCheck_4510_;
                            state = 32;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4351_);
                    lean_del_object(v___x_4346_);
                    lean_dec_ref(v_args_4344_);
                    lean_dec(v_us_4343_);
                    lean_dec(v_declName_4342_);
                    lean_dec_ref(v_letDecl_4326_);
                    v___x_4511_ = lean_box(0);
                    v___x_4512_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4512_, 0, v___x_4511_);
                    return v___x_4512_;
                }
            }
            2 => {
                v___x_4359_ = (lean_unbox(v_a_4355_) as u8);
                lean_dec(v_a_4355_);
                if v___x_4359_ == 0 {
                    lean_del_object(v___x_4346_);
                    lean_dec_ref(v_args_4344_);
                    lean_dec(v_us_4343_);
                    lean_dec(v_declName_4342_);
                    lean_dec_ref(v_letDecl_4326_);
                    v___x_4360_ = lean_box(0);
                    if v_isShared_4358_ == 0 {
                        lean_ctor_set(v___x_4357_, 0, v___x_4360_);
                        v___x_4362_ = v___x_4357_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4363_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4363_, 0, v___x_4360_);
                        v___x_4362_ = v_reuseFailAlloc_4363_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4357_);
                    lean_inc(v_declName_4342_);
                    v___x_4364_ = l_Lean_isImplicitReducible___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__0___redArg(v_declName_4342_, v_a_4333_);
                    v_a_4365_ = lean_ctor_get(v___x_4364_, 0);
                    v_isSharedCheck_4501_ = (!lean_is_exclusive(v___x_4364_)) as u8;
                    if v_isSharedCheck_4501_ == 0 {
                        v___x_4367_ = v___x_4364_;
                        v_isShared_4368_ = v_isSharedCheck_4501_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_4365_);
                        lean_dec(v___x_4364_);
                        v___x_4367_ = lean_box(0);
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
                v_val_4369_ = lean_ctor_get(v_a_4365_, 0);
                v_isSharedCheck_4500_ = (!lean_is_exclusive(v_a_4365_)) as u8;
                if v_isSharedCheck_4500_ == 0 {
                    v___x_4371_ = v_a_4365_;
                    v_isShared_4372_ = v_isSharedCheck_4500_;
                    state = 5;
                    continue;
                } else {
                    lean_inc(v_val_4369_);
                    lean_dec(v_a_4365_);
                    v___x_4371_ = lean_box(0);
                    v_isShared_4372_ = v_isSharedCheck_4500_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4373_ = (lean_unbox(v_val_4369_) as u8);
                lean_dec(v_val_4369_);
                if v___x_4373_ == 0 {
                    lean_del_object(v___x_4367_);
                    v___x_4374_ = l_Lean_Compiler_LCNF_getPhase___redArg(v_a_4330_);
                    if lean_obj_tag(v___x_4374_) == 0 {
                        v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
                        v_isSharedCheck_4487_ = (!lean_is_exclusive(v___x_4374_)) as u8;
                        if v_isSharedCheck_4487_ == 0 {
                            v___x_4377_ = v___x_4374_;
                            v_isShared_4378_ = v_isSharedCheck_4487_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4375_);
                            lean_dec(v___x_4374_);
                            v___x_4377_ = lean_box(0);
                            v_isShared_4378_ = v_isSharedCheck_4487_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4371_);
                        lean_del_object(v___x_4346_);
                        lean_dec_ref(v_args_4344_);
                        lean_dec(v_us_4343_);
                        lean_dec(v_declName_4342_);
                        lean_dec_ref(v_letDecl_4326_);
                        v_a_4488_ = lean_ctor_get(v___x_4374_, 0);
                        v_isSharedCheck_4495_ = (!lean_is_exclusive(v___x_4374_)) as u8;
                        if v_isSharedCheck_4495_ == 0 {
                            v___x_4490_ = v___x_4374_;
                            v_isShared_4491_ = v_isSharedCheck_4495_;
                            state = 29;
                            continue;
                        } else {
                            lean_inc(v_a_4488_);
                            lean_dec(v___x_4374_);
                            v___x_4490_ = lean_box(0);
                            v_isShared_4491_ = v_isSharedCheck_4495_;
                            state = 29;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4371_);
                    lean_del_object(v___x_4346_);
                    lean_dec_ref(v_args_4344_);
                    lean_dec(v_us_4343_);
                    lean_dec(v_declName_4342_);
                    lean_dec_ref(v_letDecl_4326_);
                    v___x_4496_ = lean_box(0);
                    if v_isShared_4368_ == 0 {
                        lean_ctor_set(v___x_4367_, 0, v___x_4496_);
                        v___x_4498_ = v___x_4367_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_4499_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4499_, 0, v___x_4496_);
                        v___x_4498_ = v_reuseFailAlloc_4499_;
                        state = 31;
                        continue;
                    }
                }
            }
            6 => {
                v___x_4379_ = (lean_unbox(v_a_4375_) as u8);
                lean_inc(v_declName_4342_);
                v___x_4380_ = l_Lean_Compiler_LCNF_getDeclAt_x3f(
                    v_declName_4342_,
                    v___x_4379_,
                    v_a_4332_,
                    v_a_4333_,
                );
                if lean_obj_tag(v___x_4380_) == 0 {
                    v_a_4381_ = lean_ctor_get(v___x_4380_, 0);
                    v_isSharedCheck_4478_ = (!lean_is_exclusive(v___x_4380_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4383_ = v___x_4380_;
                        v_isShared_4384_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4381_);
                        lean_dec(v___x_4380_);
                        v___x_4383_ = lean_box(0);
                        v_isShared_4384_ = v_isSharedCheck_4478_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4377_);
                    lean_dec(v_a_4375_);
                    lean_del_object(v___x_4371_);
                    lean_del_object(v___x_4346_);
                    lean_dec_ref(v_args_4344_);
                    lean_dec(v_us_4343_);
                    lean_dec(v_declName_4342_);
                    lean_dec_ref(v_letDecl_4326_);
                    v_a_4479_ = lean_ctor_get(v___x_4380_, 0);
                    v_isSharedCheck_4486_ = (!lean_is_exclusive(v___x_4380_)) as u8;
                    if v_isSharedCheck_4486_ == 0 {
                        v___x_4481_ = v___x_4380_;
                        v_isShared_4482_ = v_isSharedCheck_4486_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_4479_);
                        lean_dec(v___x_4380_);
                        v___x_4481_ = lean_box(0);
                        v_isShared_4482_ = v_isSharedCheck_4486_;
                        state = 27;
                        continue;
                    }
                }
            }
            7 => {
                if lean_obj_tag(v_a_4381_) == 1 {
                    v_val_4390_ = lean_ctor_get(v_a_4381_, 0);
                    v_isSharedCheck_4477_ = (!lean_is_exclusive(v_a_4381_)) as u8;
                    if v_isSharedCheck_4477_ == 0 {
                        v___x_4392_ = v_a_4381_;
                        v_isShared_4393_ = v_isSharedCheck_4477_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_val_4390_);
                        lean_dec(v_a_4381_);
                        v___x_4392_ = lean_box(0);
                        v_isShared_4393_ = v_isSharedCheck_4477_;
                        state = 10;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4381_);
                    lean_del_object(v___x_4377_);
                    lean_dec(v_a_4375_);
                    lean_del_object(v___x_4371_);
                    lean_del_object(v___x_4346_);
                    lean_dec_ref(v_args_4344_);
                    lean_dec(v_us_4343_);
                    lean_dec(v_declName_4342_);
                    lean_dec_ref(v_letDecl_4326_);
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4386_ = lean_box(0);
                if v_isShared_4384_ == 0 {
                    lean_ctor_set(v___x_4383_, 0, v___x_4386_);
                    v___x_4388_ = v___x_4383_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4389_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4389_, 0, v___x_4386_);
                    v___x_4388_ = v_reuseFailAlloc_4389_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4388_;
            }
            10 => {
                v___x_4394_ = (lean_unbox(v_a_4375_) as u8);
                lean_dec(v_a_4375_);
                v___x_4395_ = l_Lean_Compiler_LCNF_Phase_toPurity(v___x_4394_);
                if v___x_4395_ == 0 {
                    lean_del_object(v___x_4383_);
                    v___x_4396_ = lean_array_get_size(v_args_4344_);
                    v___x_4397_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_4390_);
                    lean_dec(v_val_4390_);
                    v___x_4398_ = lean_nat_dec_lt(v___x_4396_, v___x_4397_);
                    lean_dec(v___x_4397_);
                    if v___x_4398_ == 0 {
                        lean_del_object(v___x_4392_);
                        lean_del_object(v___x_4371_);
                        lean_del_object(v___x_4346_);
                        lean_dec_ref(v_args_4344_);
                        lean_dec(v_us_4343_);
                        lean_dec(v_declName_4342_);
                        lean_dec_ref(v_letDecl_4326_);
                        v___x_4399_ = lean_box(0);
                        if v_isShared_4378_ == 0 {
                            lean_ctor_set(v___x_4377_, 0, v___x_4399_);
                            v___x_4401_ = v___x_4377_;
                            state = 11;
                            continue;
                        } else {
                            v_reuseFailAlloc_4402_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4399_);
                            v___x_4401_ = v_reuseFailAlloc_4402_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4377_);
                        lean_inc_ref(v_type_4341_);
                        v___x_4403_ = l_Lean_Compiler_LCNF_mkNewParams(
                            v___x_4395_,
                            v_type_4341_,
                            v_a_4330_,
                            v_a_4331_,
                            v_a_4332_,
                            v_a_4333_,
                        );
                        if lean_obj_tag(v___x_4403_) == 0 {
                            v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
                            lean_inc_n(v_a_4404_, 2);
                            lean_dec_ref_known(v___x_4403_, 1);
                            v_sz_4405_ = lean_array_size(v_a_4404_);
                            v___x_4406_ = 0usize;
                            v___x_4407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_4405_, v___x_4406_, v_a_4404_);
                            v___x_4408_ = l_Array_append___redArg(v_args_4344_, v___x_4407_);
                            lean_dec_ref(v___x_4407_);
                            if v_isShared_4347_ == 0 {
                                lean_ctor_set(v___x_4346_, 2, v___x_4408_);
                                v___x_4410_ = v___x_4346_;
                                state = 12;
                                continue;
                            } else {
                                v_reuseFailAlloc_4468_ = lean_alloc_ctor(3, 3, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_4468_, 0, v_declName_4342_);
                                lean_ctor_set(v_reuseFailAlloc_4468_, 1, v_us_4343_);
                                lean_ctor_set(v_reuseFailAlloc_4468_, 2, v___x_4408_);
                                v___x_4410_ = v_reuseFailAlloc_4468_;
                                state = 12;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_4392_);
                            lean_del_object(v___x_4371_);
                            lean_del_object(v___x_4346_);
                            lean_dec_ref(v_args_4344_);
                            lean_dec(v_us_4343_);
                            lean_dec(v_declName_4342_);
                            lean_dec_ref(v_letDecl_4326_);
                            v_a_4469_ = lean_ctor_get(v___x_4403_, 0);
                            v_isSharedCheck_4476_ = (!lean_is_exclusive(v___x_4403_)) as u8;
                            if v_isSharedCheck_4476_ == 0 {
                                v___x_4471_ = v___x_4403_;
                                v_isShared_4472_ = v_isSharedCheck_4476_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_4469_);
                                lean_dec(v___x_4403_);
                                v___x_4471_ = lean_box(0);
                                v_isShared_4472_ = v_isSharedCheck_4476_;
                                state = 25;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4392_);
                    lean_dec(v_val_4390_);
                    lean_del_object(v___x_4377_);
                    lean_del_object(v___x_4371_);
                    lean_del_object(v___x_4346_);
                    lean_dec_ref(v_args_4344_);
                    lean_dec(v_us_4343_);
                    lean_dec(v_declName_4342_);
                    lean_dec_ref(v_letDecl_4326_);
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
                if lean_obj_tag(v___x_4412_) == 0 {
                    v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
                    lean_inc(v_a_4413_);
                    lean_dec_ref_known(v___x_4412_, 1);
                    v_fvarId_4414_ = lean_ctor_get(v_a_4413_, 0);
                    lean_inc(v_fvarId_4414_);
                    if v_isShared_4372_ == 0 {
                        lean_ctor_set_tag(v___x_4371_, 5);
                        lean_ctor_set(v___x_4371_, 0, v_fvarId_4414_);
                        v___x_4416_ = v___x_4371_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_4459_ = lean_alloc_ctor(5, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_fvarId_4414_);
                        v___x_4416_ = v_reuseFailAlloc_4459_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4404_);
                    lean_del_object(v___x_4392_);
                    lean_del_object(v___x_4371_);
                    lean_dec_ref(v_letDecl_4326_);
                    v_a_4460_ = lean_ctor_get(v___x_4412_, 0);
                    v_isSharedCheck_4467_ = (!lean_is_exclusive(v___x_4412_)) as u8;
                    if v_isSharedCheck_4467_ == 0 {
                        v___x_4462_ = v___x_4412_;
                        v_isShared_4463_ = v_isSharedCheck_4467_;
                        state = 23;
                        continue;
                    } else {
                        lean_inc(v_a_4460_);
                        lean_dec(v___x_4412_);
                        v___x_4462_ = lean_box(0);
                        v_isShared_4463_ = v_isSharedCheck_4467_;
                        state = 23;
                        continue;
                    }
                }
            }
            13 => {
                v___x_4417_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4417_, 0, v_a_4413_);
                lean_ctor_set(v___x_4417_, 1, v___x_4416_);
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
                if lean_obj_tag(v___x_4419_) == 0 {
                    v_a_4420_ = lean_ctor_get(v___x_4419_, 0);
                    lean_inc(v_a_4420_);
                    lean_dec_ref_known(v___x_4419_, 1);
                    v_fvarId_4421_ = lean_ctor_get(v_a_4420_, 0);
                    lean_inc(v_fvarId_4421_);
                    lean_inc(v_fvarId_4340_);
                    v___x_4422_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_4340_,
                        v_fvarId_4421_,
                        v_a_4328_,
                        v_a_4330_,
                        v_a_4331_,
                        v_a_4332_,
                        v_a_4333_,
                    );
                    if lean_obj_tag(v___x_4422_) == 0 {
                        lean_dec_ref_known(v___x_4422_, 1);
                        v___x_4423_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
                            v_letDecl_4326_,
                            v_a_4328_,
                            v_a_4331_,
                        );
                        lean_dec_ref(v_letDecl_4326_);
                        if lean_obj_tag(v___x_4423_) == 0 {
                            v_isSharedCheck_4433_ = (!lean_is_exclusive(v___x_4423_)) as u8;
                            if v_isSharedCheck_4433_ == 0 {
                                v_unused_4434_ = lean_ctor_get(v___x_4423_, 0);
                                lean_dec(v_unused_4434_);
                                v___x_4425_ = v___x_4423_;
                                v_isShared_4426_ = v_isSharedCheck_4433_;
                                state = 14;
                                continue;
                            } else {
                                lean_dec(v___x_4423_);
                                v___x_4425_ = lean_box(0);
                                v_isShared_4426_ = v_isSharedCheck_4433_;
                                state = 14;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_4420_);
                            lean_del_object(v___x_4392_);
                            v_a_4435_ = lean_ctor_get(v___x_4423_, 0);
                            v_isSharedCheck_4442_ = (!lean_is_exclusive(v___x_4423_)) as u8;
                            if v_isSharedCheck_4442_ == 0 {
                                v___x_4437_ = v___x_4423_;
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_4435_);
                                lean_dec(v___x_4423_);
                                v___x_4437_ = lean_box(0);
                                v_isShared_4438_ = v_isSharedCheck_4442_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_4420_);
                        lean_del_object(v___x_4392_);
                        lean_dec_ref(v_letDecl_4326_);
                        v_a_4443_ = lean_ctor_get(v___x_4422_, 0);
                        v_isSharedCheck_4450_ = (!lean_is_exclusive(v___x_4422_)) as u8;
                        if v_isSharedCheck_4450_ == 0 {
                            v___x_4445_ = v___x_4422_;
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_4443_);
                            lean_dec(v___x_4422_);
                            v___x_4445_ = lean_box(0);
                            v_isShared_4446_ = v_isSharedCheck_4450_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_4392_);
                    lean_dec_ref(v_letDecl_4326_);
                    v_a_4451_ = lean_ctor_get(v___x_4419_, 0);
                    v_isSharedCheck_4458_ = (!lean_is_exclusive(v___x_4419_)) as u8;
                    if v_isSharedCheck_4458_ == 0 {
                        v___x_4453_ = v___x_4419_;
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_4451_);
                        lean_dec(v___x_4419_);
                        v___x_4453_ = lean_box(0);
                        v_isShared_4454_ = v_isSharedCheck_4458_;
                        state = 21;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_4393_ == 0 {
                    lean_ctor_set(v___x_4392_, 0, v_a_4420_);
                    v___x_4428_ = v___x_4392_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_a_4420_);
                    v___x_4428_ = v_reuseFailAlloc_4432_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                if v_isShared_4426_ == 0 {
                    lean_ctor_set(v___x_4425_, 0, v___x_4428_);
                    v___x_4430_ = v___x_4425_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4431_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4431_, 0, v___x_4428_);
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
                    v_reuseFailAlloc_4441_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4441_, 0, v_a_4435_);
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
                    v_reuseFailAlloc_4449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4449_, 0, v_a_4443_);
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
                    v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
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
                    v_reuseFailAlloc_4466_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 0, v_a_4460_);
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
                    v_reuseFailAlloc_4475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4475_, 0, v_a_4469_);
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
                    v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
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
                    v_reuseFailAlloc_4494_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4494_, 0, v_a_4488_);
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
                    v_reuseFailAlloc_4509_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4509_, 0, v_a_4503_);
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
    mut v_letDecl_4516_: *mut LeanObject,
    mut v_a_4517_: *mut LeanObject,
    mut v_a_4518_: *mut LeanObject,
    mut v_a_4519_: *mut LeanObject,
    mut v_a_4520_: *mut LeanObject,
    mut v_a_4521_: *mut LeanObject,
    mut v_a_4522_: *mut LeanObject,
    mut v_a_4523_: *mut LeanObject,
    mut v_a_4524_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4525_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4523_);
    lean_dec_ref(v_a_4522_);
    lean_dec(v_a_4521_);
    lean_dec_ref(v_a_4520_);
    lean_dec_ref(v_a_4519_);
    lean_dec(v_a_4518_);
    lean_dec_ref(v_a_4517_);
    return v_res_4525_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(
    mut v___x_4526_: u8,
    mut v_sz_4527_: usize,
    mut v_i_4528_: usize,
    mut v_bs_4529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    v___x_4530_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___redArg(v_sz_4527_, v_i_4528_, v_bs_4529_);
    return v___x_4530_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1___boxed(
    mut v___x_4531_: *mut LeanObject,
    mut v_sz_4532_: *mut LeanObject,
    mut v_i_4533_: *mut LeanObject,
    mut v_bs_4534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_24447__boxed_4535_: u8 = 0;
    let mut v_sz_boxed_4536_: usize = 0;
    let mut v_i_boxed_4537_: usize = 0;
    let mut v_res_4538_: *mut LeanObject = core::ptr::null_mut();
    v___x_24447__boxed_4535_ = (lean_unbox(v___x_4531_) as u8);
    v_sz_boxed_4536_ = lean_unbox_usize(v_sz_4532_);
    lean_dec(v_sz_4532_);
    v_i_boxed_4537_ = lean_unbox_usize(v_i_4533_);
    lean_dec(v_i_4533_);
    v_res_4538_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Simp_etaPolyApp_x3f_spec__1(v___x_24447__boxed_4535_, v_sz_boxed_4536_, v_i_boxed_4537_, v_bs_4534_);
    return v_res_4538_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(
    mut v_c_4539_: *mut LeanObject,
    mut v_fvarId_4540_: *mut LeanObject,
    mut v_a_4541_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4546_: u8 = 0;
    let mut v___x_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: u8 = 0;
    let mut v___x_4550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4554_: u8 = 0;
    let mut v___x_4555_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v___x_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4565_: u8 = 0;
    let mut v___x_4566_: u8 = 0;
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4568_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_c_4539_) == 5 {
                    v_fvarId_4543_ = lean_ctor_get(v_c_4539_, 0);
                    v_isSharedCheck_4565_ = (!lean_is_exclusive(v_c_4539_)) as u8;
                    if v_isSharedCheck_4565_ == 0 {
                        v___x_4545_ = v_c_4539_;
                        v_isShared_4546_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_4543_);
                        lean_dec(v_c_4539_);
                        v___x_4545_ = lean_box(0);
                        v_isShared_4546_ = v_isSharedCheck_4565_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_c_4539_);
                    v___x_4566_ = 0;
                    v___x_4567_ = lean_box((v___x_4566_) as usize);
                    v___x_4568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4568_, 0, v___x_4567_);
                    return v___x_4568_;
                }
            }
            1 => {
                v___x_4547_ = lean_st_ref_get(v_a_4541_);
                v_subst_4548_ = lean_ctor_get(v___x_4547_, 0);
                lean_inc_ref(v_subst_4548_);
                lean_dec(v___x_4547_);
                v___x_4549_ = 0;
                v___x_4550_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v_subst_4548_,
                    v_fvarId_4543_,
                    v___x_4549_,
                );
                lean_dec_ref(v_subst_4548_);
                if lean_obj_tag(v___x_4550_) == 0 {
                    lean_del_object(v___x_4545_);
                    v_fvarId_4551_ = lean_ctor_get(v___x_4550_, 0);
                    v_isSharedCheck_4560_ = (!lean_is_exclusive(v___x_4550_)) as u8;
                    if v_isSharedCheck_4560_ == 0 {
                        v___x_4553_ = v___x_4550_;
                        v_isShared_4554_ = v_isSharedCheck_4560_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_fvarId_4551_);
                        lean_dec(v___x_4550_);
                        v___x_4553_ = lean_box(0);
                        v_isShared_4554_ = v_isSharedCheck_4560_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4561_ = lean_box((v___x_4549_) as usize);
                    if v_isShared_4546_ == 0 {
                        lean_ctor_set_tag(v___x_4545_, 0);
                        lean_ctor_set(v___x_4545_, 0, v___x_4561_);
                        v___x_4563_ = v___x_4545_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4564_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4564_, 0, v___x_4561_);
                        v___x_4563_ = v_reuseFailAlloc_4564_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4555_ = l_Lean_instBEqFVarId_beq(v_fvarId_4551_, v_fvarId_4540_);
                lean_dec(v_fvarId_4551_);
                v___x_4556_ = lean_box((v___x_4555_) as usize);
                if v_isShared_4554_ == 0 {
                    lean_ctor_set(v___x_4553_, 0, v___x_4556_);
                    v___x_4558_ = v___x_4553_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4559_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4559_, 0, v___x_4556_);
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
    mut v_c_4569_: *mut LeanObject,
    mut v_fvarId_4570_: *mut LeanObject,
    mut v_a_4571_: *mut LeanObject,
    mut v_a_4572_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4573_: *mut LeanObject = core::ptr::null_mut();
    v_res_4573_ =
        l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_4569_, v_fvarId_4570_, v_a_4571_);
    lean_dec(v_a_4571_);
    lean_dec(v_fvarId_4570_);
    return v_res_4573_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isReturnOf(
    mut v_c_4574_: *mut LeanObject,
    mut v_fvarId_4575_: *mut LeanObject,
    mut v_a_4576_: *mut LeanObject,
    mut v_a_4577_: *mut LeanObject,
    mut v_a_4578_: *mut LeanObject,
    mut v_a_4579_: *mut LeanObject,
    mut v_a_4580_: *mut LeanObject,
    mut v_a_4581_: *mut LeanObject,
    mut v_a_4582_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4584_: *mut LeanObject = core::ptr::null_mut();
    v___x_4584_ =
        l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(v_c_4574_, v_fvarId_4575_, v_a_4577_);
    return v___x_4584_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(
    mut v_c_4585_: *mut LeanObject,
    mut v_fvarId_4586_: *mut LeanObject,
    mut v_a_4587_: *mut LeanObject,
    mut v_a_4588_: *mut LeanObject,
    mut v_a_4589_: *mut LeanObject,
    mut v_a_4590_: *mut LeanObject,
    mut v_a_4591_: *mut LeanObject,
    mut v_a_4592_: *mut LeanObject,
    mut v_a_4593_: *mut LeanObject,
    mut v_a_4594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4595_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4593_);
    lean_dec_ref(v_a_4592_);
    lean_dec(v_a_4591_);
    lean_dec_ref(v_a_4590_);
    lean_dec_ref(v_a_4589_);
    lean_dec(v_a_4588_);
    lean_dec_ref(v_a_4587_);
    lean_dec(v_fvarId_4586_);
    return v_res_4595_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(
    mut v_value_4596_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: u8 = 0;
    let mut v___x_4606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_value_4596_) == 4 {
                    v_fvarId_4601_ = lean_ctor_get(v_value_4596_, 0);
                    v_args_4602_ = lean_ctor_get(v_value_4596_, 1);
                    v___x_4603_ = lean_array_get_size(v_args_4602_);
                    v___x_4604_ = lean_unsigned_to_nat(0);
                    v___x_4605_ = lean_nat_dec_eq(v___x_4603_, v___x_4604_);
                    if v___x_4605_ == 0 {
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_fvarId_4601_);
                        v___x_4606_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_4606_, 0, v_fvarId_4601_);
                        v___x_4607_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_4607_, 0, v___x_4606_);
                        return v___x_4607_;
                    }
                } else {
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4599_ = lean_box(0);
                v___x_4600_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4600_, 0, v___x_4599_);
                return v___x_4600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg___boxed(
    mut v_value_4608_: *mut LeanObject,
    mut v_a_4609_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4610_: *mut LeanObject = core::ptr::null_mut();
    v_res_4610_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_4608_);
    lean_dec(v_value_4608_);
    return v_res_4610_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f(
    mut v_value_4611_: *mut LeanObject,
    mut v_a_4612_: *mut LeanObject,
    mut v_a_4613_: *mut LeanObject,
    mut v_a_4614_: *mut LeanObject,
    mut v_a_4615_: *mut LeanObject,
    mut v_a_4616_: *mut LeanObject,
    mut v_a_4617_: *mut LeanObject,
    mut v_a_4618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4620_: *mut LeanObject = core::ptr::null_mut();
    v___x_4620_ = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_4611_);
    return v___x_4620_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(
    mut v_value_4621_: *mut LeanObject,
    mut v_a_4622_: *mut LeanObject,
    mut v_a_4623_: *mut LeanObject,
    mut v_a_4624_: *mut LeanObject,
    mut v_a_4625_: *mut LeanObject,
    mut v_a_4626_: *mut LeanObject,
    mut v_a_4627_: *mut LeanObject,
    mut v_a_4628_: *mut LeanObject,
    mut v_a_4629_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4630_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_4628_);
    lean_dec_ref(v_a_4627_);
    lean_dec(v_a_4626_);
    lean_dec_ref(v_a_4625_);
    lean_dec_ref(v_a_4624_);
    lean_dec(v_a_4623_);
    lean_dec_ref(v_a_4622_);
    lean_dec(v_value_4621_);
    return v_res_4630_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(
    mut v_a_4631_: *mut LeanObject,
    mut v___x_4632_: *mut LeanObject,
    mut v_fvarId_4633_: *mut LeanObject,
    mut v___y_4634_: *mut LeanObject,
    mut v___y_4635_: *mut LeanObject,
    mut v___y_4636_: *mut LeanObject,
    mut v___y_4637_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    v_fvarId_4639_ = lean_ctor_get(v_a_4631_, 0);
    v___x_4640_ = lean_alloc_ctor(1, 1, (0) as u32);
    lean_ctor_set(v___x_4640_, 0, v_fvarId_4633_);
    v___x_4641_ = lean_mk_empty_array_with_capacity(v___x_4632_);
    v___x_4642_ = lean_array_push(v___x_4641_, v___x_4640_);
    lean_inc(v_fvarId_4639_);
    v___x_4643_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_4643_, 0, v_fvarId_4639_);
    lean_ctor_set(v___x_4643_, 1, v___x_4642_);
    v___x_4644_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4644_, 0, v___x_4643_);
    return v___x_4644_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed(
    mut v_a_4645_: *mut LeanObject,
    mut v___x_4646_: *mut LeanObject,
    mut v_fvarId_4647_: *mut LeanObject,
    mut v___y_4648_: *mut LeanObject,
    mut v___y_4649_: *mut LeanObject,
    mut v___y_4650_: *mut LeanObject,
    mut v___y_4651_: *mut LeanObject,
    mut v___y_4652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4653_: *mut LeanObject = core::ptr::null_mut();
    v_res_4653_ = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(
        v_a_4645_,
        v___x_4646_,
        v_fvarId_4647_,
        v___y_4648_,
        v___y_4649_,
        v___y_4650_,
        v___y_4651_,
    );
    lean_dec(v___y_4651_);
    lean_dec_ref(v___y_4650_);
    lean_dec(v___y_4649_);
    lean_dec_ref(v___y_4648_);
    lean_dec(v___x_4646_);
    lean_dec_ref(v_a_4645_);
    return v_res_4653_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(
    mut v_pu_4654_: u8,
    mut v_t_4655_: u8,
    mut v_args_4656_: *mut LeanObject,
    mut v___y_4657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4659_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4662_: *mut LeanObject = core::ptr::null_mut();
    v___x_4659_ = lean_st_ref_get(v___y_4657_);
    v_subst_4660_ = lean_ctor_get(v___x_4659_, 0);
    lean_inc_ref(v_subst_4660_);
    lean_dec(v___x_4659_);
    v___x_4661_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(
        v_pu_4654_,
        v_subst_4660_,
        v_args_4656_,
        v_t_4655_,
    );
    lean_dec_ref(v_subst_4660_);
    v___x_4662_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4662_, 0, v___x_4661_);
    return v___x_4662_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg___boxed(
    mut v_pu_4663_: *mut LeanObject,
    mut v_t_4664_: *mut LeanObject,
    mut v_args_4665_: *mut LeanObject,
    mut v___y_4666_: *mut LeanObject,
    mut v___y_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4668_: u8 = 0;
    let mut v_t_boxed_4669_: u8 = 0;
    let mut v_res_4670_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4668_ = (lean_unbox(v_pu_4663_) as u8);
    v_t_boxed_4669_ = (lean_unbox(v_t_4664_) as u8);
    v_res_4670_ =
        l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(
            v_pu_boxed_4668_,
            v_t_boxed_4669_,
            v_args_4665_,
            v___y_4666_,
        );
    lean_dec(v___y_4666_);
    return v_res_4670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(
    mut v_as_4671_: *mut LeanObject,
    mut v_i_4672_: usize,
    mut v_stop_4673_: usize,
    mut v_b_4674_: *mut LeanObject,
    mut v___y_4675_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4677_: u8 = 0;
    let mut v___x_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4681_: usize = 0;
    let mut v___x_4682_: usize = 0;
    let mut v___x_4684_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4677_ = lean_usize_dec_eq(v_i_4672_, v_stop_4673_);
                if v___x_4677_ == 0 {
                    v___x_4678_ = lean_array_uget_borrowed(v_as_4671_, v_i_4672_);
                    lean_inc(v___x_4678_);
                    v___x_4679_ =
                        l_Lean_Compiler_LCNF_Simp_markUsedArg___redArg(v___x_4678_, v___y_4675_);
                    if lean_obj_tag(v___x_4679_) == 0 {
                        v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
                        lean_inc(v_a_4680_);
                        lean_dec_ref_known(v___x_4679_, 1);
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
                    v___x_4684_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4684_, 0, v_b_4674_);
                    return v___x_4684_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg___boxed(
    mut v_as_4685_: *mut LeanObject,
    mut v_i_4686_: *mut LeanObject,
    mut v_stop_4687_: *mut LeanObject,
    mut v_b_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4691_: usize = 0;
    let mut v_stop_boxed_4692_: usize = 0;
    let mut v_res_4693_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4691_ = lean_unbox_usize(v_i_4686_);
    lean_dec(v_i_4686_);
    v_stop_boxed_4692_ = lean_unbox_usize(v_stop_4687_);
    lean_dec(v_stop_4687_);
    v_res_4693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_4685_, v_i_boxed_4691_, v_stop_boxed_4692_, v_b_4688_, v___y_4689_);
    lean_dec(v___y_4689_);
    lean_dec_ref(v_as_4685_);
    return v_res_4693_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(
    mut v_as_4694_: *mut LeanObject,
    mut v_i_4695_: usize,
    mut v_stop_4696_: usize,
) -> u8 {
    let mut v___x_4697_: u8 = 0;
    let mut v___x_4698_: u8 = 0;
    let mut v___y_4700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4701_: usize = 0;
    let mut v___x_4702_: usize = 0;
    let mut v___x_4704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4708_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4697_ = lean_usize_dec_eq(v_i_4695_, v_stop_4696_);
                if v___x_4697_ == 0 {
                    v___x_4698_ = 1;
                    v___x_4704_ = lean_array_uget_borrowed(v_as_4694_, v_i_4695_);
                    match lean_obj_tag(v___x_4704_) {
                        0 => {
                            v_code_4705_ = lean_ctor_get(v___x_4704_, 2);
                            v___y_4700_ = v_code_4705_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_4706_ = lean_ctor_get(v___x_4704_, 1);
                            v___y_4700_ = v_code_4706_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_4707_ = lean_ctor_get(v___x_4704_, 0);
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
                if lean_obj_tag(v___y_4700_) == 6 {
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
    mut v_as_4709_: *mut LeanObject,
    mut v_i_4710_: *mut LeanObject,
    mut v_stop_4711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4712_: usize = 0;
    let mut v_stop_boxed_4713_: usize = 0;
    let mut v_res_4714_: u8 = 0;
    let mut v_r_4715_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4712_ = lean_unbox_usize(v_i_4710_);
    lean_dec(v_i_4710_);
    v_stop_boxed_4713_ = lean_unbox_usize(v_stop_4711_);
    lean_dec(v_stop_4711_);
    v_res_4714_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__11(v_as_4709_, v_i_boxed_4712_, v_stop_boxed_4713_);
    lean_dec_ref(v_as_4709_);
    v_r_4715_ = lean_box((v_res_4714_) as usize);
    return v_r_4715_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(
    mut v_pu_4716_: u8,
    mut v_t_4717_: u8,
    mut v_i_4718_: *mut LeanObject,
    mut v_as_4719_: *mut LeanObject,
    mut v___y_4720_: *mut LeanObject,
    mut v___y_4721_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4730_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4733_: usize = 0;
    let mut v___x_4734_: usize = 0;
    let mut v___x_4735_: u8 = 0;
    let mut v___x_4736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4746_: u8 = 0;
    let mut v___x_4748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4750_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4723_ = lean_array_get_size(v_as_4719_);
                v___x_4724_ = lean_nat_dec_lt(v_i_4718_, v___x_4723_);
                if v___x_4724_ == 0 {
                    lean_dec(v_i_4718_);
                    v___x_4725_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4725_, 0, v_as_4719_);
                    return v___x_4725_;
                } else {
                    v_a_4726_ = lean_array_fget_borrowed(v_as_4719_, v_i_4718_);
                    v_type_4727_ = lean_ctor_get(v_a_4726_, 2);
                    v___x_4728_ = lean_st_ref_get(v___y_4720_);
                    v_subst_4729_ = lean_ctor_get(v___x_4728_, 0);
                    lean_inc_ref(v_subst_4729_);
                    lean_dec(v___x_4728_);
                    lean_inc_ref(v_type_4727_);
                    v___x_4730_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v_pu_4716_, v_subst_4729_, v_t_4717_, v_type_4727_);
                    lean_dec_ref(v_subst_4729_);
                    lean_inc(v_a_4726_);
                    v___x_4731_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(v_pu_4716_, v_a_4726_, v___x_4730_, v___y_4721_);
                    if lean_obj_tag(v___x_4731_) == 0 {
                        v_a_4732_ = lean_ctor_get(v___x_4731_, 0);
                        lean_inc(v_a_4732_);
                        lean_dec_ref_known(v___x_4731_, 1);
                        v___x_4733_ = lean_ptr_addr(v_a_4726_);
                        v___x_4734_ = lean_ptr_addr(v_a_4732_);
                        v___x_4735_ = lean_usize_dec_eq(v___x_4733_, v___x_4734_);
                        if v___x_4735_ == 0 {
                            v___x_4736_ = lean_unsigned_to_nat(1);
                            v___x_4737_ = lean_nat_add(v_i_4718_, v___x_4736_);
                            v___x_4738_ = lean_array_fset(v_as_4719_, v_i_4718_, v_a_4732_);
                            lean_dec(v_i_4718_);
                            v_i_4718_ = v___x_4737_;
                            v_as_4719_ = v___x_4738_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_4732_);
                            v___x_4740_ = lean_unsigned_to_nat(1);
                            v___x_4741_ = lean_nat_add(v_i_4718_, v___x_4740_);
                            lean_dec(v_i_4718_);
                            v_i_4718_ = v___x_4741_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_as_4719_);
                        lean_dec(v_i_4718_);
                        v_a_4743_ = lean_ctor_get(v___x_4731_, 0);
                        v_isSharedCheck_4750_ = (!lean_is_exclusive(v___x_4731_)) as u8;
                        if v_isSharedCheck_4750_ == 0 {
                            v___x_4745_ = v___x_4731_;
                            v_isShared_4746_ = v_isSharedCheck_4750_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4743_);
                            lean_dec(v___x_4731_);
                            v___x_4745_ = lean_box(0);
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
                    v_reuseFailAlloc_4749_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4749_, 0, v_a_4743_);
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
    mut v_pu_4751_: *mut LeanObject,
    mut v_t_4752_: *mut LeanObject,
    mut v_i_4753_: *mut LeanObject,
    mut v_as_4754_: *mut LeanObject,
    mut v___y_4755_: *mut LeanObject,
    mut v___y_4756_: *mut LeanObject,
    mut v___y_4757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4758_: u8 = 0;
    let mut v_t_boxed_4759_: u8 = 0;
    let mut v_res_4760_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4758_ = (lean_unbox(v_pu_4751_) as u8);
    v_t_boxed_4759_ = (lean_unbox(v_t_4752_) as u8);
    v_res_4760_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_boxed_4758_, v_t_boxed_4759_, v_i_4753_, v_as_4754_, v___y_4755_, v___y_4756_);
    lean_dec(v___y_4756_);
    lean_dec(v___y_4755_);
    return v_res_4760_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(
    mut v_pu_4761_: u8,
    mut v_t_4762_: u8,
    mut v_ps_4763_: *mut LeanObject,
    mut v___y_4764_: *mut LeanObject,
    mut v___y_4765_: *mut LeanObject,
    mut v___y_4766_: *mut LeanObject,
    mut v___y_4767_: *mut LeanObject,
    mut v___y_4768_: *mut LeanObject,
    mut v___y_4769_: *mut LeanObject,
    mut v___y_4770_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: *mut LeanObject = core::ptr::null_mut();
    v___x_4772_ = lean_unsigned_to_nat(0);
    v___x_4773_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_4761_, v_t_4762_, v___x_4772_, v_ps_4763_, v___y_4765_, v___y_4768_);
    return v___x_4773_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17___boxed(
    mut v_pu_4774_: *mut LeanObject,
    mut v_t_4775_: *mut LeanObject,
    mut v_ps_4776_: *mut LeanObject,
    mut v___y_4777_: *mut LeanObject,
    mut v___y_4778_: *mut LeanObject,
    mut v___y_4779_: *mut LeanObject,
    mut v___y_4780_: *mut LeanObject,
    mut v___y_4781_: *mut LeanObject,
    mut v___y_4782_: *mut LeanObject,
    mut v___y_4783_: *mut LeanObject,
    mut v___y_4784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4785_: u8 = 0;
    let mut v_t_boxed_4786_: u8 = 0;
    let mut v_res_4787_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4785_ = (lean_unbox(v_pu_4774_) as u8);
    v_t_boxed_4786_ = (lean_unbox(v_t_4775_) as u8);
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
    lean_dec(v___y_4783_);
    lean_dec_ref(v___y_4782_);
    lean_dec(v___y_4781_);
    lean_dec_ref(v___y_4780_);
    lean_dec_ref(v___y_4779_);
    lean_dec(v___y_4778_);
    lean_dec_ref(v___y_4777_);
    return v_res_4787_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(
    mut v_pu_4788_: u8,
    mut v_t_4789_: u8,
    mut v_decl_4790_: *mut LeanObject,
    mut v___y_4791_: *mut LeanObject,
    mut v___y_4792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_type_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut LeanObject = core::ptr::null_mut();
    v_type_4794_ = lean_ctor_get(v_decl_4790_, 2);
    v_value_4795_ = lean_ctor_get(v_decl_4790_, 3);
    v___x_4796_ = lean_st_ref_get(v___y_4791_);
    v_subst_4797_ = lean_ctor_get(v___x_4796_, 0);
    lean_inc_ref(v_subst_4797_);
    lean_dec(v___x_4796_);
    v___x_4798_ = lean_st_ref_get(v___y_4791_);
    v_subst_4799_ = lean_ctor_get(v___x_4798_, 0);
    lean_inc_ref(v_subst_4799_);
    lean_dec(v___x_4798_);
    lean_inc_ref(v_type_4794_);
    v___x_4800_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
        v_pu_4788_,
        v_subst_4797_,
        v_t_4789_,
        v_type_4794_,
    );
    lean_dec_ref(v_subst_4797_);
    lean_inc(v_value_4795_);
    v___x_4801_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(
        v_pu_4788_,
        v_subst_4799_,
        v_value_4795_,
        v_t_4789_,
    );
    lean_dec_ref(v_subst_4799_);
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
    mut v_pu_4803_: *mut LeanObject,
    mut v_t_4804_: *mut LeanObject,
    mut v_decl_4805_: *mut LeanObject,
    mut v___y_4806_: *mut LeanObject,
    mut v___y_4807_: *mut LeanObject,
    mut v___y_4808_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4809_: u8 = 0;
    let mut v_t_boxed_4810_: u8 = 0;
    let mut v_res_4811_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4809_ = (lean_unbox(v_pu_4803_) as u8);
    v_t_boxed_4810_ = (lean_unbox(v_t_4804_) as u8);
    v_res_4811_ =
        l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(
            v_pu_boxed_4809_,
            v_t_boxed_4810_,
            v_decl_4805_,
            v___y_4806_,
            v___y_4807_,
        );
    lean_dec(v___y_4807_);
    lean_dec(v___y_4806_);
    return v_res_4811_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(
    mut v___y_4812_: *mut LeanObject,
    mut v___f_4813_: *mut LeanObject,
    mut v___y_4814_: *mut LeanObject,
    mut v___y_4815_: *mut LeanObject,
    mut v_fvarId_4816_: *mut LeanObject,
    mut v___y_4817_: *mut LeanObject,
    mut v___y_4818_: *mut LeanObject,
    mut v___y_4819_: *mut LeanObject,
    mut v___y_4820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4827_: u8 = 0;
    let mut v___x_4829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc(v_fvarId_4816_);
                v___x_4822_ =
                    l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(v_fvarId_4816_, v___y_4812_);
                if lean_obj_tag(v___x_4822_) == 0 {
                    lean_dec_ref_known(v___x_4822_, 1);
                    lean_inc(v___y_4820_);
                    lean_inc_ref(v___y_4819_);
                    lean_inc(v___y_4818_);
                    lean_inc_ref(v___y_4817_);
                    lean_inc_ref(v___y_4815_);
                    lean_inc(v___y_4812_);
                    lean_inc_ref(v___y_4814_);
                    v___x_4823_ = lean_apply_9(
                        v___f_4813_,
                        v_fvarId_4816_,
                        v___y_4814_,
                        v___y_4812_,
                        v___y_4815_,
                        v___y_4817_,
                        v___y_4818_,
                        v___y_4819_,
                        v___y_4820_,
                        lean_box(0),
                    );
                    return v___x_4823_;
                } else {
                    lean_dec(v_fvarId_4816_);
                    lean_dec_ref(v___f_4813_);
                    v_a_4824_ = lean_ctor_get(v___x_4822_, 0);
                    v_isSharedCheck_4831_ = (!lean_is_exclusive(v___x_4822_)) as u8;
                    if v_isSharedCheck_4831_ == 0 {
                        v___x_4826_ = v___x_4822_;
                        v_isShared_4827_ = v_isSharedCheck_4831_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4824_);
                        lean_dec(v___x_4822_);
                        v___x_4826_ = lean_box(0);
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
                    v_reuseFailAlloc_4830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4830_, 0, v_a_4824_);
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
    mut v___y_4832_: *mut LeanObject,
    mut v___f_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
    mut v_fvarId_4836_: *mut LeanObject,
    mut v___y_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
    mut v___y_4841_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4842_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4840_);
    lean_dec_ref(v___y_4839_);
    lean_dec(v___y_4838_);
    lean_dec_ref(v___y_4837_);
    lean_dec_ref(v___y_4835_);
    lean_dec_ref(v___y_4834_);
    lean_dec(v___y_4832_);
    return v_res_4842_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(
    mut v_x_4843_: *mut LeanObject,
    mut v_x_4844_: *mut LeanObject,
    mut v_x_4845_: *mut LeanObject,
    mut v_x_4846_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4851_: u8 = 0;
    let mut v___x_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: u8 = 0;
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: u8 = 0;
    let mut v___x_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4868_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4847_ = lean_ctor_get(v_x_4843_, 0);
                v_vs_4848_ = lean_ctor_get(v_x_4843_, 1);
                v_isSharedCheck_4872_ = (!lean_is_exclusive(v_x_4843_)) as u8;
                if v_isSharedCheck_4872_ == 0 {
                    v___x_4850_ = v_x_4843_;
                    v_isShared_4851_ = v_isSharedCheck_4872_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_4848_);
                    lean_inc(v_ks_4847_);
                    lean_dec(v_x_4843_);
                    v___x_4850_ = lean_box(0);
                    v_isShared_4851_ = v_isSharedCheck_4872_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4852_ = lean_array_get_size(v_ks_4847_);
                v___x_4853_ = lean_nat_dec_lt(v_x_4844_, v___x_4852_);
                if v___x_4853_ == 0 {
                    lean_dec(v_x_4844_);
                    v___x_4854_ = lean_array_push(v_ks_4847_, v_x_4845_);
                    v___x_4855_ = lean_array_push(v_vs_4848_, v_x_4846_);
                    if v_isShared_4851_ == 0 {
                        lean_ctor_set(v___x_4850_, 1, v___x_4855_);
                        lean_ctor_set(v___x_4850_, 0, v___x_4854_);
                        v___x_4857_ = v___x_4850_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4858_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4858_, 0, v___x_4854_);
                        lean_ctor_set(v_reuseFailAlloc_4858_, 1, v___x_4855_);
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
                            v_reuseFailAlloc_4866_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4866_, 0, v_ks_4847_);
                            lean_ctor_set(v_reuseFailAlloc_4866_, 1, v_vs_4848_);
                            v___x_4862_ = v_reuseFailAlloc_4866_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4867_ = lean_array_fset(v_ks_4847_, v_x_4844_, v_x_4845_);
                        v___x_4868_ = lean_array_fset(v_vs_4848_, v_x_4844_, v_x_4846_);
                        lean_dec(v_x_4844_);
                        if v_isShared_4851_ == 0 {
                            lean_ctor_set(v___x_4850_, 1, v___x_4868_);
                            lean_ctor_set(v___x_4850_, 0, v___x_4867_);
                            v___x_4870_ = v___x_4850_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4871_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4871_, 0, v___x_4867_);
                            lean_ctor_set(v_reuseFailAlloc_4871_, 1, v___x_4868_);
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
                v___x_4863_ = lean_unsigned_to_nat(1);
                v___x_4864_ = lean_nat_add(v_x_4844_, v___x_4863_);
                lean_dec(v_x_4844_);
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
    mut v_n_4873_: *mut LeanObject,
    mut v_k_4874_: *mut LeanObject,
    mut v_v_4875_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    v___x_4876_ = lean_unsigned_to_nat(0);
    v___x_4877_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_n_4873_, v___x_4876_, v_k_4874_, v_v_4875_);
    return v___x_4877_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0()
-> u64 {
    let mut v___x_4878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4879_: u64 = 0;
    v___x_4878_ = lean_unsigned_to_nat(1723);
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
    v___x_4884_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__0);
    v___x_4885_ = lean_usize_sub(v___x_4884_, v___x_4883_);
    return v___x_4885_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_4886_: *mut LeanObject = core::ptr::null_mut();
    v___x_4886_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_4886_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(
    mut v_x_4887_: *mut LeanObject,
    mut v_x_4888_: usize,
    mut v_x_4889_: usize,
    mut v_x_4890_: *mut LeanObject,
    mut v_x_4891_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_4892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: usize = 0;
    let mut v___x_4894_: usize = 0;
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: usize = 0;
    let mut v_j_4897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4899_: u8 = 0;
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4902_: u8 = 0;
    let mut v_v_4903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_4912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4916_: u8 = 0;
    let mut v___x_4917_: u8 = 0;
    let mut v___x_4918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4923_: u8 = 0;
    let mut v_node_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v___x_4928_: usize = 0;
    let mut v___x_4929_: usize = 0;
    let mut v___x_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4934_: u8 = 0;
    let mut v___x_4935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4936_: u8 = 0;
    let mut v_unused_4937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4942_: u8 = 0;
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_4945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4947_: u8 = 0;
    let mut v_ks_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_4949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4953_: usize = 0;
    let mut v___x_4954_: u8 = 0;
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: u8 = 0;
    let mut v_reuseFailAlloc_4958_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4959_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4887_) == 0 {
                    v_es_4892_ = lean_ctor_get(v_x_4887_, 0);
                    v___x_4893_ = 5usize;
                    v___x_4894_ = 1usize;
                    v___x_4895_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_4896_ = lean_usize_land(v_x_4888_, v___x_4895_);
                    v_j_4897_ = lean_usize_to_nat(v___x_4896_);
                    v___x_4898_ = lean_array_get_size(v_es_4892_);
                    v___x_4899_ = lean_nat_dec_lt(v_j_4897_, v___x_4898_);
                    if v___x_4899_ == 0 {
                        lean_dec(v_j_4897_);
                        lean_dec(v_x_4891_);
                        lean_dec(v_x_4890_);
                        return v_x_4887_;
                    } else {
                        lean_inc_ref(v_es_4892_);
                        v_isSharedCheck_4936_ = (!lean_is_exclusive(v_x_4887_)) as u8;
                        if v_isSharedCheck_4936_ == 0 {
                            v_unused_4937_ = lean_ctor_get(v_x_4887_, 0);
                            lean_dec(v_unused_4937_);
                            v___x_4901_ = v_x_4887_;
                            v_isShared_4902_ = v_isSharedCheck_4936_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_4887_);
                            v___x_4901_ = lean_box(0);
                            v_isShared_4902_ = v_isSharedCheck_4936_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4938_ = lean_ctor_get(v_x_4887_, 0);
                    v_vs_4939_ = lean_ctor_get(v_x_4887_, 1);
                    v_isSharedCheck_4959_ = (!lean_is_exclusive(v_x_4887_)) as u8;
                    if v_isSharedCheck_4959_ == 0 {
                        v___x_4941_ = v_x_4887_;
                        v_isShared_4942_ = v_isSharedCheck_4959_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_4939_);
                        lean_inc(v_ks_4938_);
                        lean_dec(v_x_4887_);
                        v___x_4941_ = lean_box(0);
                        v_isShared_4942_ = v_isSharedCheck_4959_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4903_ = lean_array_fget(v_es_4892_, v_j_4897_);
                v___x_4904_ = lean_box(0);
                v_xs_x27_4905_ = lean_array_fset(v_es_4892_, v_j_4897_, v___x_4904_);
                match lean_obj_tag(v_v_4903_) {
                    0 => {
                        v_key_4912_ = lean_ctor_get(v_v_4903_, 0);
                        v_val_4913_ = lean_ctor_get(v_v_4903_, 1);
                        v_isSharedCheck_4923_ = (!lean_is_exclusive(v_v_4903_)) as u8;
                        if v_isSharedCheck_4923_ == 0 {
                            v___x_4915_ = v_v_4903_;
                            v_isShared_4916_ = v_isSharedCheck_4923_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_4913_);
                            lean_inc(v_key_4912_);
                            lean_dec(v_v_4903_);
                            v___x_4915_ = lean_box(0);
                            v_isShared_4916_ = v_isSharedCheck_4923_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4924_ = lean_ctor_get(v_v_4903_, 0);
                        v_isSharedCheck_4934_ = (!lean_is_exclusive(v_v_4903_)) as u8;
                        if v_isSharedCheck_4934_ == 0 {
                            v___x_4926_ = v_v_4903_;
                            v_isShared_4927_ = v_isSharedCheck_4934_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_4924_);
                            lean_dec(v_v_4903_);
                            v___x_4926_ = lean_box(0);
                            v_isShared_4927_ = v_isSharedCheck_4934_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4935_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_4935_, 0, v_x_4890_);
                        lean_ctor_set(v___x_4935_, 1, v_x_4891_);
                        v___y_4907_ = v___x_4935_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4908_ = lean_array_fset(v_xs_x27_4905_, v_j_4897_, v___y_4907_);
                lean_dec(v_j_4897_);
                if v_isShared_4902_ == 0 {
                    lean_ctor_set(v___x_4901_, 0, v___x_4908_);
                    v___x_4910_ = v___x_4901_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4911_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4911_, 0, v___x_4908_);
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
                    lean_del_object(v___x_4915_);
                    v___x_4918_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4912_,
                        v_val_4913_,
                        v_x_4890_,
                        v_x_4891_,
                    );
                    v___x_4919_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4919_, 0, v___x_4918_);
                    v___y_4907_ = v___x_4919_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_4913_);
                    lean_dec(v_key_4912_);
                    if v_isShared_4916_ == 0 {
                        lean_ctor_set(v___x_4915_, 1, v_x_4891_);
                        lean_ctor_set(v___x_4915_, 0, v_x_4890_);
                        v___x_4921_ = v___x_4915_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4922_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4922_, 0, v_x_4890_);
                        lean_ctor_set(v_reuseFailAlloc_4922_, 1, v_x_4891_);
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
                    lean_ctor_set(v___x_4926_, 0, v___x_4930_);
                    v___x_4932_ = v___x_4926_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4933_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4933_, 0, v___x_4930_);
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
                    v_reuseFailAlloc_4958_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4958_, 0, v_ks_4938_);
                    lean_ctor_set(v_reuseFailAlloc_4958_, 1, v_vs_4939_);
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
                    v___x_4956_ = lean_unsigned_to_nat(4);
                    v___x_4957_ = lean_nat_dec_lt(v___x_4955_, v___x_4956_);
                    lean_dec(v___x_4955_);
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
                    v_ks_4948_ = lean_ctor_get(v_newNode_4945_, 0);
                    lean_inc_ref(v_ks_4948_);
                    v_vs_4949_ = lean_ctor_get(v_newNode_4945_, 1);
                    lean_inc_ref(v_vs_4949_);
                    lean_dec_ref(v_newNode_4945_);
                    v___x_4950_ = lean_unsigned_to_nat(0);
                    v___x_4951_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___closed__2);
                    v___x_4952_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_x_4889_, v_ks_4948_, v_vs_4949_, v___x_4950_, v___x_4951_);
                    lean_dec_ref(v_vs_4949_);
                    lean_dec_ref(v_ks_4948_);
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
    mut v_keys_4961_: *mut LeanObject,
    mut v_vals_4962_: *mut LeanObject,
    mut v_i_4963_: *mut LeanObject,
    mut v_entries_4964_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: u8 = 0;
    let mut v_k_4967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4970_: u64 = 0;
    let mut v_h_4971_: usize = 0;
    let mut v___x_4972_: usize = 0;
    let mut v___x_4973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4974_: usize = 0;
    let mut v___x_4975_: usize = 0;
    let mut v___x_4976_: usize = 0;
    let mut v_h_4977_: usize = 0;
    let mut v___x_4978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4981_: u64 = 0;
    let mut v_hash_4982_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4965_ = lean_array_get_size(v_keys_4961_);
                v___x_4966_ = lean_nat_dec_lt(v_i_4963_, v___x_4965_);
                if v___x_4966_ == 0 {
                    lean_dec(v_i_4963_);
                    return v_entries_4964_;
                } else {
                    v_k_4967_ = lean_array_fget_borrowed(v_keys_4961_, v_i_4963_);
                    v_v_4968_ = lean_array_fget_borrowed(v_vals_4962_, v_i_4963_);
                    if lean_obj_tag(v_k_4967_) == 0 {
                        v___x_4981_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
                        v___y_4970_ = v___x_4981_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4982_ = lean_ctor_get_uint64(
                            v_k_4967_,
                            (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
                v___x_4973_ = lean_unsigned_to_nat(1);
                v___x_4974_ = 1usize;
                v___x_4975_ = lean_usize_sub(v_depth_4960_, v___x_4974_);
                v___x_4976_ = lean_usize_mul(v___x_4972_, v___x_4975_);
                v_h_4977_ = lean_usize_shift_right(v_h_4971_, v___x_4976_);
                v___x_4978_ = lean_nat_add(v_i_4963_, v___x_4973_);
                lean_dec(v_i_4963_);
                lean_inc(v_v_4968_);
                lean_inc(v_k_4967_);
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
    mut v_depth_4983_: *mut LeanObject,
    mut v_keys_4984_: *mut LeanObject,
    mut v_vals_4985_: *mut LeanObject,
    mut v_i_4986_: *mut LeanObject,
    mut v_entries_4987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_4988_: usize = 0;
    let mut v_res_4989_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_4988_ = lean_unbox_usize(v_depth_4983_);
    lean_dec(v_depth_4983_);
    v_res_4989_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_boxed_4988_, v_keys_4984_, v_vals_4985_, v_i_4986_, v_entries_4987_);
    lean_dec_ref(v_vals_4985_);
    lean_dec_ref(v_keys_4984_);
    return v_res_4989_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg___boxed(
    mut v_x_4990_: *mut LeanObject,
    mut v_x_4991_: *mut LeanObject,
    mut v_x_4992_: *mut LeanObject,
    mut v_x_4993_: *mut LeanObject,
    mut v_x_4994_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_47256__boxed_4995_: usize = 0;
    let mut v_x_47257__boxed_4996_: usize = 0;
    let mut v_res_4997_: *mut LeanObject = core::ptr::null_mut();
    v_x_47256__boxed_4995_ = lean_unbox_usize(v_x_4991_);
    lean_dec(v_x_4991_);
    v_x_47257__boxed_4996_ = lean_unbox_usize(v_x_4992_);
    lean_dec(v_x_4992_);
    v_res_4997_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_4990_, v_x_47256__boxed_4995_, v_x_47257__boxed_4996_, v_x_4993_, v_x_4994_);
    return v_res_4997_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(
    mut v_x_4998_: *mut LeanObject,
    mut v_x_4999_: *mut LeanObject,
    mut v_x_5000_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5002_: u64 = 0;
    let mut v___x_5003_: usize = 0;
    let mut v___x_5004_: usize = 0;
    let mut v___x_5005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: u64 = 0;
    let mut v_hash_5007_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4999_) == 0 {
                    v___x_5006_ = lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg___closed__0);
                    v___y_5002_ = v___x_5006_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5007_ = lean_ctor_get_uint64(
                        v_x_4999_,
                        (core::mem::size_of::<*mut LeanObject>() * 2) as u32,
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
    mut v_a_5008_: *mut LeanObject,
    mut v_b_5009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_array_5010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_5011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5015_: u8 = 0;
    let mut v___x_5016_: u8 = 0;
    let mut v___x_5017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5025_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_5010_ = lean_ctor_get(v_a_5008_, 0);
                v_start_5011_ = lean_ctor_get(v_a_5008_, 1);
                v_stop_5012_ = lean_ctor_get(v_a_5008_, 2);
                v_isSharedCheck_5025_ = (!lean_is_exclusive(v_a_5008_)) as u8;
                if v_isSharedCheck_5025_ == 0 {
                    v___x_5014_ = v_a_5008_;
                    v_isShared_5015_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_stop_5012_);
                    lean_inc(v_start_5011_);
                    lean_inc(v_array_5010_);
                    lean_dec(v_a_5008_);
                    v___x_5014_ = lean_box(0);
                    v_isShared_5015_ = v_isSharedCheck_5025_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5016_ = lean_nat_dec_lt(v_start_5011_, v_stop_5012_);
                if v___x_5016_ == 0 {
                    lean_del_object(v___x_5014_);
                    lean_dec(v_stop_5012_);
                    lean_dec(v_start_5011_);
                    lean_dec_ref(v_array_5010_);
                    return v_b_5009_;
                } else {
                    v___x_5017_ = lean_unsigned_to_nat(1);
                    v___x_5018_ = lean_nat_add(v_start_5011_, v___x_5017_);
                    lean_inc_ref(v_array_5010_);
                    if v_isShared_5015_ == 0 {
                        lean_ctor_set(v___x_5014_, 1, v___x_5018_);
                        v___x_5020_ = v___x_5014_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5024_ = lean_alloc_ctor(0, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_array_5010_);
                        lean_ctor_set(v_reuseFailAlloc_5024_, 1, v___x_5018_);
                        lean_ctor_set(v_reuseFailAlloc_5024_, 2, v_stop_5012_);
                        v___x_5020_ = v_reuseFailAlloc_5024_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5021_ = lean_array_fget(v_array_5010_, v_start_5011_);
                lean_dec(v_start_5011_);
                lean_dec_ref(v_array_5010_);
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
    mut v_as_5026_: *mut LeanObject,
    mut v_sz_5027_: usize,
    mut v_i_5028_: usize,
    mut v_b_5029_: *mut LeanObject,
    mut v___y_5030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5032_: u8 = 0;
    let mut v___x_5033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_array_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_start_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_stop_5036_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: u8 = 0;
    let mut v___x_5038_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5041_: u8 = 0;
    let mut v___x_5042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5043_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_5045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_5046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_5047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_5048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simplified_5049_: u8 = 0;
    let mut v_visited_5050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inline_5051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_5052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5055_: u8 = 0;
    let mut v___x_5056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5060_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5061_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5065_: usize = 0;
    let mut v___x_5066_: usize = 0;
    let mut v_reuseFailAlloc_5068_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5070_: u8 = 0;
    let mut v_isSharedCheck_5071_: u8 = 0;
    let mut v_unused_5072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5074_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5032_ = lean_usize_dec_lt(v_i_5028_, v_sz_5027_);
                if v___x_5032_ == 0 {
                    v___x_5033_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5033_, 0, v_b_5029_);
                    return v___x_5033_;
                } else {
                    v_array_5034_ = lean_ctor_get(v_b_5029_, 0);
                    v_start_5035_ = lean_ctor_get(v_b_5029_, 1);
                    v_stop_5036_ = lean_ctor_get(v_b_5029_, 2);
                    v___x_5037_ = lean_nat_dec_lt(v_start_5035_, v_stop_5036_);
                    if v___x_5037_ == 0 {
                        v___x_5038_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_5038_, 0, v_b_5029_);
                        return v___x_5038_;
                    } else {
                        lean_inc(v_stop_5036_);
                        lean_inc(v_start_5035_);
                        lean_inc_ref(v_array_5034_);
                        v_isSharedCheck_5071_ = (!lean_is_exclusive(v_b_5029_)) as u8;
                        if v_isSharedCheck_5071_ == 0 {
                            v_unused_5072_ = lean_ctor_get(v_b_5029_, 2);
                            lean_dec(v_unused_5072_);
                            v_unused_5073_ = lean_ctor_get(v_b_5029_, 1);
                            lean_dec(v_unused_5073_);
                            v_unused_5074_ = lean_ctor_get(v_b_5029_, 0);
                            lean_dec(v_unused_5074_);
                            v___x_5040_ = v_b_5029_;
                            v_isShared_5041_ = v_isSharedCheck_5071_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_b_5029_);
                            v___x_5040_ = lean_box(0);
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
                v_fvarId_5044_ = lean_ctor_get(v_a_5043_, 0);
                v_subst_5045_ = lean_ctor_get(v___x_5042_, 0);
                v_used_5046_ = lean_ctor_get(v___x_5042_, 1);
                v_binderRenaming_5047_ = lean_ctor_get(v___x_5042_, 2);
                v_funDeclInfoMap_5048_ = lean_ctor_get(v___x_5042_, 3);
                v_simplified_5049_ = lean_ctor_get_uint8(
                    v___x_5042_,
                    (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                );
                v_visited_5050_ = lean_ctor_get(v___x_5042_, 4);
                v_inline_5051_ = lean_ctor_get(v___x_5042_, 5);
                v_inlineLocal_5052_ = lean_ctor_get(v___x_5042_, 6);
                v_isSharedCheck_5070_ = (!lean_is_exclusive(v___x_5042_)) as u8;
                if v_isSharedCheck_5070_ == 0 {
                    v___x_5054_ = v___x_5042_;
                    v_isShared_5055_ = v_isSharedCheck_5070_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_inlineLocal_5052_);
                    lean_inc(v_inline_5051_);
                    lean_inc(v_visited_5050_);
                    lean_inc(v_funDeclInfoMap_5048_);
                    lean_inc(v_binderRenaming_5047_);
                    lean_inc(v_used_5046_);
                    lean_inc(v_subst_5045_);
                    lean_dec(v___x_5042_);
                    v___x_5054_ = lean_box(0);
                    v_isShared_5055_ = v_isSharedCheck_5070_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5056_ = lean_array_fget_borrowed(v_array_5034_, v_start_5035_);
                lean_inc(v___x_5056_);
                lean_inc(v_fvarId_5044_);
                v___x_5057_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_5045_, v_fvarId_5044_, v___x_5056_);
                if v_isShared_5055_ == 0 {
                    lean_ctor_set(v___x_5054_, 0, v___x_5057_);
                    v___x_5059_ = v___x_5054_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5069_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 0, v___x_5057_);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 1, v_used_5046_);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 2, v_binderRenaming_5047_);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 3, v_funDeclInfoMap_5048_);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 4, v_visited_5050_);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 5, v_inline_5051_);
                    lean_ctor_set(v_reuseFailAlloc_5069_, 6, v_inlineLocal_5052_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_5069_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                        v_simplified_5049_,
                    );
                    v___x_5059_ = v_reuseFailAlloc_5069_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5060_ = lean_st_ref_set(v___y_5030_, v___x_5059_);
                v___x_5061_ = lean_unsigned_to_nat(1);
                v___x_5062_ = lean_nat_add(v_start_5035_, v___x_5061_);
                lean_dec(v_start_5035_);
                if v_isShared_5041_ == 0 {
                    lean_ctor_set(v___x_5040_, 1, v___x_5062_);
                    v___x_5064_ = v___x_5040_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5068_ = lean_alloc_ctor(0, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5068_, 0, v_array_5034_);
                    lean_ctor_set(v_reuseFailAlloc_5068_, 1, v___x_5062_);
                    lean_ctor_set(v_reuseFailAlloc_5068_, 2, v_stop_5036_);
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
    mut v_as_5075_: *mut LeanObject,
    mut v_sz_5076_: *mut LeanObject,
    mut v_i_5077_: *mut LeanObject,
    mut v_b_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5081_: usize = 0;
    let mut v_i_boxed_5082_: usize = 0;
    let mut v_res_5083_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5081_ = lean_unbox_usize(v_sz_5076_);
    lean_dec(v_sz_5076_);
    v_i_boxed_5082_ = lean_unbox_usize(v_i_5077_);
    lean_dec(v_i_5077_);
    v_res_5083_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_5075_, v_sz_boxed_5081_, v_i_boxed_5082_, v_b_5078_, v___y_5079_);
    lean_dec(v___y_5079_);
    lean_dec_ref(v_as_5075_);
    return v_res_5083_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(
    mut v_as_5084_: *mut LeanObject,
    mut v_i_5085_: usize,
    mut v_stop_5086_: usize,
    mut v_b_5087_: *mut LeanObject,
    mut v___y_5088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5090_: u8 = 0;
    let mut v___x_5091_: u8 = 0;
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5095_: usize = 0;
    let mut v___x_5096_: usize = 0;
    let mut v___x_5098_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_5093_) == 0 {
                        v_a_5094_ = lean_ctor_get(v___x_5093_, 0);
                        lean_inc(v_a_5094_);
                        lean_dec_ref_known(v___x_5093_, 1);
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
                    v___x_5098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5098_, 0, v_b_5087_);
                    return v___x_5098_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg___boxed(
    mut v_as_5099_: *mut LeanObject,
    mut v_i_5100_: *mut LeanObject,
    mut v_stop_5101_: *mut LeanObject,
    mut v_b_5102_: *mut LeanObject,
    mut v___y_5103_: *mut LeanObject,
    mut v___y_5104_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5105_: usize = 0;
    let mut v_stop_boxed_5106_: usize = 0;
    let mut v_res_5107_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5105_ = lean_unbox_usize(v_i_5100_);
    lean_dec(v_i_5100_);
    v_stop_boxed_5106_ = lean_unbox_usize(v_stop_5101_);
    lean_dec(v_stop_5101_);
    v_res_5107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_5099_, v_i_boxed_5105_, v_stop_boxed_5106_, v_b_5102_, v___y_5103_);
    lean_dec(v___y_5103_);
    lean_dec_ref(v_as_5099_);
    return v_res_5107_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3___closed__0()
-> *mut LeanObject {
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: *mut LeanObject = core::ptr::null_mut();
    v___x_5108_ = 0;
    v___x_5109_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_5108_);
    return v___x_5109_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(
    mut v_msg_5110_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5112_: *mut LeanObject = core::ptr::null_mut();
    v___x_5111_ = lean_obj_once(
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
    mut v_as_5113_: *mut LeanObject,
    mut v_i_5114_: usize,
    mut v_stop_5115_: usize,
    mut v___y_5116_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5118_: u8 = 0;
    let mut v___x_5119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_5120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5122_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5125_: u8 = 0;
    let mut v___x_5126_: u8 = 0;
    let mut v___x_5127_: usize = 0;
    let mut v___x_5128_: usize = 0;
    let mut v___x_5131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5133_: u8 = 0;
    let mut v___x_5134_: u8 = 0;
    let mut v___x_5135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5136_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5118_ = lean_usize_dec_eq(v_i_5114_, v_stop_5115_);
                if v___x_5118_ == 0 {
                    v___x_5119_ = lean_array_uget_borrowed(v_as_5113_, v_i_5114_);
                    v_type_5120_ = lean_ctor_get(v___x_5119_, 2);
                    v___x_5121_ = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(
                        v_type_5120_,
                        v___y_5116_,
                    );
                    if lean_obj_tag(v___x_5121_) == 0 {
                        v_a_5122_ = lean_ctor_get(v___x_5121_, 0);
                        v_isSharedCheck_5133_ = (!lean_is_exclusive(v___x_5121_)) as u8;
                        if v_isSharedCheck_5133_ == 0 {
                            v___x_5124_ = v___x_5121_;
                            v_isShared_5125_ = v_isSharedCheck_5133_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5122_);
                            lean_dec(v___x_5121_);
                            v___x_5124_ = lean_box(0);
                            v_isShared_5125_ = v_isSharedCheck_5133_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_5121_;
                    }
                } else {
                    v___x_5134_ = 0;
                    v___x_5135_ = lean_box((v___x_5134_) as usize);
                    v___x_5136_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5136_, 0, v___x_5135_);
                    return v___x_5136_;
                }
            }
            1 => {
                v___x_5126_ = (lean_unbox(v_a_5122_) as u8);
                if v___x_5126_ == 0 {
                    lean_del_object(v___x_5124_);
                    lean_dec(v_a_5122_);
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
                        v_reuseFailAlloc_5132_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5132_, 0, v_a_5122_);
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
    mut v_as_5137_: *mut LeanObject,
    mut v_i_5138_: *mut LeanObject,
    mut v_stop_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
    mut v___y_5141_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5142_: usize = 0;
    let mut v_stop_boxed_5143_: usize = 0;
    let mut v_res_5144_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5142_ = lean_unbox_usize(v_i_5138_);
    lean_dec(v_i_5138_);
    v_stop_boxed_5143_ = lean_unbox_usize(v_stop_5139_);
    lean_dec(v_stop_5139_);
    v_res_5144_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_5137_, v_i_boxed_5142_, v_stop_boxed_5143_, v___y_5140_);
    lean_dec(v___y_5140_);
    lean_dec_ref(v_as_5137_);
    return v_res_5144_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(
    mut v_as_5145_: *mut LeanObject,
    mut v_i_5146_: usize,
    mut v_stop_5147_: usize,
    mut v_b_5148_: *mut LeanObject,
    mut v___y_5149_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5151_: u8 = 0;
    let mut v___x_5152_: u8 = 0;
    let mut v___x_5153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: usize = 0;
    let mut v___x_5157_: usize = 0;
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
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
                    if lean_obj_tag(v___x_5154_) == 0 {
                        v_a_5155_ = lean_ctor_get(v___x_5154_, 0);
                        lean_inc(v_a_5155_);
                        lean_dec_ref_known(v___x_5154_, 1);
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
                    v___x_5159_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5159_, 0, v_b_5148_);
                    return v___x_5159_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg___boxed(
    mut v_as_5160_: *mut LeanObject,
    mut v_i_5161_: *mut LeanObject,
    mut v_stop_5162_: *mut LeanObject,
    mut v_b_5163_: *mut LeanObject,
    mut v___y_5164_: *mut LeanObject,
    mut v___y_5165_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5166_: usize = 0;
    let mut v_stop_boxed_5167_: usize = 0;
    let mut v_res_5168_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5166_ = lean_unbox_usize(v_i_5161_);
    lean_dec(v_i_5161_);
    v_stop_boxed_5167_ = lean_unbox_usize(v_stop_5162_);
    lean_dec(v_stop_5162_);
    v_res_5168_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_5160_, v_i_boxed_5166_, v_stop_boxed_5167_, v_b_5163_, v___y_5164_);
    lean_dec(v___y_5164_);
    lean_dec_ref(v_as_5160_);
    return v_res_5168_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(
    mut v_as_5169_: *mut LeanObject,
    mut v_i_5170_: usize,
    mut v_stop_5171_: usize,
    mut v_b_5172_: *mut LeanObject,
    mut v___y_5173_: *mut LeanObject,
    mut v___y_5174_: *mut LeanObject,
    mut v___y_5175_: *mut LeanObject,
    mut v___y_5176_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_5179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: usize = 0;
    let mut v___x_5181_: usize = 0;
    let mut v___y_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5185_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5186_: u8 = 0;
    let mut v___x_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5191_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5192_: u8 = 0;
    let mut v___x_5193_: u8 = 0;
    let mut v___x_5194_: usize = 0;
    let mut v___x_5195_: usize = 0;
    let mut v___x_5196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: usize = 0;
    let mut v___x_5198_: usize = 0;
    let mut v___x_5199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5200_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5186_ = lean_usize_dec_eq(v_i_5170_, v_stop_5171_);
                if v___x_5186_ == 0 {
                    v___x_5187_ = lean_unsigned_to_nat(0);
                    v___x_5188_ = lean_array_uget_borrowed(v_as_5169_, v_i_5170_);
                    v___x_5189_ = l_Lean_Compiler_LCNF_Alt_getParams(v___x_5188_);
                    v___x_5190_ = lean_array_get_size(v___x_5189_);
                    v___x_5191_ = lean_box(0);
                    v___x_5192_ = lean_nat_dec_lt(v___x_5187_, v___x_5190_);
                    if v___x_5192_ == 0 {
                        lean_dec_ref(v___x_5189_);
                        v_a_5179_ = v___x_5191_;
                        state = 1;
                        continue;
                    } else {
                        v___x_5193_ = lean_nat_dec_le(v___x_5190_, v___x_5190_);
                        if v___x_5193_ == 0 {
                            if v___x_5192_ == 0 {
                                lean_dec_ref(v___x_5189_);
                                v_a_5179_ = v___x_5191_;
                                state = 1;
                                continue;
                            } else {
                                v___x_5194_ = 0usize;
                                v___x_5195_ = lean_usize_of_nat(v___x_5190_);
                                v___x_5196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_5189_, v___x_5194_, v___x_5195_, v___x_5191_, v___y_5174_);
                                lean_dec_ref(v___x_5189_);
                                v___y_5184_ = v___x_5196_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v___x_5197_ = 0usize;
                            v___x_5198_ = lean_usize_of_nat(v___x_5190_);
                            v___x_5199_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v___x_5189_, v___x_5197_, v___x_5198_, v___x_5191_, v___y_5174_);
                            lean_dec_ref(v___x_5189_);
                            v___y_5184_ = v___x_5199_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_5200_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5200_, 0, v_b_5172_);
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
                if lean_obj_tag(v___y_5184_) == 0 {
                    v_a_5185_ = lean_ctor_get(v___y_5184_, 0);
                    lean_inc(v_a_5185_);
                    lean_dec_ref_known(v___y_5184_, 1);
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
    mut v_as_5201_: *mut LeanObject,
    mut v_i_5202_: *mut LeanObject,
    mut v_stop_5203_: *mut LeanObject,
    mut v_b_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5210_: usize = 0;
    let mut v_stop_boxed_5211_: usize = 0;
    let mut v_res_5212_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5210_ = lean_unbox_usize(v_i_5202_);
    lean_dec(v_i_5202_);
    v_stop_boxed_5211_ = lean_unbox_usize(v_stop_5203_);
    lean_dec(v_stop_5203_);
    v_res_5212_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_5201_, v_i_boxed_5210_, v_stop_boxed_5211_, v_b_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
    lean_dec(v___y_5208_);
    lean_dec_ref(v___y_5207_);
    lean_dec(v___y_5206_);
    lean_dec_ref(v___y_5205_);
    lean_dec_ref(v_as_5201_);
    return v_res_5212_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(
    mut v_as_5213_: *mut LeanObject,
    mut v_i_5214_: usize,
    mut v_stop_5215_: usize,
    mut v___y_5216_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5218_: u8 = 0;
    let mut v___x_5219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5220_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5225_: u8 = 0;
    let mut v___x_5226_: u8 = 0;
    let mut v___x_5227_: usize = 0;
    let mut v___x_5228_: usize = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5232_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5233_: u8 = 0;
    let mut v___x_5234_: u8 = 0;
    let mut v___x_5235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5218_ = lean_usize_dec_eq(v_i_5214_, v_stop_5215_);
                if v___x_5218_ == 0 {
                    v___x_5219_ = lean_array_uget_borrowed(v_as_5213_, v_i_5214_);
                    v_fvarId_5220_ = lean_ctor_get(v___x_5219_, 0);
                    v___x_5221_ =
                        l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_5220_, v___y_5216_);
                    if lean_obj_tag(v___x_5221_) == 0 {
                        v_a_5222_ = lean_ctor_get(v___x_5221_, 0);
                        v_isSharedCheck_5233_ = (!lean_is_exclusive(v___x_5221_)) as u8;
                        if v_isSharedCheck_5233_ == 0 {
                            v___x_5224_ = v___x_5221_;
                            v_isShared_5225_ = v_isSharedCheck_5233_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5222_);
                            lean_dec(v___x_5221_);
                            v___x_5224_ = lean_box(0);
                            v_isShared_5225_ = v_isSharedCheck_5233_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_5221_;
                    }
                } else {
                    v___x_5234_ = 0;
                    v___x_5235_ = lean_box((v___x_5234_) as usize);
                    v___x_5236_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5236_, 0, v___x_5235_);
                    return v___x_5236_;
                }
            }
            1 => {
                v___x_5226_ = (lean_unbox(v_a_5222_) as u8);
                if v___x_5226_ == 0 {
                    lean_del_object(v___x_5224_);
                    lean_dec(v_a_5222_);
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
                        v_reuseFailAlloc_5232_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_a_5222_);
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
    mut v_as_5237_: *mut LeanObject,
    mut v_i_5238_: *mut LeanObject,
    mut v_stop_5239_: *mut LeanObject,
    mut v___y_5240_: *mut LeanObject,
    mut v___y_5241_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_5242_: usize = 0;
    let mut v_stop_boxed_5243_: usize = 0;
    let mut v_res_5244_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_5242_ = lean_unbox_usize(v_i_5238_);
    lean_dec(v_i_5238_);
    v_stop_boxed_5243_ = lean_unbox_usize(v_stop_5239_);
    lean_dec(v_stop_5239_);
    v_res_5244_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_5237_, v_i_boxed_5242_, v_stop_boxed_5243_, v___y_5240_);
    lean_dec(v___y_5240_);
    lean_dec_ref(v_as_5237_);
    return v_res_5244_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3() -> *mut LeanObject {
    let mut v___x_5248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5253_: *mut LeanObject = core::ptr::null_mut();
    v___x_5248_ = l_Lean_Compiler_LCNF_Simp_simp___closed__2;
    v___x_5249_ = lean_unsigned_to_nat(9);
    v___x_5250_ = lean_unsigned_to_nat(641);
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
    mut v___x_5257_: *mut LeanObject,
    mut v___x_5258_: *mut LeanObject,
    mut v_fvarId_5259_: *mut LeanObject,
    mut v_k_5260_: *mut LeanObject,
    mut v_args_5261_: *mut LeanObject,
    mut v___x_5262_: u8,
    mut v___x_5263_: *mut LeanObject,
    mut v_result_5264_: *mut LeanObject,
    mut v___y_5265_: *mut LeanObject,
    mut v___y_5266_: *mut LeanObject,
    mut v___y_5267_: *mut LeanObject,
    mut v___y_5268_: *mut LeanObject,
    mut v___y_5269_: *mut LeanObject,
    mut v___y_5270_: *mut LeanObject,
    mut v___y_5271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_lower_5274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_5275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5289_: u8 = 0;
    let mut v___x_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5293_: u8 = 0;
    let mut v_a_5294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5297_: u8 = 0;
    let mut v___x_5299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5301_: u8 = 0;
    let mut v___x_5302_: u8 = 0;
    let mut v___x_5303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5308_: u8 = 0;
    let mut v___x_5310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5312_: u8 = 0;
    let mut v___x_5313_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5302_ = lean_nat_dec_lt(v___x_5257_, v___x_5258_);
                if v___x_5302_ == 0 {
                    lean_dec(v___x_5263_);
                    lean_dec_ref(v_args_5261_);
                    lean_dec(v___x_5258_);
                    lean_dec(v___x_5257_);
                    v___x_5303_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_5259_,
                        v_result_5264_,
                        v___y_5266_,
                        v___y_5268_,
                        v___y_5269_,
                        v___y_5270_,
                        v___y_5271_,
                    );
                    if lean_obj_tag(v___x_5303_) == 0 {
                        lean_dec_ref_known(v___x_5303_, 1);
                        lean_inc_ref(v___y_5270_);
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
                        lean_dec_ref(v_k_5260_);
                        v_a_5305_ = lean_ctor_get(v___x_5303_, 0);
                        v_isSharedCheck_5312_ = (!lean_is_exclusive(v___x_5303_)) as u8;
                        if v_isSharedCheck_5312_ == 0 {
                            v___x_5307_ = v___x_5303_;
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5305_);
                            lean_dec(v___x_5303_);
                            v___x_5307_ = lean_box(0);
                            v_isShared_5308_ = v_isSharedCheck_5312_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    v___x_5313_ = lean_nat_dec_le(v___x_5257_, v___x_5263_);
                    if v___x_5313_ == 0 {
                        lean_dec(v___x_5263_);
                        v_lower_5274_ = v___x_5257_;
                        v_upper_5275_ = v___x_5258_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5257_);
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
                v___x_5278_ = lean_alloc_ctor(4, 2, (0) as u32);
                lean_ctor_set(v___x_5278_, 0, v_result_5264_);
                lean_ctor_set(v___x_5278_, 1, v___x_5277_);
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
                if lean_obj_tag(v___x_5280_) == 0 {
                    v_a_5281_ = lean_ctor_get(v___x_5280_, 0);
                    lean_inc(v_a_5281_);
                    lean_dec_ref_known(v___x_5280_, 1);
                    v_fvarId_5282_ = lean_ctor_get(v_a_5281_, 0);
                    lean_inc(v_fvarId_5282_);
                    v___x_5283_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_5259_,
                        v_fvarId_5282_,
                        v___y_5266_,
                        v___y_5268_,
                        v___y_5269_,
                        v___y_5270_,
                        v___y_5271_,
                    );
                    if lean_obj_tag(v___x_5283_) == 0 {
                        lean_dec_ref_known(v___x_5283_, 1);
                        v___x_5284_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_5284_, 0, v_a_5281_);
                        lean_ctor_set(v___x_5284_, 1, v_k_5260_);
                        lean_inc_ref(v___y_5270_);
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
                        lean_dec(v_a_5281_);
                        lean_dec_ref(v_k_5260_);
                        v_a_5286_ = lean_ctor_get(v___x_5283_, 0);
                        v_isSharedCheck_5293_ = (!lean_is_exclusive(v___x_5283_)) as u8;
                        if v_isSharedCheck_5293_ == 0 {
                            v___x_5288_ = v___x_5283_;
                            v_isShared_5289_ = v_isSharedCheck_5293_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5286_);
                            lean_dec(v___x_5283_);
                            v___x_5288_ = lean_box(0);
                            v_isShared_5289_ = v_isSharedCheck_5293_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_5260_);
                    lean_dec(v_fvarId_5259_);
                    v_a_5294_ = lean_ctor_get(v___x_5280_, 0);
                    v_isSharedCheck_5301_ = (!lean_is_exclusive(v___x_5280_)) as u8;
                    if v_isSharedCheck_5301_ == 0 {
                        v___x_5296_ = v___x_5280_;
                        v_isShared_5297_ = v_isSharedCheck_5301_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_5294_);
                        lean_dec(v___x_5280_);
                        v___x_5296_ = lean_box(0);
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
                    v_reuseFailAlloc_5292_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5292_, 0, v_a_5286_);
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
                    v_reuseFailAlloc_5300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5300_, 0, v_a_5294_);
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
                    v_reuseFailAlloc_5311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5311_, 0, v_a_5305_);
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
    mut v___x_5314_: *mut LeanObject,
    mut v___x_5315_: *mut LeanObject,
    mut v_fvarId_5316_: *mut LeanObject,
    mut v_k_5317_: *mut LeanObject,
    mut v_args_5318_: *mut LeanObject,
    mut v___x_5319_: *mut LeanObject,
    mut v___x_5320_: *mut LeanObject,
    mut v_result_5321_: *mut LeanObject,
    mut v___y_5322_: *mut LeanObject,
    mut v___y_5323_: *mut LeanObject,
    mut v___y_5324_: *mut LeanObject,
    mut v___y_5325_: *mut LeanObject,
    mut v___y_5326_: *mut LeanObject,
    mut v___y_5327_: *mut LeanObject,
    mut v___y_5328_: *mut LeanObject,
    mut v___y_5329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_47787__boxed_5330_: u8 = 0;
    let mut v_res_5331_: *mut LeanObject = core::ptr::null_mut();
    v___x_47787__boxed_5330_ = (lean_unbox(v___x_5319_) as u8);
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
    lean_dec(v___y_5328_);
    lean_dec_ref(v___y_5327_);
    lean_dec(v___y_5326_);
    lean_dec_ref(v___y_5325_);
    lean_dec_ref(v___y_5324_);
    lean_dec(v___y_5323_);
    lean_dec_ref(v___y_5322_);
    return v_res_5331_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(
    mut v_letDecl_5332_: *mut LeanObject,
    mut v_k_5333_: *mut LeanObject,
    mut v_a_5334_: *mut LeanObject,
    mut v_a_5335_: *mut LeanObject,
    mut v_a_5336_: *mut LeanObject,
    mut v_a_5337_: *mut LeanObject,
    mut v_a_5338_: *mut LeanObject,
    mut v_a_5339_: *mut LeanObject,
    mut v_a_5340_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5351_: u8 = 0;
    let mut v_val_5352_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5355_: u8 = 0;
    let mut v_params_5356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_5357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fType_5358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_5360_: u8 = 0;
    let mut v___x_5361_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5363_: u8 = 0;
    let mut v___y_5365_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5369_: u8 = 0;
    let mut v___y_5370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5372_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5381_: u8 = 0;
    let mut v___x_5382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: u8 = 0;
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5390_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5396_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5404_: u8 = 0;
    let mut v___x_5405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5411_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5412_: u8 = 0;
    let mut v_a_5413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5416_: u8 = 0;
    let mut v___x_5418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5420_: u8 = 0;
    let mut v_a_5421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5424_: u8 = 0;
    let mut v___x_5426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5428_: u8 = 0;
    let mut v_a_5429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5432_: u8 = 0;
    let mut v___x_5434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5436_: u8 = 0;
    let mut v_a_5437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5440_: u8 = 0;
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5444_: u8 = 0;
    let mut v___x_5445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5461_: u8 = 0;
    let mut v___x_5463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5468_: u8 = 0;
    let mut v_a_5469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5472_: u8 = 0;
    let mut v___x_5474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5476_: u8 = 0;
    let mut v_a_5477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5480_: u8 = 0;
    let mut v___x_5482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5484_: u8 = 0;
    let mut v_a_5485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5488_: u8 = 0;
    let mut v___x_5490_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5492_: u8 = 0;
    let mut v_a_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5496_: u8 = 0;
    let mut v___x_5498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5500_: u8 = 0;
    let mut v_a_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5504_: u8 = 0;
    let mut v___x_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5508_: u8 = 0;
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5513_: u8 = 0;
    let mut v___x_5515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5520_: u8 = 0;
    let mut v_a_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5524_: u8 = 0;
    let mut v___x_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5528_: u8 = 0;
    let mut v_a_5529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5532_: u8 = 0;
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5536_: u8 = 0;
    let mut v_a_5537_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5540_: u8 = 0;
    let mut v___x_5542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5544_: u8 = 0;
    let mut v___y_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_5552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5554_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5558_: u8 = 0;
    let mut v___x_5559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_5561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5562_: u8 = 0;
    let mut v___x_5563_: u8 = 0;
    let mut v___x_5564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5569_: u8 = 0;
    let mut v___x_5570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5574_: u8 = 0;
    let mut v_a_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5580_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5582_: u8 = 0;
    let mut v_a_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5586_: u8 = 0;
    let mut v___x_5588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5590_: u8 = 0;
    let mut v_a_5591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5594_: u8 = 0;
    let mut v___x_5596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5598_: u8 = 0;
    let mut v___x_5599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5609_: u8 = 0;
    let mut v___x_5610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5614_: u8 = 0;
    let mut v_a_5615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5618_: u8 = 0;
    let mut v___x_5620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5622_: u8 = 0;
    let mut v_a_5623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5626_: u8 = 0;
    let mut v___x_5628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5630_: u8 = 0;
    let mut v_a_5631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5633_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5634_: u8 = 0;
    let mut v___x_5636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5638_: u8 = 0;
    let mut v_a_5639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5642_: u8 = 0;
    let mut v___x_5644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5646_: u8 = 0;
    let mut v_declName_5647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_5650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_config_5651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineStack_5652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineStackOccs_5653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5658_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5662_: u8 = 0;
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5666_: u8 = 0;
    let mut v_isSharedCheck_5667_: u8 = 0;
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5671_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5672_: u8 = 0;
    let mut v_a_5673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5676_: u8 = 0;
    let mut v___x_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5680_: u8 = 0;
    let mut v_isSharedCheck_5681_: u8 = 0;
    let mut v_unused_5682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_5683_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_5342_ = lean_ctor_get(v_letDecl_5332_, 0);
                v_value_5343_ = lean_ctor_get(v_letDecl_5332_, 3);
                v_isSharedCheck_5681_ = (!lean_is_exclusive(v_letDecl_5332_)) as u8;
                if v_isSharedCheck_5681_ == 0 {
                    v_unused_5682_ = lean_ctor_get(v_letDecl_5332_, 2);
                    lean_dec(v_unused_5682_);
                    v_unused_5683_ = lean_ctor_get(v_letDecl_5332_, 1);
                    lean_dec(v_unused_5683_);
                    v___x_5345_ = v_letDecl_5332_;
                    v_isShared_5346_ = v_isSharedCheck_5681_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_value_5343_);
                    lean_inc(v_fvarId_5342_);
                    lean_dec(v_letDecl_5332_);
                    v___x_5345_ = lean_box(0);
                    v_isShared_5346_ = v_isSharedCheck_5681_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_value_5343_);
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
                if lean_obj_tag(v___x_5347_) == 0 {
                    v_a_5348_ = lean_ctor_get(v___x_5347_, 0);
                    v_isSharedCheck_5672_ = (!lean_is_exclusive(v___x_5347_)) as u8;
                    if v_isSharedCheck_5672_ == 0 {
                        v___x_5350_ = v___x_5347_;
                        v_isShared_5351_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5348_);
                        lean_dec(v___x_5347_);
                        v___x_5350_ = lean_box(0);
                        v_isShared_5351_ = v_isSharedCheck_5672_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5345_);
                    lean_dec(v_value_5343_);
                    lean_dec(v_fvarId_5342_);
                    lean_dec_ref(v_k_5333_);
                    v_a_5673_ = lean_ctor_get(v___x_5347_, 0);
                    v_isSharedCheck_5680_ = (!lean_is_exclusive(v___x_5347_)) as u8;
                    if v_isSharedCheck_5680_ == 0 {
                        v___x_5675_ = v___x_5347_;
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 61;
                        continue;
                    } else {
                        lean_inc(v_a_5673_);
                        lean_dec(v___x_5347_);
                        v___x_5675_ = lean_box(0);
                        v_isShared_5676_ = v_isSharedCheck_5680_;
                        state = 61;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5348_) == 1 {
                    lean_del_object(v___x_5350_);
                    v_val_5352_ = lean_ctor_get(v_a_5348_, 0);
                    v_isSharedCheck_5667_ = (!lean_is_exclusive(v_a_5348_)) as u8;
                    if v_isSharedCheck_5667_ == 0 {
                        v___x_5354_ = v_a_5348_;
                        v_isShared_5355_ = v_isSharedCheck_5667_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_5352_);
                        lean_dec(v_a_5348_);
                        v___x_5354_ = lean_box(0);
                        v_isShared_5355_ = v_isSharedCheck_5667_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5348_);
                    lean_del_object(v___x_5345_);
                    lean_dec(v_value_5343_);
                    lean_dec(v_fvarId_5342_);
                    lean_dec_ref(v_k_5333_);
                    v___x_5668_ = lean_box(0);
                    if v_isShared_5351_ == 0 {
                        lean_ctor_set(v___x_5350_, 0, v___x_5668_);
                        v___x_5670_ = v___x_5350_;
                        state = 60;
                        continue;
                    } else {
                        v_reuseFailAlloc_5671_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5671_, 0, v___x_5668_);
                        v___x_5670_ = v_reuseFailAlloc_5671_;
                        state = 60;
                        continue;
                    }
                }
            }
            3 => {
                v_params_5356_ = lean_ctor_get(v_val_5352_, 0);
                v_value_5357_ = lean_ctor_get(v_val_5352_, 1);
                v_fType_5358_ = lean_ctor_get(v_val_5352_, 2);
                v_args_5359_ = lean_ctor_get(v_val_5352_, 3);
                v_recursive_5360_ = lean_ctor_get_uint8(
                    v_val_5352_,
                    (core::mem::size_of::<*mut LeanObject>() * 4 + 2) as u32,
                );
                v___x_5361_ = lean_array_get_size(v_args_5359_);
                v___x_5362_ = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(v_val_5352_);
                v___x_5363_ = lean_nat_dec_lt(v___x_5361_, v___x_5362_);
                if lean_obj_tag(v_value_5343_) == 3 {
                    v_declName_5647_ = lean_ctor_get(v_value_5343_, 0);
                    lean_inc_n(v_declName_5647_, 2);
                    lean_dec_ref_known(v_value_5343_, 3);
                    v___x_5648_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withInlining_check(v_recursive_5360_, v_declName_5647_, v_a_5334_, v_a_5335_, v_a_5336_, v_a_5337_, v_a_5338_, v_a_5339_, v_a_5340_);
                    if lean_obj_tag(v___x_5648_) == 0 {
                        v_a_5649_ = lean_ctor_get(v___x_5648_, 0);
                        lean_inc(v_a_5649_);
                        lean_dec_ref_known(v___x_5648_, 1);
                        v_declName_5650_ = lean_ctor_get(v_a_5334_, 0);
                        v_config_5651_ = lean_ctor_get(v_a_5334_, 1);
                        v_inlineStack_5652_ = lean_ctor_get(v_a_5334_, 2);
                        v_inlineStackOccs_5653_ = lean_ctor_get(v_a_5334_, 3);
                        lean_inc(v_inlineStack_5652_);
                        lean_inc(v_declName_5647_);
                        v___x_5654_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v___x_5654_, 0, v_declName_5647_);
                        lean_ctor_set(v___x_5654_, 1, v_inlineStack_5652_);
                        lean_inc_ref(v_inlineStackOccs_5653_);
                        v___x_5655_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_inlineStackOccs_5653_, v_declName_5647_, v_a_5649_);
                        lean_inc_ref(v_config_5651_);
                        lean_inc(v_declName_5650_);
                        if v_isShared_5346_ == 0 {
                            lean_ctor_set(v___x_5345_, 3, v___x_5655_);
                            lean_ctor_set(v___x_5345_, 2, v___x_5654_);
                            lean_ctor_set(v___x_5345_, 1, v_config_5651_);
                            lean_ctor_set(v___x_5345_, 0, v_declName_5650_);
                            v___x_5657_ = v___x_5345_;
                            state = 57;
                            continue;
                        } else {
                            v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 4, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_5658_, 0, v_declName_5650_);
                            lean_ctor_set(v_reuseFailAlloc_5658_, 1, v_config_5651_);
                            lean_ctor_set(v_reuseFailAlloc_5658_, 2, v___x_5654_);
                            lean_ctor_set(v_reuseFailAlloc_5658_, 3, v___x_5655_);
                            v___x_5657_ = v_reuseFailAlloc_5658_;
                            state = 57;
                            continue;
                        }
                    } else {
                        lean_dec(v_declName_5647_);
                        lean_dec(v___x_5362_);
                        lean_del_object(v___x_5354_);
                        lean_dec(v_val_5352_);
                        lean_del_object(v___x_5345_);
                        lean_dec(v_fvarId_5342_);
                        lean_dec_ref(v_k_5333_);
                        v_a_5659_ = lean_ctor_get(v___x_5648_, 0);
                        v_isSharedCheck_5666_ = (!lean_is_exclusive(v___x_5648_)) as u8;
                        if v_isSharedCheck_5666_ == 0 {
                            v___x_5661_ = v___x_5648_;
                            v_isShared_5662_ = v_isSharedCheck_5666_;
                            state = 58;
                            continue;
                        } else {
                            lean_inc(v_a_5659_);
                            lean_dec(v___x_5648_);
                            v___x_5661_ = lean_box(0);
                            v_isShared_5662_ = v_isSharedCheck_5666_;
                            state = 58;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5345_);
                    lean_dec(v_value_5343_);
                    lean_inc_ref(v_a_5334_);
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
                lean_inc_ref(v___y_5370_);
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
                if lean_obj_tag(v___x_5378_) == 0 {
                    v_a_5379_ = lean_ctor_get(v___x_5378_, 0);
                    lean_inc(v_a_5379_);
                    lean_dec_ref_known(v___x_5378_, 1);
                    v___x_5380_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5374_);
                    if lean_obj_tag(v___x_5380_) == 0 {
                        lean_dec_ref_known(v___x_5380_, 1);
                        v___x_5381_ = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(v_a_5379_);
                        if v___x_5381_ == 0 {
                            lean_dec_ref(v___y_5367_);
                            v___x_5382_ = lean_mk_empty_array_with_capacity(v___y_5366_);
                            lean_dec(v___y_5366_);
                            lean_inc_ref(v___x_5382_);
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
                            if lean_obj_tag(v___x_5384_) == 0 {
                                v_a_5385_ = lean_ctor_get(v___x_5384_, 0);
                                lean_inc_n(v_a_5385_, 2);
                                lean_dec_ref_known(v___x_5384_, 1);
                                v___x_5386_ = l_Lean_Expr_headBeta(v_a_5385_);
                                v___x_5387_ = l_Lean_Expr_isForall(v___x_5386_);
                                lean_dec_ref(v___x_5386_);
                                if v___x_5387_ == 0 {
                                    lean_dec_ref(v___x_5382_);
                                    v___x_5388_ = l_Lean_Compiler_LCNF_mkAuxParam(
                                        v___y_5369_,
                                        v_a_5385_,
                                        v___x_5363_,
                                        v___y_5368_,
                                        v___y_5371_,
                                        v___y_5370_,
                                        v___y_5375_,
                                    );
                                    if lean_obj_tag(v___x_5388_) == 0 {
                                        v_a_5389_ = lean_ctor_get(v___x_5388_, 0);
                                        lean_inc(v_a_5389_);
                                        lean_dec_ref_known(v___x_5388_, 1);
                                        v_fvarId_5390_ = lean_ctor_get(v_a_5389_, 0);
                                        lean_inc(v___y_5375_);
                                        lean_inc_ref(v___y_5370_);
                                        lean_inc(v___y_5371_);
                                        lean_inc_ref(v___y_5368_);
                                        lean_inc_ref(v___y_5372_);
                                        lean_inc(v___y_5374_);
                                        lean_inc(v_fvarId_5390_);
                                        v___x_5391_ = lean_apply_9(
                                            v___y_5376_,
                                            v_fvarId_5390_,
                                            v___y_5373_,
                                            v___y_5374_,
                                            v___y_5372_,
                                            v___y_5368_,
                                            v___y_5371_,
                                            v___y_5370_,
                                            v___y_5375_,
                                            lean_box(0),
                                        );
                                        if lean_obj_tag(v___x_5391_) == 0 {
                                            v_a_5392_ = lean_ctor_get(v___x_5391_, 0);
                                            lean_inc(v_a_5392_);
                                            lean_dec_ref_known(v___x_5391_, 1);
                                            v___x_5393_ = lean_unsigned_to_nat(1);
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
                                            if lean_obj_tag(v___x_5397_) == 0 {
                                                v_a_5398_ = lean_ctor_get(v___x_5397_, 0);
                                                lean_inc_n(v_a_5398_, 2);
                                                lean_dec_ref_known(v___x_5397_, 1);
                                                v___f_5399_ = lean_alloc_closure(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0___boxed as *mut core::ffi::c_void, 8, 2);
                                                lean_closure_set(v___f_5399_, 0, v_a_5398_);
                                                lean_closure_set(v___f_5399_, 1, v___x_5393_);
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
                                                if lean_obj_tag(v___x_5400_) == 0 {
                                                    v_a_5401_ = lean_ctor_get(v___x_5400_, 0);
                                                    v_isSharedCheck_5412_ =
                                                        (!lean_is_exclusive(v___x_5400_)) as u8;
                                                    if v_isSharedCheck_5412_ == 0 {
                                                        v___x_5403_ = v___x_5400_;
                                                        v_isShared_5404_ = v_isSharedCheck_5412_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5401_);
                                                        lean_dec(v___x_5400_);
                                                        v___x_5403_ = lean_box(0);
                                                        v_isShared_5404_ = v_isSharedCheck_5412_;
                                                        state = 5;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_a_5398_);
                                                    lean_del_object(v___x_5354_);
                                                    v_a_5413_ = lean_ctor_get(v___x_5400_, 0);
                                                    v_isSharedCheck_5420_ =
                                                        (!lean_is_exclusive(v___x_5400_)) as u8;
                                                    if v_isSharedCheck_5420_ == 0 {
                                                        v___x_5415_ = v___x_5400_;
                                                        v_isShared_5416_ = v_isSharedCheck_5420_;
                                                        state = 8;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5413_);
                                                        lean_dec(v___x_5400_);
                                                        v___x_5415_ = lean_box(0);
                                                        v_isShared_5416_ = v_isSharedCheck_5420_;
                                                        state = 8;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_5379_);
                                                lean_del_object(v___x_5354_);
                                                v_a_5421_ = lean_ctor_get(v___x_5397_, 0);
                                                v_isSharedCheck_5428_ =
                                                    (!lean_is_exclusive(v___x_5397_)) as u8;
                                                if v_isSharedCheck_5428_ == 0 {
                                                    v___x_5423_ = v___x_5397_;
                                                    v_isShared_5424_ = v_isSharedCheck_5428_;
                                                    state = 10;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5421_);
                                                    lean_dec(v___x_5397_);
                                                    v___x_5423_ = lean_box(0);
                                                    v_isShared_5424_ = v_isSharedCheck_5428_;
                                                    state = 10;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec(v_a_5389_);
                                            lean_dec(v_a_5379_);
                                            lean_del_object(v___x_5354_);
                                            v_a_5429_ = lean_ctor_get(v___x_5391_, 0);
                                            v_isSharedCheck_5436_ =
                                                (!lean_is_exclusive(v___x_5391_)) as u8;
                                            if v_isSharedCheck_5436_ == 0 {
                                                v___x_5431_ = v___x_5391_;
                                                v_isShared_5432_ = v_isSharedCheck_5436_;
                                                state = 12;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5429_);
                                                lean_dec(v___x_5391_);
                                                v___x_5431_ = lean_box(0);
                                                v_isShared_5432_ = v_isSharedCheck_5436_;
                                                state = 12;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_5379_);
                                        lean_dec_ref(v___y_5376_);
                                        lean_dec_ref(v___y_5373_);
                                        lean_del_object(v___x_5354_);
                                        v_a_5437_ = lean_ctor_get(v___x_5388_, 0);
                                        v_isSharedCheck_5444_ =
                                            (!lean_is_exclusive(v___x_5388_)) as u8;
                                        if v_isSharedCheck_5444_ == 0 {
                                            v___x_5439_ = v___x_5388_;
                                            v_isShared_5440_ = v_isSharedCheck_5444_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5437_);
                                            lean_dec(v___x_5388_);
                                            v___x_5439_ = lean_box(0);
                                            v_isShared_5440_ = v_isSharedCheck_5444_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5385_);
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
                                    if lean_obj_tag(v___x_5446_) == 0 {
                                        v_a_5447_ = lean_ctor_get(v___x_5446_, 0);
                                        lean_inc(v_a_5447_);
                                        lean_dec_ref_known(v___x_5446_, 1);
                                        v___x_5448_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(
                                            v_a_5447_,
                                            v___y_5368_,
                                            v___y_5371_,
                                            v___y_5370_,
                                            v___y_5375_,
                                        );
                                        if lean_obj_tag(v___x_5448_) == 0 {
                                            v_a_5449_ = lean_ctor_get(v___x_5448_, 0);
                                            lean_inc(v_a_5449_);
                                            lean_dec_ref_known(v___x_5448_, 1);
                                            v_fvarId_5450_ = lean_ctor_get(v_a_5449_, 0);
                                            lean_inc(v___y_5375_);
                                            lean_inc_ref(v___y_5370_);
                                            lean_inc(v___y_5371_);
                                            lean_inc_ref(v___y_5368_);
                                            lean_inc_ref(v___y_5372_);
                                            lean_inc(v___y_5374_);
                                            lean_inc_ref(v___y_5373_);
                                            lean_inc(v_fvarId_5450_);
                                            v___x_5451_ = lean_apply_9(
                                                v___y_5376_,
                                                v_fvarId_5450_,
                                                v___y_5373_,
                                                v___y_5374_,
                                                v___y_5372_,
                                                v___y_5368_,
                                                v___y_5371_,
                                                v___y_5370_,
                                                v___y_5375_,
                                                lean_box(0),
                                            );
                                            if lean_obj_tag(v___x_5451_) == 0 {
                                                v_a_5452_ = lean_ctor_get(v___x_5451_, 0);
                                                lean_inc(v_a_5452_);
                                                lean_dec_ref_known(v___x_5451_, 1);
                                                v___x_5453_ = lean_alloc_ctor(1, 1, (0) as u32);
                                                lean_ctor_set(v___x_5453_, 0, v_a_5449_);
                                                v___x_5454_ = lean_unsigned_to_nat(1);
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
                                                lean_dec_ref(v___y_5373_);
                                                lean_dec_ref(v___x_5456_);
                                                if lean_obj_tag(v___x_5457_) == 0 {
                                                    v_a_5458_ = lean_ctor_get(v___x_5457_, 0);
                                                    v_isSharedCheck_5468_ =
                                                        (!lean_is_exclusive(v___x_5457_)) as u8;
                                                    if v_isSharedCheck_5468_ == 0 {
                                                        v___x_5460_ = v___x_5457_;
                                                        v_isShared_5461_ = v_isSharedCheck_5468_;
                                                        state = 16;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5458_);
                                                        lean_dec(v___x_5457_);
                                                        v___x_5460_ = lean_box(0);
                                                        v_isShared_5461_ = v_isSharedCheck_5468_;
                                                        state = 16;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_del_object(v___x_5354_);
                                                    v_a_5469_ = lean_ctor_get(v___x_5457_, 0);
                                                    v_isSharedCheck_5476_ =
                                                        (!lean_is_exclusive(v___x_5457_)) as u8;
                                                    if v_isSharedCheck_5476_ == 0 {
                                                        v___x_5471_ = v___x_5457_;
                                                        v_isShared_5472_ = v_isSharedCheck_5476_;
                                                        state = 19;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_5469_);
                                                        lean_dec(v___x_5457_);
                                                        v___x_5471_ = lean_box(0);
                                                        v_isShared_5472_ = v_isSharedCheck_5476_;
                                                        state = 19;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_5449_);
                                                lean_dec_ref(v___y_5373_);
                                                lean_del_object(v___x_5354_);
                                                v_a_5477_ = lean_ctor_get(v___x_5451_, 0);
                                                v_isSharedCheck_5484_ =
                                                    (!lean_is_exclusive(v___x_5451_)) as u8;
                                                if v_isSharedCheck_5484_ == 0 {
                                                    v___x_5479_ = v___x_5451_;
                                                    v_isShared_5480_ = v_isSharedCheck_5484_;
                                                    state = 21;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_5477_);
                                                    lean_dec(v___x_5451_);
                                                    v___x_5479_ = lean_box(0);
                                                    v_isShared_5480_ = v_isSharedCheck_5484_;
                                                    state = 21;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___y_5376_);
                                            lean_dec_ref(v___y_5373_);
                                            lean_del_object(v___x_5354_);
                                            v_a_5485_ = lean_ctor_get(v___x_5448_, 0);
                                            v_isSharedCheck_5492_ =
                                                (!lean_is_exclusive(v___x_5448_)) as u8;
                                            if v_isSharedCheck_5492_ == 0 {
                                                v___x_5487_ = v___x_5448_;
                                                v_isShared_5488_ = v_isSharedCheck_5492_;
                                                state = 23;
                                                continue;
                                            } else {
                                                lean_inc(v_a_5485_);
                                                lean_dec(v___x_5448_);
                                                v___x_5487_ = lean_box(0);
                                                v_isShared_5488_ = v_isSharedCheck_5492_;
                                                state = 23;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec_ref(v___y_5376_);
                                        lean_dec_ref(v___y_5373_);
                                        lean_del_object(v___x_5354_);
                                        v_a_5493_ = lean_ctor_get(v___x_5446_, 0);
                                        v_isSharedCheck_5500_ =
                                            (!lean_is_exclusive(v___x_5446_)) as u8;
                                        if v_isSharedCheck_5500_ == 0 {
                                            v___x_5495_ = v___x_5446_;
                                            v_isShared_5496_ = v_isSharedCheck_5500_;
                                            state = 25;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5493_);
                                            lean_dec(v___x_5446_);
                                            v___x_5495_ = lean_box(0);
                                            v_isShared_5496_ = v_isSharedCheck_5500_;
                                            state = 25;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v___x_5382_);
                                lean_dec(v_a_5379_);
                                lean_dec_ref(v___y_5376_);
                                lean_dec_ref(v___y_5373_);
                                lean_del_object(v___x_5354_);
                                v_a_5501_ = lean_ctor_get(v___x_5384_, 0);
                                v_isSharedCheck_5508_ = (!lean_is_exclusive(v___x_5384_)) as u8;
                                if v_isSharedCheck_5508_ == 0 {
                                    v___x_5503_ = v___x_5384_;
                                    v_isShared_5504_ = v_isSharedCheck_5508_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_inc(v_a_5501_);
                                    lean_dec(v___x_5384_);
                                    v___x_5503_ = lean_box(0);
                                    v_isShared_5504_ = v_isSharedCheck_5508_;
                                    state = 27;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v___y_5376_);
                            lean_dec_ref(v___y_5373_);
                            lean_dec(v___y_5366_);
                            lean_dec_ref(v___y_5365_);
                            lean_dec_ref(v_fType_5358_);
                            v___x_5509_ = l_Lean_Compiler_LCNF_CompilerM_codeBind(
                                v___y_5369_,
                                v_a_5379_,
                                v___y_5367_,
                                v___y_5368_,
                                v___y_5371_,
                                v___y_5370_,
                                v___y_5375_,
                            );
                            if lean_obj_tag(v___x_5509_) == 0 {
                                v_a_5510_ = lean_ctor_get(v___x_5509_, 0);
                                v_isSharedCheck_5520_ = (!lean_is_exclusive(v___x_5509_)) as u8;
                                if v_isSharedCheck_5520_ == 0 {
                                    v___x_5512_ = v___x_5509_;
                                    v_isShared_5513_ = v_isSharedCheck_5520_;
                                    state = 29;
                                    continue;
                                } else {
                                    lean_inc(v_a_5510_);
                                    lean_dec(v___x_5509_);
                                    v___x_5512_ = lean_box(0);
                                    v_isShared_5513_ = v_isSharedCheck_5520_;
                                    state = 29;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_5354_);
                                v_a_5521_ = lean_ctor_get(v___x_5509_, 0);
                                v_isSharedCheck_5528_ = (!lean_is_exclusive(v___x_5509_)) as u8;
                                if v_isSharedCheck_5528_ == 0 {
                                    v___x_5523_ = v___x_5509_;
                                    v_isShared_5524_ = v_isSharedCheck_5528_;
                                    state = 32;
                                    continue;
                                } else {
                                    lean_inc(v_a_5521_);
                                    lean_dec(v___x_5509_);
                                    v___x_5523_ = lean_box(0);
                                    v_isShared_5524_ = v_isSharedCheck_5528_;
                                    state = 32;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_5379_);
                        lean_dec_ref(v___y_5376_);
                        lean_dec_ref(v___y_5373_);
                        lean_dec_ref(v___y_5367_);
                        lean_dec(v___y_5366_);
                        lean_dec_ref(v___y_5365_);
                        lean_dec_ref(v_fType_5358_);
                        lean_del_object(v___x_5354_);
                        v_a_5529_ = lean_ctor_get(v___x_5380_, 0);
                        v_isSharedCheck_5536_ = (!lean_is_exclusive(v___x_5380_)) as u8;
                        if v_isSharedCheck_5536_ == 0 {
                            v___x_5531_ = v___x_5380_;
                            v_isShared_5532_ = v_isSharedCheck_5536_;
                            state = 34;
                            continue;
                        } else {
                            lean_inc(v_a_5529_);
                            lean_dec(v___x_5380_);
                            v___x_5531_ = lean_box(0);
                            v_isShared_5532_ = v_isSharedCheck_5536_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_5376_);
                    lean_dec_ref(v___y_5373_);
                    lean_dec_ref(v___y_5367_);
                    lean_dec(v___y_5366_);
                    lean_dec_ref(v___y_5365_);
                    lean_dec_ref(v_fType_5358_);
                    lean_del_object(v___x_5354_);
                    v_a_5537_ = lean_ctor_get(v___x_5378_, 0);
                    v_isSharedCheck_5544_ = (!lean_is_exclusive(v___x_5378_)) as u8;
                    if v_isSharedCheck_5544_ == 0 {
                        v___x_5539_ = v___x_5378_;
                        v_isShared_5540_ = v_isSharedCheck_5544_;
                        state = 36;
                        continue;
                    } else {
                        lean_inc(v_a_5537_);
                        lean_dec(v___x_5378_);
                        v___x_5539_ = lean_box(0);
                        v_isShared_5540_ = v_isSharedCheck_5544_;
                        state = 36;
                        continue;
                    }
                }
            }
            5 => {
                v___x_5405_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_5405_, 0, v_a_5398_);
                lean_ctor_set(v___x_5405_, 1, v_a_5401_);
                if v_isShared_5355_ == 0 {
                    lean_ctor_set(v___x_5354_, 0, v___x_5405_);
                    v___x_5407_ = v___x_5354_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5411_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5411_, 0, v___x_5405_);
                    v___x_5407_ = v_reuseFailAlloc_5411_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_5404_ == 0 {
                    lean_ctor_set(v___x_5403_, 0, v___x_5407_);
                    v___x_5409_ = v___x_5403_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5410_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5410_, 0, v___x_5407_);
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
                    v_reuseFailAlloc_5419_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5419_, 0, v_a_5413_);
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
                    v_reuseFailAlloc_5427_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5427_, 0, v_a_5421_);
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
                    v_reuseFailAlloc_5435_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5435_, 0, v_a_5429_);
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
                    v_reuseFailAlloc_5443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5443_, 0, v_a_5437_);
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
                    lean_ctor_set(v___x_5354_, 0, v_a_5458_);
                    v___x_5463_ = v___x_5354_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_5467_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5467_, 0, v_a_5458_);
                    v___x_5463_ = v_reuseFailAlloc_5467_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v_isShared_5461_ == 0 {
                    lean_ctor_set(v___x_5460_, 0, v___x_5463_);
                    v___x_5465_ = v___x_5460_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5463_);
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
                    v_reuseFailAlloc_5475_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5475_, 0, v_a_5469_);
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
                    v_reuseFailAlloc_5483_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5483_, 0, v_a_5477_);
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
                    v_reuseFailAlloc_5491_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5491_, 0, v_a_5485_);
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
                    v_reuseFailAlloc_5499_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5499_, 0, v_a_5493_);
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
                    v_reuseFailAlloc_5507_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5507_, 0, v_a_5501_);
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
                    lean_ctor_set(v___x_5354_, 0, v_a_5510_);
                    v___x_5515_ = v___x_5354_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5519_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5519_, 0, v_a_5510_);
                    v___x_5515_ = v_reuseFailAlloc_5519_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_5513_ == 0 {
                    lean_ctor_set(v___x_5512_, 0, v___x_5515_);
                    v___x_5517_ = v___x_5512_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_5518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5518_, 0, v___x_5515_);
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
                    v_reuseFailAlloc_5527_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5527_, 0, v_a_5521_);
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
                    v_reuseFailAlloc_5535_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5535_, 0, v_a_5529_);
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
                    v_reuseFailAlloc_5543_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5543_, 0, v_a_5537_);
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
                    lean_inc_ref_n(v_args_5359_, 2);
                    lean_inc_ref(v_fType_5358_);
                    lean_inc_ref(v_value_5357_);
                    lean_inc_ref(v_params_5356_);
                    lean_dec(v_val_5352_);
                    v___x_5553_ = lean_unsigned_to_nat(0);
                    lean_inc(v___x_5362_);
                    v___x_5554_ =
                        l_Array_toSubarray___redArg(v_args_5359_, v___x_5553_, v___x_5362_);
                    lean_inc_ref(v___x_5554_);
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
                    lean_dec_ref(v_params_5356_);
                    if lean_obj_tag(v___x_5556_) == 0 {
                        v_a_5557_ = lean_ctor_get(v___x_5556_, 0);
                        lean_inc(v_a_5557_);
                        lean_dec_ref_known(v___x_5556_, 1);
                        v___x_5558_ = 0;
                        v___x_5559_ = lean_box((v___x_5558_) as usize);
                        lean_inc_ref(v_k_5333_);
                        lean_inc(v_fvarId_5342_);
                        lean_inc(v___x_5362_);
                        v___f_5560_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed
                                as *mut core::ffi::c_void,
                            16,
                            7,
                        );
                        lean_closure_set(v___f_5560_, 0, v___x_5362_);
                        lean_closure_set(v___f_5560_, 1, v___x_5361_);
                        lean_closure_set(v___f_5560_, 2, v_fvarId_5342_);
                        lean_closure_set(v___f_5560_, 3, v_k_5333_);
                        lean_closure_set(v___f_5560_, 4, v_args_5359_);
                        lean_closure_set(v___f_5560_, 5, v___x_5559_);
                        lean_closure_set(v___f_5560_, 6, v___x_5553_);
                        lean_inc_ref(v___y_5548_);
                        lean_inc_ref(v___y_5546_);
                        lean_inc_ref(v___f_5560_);
                        lean_inc(v___y_5547_);
                        v___f_5561_ = lean_alloc_closure(
                            l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2___boxed
                                as *mut core::ffi::c_void,
                            10,
                            4,
                        );
                        lean_closure_set(v___f_5561_, 0, v___y_5547_);
                        lean_closure_set(v___f_5561_, 1, v___f_5560_);
                        lean_closure_set(v___f_5561_, 2, v___y_5546_);
                        lean_closure_set(v___f_5561_, 3, v___y_5548_);
                        v___x_5562_ = l_Lean_Compiler_LCNF_Code_isReturnOf___redArg(
                            v_k_5333_,
                            v_fvarId_5342_,
                        );
                        lean_dec(v_fvarId_5342_);
                        lean_dec_ref(v_k_5333_);
                        if v___x_5562_ == 0 {
                            lean_dec(v___x_5362_);
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
                            lean_dec(v___x_5362_);
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
                                lean_dec_ref(v___f_5561_);
                                lean_dec_ref(v___f_5560_);
                                lean_dec_ref(v___x_5554_);
                                lean_dec_ref(v_fType_5358_);
                                lean_del_object(v___x_5354_);
                                v___x_5564_ =
                                    l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5547_);
                                if lean_obj_tag(v___x_5564_) == 0 {
                                    lean_dec_ref_known(v___x_5564_, 1);
                                    lean_inc_ref(v___y_5551_);
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
                                    lean_dec_ref(v___y_5546_);
                                    if lean_obj_tag(v___x_5565_) == 0 {
                                        v_a_5566_ = lean_ctor_get(v___x_5565_, 0);
                                        v_isSharedCheck_5574_ =
                                            (!lean_is_exclusive(v___x_5565_)) as u8;
                                        if v_isSharedCheck_5574_ == 0 {
                                            v___x_5568_ = v___x_5565_;
                                            v_isShared_5569_ = v_isSharedCheck_5574_;
                                            state = 39;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5566_);
                                            lean_dec(v___x_5565_);
                                            v___x_5568_ = lean_box(0);
                                            v_isShared_5569_ = v_isSharedCheck_5574_;
                                            state = 39;
                                            continue;
                                        }
                                    } else {
                                        v_a_5575_ = lean_ctor_get(v___x_5565_, 0);
                                        v_isSharedCheck_5582_ =
                                            (!lean_is_exclusive(v___x_5565_)) as u8;
                                        if v_isSharedCheck_5582_ == 0 {
                                            v___x_5577_ = v___x_5565_;
                                            v_isShared_5578_ = v_isSharedCheck_5582_;
                                            state = 41;
                                            continue;
                                        } else {
                                            lean_inc(v_a_5575_);
                                            lean_dec(v___x_5565_);
                                            v___x_5577_ = lean_box(0);
                                            v_isShared_5578_ = v_isSharedCheck_5582_;
                                            state = 41;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_5557_);
                                    lean_dec_ref(v___y_5546_);
                                    v_a_5583_ = lean_ctor_get(v___x_5564_, 0);
                                    v_isSharedCheck_5590_ = (!lean_is_exclusive(v___x_5564_)) as u8;
                                    if v_isSharedCheck_5590_ == 0 {
                                        v___x_5585_ = v___x_5564_;
                                        v_isShared_5586_ = v_isSharedCheck_5590_;
                                        state = 43;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5583_);
                                        lean_dec(v___x_5564_);
                                        v___x_5585_ = lean_box(0);
                                        v_isShared_5586_ = v_isSharedCheck_5590_;
                                        state = 43;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec_ref(v___x_5554_);
                        lean_dec_ref(v___y_5546_);
                        lean_dec(v___x_5362_);
                        lean_dec_ref(v_args_5359_);
                        lean_dec_ref(v_fType_5358_);
                        lean_del_object(v___x_5354_);
                        lean_dec(v_fvarId_5342_);
                        lean_dec_ref(v_k_5333_);
                        v_a_5591_ = lean_ctor_get(v___x_5556_, 0);
                        v_isSharedCheck_5598_ = (!lean_is_exclusive(v___x_5556_)) as u8;
                        if v_isSharedCheck_5598_ == 0 {
                            v___x_5593_ = v___x_5556_;
                            v_isShared_5594_ = v_isSharedCheck_5598_;
                            state = 45;
                            continue;
                        } else {
                            lean_inc(v_a_5591_);
                            lean_dec(v___x_5556_);
                            v___x_5593_ = lean_box(0);
                            v_isShared_5594_ = v_isSharedCheck_5598_;
                            state = 45;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_5362_);
                    lean_del_object(v___x_5354_);
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
                    if lean_obj_tag(v___x_5599_) == 0 {
                        v_a_5600_ = lean_ctor_get(v___x_5599_, 0);
                        lean_inc(v_a_5600_);
                        lean_dec_ref_known(v___x_5599_, 1);
                        v_fvarId_5601_ = lean_ctor_get(v_a_5600_, 0);
                        lean_inc(v_fvarId_5601_);
                        v___x_5602_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                            v_fvarId_5342_,
                            v_fvarId_5601_,
                            v___y_5547_,
                            v___y_5549_,
                            v___y_5550_,
                            v___y_5551_,
                            v___y_5552_,
                        );
                        if lean_obj_tag(v___x_5602_) == 0 {
                            lean_dec_ref_known(v___x_5602_, 1);
                            v___x_5603_ =
                                l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5547_);
                            if lean_obj_tag(v___x_5603_) == 0 {
                                lean_dec_ref_known(v___x_5603_, 1);
                                v___x_5604_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_5604_, 0, v_a_5600_);
                                lean_ctor_set(v___x_5604_, 1, v_k_5333_);
                                lean_inc_ref(v___y_5551_);
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
                                lean_dec_ref(v___y_5546_);
                                if lean_obj_tag(v___x_5605_) == 0 {
                                    v_a_5606_ = lean_ctor_get(v___x_5605_, 0);
                                    v_isSharedCheck_5614_ = (!lean_is_exclusive(v___x_5605_)) as u8;
                                    if v_isSharedCheck_5614_ == 0 {
                                        v___x_5608_ = v___x_5605_;
                                        v_isShared_5609_ = v_isSharedCheck_5614_;
                                        state = 47;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5606_);
                                        lean_dec(v___x_5605_);
                                        v___x_5608_ = lean_box(0);
                                        v_isShared_5609_ = v_isSharedCheck_5614_;
                                        state = 47;
                                        continue;
                                    }
                                } else {
                                    v_a_5615_ = lean_ctor_get(v___x_5605_, 0);
                                    v_isSharedCheck_5622_ = (!lean_is_exclusive(v___x_5605_)) as u8;
                                    if v_isSharedCheck_5622_ == 0 {
                                        v___x_5617_ = v___x_5605_;
                                        v_isShared_5618_ = v_isSharedCheck_5622_;
                                        state = 49;
                                        continue;
                                    } else {
                                        lean_inc(v_a_5615_);
                                        lean_dec(v___x_5605_);
                                        v___x_5617_ = lean_box(0);
                                        v_isShared_5618_ = v_isSharedCheck_5622_;
                                        state = 49;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_5600_);
                                lean_dec_ref(v___y_5546_);
                                lean_dec_ref(v_k_5333_);
                                v_a_5623_ = lean_ctor_get(v___x_5603_, 0);
                                v_isSharedCheck_5630_ = (!lean_is_exclusive(v___x_5603_)) as u8;
                                if v_isSharedCheck_5630_ == 0 {
                                    v___x_5625_ = v___x_5603_;
                                    v_isShared_5626_ = v_isSharedCheck_5630_;
                                    state = 51;
                                    continue;
                                } else {
                                    lean_inc(v_a_5623_);
                                    lean_dec(v___x_5603_);
                                    v___x_5625_ = lean_box(0);
                                    v_isShared_5626_ = v_isSharedCheck_5630_;
                                    state = 51;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5600_);
                            lean_dec_ref(v___y_5546_);
                            lean_dec_ref(v_k_5333_);
                            v_a_5631_ = lean_ctor_get(v___x_5602_, 0);
                            v_isSharedCheck_5638_ = (!lean_is_exclusive(v___x_5602_)) as u8;
                            if v_isSharedCheck_5638_ == 0 {
                                v___x_5633_ = v___x_5602_;
                                v_isShared_5634_ = v_isSharedCheck_5638_;
                                state = 53;
                                continue;
                            } else {
                                lean_inc(v_a_5631_);
                                lean_dec(v___x_5602_);
                                v___x_5633_ = lean_box(0);
                                v_isShared_5634_ = v_isSharedCheck_5638_;
                                state = 53;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v___y_5546_);
                        lean_dec(v_fvarId_5342_);
                        lean_dec_ref(v_k_5333_);
                        v_a_5639_ = lean_ctor_get(v___x_5599_, 0);
                        v_isSharedCheck_5646_ = (!lean_is_exclusive(v___x_5599_)) as u8;
                        if v_isSharedCheck_5646_ == 0 {
                            v___x_5641_ = v___x_5599_;
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 55;
                            continue;
                        } else {
                            lean_inc(v_a_5639_);
                            lean_dec(v___x_5599_);
                            v___x_5641_ = lean_box(0);
                            v_isShared_5642_ = v_isSharedCheck_5646_;
                            state = 55;
                            continue;
                        }
                    }
                }
            }
            39 => {
                v___x_5570_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5570_, 0, v_a_5566_);
                if v_isShared_5569_ == 0 {
                    lean_ctor_set(v___x_5568_, 0, v___x_5570_);
                    v___x_5572_ = v___x_5568_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5570_);
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
                    v_reuseFailAlloc_5581_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5581_, 0, v_a_5575_);
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
                    v_reuseFailAlloc_5589_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5589_, 0, v_a_5583_);
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
                    v_reuseFailAlloc_5597_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5597_, 0, v_a_5591_);
                    v___x_5596_ = v_reuseFailAlloc_5597_;
                    state = 46;
                    continue;
                }
            }
            46 => {
                return v___x_5596_;
            }
            47 => {
                v___x_5610_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5610_, 0, v_a_5606_);
                if v_isShared_5609_ == 0 {
                    lean_ctor_set(v___x_5608_, 0, v___x_5610_);
                    v___x_5612_ = v___x_5608_;
                    state = 48;
                    continue;
                } else {
                    v_reuseFailAlloc_5613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5613_, 0, v___x_5610_);
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
                    v_reuseFailAlloc_5621_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5621_, 0, v_a_5615_);
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
                    v_reuseFailAlloc_5629_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5629_, 0, v_a_5623_);
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
                    v_reuseFailAlloc_5637_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5637_, 0, v_a_5631_);
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
                    v_reuseFailAlloc_5645_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5645_, 0, v_a_5639_);
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
                    v_reuseFailAlloc_5665_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5665_, 0, v_a_5659_);
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
                    v_reuseFailAlloc_5679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5679_, 0, v_a_5673_);
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
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___closed__0() -> *mut LeanObject {
    let mut v___x_5684_: u8 = 0;
    let mut v___x_5685_: *mut LeanObject = core::ptr::null_mut();
    v___x_5684_ = 0;
    v___x_5685_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_5684_);
    return v___x_5685_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(
    mut v_cases_5686_: *mut LeanObject,
    mut v_a_5687_: *mut LeanObject,
    mut v_a_5688_: *mut LeanObject,
    mut v_a_5689_: *mut LeanObject,
    mut v_a_5690_: *mut LeanObject,
    mut v_a_5691_: *mut LeanObject,
    mut v_a_5692_: *mut LeanObject,
    mut v_a_5693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_5698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_5699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_5701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5702_: u8 = 0;
    let mut v___x_5703_: u8 = 0;
    let mut v___x_5704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5710_: u8 = 0;
    let mut v_val_5711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5714_: u8 = 0;
    let mut v___x_5715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_5716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5722_: u8 = 0;
    let mut v_val_5723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5726_: u8 = 0;
    let mut v_induct_5727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: u8 = 0;
    let mut v___x_5729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_5734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5738_: u8 = 0;
    let mut v___x_5740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5743_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_5746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_5748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_5749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5751_: usize = 0;
    let mut v___x_5752_: usize = 0;
    let mut v___x_5753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5759_: u8 = 0;
    let mut v___x_5761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5766_: u8 = 0;
    let mut v_unused_5767_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5771_: u8 = 0;
    let mut v___x_5773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5775_: u8 = 0;
    let mut v_a_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5779_: u8 = 0;
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5783_: u8 = 0;
    let mut v_a_5784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5787_: u8 = 0;
    let mut v___x_5789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5791_: u8 = 0;
    let mut v_numParams_5792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5795_: u8 = 0;
    let mut v_params_5796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5801_: u8 = 0;
    let mut v_zero_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_5803_: u8 = 0;
    let mut v___x_5804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5808_: u8 = 0;
    let mut v___x_5810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5815_: u8 = 0;
    let mut v_a_5816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5819_: u8 = 0;
    let mut v___x_5821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5823_: u8 = 0;
    let mut v_one_5824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_5825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_5836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5843_: u8 = 0;
    let mut v___x_5845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5853_: u8 = 0;
    let mut v_unused_5854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5858_: u8 = 0;
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5862_: u8 = 0;
    let mut v_a_5863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5866_: u8 = 0;
    let mut v___x_5868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5870_: u8 = 0;
    let mut v_a_5871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5874_: u8 = 0;
    let mut v___x_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5878_: u8 = 0;
    let mut v_a_5879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5882_: u8 = 0;
    let mut v___x_5884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5886_: u8 = 0;
    let mut v_reuseFailAlloc_5887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5889_: u8 = 0;
    let mut v_code_5890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5895_: u8 = 0;
    let mut v___x_5897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5902_: u8 = 0;
    let mut v_a_5903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5906_: u8 = 0;
    let mut v___x_5908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5910_: u8 = 0;
    let mut v_a_5911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5914_: u8 = 0;
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5918_: u8 = 0;
    let mut v_a_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5922_: u8 = 0;
    let mut v___x_5924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5926_: u8 = 0;
    let mut v_reuseFailAlloc_5927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5928_: u8 = 0;
    let mut v_isSharedCheck_5929_: u8 = 0;
    let mut v_isSharedCheck_5930_: u8 = 0;
    let mut v_isSharedCheck_5931_: u8 = 0;
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5936_: u8 = 0;
    let mut v_a_5937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5940_: u8 = 0;
    let mut v___x_5942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5944_: u8 = 0;
    let mut v___x_5945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5949_: u8 = 0;
    let mut v___x_5950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5954_: u8 = 0;
    let mut v_a_5955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5958_: u8 = 0;
    let mut v___x_5960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5962_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_typeName_5698_ = lean_ctor_get(v_cases_5686_, 0);
                v_discr_5699_ = lean_ctor_get(v_cases_5686_, 2);
                v___x_5700_ = lean_st_ref_get(v_a_5688_);
                v_subst_5701_ = lean_ctor_get(v___x_5700_, 0);
                lean_inc_ref(v_subst_5701_);
                lean_dec(v___x_5700_);
                v___x_5702_ = 0;
                v___x_5703_ = 0;
                lean_inc(v_discr_5699_);
                v___x_5704_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                    v_subst_5701_,
                    v_discr_5699_,
                    v___x_5703_,
                );
                lean_dec_ref(v_subst_5701_);
                if lean_obj_tag(v___x_5704_) == 0 {
                    v_fvarId_5705_ = lean_ctor_get(v___x_5704_, 0);
                    lean_inc(v_fvarId_5705_);
                    lean_dec_ref_known(v___x_5704_, 1);
                    v___x_5706_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
                        v_fvarId_5705_,
                        v_a_5689_,
                        v_a_5691_,
                        v_a_5693_,
                    );
                    lean_dec(v_fvarId_5705_);
                    if lean_obj_tag(v___x_5706_) == 0 {
                        v_a_5707_ = lean_ctor_get(v___x_5706_, 0);
                        v_isSharedCheck_5936_ = (!lean_is_exclusive(v___x_5706_)) as u8;
                        if v_isSharedCheck_5936_ == 0 {
                            v___x_5709_ = v___x_5706_;
                            v_isShared_5710_ = v_isSharedCheck_5936_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_5707_);
                            lean_dec(v___x_5706_);
                            v___x_5709_ = lean_box(0);
                            v_isShared_5710_ = v_isSharedCheck_5936_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_cases_5686_);
                        v_a_5937_ = lean_ctor_get(v___x_5706_, 0);
                        v_isSharedCheck_5944_ = (!lean_is_exclusive(v___x_5706_)) as u8;
                        if v_isSharedCheck_5944_ == 0 {
                            v___x_5939_ = v___x_5706_;
                            v_isShared_5940_ = v_isSharedCheck_5944_;
                            state = 49;
                            continue;
                        } else {
                            lean_inc(v_a_5937_);
                            lean_dec(v___x_5706_);
                            v___x_5939_ = lean_box(0);
                            v_isShared_5940_ = v_isSharedCheck_5944_;
                            state = 49;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_cases_5686_);
                    v___x_5945_ = l_Lean_Compiler_LCNF_mkReturnErased(
                        v___x_5702_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                    );
                    if lean_obj_tag(v___x_5945_) == 0 {
                        v_a_5946_ = lean_ctor_get(v___x_5945_, 0);
                        v_isSharedCheck_5954_ = (!lean_is_exclusive(v___x_5945_)) as u8;
                        if v_isSharedCheck_5954_ == 0 {
                            v___x_5948_ = v___x_5945_;
                            v_isShared_5949_ = v_isSharedCheck_5954_;
                            state = 51;
                            continue;
                        } else {
                            lean_inc(v_a_5946_);
                            lean_dec(v___x_5945_);
                            v___x_5948_ = lean_box(0);
                            v_isShared_5949_ = v_isSharedCheck_5954_;
                            state = 51;
                            continue;
                        }
                    } else {
                        v_a_5955_ = lean_ctor_get(v___x_5945_, 0);
                        v_isSharedCheck_5962_ = (!lean_is_exclusive(v___x_5945_)) as u8;
                        if v_isSharedCheck_5962_ == 0 {
                            v___x_5957_ = v___x_5945_;
                            v_isShared_5958_ = v_isSharedCheck_5962_;
                            state = 53;
                            continue;
                        } else {
                            lean_inc(v_a_5955_);
                            lean_dec(v___x_5945_);
                            v___x_5957_ = lean_box(0);
                            v_isShared_5958_ = v_isSharedCheck_5962_;
                            state = 53;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5696_ = lean_box(0);
                v___x_5697_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_5697_, 0, v___x_5696_);
                return v___x_5697_;
            }
            2 => {
                if lean_obj_tag(v_a_5707_) == 1 {
                    v_val_5711_ = lean_ctor_get(v_a_5707_, 0);
                    v_isSharedCheck_5931_ = (!lean_is_exclusive(v_a_5707_)) as u8;
                    if v_isSharedCheck_5931_ == 0 {
                        v___x_5713_ = v_a_5707_;
                        v_isShared_5714_ = v_isSharedCheck_5931_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_val_5711_);
                        lean_dec(v_a_5707_);
                        v___x_5713_ = lean_box(0);
                        v_isShared_5714_ = v_isSharedCheck_5931_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_5707_);
                    lean_dec_ref(v_cases_5686_);
                    v___x_5932_ = lean_box(0);
                    if v_isShared_5710_ == 0 {
                        lean_ctor_set(v___x_5709_, 0, v___x_5932_);
                        v___x_5934_ = v___x_5709_;
                        state = 48;
                        continue;
                    } else {
                        v_reuseFailAlloc_5935_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5935_, 0, v___x_5932_);
                        v___x_5934_ = v_reuseFailAlloc_5935_;
                        state = 48;
                        continue;
                    }
                }
            }
            3 => {
                v___x_5715_ = lean_st_ref_get(v_a_5693_);
                v_env_5716_ = lean_ctor_get(v___x_5715_, 0);
                lean_inc_ref(v_env_5716_);
                lean_dec(v___x_5715_);
                v___x_5717_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_5711_);
                lean_inc(v___x_5717_);
                v___x_5718_ = l_Lean_Environment_find_x3f(v_env_5716_, v___x_5717_, v___x_5703_);
                if lean_obj_tag(v___x_5718_) == 1 {
                    v_val_5719_ = lean_ctor_get(v___x_5718_, 0);
                    v_isSharedCheck_5930_ = (!lean_is_exclusive(v___x_5718_)) as u8;
                    if v_isSharedCheck_5930_ == 0 {
                        v___x_5721_ = v___x_5718_;
                        v_isShared_5722_ = v_isSharedCheck_5930_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_val_5719_);
                        lean_dec(v___x_5718_);
                        v___x_5721_ = lean_box(0);
                        v_isShared_5722_ = v_isSharedCheck_5930_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_5718_);
                    lean_dec(v___x_5717_);
                    lean_del_object(v___x_5713_);
                    lean_dec(v_val_5711_);
                    lean_del_object(v___x_5709_);
                    lean_dec_ref(v_cases_5686_);
                    state = 1;
                    continue;
                }
            }
            4 => {
                if lean_obj_tag(v_val_5719_) == 6 {
                    v_val_5723_ = lean_ctor_get(v_val_5719_, 0);
                    v_isSharedCheck_5929_ = (!lean_is_exclusive(v_val_5719_)) as u8;
                    if v_isSharedCheck_5929_ == 0 {
                        v___x_5725_ = v_val_5719_;
                        v_isShared_5726_ = v_isSharedCheck_5929_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_val_5723_);
                        lean_dec(v_val_5719_);
                        v___x_5725_ = lean_box(0);
                        v_isShared_5726_ = v_isSharedCheck_5929_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5721_);
                    lean_dec(v_val_5719_);
                    lean_dec(v___x_5717_);
                    lean_del_object(v___x_5713_);
                    lean_dec(v_val_5711_);
                    lean_del_object(v___x_5709_);
                    lean_dec_ref(v_cases_5686_);
                    state = 1;
                    continue;
                }
            }
            5 => {
                v_induct_5727_ = lean_ctor_get(v_val_5723_, 1);
                lean_inc(v_induct_5727_);
                lean_dec_ref(v_val_5723_);
                v___x_5728_ = lean_name_eq(v_typeName_5698_, v_induct_5727_);
                lean_dec(v_induct_5727_);
                if v___x_5728_ == 0 {
                    lean_del_object(v___x_5725_);
                    lean_del_object(v___x_5721_);
                    lean_dec(v___x_5717_);
                    lean_del_object(v___x_5713_);
                    lean_dec(v_val_5711_);
                    lean_dec_ref(v_cases_5686_);
                    v___x_5729_ = lean_box(0);
                    if v_isShared_5710_ == 0 {
                        lean_ctor_set(v___x_5709_, 0, v___x_5729_);
                        v___x_5731_ = v___x_5709_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_5732_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5732_, 0, v___x_5729_);
                        v___x_5731_ = v_reuseFailAlloc_5732_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5709_);
                    v___x_5733_ = l_Lean_Compiler_LCNF_Cases_extractAlt_x21(
                        v___x_5702_,
                        v_cases_5686_,
                        v___x_5717_,
                    );
                    v_fst_5734_ = lean_ctor_get(v___x_5733_, 0);
                    v_snd_5735_ = lean_ctor_get(v___x_5733_, 1);
                    v_isSharedCheck_5928_ = (!lean_is_exclusive(v___x_5733_)) as u8;
                    if v_isSharedCheck_5928_ == 0 {
                        v___x_5737_ = v___x_5733_;
                        v_isShared_5738_ = v_isSharedCheck_5928_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_snd_5735_);
                        lean_inc(v_fst_5734_);
                        lean_dec(v___x_5733_);
                        v___x_5737_ = lean_box(0);
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
                    lean_ctor_set_tag(v___x_5725_, 4);
                    lean_ctor_set(v___x_5725_, 0, v_snd_5735_);
                    v___x_5740_ = v___x_5725_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5927_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5927_, 0, v_snd_5735_);
                    v___x_5740_ = v_reuseFailAlloc_5927_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5741_ =
                    l_Lean_Compiler_LCNF_eraseCode___redArg(v___x_5702_, v___x_5740_, v_a_5691_);
                lean_dec_ref(v___x_5740_);
                if lean_obj_tag(v___x_5741_) == 0 {
                    lean_dec_ref_known(v___x_5741_, 1);
                    v___x_5742_ = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v_a_5688_);
                    if lean_obj_tag(v___x_5742_) == 0 {
                        lean_dec_ref_known(v___x_5742_, 1);
                        if lean_obj_tag(v_fst_5734_) == 0 {
                            if lean_obj_tag(v_val_5711_) == 0 {
                                lean_del_object(v___x_5737_);
                                lean_del_object(v___x_5713_);
                                v_params_5743_ = lean_ctor_get(v_fst_5734_, 1);
                                lean_inc_ref(v_params_5743_);
                                v_code_5744_ = lean_ctor_get(v_fst_5734_, 2);
                                lean_inc_ref(v_code_5744_);
                                lean_dec_ref_known(v_fst_5734_, 3);
                                v_val_5745_ = lean_ctor_get(v_val_5711_, 0);
                                lean_inc_ref(v_val_5745_);
                                v_args_5746_ = lean_ctor_get(v_val_5711_, 1);
                                lean_inc_ref(v_args_5746_);
                                lean_dec_ref_known(v_val_5711_, 2);
                                v_numParams_5792_ = lean_ctor_get(v_val_5745_, 3);
                                lean_inc(v_numParams_5792_);
                                lean_dec_ref(v_val_5745_);
                                v___x_5793_ = lean_unsigned_to_nat(0);
                                v___x_5794_ = lean_array_get_size(v_args_5746_);
                                v___x_5795_ = lean_nat_dec_le(v_numParams_5792_, v___x_5793_);
                                if v___x_5795_ == 0 {
                                    v_lower_5748_ = v_numParams_5792_;
                                    v_upper_5749_ = v___x_5794_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_dec(v_numParams_5792_);
                                    v_lower_5748_ = v___x_5793_;
                                    v_upper_5749_ = v___x_5794_;
                                    state = 9;
                                    continue;
                                }
                            } else {
                                v_params_5796_ = lean_ctor_get(v_fst_5734_, 1);
                                lean_inc_ref(v_params_5796_);
                                v_code_5797_ = lean_ctor_get(v_fst_5734_, 2);
                                lean_inc_ref(v_code_5797_);
                                lean_dec_ref_known(v_fst_5734_, 3);
                                v_n_5798_ = lean_ctor_get(v_val_5711_, 0);
                                v_isSharedCheck_5889_ = (!lean_is_exclusive(v_val_5711_)) as u8;
                                if v_isSharedCheck_5889_ == 0 {
                                    v___x_5800_ = v_val_5711_;
                                    v_isShared_5801_ = v_isSharedCheck_5889_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_n_5798_);
                                    lean_dec(v_val_5711_);
                                    v___x_5800_ = lean_box(0);
                                    v_isShared_5801_ = v_isSharedCheck_5889_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_del_object(v___x_5737_);
                            lean_del_object(v___x_5713_);
                            lean_dec(v_val_5711_);
                            v_code_5890_ = lean_ctor_get(v_fst_5734_, 0);
                            lean_inc_ref(v_code_5890_);
                            lean_dec_ref_known(v_fst_5734_, 1);
                            lean_inc_ref(v_a_5692_);
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
                            if lean_obj_tag(v___x_5891_) == 0 {
                                v_a_5892_ = lean_ctor_get(v___x_5891_, 0);
                                v_isSharedCheck_5902_ = (!lean_is_exclusive(v___x_5891_)) as u8;
                                if v_isSharedCheck_5902_ == 0 {
                                    v___x_5894_ = v___x_5891_;
                                    v_isShared_5895_ = v_isSharedCheck_5902_;
                                    state = 39;
                                    continue;
                                } else {
                                    lean_inc(v_a_5892_);
                                    lean_dec(v___x_5891_);
                                    v___x_5894_ = lean_box(0);
                                    v_isShared_5895_ = v_isSharedCheck_5902_;
                                    state = 39;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_5721_);
                                v_a_5903_ = lean_ctor_get(v___x_5891_, 0);
                                v_isSharedCheck_5910_ = (!lean_is_exclusive(v___x_5891_)) as u8;
                                if v_isSharedCheck_5910_ == 0 {
                                    v___x_5905_ = v___x_5891_;
                                    v_isShared_5906_ = v_isSharedCheck_5910_;
                                    state = 42;
                                    continue;
                                } else {
                                    lean_inc(v_a_5903_);
                                    lean_dec(v___x_5891_);
                                    v___x_5905_ = lean_box(0);
                                    v_isShared_5906_ = v_isSharedCheck_5910_;
                                    state = 42;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_del_object(v___x_5737_);
                        lean_dec(v_fst_5734_);
                        lean_del_object(v___x_5721_);
                        lean_del_object(v___x_5713_);
                        lean_dec(v_val_5711_);
                        v_a_5911_ = lean_ctor_get(v___x_5742_, 0);
                        v_isSharedCheck_5918_ = (!lean_is_exclusive(v___x_5742_)) as u8;
                        if v_isSharedCheck_5918_ == 0 {
                            v___x_5913_ = v___x_5742_;
                            v_isShared_5914_ = v_isSharedCheck_5918_;
                            state = 44;
                            continue;
                        } else {
                            lean_inc(v_a_5911_);
                            lean_dec(v___x_5742_);
                            v___x_5913_ = lean_box(0);
                            v_isShared_5914_ = v_isSharedCheck_5918_;
                            state = 44;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_5737_);
                    lean_dec(v_fst_5734_);
                    lean_del_object(v___x_5721_);
                    lean_del_object(v___x_5713_);
                    lean_dec(v_val_5711_);
                    v_a_5919_ = lean_ctor_get(v___x_5741_, 0);
                    v_isSharedCheck_5926_ = (!lean_is_exclusive(v___x_5741_)) as u8;
                    if v_isSharedCheck_5926_ == 0 {
                        v___x_5921_ = v___x_5741_;
                        v_isShared_5922_ = v_isSharedCheck_5926_;
                        state = 46;
                        continue;
                    } else {
                        lean_inc(v_a_5919_);
                        lean_dec(v___x_5741_);
                        v___x_5921_ = lean_box(0);
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
                if lean_obj_tag(v___x_5753_) == 0 {
                    lean_dec_ref_known(v___x_5753_, 1);
                    lean_inc_ref(v_a_5692_);
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
                    if lean_obj_tag(v___x_5754_) == 0 {
                        v_a_5755_ = lean_ctor_get(v___x_5754_, 0);
                        lean_inc(v_a_5755_);
                        lean_dec_ref_known(v___x_5754_, 1);
                        v___x_5756_ = l_Lean_Compiler_LCNF_eraseParams___redArg(
                            v___x_5702_,
                            v_params_5743_,
                            v_a_5691_,
                        );
                        lean_dec_ref(v_params_5743_);
                        if lean_obj_tag(v___x_5756_) == 0 {
                            v_isSharedCheck_5766_ = (!lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5766_ == 0 {
                                v_unused_5767_ = lean_ctor_get(v___x_5756_, 0);
                                lean_dec(v_unused_5767_);
                                v___x_5758_ = v___x_5756_;
                                v_isShared_5759_ = v_isSharedCheck_5766_;
                                state = 10;
                                continue;
                            } else {
                                lean_dec(v___x_5756_);
                                v___x_5758_ = lean_box(0);
                                v_isShared_5759_ = v_isSharedCheck_5766_;
                                state = 10;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_5755_);
                            lean_del_object(v___x_5721_);
                            v_a_5768_ = lean_ctor_get(v___x_5756_, 0);
                            v_isSharedCheck_5775_ = (!lean_is_exclusive(v___x_5756_)) as u8;
                            if v_isSharedCheck_5775_ == 0 {
                                v___x_5770_ = v___x_5756_;
                                v_isShared_5771_ = v_isSharedCheck_5775_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_5768_);
                                lean_dec(v___x_5756_);
                                v___x_5770_ = lean_box(0);
                                v_isShared_5771_ = v_isSharedCheck_5775_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_params_5743_);
                        lean_del_object(v___x_5721_);
                        v_a_5776_ = lean_ctor_get(v___x_5754_, 0);
                        v_isSharedCheck_5783_ = (!lean_is_exclusive(v___x_5754_)) as u8;
                        if v_isSharedCheck_5783_ == 0 {
                            v___x_5778_ = v___x_5754_;
                            v_isShared_5779_ = v_isSharedCheck_5783_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_5776_);
                            lean_dec(v___x_5754_);
                            v___x_5778_ = lean_box(0);
                            v_isShared_5779_ = v_isSharedCheck_5783_;
                            state = 15;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_code_5744_);
                    lean_dec_ref(v_params_5743_);
                    lean_del_object(v___x_5721_);
                    v_a_5784_ = lean_ctor_get(v___x_5753_, 0);
                    v_isSharedCheck_5791_ = (!lean_is_exclusive(v___x_5753_)) as u8;
                    if v_isSharedCheck_5791_ == 0 {
                        v___x_5786_ = v___x_5753_;
                        v_isShared_5787_ = v_isSharedCheck_5791_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_5784_);
                        lean_dec(v___x_5753_);
                        v___x_5786_ = lean_box(0);
                        v_isShared_5787_ = v_isSharedCheck_5791_;
                        state = 17;
                        continue;
                    }
                }
            }
            10 => {
                if v_isShared_5722_ == 0 {
                    lean_ctor_set(v___x_5721_, 0, v_a_5755_);
                    v___x_5761_ = v___x_5721_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_5765_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5765_, 0, v_a_5755_);
                    v___x_5761_ = v_reuseFailAlloc_5765_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_5759_ == 0 {
                    lean_ctor_set(v___x_5758_, 0, v___x_5761_);
                    v___x_5763_ = v___x_5758_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5764_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5764_, 0, v___x_5761_);
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
                    v_reuseFailAlloc_5774_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5774_, 0, v_a_5768_);
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
                    v_reuseFailAlloc_5782_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5782_, 0, v_a_5776_);
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
                    v_reuseFailAlloc_5790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5790_, 0, v_a_5784_);
                    v___x_5789_ = v_reuseFailAlloc_5790_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5789_;
            }
            19 => {
                v_zero_5802_ = lean_unsigned_to_nat(0);
                v_isZero_5803_ = lean_nat_dec_eq(v_n_5798_, v_zero_5802_);
                if v_isZero_5803_ == 1 {
                    lean_del_object(v___x_5800_);
                    lean_dec(v_n_5798_);
                    lean_dec_ref(v_params_5796_);
                    lean_del_object(v___x_5737_);
                    lean_del_object(v___x_5713_);
                    lean_inc_ref(v_a_5692_);
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
                    if lean_obj_tag(v___x_5804_) == 0 {
                        v_a_5805_ = lean_ctor_get(v___x_5804_, 0);
                        v_isSharedCheck_5815_ = (!lean_is_exclusive(v___x_5804_)) as u8;
                        if v_isSharedCheck_5815_ == 0 {
                            v___x_5807_ = v___x_5804_;
                            v_isShared_5808_ = v_isSharedCheck_5815_;
                            state = 20;
                            continue;
                        } else {
                            lean_inc(v_a_5805_);
                            lean_dec(v___x_5804_);
                            v___x_5807_ = lean_box(0);
                            v_isShared_5808_ = v_isSharedCheck_5815_;
                            state = 20;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_5721_);
                        v_a_5816_ = lean_ctor_get(v___x_5804_, 0);
                        v_isSharedCheck_5823_ = (!lean_is_exclusive(v___x_5804_)) as u8;
                        if v_isSharedCheck_5823_ == 0 {
                            v___x_5818_ = v___x_5804_;
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_5816_);
                            lean_dec(v___x_5804_);
                            v___x_5818_ = lean_box(0);
                            v_isShared_5819_ = v_isSharedCheck_5823_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    v_one_5824_ = lean_unsigned_to_nat(1);
                    v_n_5825_ = lean_nat_sub(v_n_5798_, v_one_5824_);
                    lean_dec(v_n_5798_);
                    if v_isShared_5801_ == 0 {
                        lean_ctor_set_tag(v___x_5800_, 0);
                        lean_ctor_set(v___x_5800_, 0, v_n_5825_);
                        v___x_5827_ = v___x_5800_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_5888_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5888_, 0, v_n_5825_);
                        v___x_5827_ = v_reuseFailAlloc_5888_;
                        state = 25;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_5722_ == 0 {
                    lean_ctor_set(v___x_5721_, 0, v_a_5805_);
                    v___x_5810_ = v___x_5721_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_5814_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5814_, 0, v_a_5805_);
                    v___x_5810_ = v_reuseFailAlloc_5814_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                if v_isShared_5808_ == 0 {
                    lean_ctor_set(v___x_5807_, 0, v___x_5810_);
                    v___x_5812_ = v___x_5807_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_5813_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5813_, 0, v___x_5810_);
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
                    v_reuseFailAlloc_5822_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_a_5816_);
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
                    lean_ctor_set_tag(v___x_5713_, 0);
                    lean_ctor_set(v___x_5713_, 0, v___x_5827_);
                    v___x_5829_ = v___x_5713_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_5887_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5887_, 0, v___x_5827_);
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
                if lean_obj_tag(v___x_5831_) == 0 {
                    v_a_5832_ = lean_ctor_get(v___x_5831_, 0);
                    lean_inc(v_a_5832_);
                    lean_dec_ref_known(v___x_5831_, 1);
                    v___x_5833_ = lean_obj_once(
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
                    v_fvarId_5835_ = lean_ctor_get(v___x_5834_, 0);
                    v_fvarId_5836_ = lean_ctor_get(v_a_5832_, 0);
                    lean_inc(v_fvarId_5836_);
                    lean_inc(v_fvarId_5835_);
                    v___x_5837_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(
                        v_fvarId_5835_,
                        v_fvarId_5836_,
                        v_a_5688_,
                        v_a_5690_,
                        v_a_5691_,
                        v_a_5692_,
                        v_a_5693_,
                    );
                    if lean_obj_tag(v___x_5837_) == 0 {
                        lean_dec_ref_known(v___x_5837_, 1);
                        lean_inc_ref(v_a_5692_);
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
                        if lean_obj_tag(v___x_5838_) == 0 {
                            v_a_5839_ = lean_ctor_get(v___x_5838_, 0);
                            lean_inc(v_a_5839_);
                            lean_dec_ref_known(v___x_5838_, 1);
                            v___x_5840_ = l_Lean_Compiler_LCNF_eraseParams___redArg(
                                v___x_5702_,
                                v_params_5796_,
                                v_a_5691_,
                            );
                            lean_dec_ref(v_params_5796_);
                            if lean_obj_tag(v___x_5840_) == 0 {
                                v_isSharedCheck_5853_ = (!lean_is_exclusive(v___x_5840_)) as u8;
                                if v_isSharedCheck_5853_ == 0 {
                                    v_unused_5854_ = lean_ctor_get(v___x_5840_, 0);
                                    lean_dec(v_unused_5854_);
                                    v___x_5842_ = v___x_5840_;
                                    v_isShared_5843_ = v_isSharedCheck_5853_;
                                    state = 27;
                                    continue;
                                } else {
                                    lean_dec(v___x_5840_);
                                    v___x_5842_ = lean_box(0);
                                    v_isShared_5843_ = v_isSharedCheck_5853_;
                                    state = 27;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_5839_);
                                lean_dec(v_a_5832_);
                                lean_del_object(v___x_5737_);
                                lean_del_object(v___x_5721_);
                                v_a_5855_ = lean_ctor_get(v___x_5840_, 0);
                                v_isSharedCheck_5862_ = (!lean_is_exclusive(v___x_5840_)) as u8;
                                if v_isSharedCheck_5862_ == 0 {
                                    v___x_5857_ = v___x_5840_;
                                    v_isShared_5858_ = v_isSharedCheck_5862_;
                                    state = 31;
                                    continue;
                                } else {
                                    lean_inc(v_a_5855_);
                                    lean_dec(v___x_5840_);
                                    v___x_5857_ = lean_box(0);
                                    v_isShared_5858_ = v_isSharedCheck_5862_;
                                    state = 31;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_5832_);
                            lean_dec_ref(v_params_5796_);
                            lean_del_object(v___x_5737_);
                            lean_del_object(v___x_5721_);
                            v_a_5863_ = lean_ctor_get(v___x_5838_, 0);
                            v_isSharedCheck_5870_ = (!lean_is_exclusive(v___x_5838_)) as u8;
                            if v_isSharedCheck_5870_ == 0 {
                                v___x_5865_ = v___x_5838_;
                                v_isShared_5866_ = v_isSharedCheck_5870_;
                                state = 33;
                                continue;
                            } else {
                                lean_inc(v_a_5863_);
                                lean_dec(v___x_5838_);
                                v___x_5865_ = lean_box(0);
                                v_isShared_5866_ = v_isSharedCheck_5870_;
                                state = 33;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_5832_);
                        lean_dec_ref(v_code_5797_);
                        lean_dec_ref(v_params_5796_);
                        lean_del_object(v___x_5737_);
                        lean_del_object(v___x_5721_);
                        v_a_5871_ = lean_ctor_get(v___x_5837_, 0);
                        v_isSharedCheck_5878_ = (!lean_is_exclusive(v___x_5837_)) as u8;
                        if v_isSharedCheck_5878_ == 0 {
                            v___x_5873_ = v___x_5837_;
                            v_isShared_5874_ = v_isSharedCheck_5878_;
                            state = 35;
                            continue;
                        } else {
                            lean_inc(v_a_5871_);
                            lean_dec(v___x_5837_);
                            v___x_5873_ = lean_box(0);
                            v_isShared_5874_ = v_isSharedCheck_5878_;
                            state = 35;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_code_5797_);
                    lean_dec_ref(v_params_5796_);
                    lean_del_object(v___x_5737_);
                    lean_del_object(v___x_5721_);
                    v_a_5879_ = lean_ctor_get(v___x_5831_, 0);
                    v_isSharedCheck_5886_ = (!lean_is_exclusive(v___x_5831_)) as u8;
                    if v_isSharedCheck_5886_ == 0 {
                        v___x_5881_ = v___x_5831_;
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 37;
                        continue;
                    } else {
                        lean_inc(v_a_5879_);
                        lean_dec(v___x_5831_);
                        v___x_5881_ = lean_box(0);
                        v_isShared_5882_ = v_isSharedCheck_5886_;
                        state = 37;
                        continue;
                    }
                }
            }
            27 => {
                if v_isShared_5738_ == 0 {
                    lean_ctor_set(v___x_5737_, 1, v_a_5839_);
                    lean_ctor_set(v___x_5737_, 0, v_a_5832_);
                    v___x_5845_ = v___x_5737_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_5852_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5852_, 0, v_a_5832_);
                    lean_ctor_set(v_reuseFailAlloc_5852_, 1, v_a_5839_);
                    v___x_5845_ = v_reuseFailAlloc_5852_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_5722_ == 0 {
                    lean_ctor_set(v___x_5721_, 0, v___x_5845_);
                    v___x_5847_ = v___x_5721_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_5851_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5851_, 0, v___x_5845_);
                    v___x_5847_ = v_reuseFailAlloc_5851_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_5843_ == 0 {
                    lean_ctor_set(v___x_5842_, 0, v___x_5847_);
                    v___x_5849_ = v___x_5842_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_5850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5850_, 0, v___x_5847_);
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
                    v_reuseFailAlloc_5861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5861_, 0, v_a_5855_);
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
                    v_reuseFailAlloc_5869_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_a_5863_);
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
                    v_reuseFailAlloc_5877_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5877_, 0, v_a_5871_);
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
                    v_reuseFailAlloc_5885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5885_, 0, v_a_5879_);
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
                    lean_ctor_set(v___x_5721_, 0, v_a_5892_);
                    v___x_5897_ = v___x_5721_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_5901_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5901_, 0, v_a_5892_);
                    v___x_5897_ = v_reuseFailAlloc_5901_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                if v_isShared_5895_ == 0 {
                    lean_ctor_set(v___x_5894_, 0, v___x_5897_);
                    v___x_5899_ = v___x_5894_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_5900_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5900_, 0, v___x_5897_);
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
                    v_reuseFailAlloc_5909_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5909_, 0, v_a_5903_);
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
                    v_reuseFailAlloc_5917_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5917_, 0, v_a_5911_);
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
                    v_reuseFailAlloc_5925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5925_, 0, v_a_5919_);
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
                    v_reuseFailAlloc_5943_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5943_, 0, v_a_5937_);
                    v___x_5942_ = v_reuseFailAlloc_5943_;
                    state = 50;
                    continue;
                }
            }
            50 => {
                return v___x_5942_;
            }
            51 => {
                v___x_5950_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_5950_, 0, v_a_5946_);
                if v_isShared_5949_ == 0 {
                    lean_ctor_set(v___x_5948_, 0, v___x_5950_);
                    v___x_5952_ = v___x_5948_;
                    state = 52;
                    continue;
                } else {
                    v_reuseFailAlloc_5953_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5953_, 0, v___x_5950_);
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
                    v_reuseFailAlloc_5961_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5961_, 0, v_a_5955_);
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
    mut v_fvarId_5963_: *mut LeanObject,
    mut v_i_5964_: *mut LeanObject,
    mut v_as_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
    mut v___y_5967_: *mut LeanObject,
    mut v___y_5968_: *mut LeanObject,
    mut v___y_5969_: *mut LeanObject,
    mut v___y_5970_: *mut LeanObject,
    mut v___y_5971_: *mut LeanObject,
    mut v___y_5972_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5975_: u8 = 0;
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: usize = 0;
    let mut v___x_5981_: usize = 0;
    let mut v___x_5982_: u8 = 0;
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_5990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_5991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5997_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6001_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6002_: u8 = 0;
    let mut v___x_6004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6006_: u8 = 0;
    let mut v_a_6007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6010_: u8 = 0;
    let mut v___x_6012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6013_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6014_: u8 = 0;
    let mut v___x_6015_: u8 = 0;
    let mut v_a_6017_: u8 = 0;
    let mut v___x_6018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6027_: u8 = 0;
    let mut v___x_6029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6031_: u8 = 0;
    let mut v_a_6032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6035_: u8 = 0;
    let mut v___x_6037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6039_: u8 = 0;
    let mut v_a_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6047_: u8 = 0;
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6050_: u8 = 0;
    let mut v___x_6051_: usize = 0;
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6055_: u8 = 0;
    let mut v_a_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v_code_6064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6070_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6071_: u8 = 0;
    let mut v___x_6073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6075_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5974_ = lean_array_get_size(v_as_5965_);
                v___x_5975_ = lean_nat_dec_lt(v_i_5964_, v___x_5974_);
                if v___x_5975_ == 0 {
                    lean_dec(v_i_5964_);
                    lean_dec(v_fvarId_5963_);
                    v___x_5976_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5976_, 0, v_as_5965_);
                    return v___x_5976_;
                } else {
                    v_a_5977_ = lean_array_fget_borrowed(v_as_5965_, v_i_5964_);
                    if lean_obj_tag(v_a_5977_) == 0 {
                        v_ctorName_5990_ = lean_ctor_get(v_a_5977_, 0);
                        v_params_5991_ = lean_ctor_get(v_a_5977_, 1);
                        v_code_5992_ = lean_ctor_get(v_a_5977_, 2);
                        v___x_6015_ = 0;
                        v___x_6048_ = lean_unsigned_to_nat(0);
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
                                if lean_obj_tag(v___x_6053_) == 0 {
                                    v_a_6054_ = lean_ctor_get(v___x_6053_, 0);
                                    lean_inc(v_a_6054_);
                                    lean_dec_ref_known(v___x_6053_, 1);
                                    v___x_6055_ = (lean_unbox(v_a_6054_) as u8);
                                    lean_dec(v_a_6054_);
                                    v_a_6017_ = v___x_6055_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_dec_ref(v_as_5965_);
                                    lean_dec(v_i_5964_);
                                    lean_dec(v_fvarId_5963_);
                                    v_a_6056_ = lean_ctor_get(v___x_6053_, 0);
                                    v_isSharedCheck_6063_ = (!lean_is_exclusive(v___x_6053_)) as u8;
                                    if v_isSharedCheck_6063_ == 0 {
                                        v___x_6058_ = v___x_6053_;
                                        v_isShared_6059_ = v_isSharedCheck_6063_;
                                        state = 14;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6056_);
                                        lean_dec(v___x_6053_);
                                        v___x_6058_ = lean_box(0);
                                        v_isShared_6059_ = v_isSharedCheck_6063_;
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v_code_6064_ = lean_ctor_get(v_a_5977_, 0);
                        lean_inc_ref(v___y_5971_);
                        lean_inc_ref(v_code_6064_);
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
                        if lean_obj_tag(v___x_6065_) == 0 {
                            v_a_6066_ = lean_ctor_get(v___x_6065_, 0);
                            lean_inc(v_a_6066_);
                            lean_dec_ref_known(v___x_6065_, 1);
                            lean_inc_ref(v_a_5977_);
                            v___x_6067_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5977_, v_a_6066_);
                            v_a_5979_ = v___x_6067_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_as_5965_);
                            lean_dec(v_i_5964_);
                            lean_dec(v_fvarId_5963_);
                            v_a_6068_ = lean_ctor_get(v___x_6065_, 0);
                            v_isSharedCheck_6075_ = (!lean_is_exclusive(v___x_6065_)) as u8;
                            if v_isSharedCheck_6075_ == 0 {
                                v___x_6070_ = v___x_6065_;
                                v_isShared_6071_ = v_isSharedCheck_6075_;
                                state = 16;
                                continue;
                            } else {
                                lean_inc(v_a_6068_);
                                lean_dec(v___x_6065_);
                                v___x_6070_ = lean_box(0);
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
                    v___x_5983_ = lean_unsigned_to_nat(1);
                    v___x_5984_ = lean_nat_add(v_i_5964_, v___x_5983_);
                    v___x_5985_ = lean_array_fset(v_as_5965_, v_i_5964_, v_a_5979_);
                    lean_dec(v_i_5964_);
                    v_i_5964_ = v___x_5984_;
                    v_as_5965_ = v___x_5985_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_a_5979_);
                    v___x_5987_ = lean_unsigned_to_nat(1);
                    v___x_5988_ = lean_nat_add(v_i_5964_, v___x_5987_);
                    lean_dec(v_i_5964_);
                    v_i_5964_ = v___x_5988_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                lean_inc_ref(v_params_5991_);
                lean_inc(v_ctorName_5990_);
                lean_inc(v_fvarId_5963_);
                v___x_5994_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_fvarId_5963_, v_ctorName_5990_, v_params_5991_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_);
                if lean_obj_tag(v___x_5994_) == 0 {
                    v_a_5995_ = lean_ctor_get(v___x_5994_, 0);
                    lean_inc(v_a_5995_);
                    lean_dec_ref_known(v___x_5994_, 1);
                    lean_inc_ref(v___y_5971_);
                    lean_inc_ref(v_code_5992_);
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
                    lean_dec(v_a_5995_);
                    if lean_obj_tag(v___x_5996_) == 0 {
                        v_a_5997_ = lean_ctor_get(v___x_5996_, 0);
                        lean_inc(v_a_5997_);
                        lean_dec_ref_known(v___x_5996_, 1);
                        lean_inc_ref(v_a_5977_);
                        v___x_5998_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5977_, v_a_5997_);
                        v_a_5979_ = v___x_5998_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_as_5965_);
                        lean_dec(v_i_5964_);
                        lean_dec(v_fvarId_5963_);
                        v_a_5999_ = lean_ctor_get(v___x_5996_, 0);
                        v_isSharedCheck_6006_ = (!lean_is_exclusive(v___x_5996_)) as u8;
                        if v_isSharedCheck_6006_ == 0 {
                            v___x_6001_ = v___x_5996_;
                            v_isShared_6002_ = v_isSharedCheck_6006_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5999_);
                            lean_dec(v___x_5996_);
                            v___x_6001_ = lean_box(0);
                            v_isShared_6002_ = v_isSharedCheck_6006_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_as_5965_);
                    lean_dec(v_i_5964_);
                    lean_dec(v_fvarId_5963_);
                    v_a_6007_ = lean_ctor_get(v___x_5994_, 0);
                    v_isSharedCheck_6014_ = (!lean_is_exclusive(v___x_5994_)) as u8;
                    if v_isSharedCheck_6014_ == 0 {
                        v___x_6009_ = v___x_5994_;
                        v_isShared_6010_ = v_isSharedCheck_6014_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6007_);
                        lean_dec(v___x_5994_);
                        v___x_6009_ = lean_box(0);
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
                    v_reuseFailAlloc_6005_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6005_, 0, v_a_5999_);
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
                    v_reuseFailAlloc_6013_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6013_, 0, v_a_6007_);
                    v___x_6012_ = v_reuseFailAlloc_6013_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6012_;
            }
            7 => {
                if lean_obj_tag(v_code_5992_) == 6 {
                    state = 2;
                    continue;
                } else {
                    if v_a_6017_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        lean_inc_ref(v_code_5992_);
                        v___x_6018_ = l_Lean_Compiler_LCNF_Code_inferType(
                            v___x_6015_,
                            v_code_5992_,
                            v___y_5969_,
                            v___y_5970_,
                            v___y_5971_,
                            v___y_5972_,
                        );
                        if lean_obj_tag(v___x_6018_) == 0 {
                            v_a_6019_ = lean_ctor_get(v___x_6018_, 0);
                            lean_inc(v_a_6019_);
                            lean_dec_ref_known(v___x_6018_, 1);
                            v___x_6020_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                                v___x_6015_,
                                v_code_5992_,
                                v___y_5970_,
                            );
                            if lean_obj_tag(v___x_6020_) == 0 {
                                lean_dec_ref_known(v___x_6020_, 1);
                                v___x_6021_ =
                                    l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_5967_);
                                if lean_obj_tag(v___x_6021_) == 0 {
                                    lean_dec_ref_known(v___x_6021_, 1);
                                    v___x_6022_ = lean_alloc_ctor(6, 1, (0) as u32);
                                    lean_ctor_set(v___x_6022_, 0, v_a_6019_);
                                    lean_inc_ref(v_a_5977_);
                                    v___x_6023_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_5977_, v___x_6022_);
                                    v_a_5979_ = v___x_6023_;
                                    state = 1;
                                    continue;
                                } else {
                                    lean_dec(v_a_6019_);
                                    lean_dec_ref(v_as_5965_);
                                    lean_dec(v_i_5964_);
                                    lean_dec(v_fvarId_5963_);
                                    v_a_6024_ = lean_ctor_get(v___x_6021_, 0);
                                    v_isSharedCheck_6031_ = (!lean_is_exclusive(v___x_6021_)) as u8;
                                    if v_isSharedCheck_6031_ == 0 {
                                        v___x_6026_ = v___x_6021_;
                                        v_isShared_6027_ = v_isSharedCheck_6031_;
                                        state = 8;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6024_);
                                        lean_dec(v___x_6021_);
                                        v___x_6026_ = lean_box(0);
                                        v_isShared_6027_ = v_isSharedCheck_6031_;
                                        state = 8;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec(v_a_6019_);
                                lean_dec_ref(v_as_5965_);
                                lean_dec(v_i_5964_);
                                lean_dec(v_fvarId_5963_);
                                v_a_6032_ = lean_ctor_get(v___x_6020_, 0);
                                v_isSharedCheck_6039_ = (!lean_is_exclusive(v___x_6020_)) as u8;
                                if v_isSharedCheck_6039_ == 0 {
                                    v___x_6034_ = v___x_6020_;
                                    v_isShared_6035_ = v_isSharedCheck_6039_;
                                    state = 10;
                                    continue;
                                } else {
                                    lean_inc(v_a_6032_);
                                    lean_dec(v___x_6020_);
                                    v___x_6034_ = lean_box(0);
                                    v_isShared_6035_ = v_isSharedCheck_6039_;
                                    state = 10;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_as_5965_);
                            lean_dec(v_i_5964_);
                            lean_dec(v_fvarId_5963_);
                            v_a_6040_ = lean_ctor_get(v___x_6018_, 0);
                            v_isSharedCheck_6047_ = (!lean_is_exclusive(v___x_6018_)) as u8;
                            if v_isSharedCheck_6047_ == 0 {
                                v___x_6042_ = v___x_6018_;
                                v_isShared_6043_ = v_isSharedCheck_6047_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_6040_);
                                lean_dec(v___x_6018_);
                                v___x_6042_ = lean_box(0);
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
                    v_reuseFailAlloc_6030_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6030_, 0, v_a_6024_);
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
                    v_reuseFailAlloc_6038_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6038_, 0, v_a_6032_);
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
                    v_reuseFailAlloc_6046_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6046_, 0, v_a_6040_);
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
                    v_reuseFailAlloc_6062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
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
                    v_reuseFailAlloc_6074_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6074_, 0, v_a_6068_);
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
    mut v_code_6077_: *mut LeanObject,
    mut v_a_6078_: *mut LeanObject,
    mut v_a_6079_: *mut LeanObject,
    mut v_a_6080_: *mut LeanObject,
    mut v_a_6081_: *mut LeanObject,
    mut v_a_6082_: *mut LeanObject,
    mut v_a_6083_: *mut LeanObject,
    mut v_a_6084_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_6087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6089_: u8 = 0;
    let mut v___x_6090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6096_: u8 = 0;
    let mut v___x_6097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: usize = 0;
    let mut v___x_6106_: usize = 0;
    let mut v___x_6107_: u8 = 0;
    let mut v___x_6108_: usize = 0;
    let mut v___x_6109_: usize = 0;
    let mut v___x_6110_: u8 = 0;
    let mut v_decl_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: usize = 0;
    let mut v___x_6114_: usize = 0;
    let mut v___x_6115_: u8 = 0;
    let mut v___x_6116_: usize = 0;
    let mut v___x_6117_: usize = 0;
    let mut v___x_6118_: u8 = 0;
    let mut v___x_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6123_: u8 = 0;
    let mut v___y_6124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6138_: u8 = 0;
    let mut v___x_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6142_: u8 = 0;
    let mut v___x_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6146_: u8 = 0;
    let mut v_unused_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6151_: u8 = 0;
    let mut v___x_6153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6154_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6155_: u8 = 0;
    let mut v___x_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6160_: u8 = 0;
    let mut v___x_6162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6164_: u8 = 0;
    let mut v_a_6165_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6168_: u8 = 0;
    let mut v___x_6170_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6172_: u8 = 0;
    let mut v___y_6174_: u8 = 0;
    let mut v___y_6175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6189_: u8 = 0;
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6193_: u8 = 0;
    let mut v_decl_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6196_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: u8 = 0;
    let mut v___x_6210_: u8 = 0;
    let mut v___x_6211_: u8 = 0;
    let mut v___x_6212_: u8 = 0;
    let mut v___x_6213_: u8 = 0;
    let mut v___x_6214_: u8 = 0;
    let mut v___x_6215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_6216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6217_: u8 = 0;
    let mut v___x_6218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6219_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6223_: u8 = 0;
    let mut v_a_6224_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6227_: u8 = 0;
    let mut v___x_6229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6231_: u8 = 0;
    let mut v_a_6232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6235_: u8 = 0;
    let mut v___x_6237_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6239_: u8 = 0;
    let mut v_a_6240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6243_: u8 = 0;
    let mut v___x_6245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6247_: u8 = 0;
    let mut v___x_6248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_6249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6250_: u8 = 0;
    let mut v___x_6251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6253_: u8 = 0;
    let mut v_a_6254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6257_: u8 = 0;
    let mut v___x_6259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6261_: u8 = 0;
    let mut v_a_6262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6265_: u8 = 0;
    let mut v___x_6267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6269_: u8 = 0;
    let mut v___y_6271_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6273_: u8 = 0;
    let mut v___x_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6281_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6298_: u8 = 0;
    let mut v___x_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v___x_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6304_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6306_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6319_: u8 = 0;
    let mut v___x_6321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6323_: u8 = 0;
    let mut v_a_6324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6327_: u8 = 0;
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6331_: u8 = 0;
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6338_: u8 = 0;
    let mut v___x_6340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6342_: u8 = 0;
    let mut v_unused_6343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6347_: u8 = 0;
    let mut v___x_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6351_: u8 = 0;
    let mut v___x_6352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6365_: u8 = 0;
    let mut v___x_6367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6369_: u8 = 0;
    let mut v_a_6370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6373_: u8 = 0;
    let mut v___x_6375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6377_: u8 = 0;
    let mut v___x_6378_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6382_: u8 = 0;
    let mut v___x_6383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6386_: u8 = 0;
    let mut v___x_6388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6390_: u8 = 0;
    let mut v_unused_6391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6392_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6395_: u8 = 0;
    let mut v___x_6397_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6399_: u8 = 0;
    let mut v___x_6400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6401_: usize = 0;
    let mut v___x_6402_: usize = 0;
    let mut v___x_6403_: u8 = 0;
    let mut v___x_6404_: usize = 0;
    let mut v___x_6405_: usize = 0;
    let mut v___x_6406_: u8 = 0;
    let mut v_a_6407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6410_: u8 = 0;
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6413_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6414_: u8 = 0;
    let mut v_a_6415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6418_: u8 = 0;
    let mut v___x_6420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6422_: u8 = 0;
    let mut v_a_6423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6426_: u8 = 0;
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6430_: u8 = 0;
    let mut v_a_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6434_: u8 = 0;
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6438_: u8 = 0;
    let mut v_a_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6442_: u8 = 0;
    let mut v___x_6444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6446_: u8 = 0;
    let mut v_a_6447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6450_: u8 = 0;
    let mut v___x_6452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6454_: u8 = 0;
    let mut v_a_6455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6458_: u8 = 0;
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6462_: u8 = 0;
    let mut v___y_6464_: u8 = 0;
    let mut v___y_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6478_: u8 = 0;
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: u8 = 0;
    let mut v___x_6481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_6482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_used_6483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_6484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_6485_: *mut LeanObject = core::ptr::null_mut();
    let mut v_simplified_6486_: u8 = 0;
    let mut v_visited_6487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inline_6488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_6489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6492_: u8 = 0;
    let mut v___x_6493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6500_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6503_: u8 = 0;
    let mut v___x_6505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6507_: u8 = 0;
    let mut v_reuseFailAlloc_6508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6509_: u8 = 0;
    let mut v___y_6511_: u8 = 0;
    let mut v___y_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6521_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6524_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_6533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6537_: u8 = 0;
    let mut v___x_6539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6541_: u8 = 0;
    let mut v_a_6542_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6544_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6545_: u8 = 0;
    let mut v___x_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6548_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6549_: u8 = 0;
    let mut v_a_6550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6553_: u8 = 0;
    let mut v___x_6555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6557_: u8 = 0;
    let mut v___y_6559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6561_: u8 = 0;
    let mut v___x_6562_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6568_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6570_: u8 = 0;
    let mut v___x_6571_: usize = 0;
    let mut v___x_6572_: usize = 0;
    let mut v___x_6573_: u8 = 0;
    let mut v___y_6575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6578_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6580_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6583_: u8 = 0;
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6587_: u8 = 0;
    let mut v___y_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6594_: u8 = 0;
    let mut v___x_6595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6598_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6599_: u8 = 0;
    let mut v_unused_6600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6604_: u8 = 0;
    let mut v___x_6606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6608_: u8 = 0;
    let mut v___y_6610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6616_: u8 = 0;
    let mut v___x_6618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6620_: u8 = 0;
    let mut v___y_6622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: u8 = 0;
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: u8 = 0;
    let mut v___x_6634_: usize = 0;
    let mut v___x_6635_: usize = 0;
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: usize = 0;
    let mut v___x_6638_: usize = 0;
    let mut v___x_6639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6654_: u8 = 0;
    let mut v___x_6655_: u8 = 0;
    let mut v___x_6656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6662_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6664_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6671_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6672_: u8 = 0;
    let mut v___x_6673_: usize = 0;
    let mut v___x_6674_: usize = 0;
    let mut v___x_6675_: u8 = 0;
    let mut v___x_6676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: usize = 0;
    let mut v___x_6678_: usize = 0;
    let mut v___x_6679_: u8 = 0;
    let mut v___x_6680_: usize = 0;
    let mut v___x_6681_: usize = 0;
    let mut v___x_6682_: u8 = 0;
    let mut v_a_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6686_: u8 = 0;
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6690_: u8 = 0;
    let mut v___y_6692_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6693_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6697_: u8 = 0;
    let mut v___x_6699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6701_: u8 = 0;
    let mut v_unused_6702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6705_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6706_: u8 = 0;
    let mut v___x_6708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6710_: u8 = 0;
    let mut v___y_6712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6718_: u8 = 0;
    let mut v___x_6720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6722_: u8 = 0;
    let mut v___y_6724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6727_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6729_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6730_: u8 = 0;
    let mut v___x_6731_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6732_: u8 = 0;
    let mut v___x_6733_: usize = 0;
    let mut v___x_6734_: usize = 0;
    let mut v___x_6735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6736_: usize = 0;
    let mut v___x_6737_: usize = 0;
    let mut v___x_6738_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6740_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_6746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6748_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: u8 = 0;
    let mut v___x_6750_: u8 = 0;
    let mut v___x_6751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6753_: u8 = 0;
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6758_: u8 = 0;
    let mut v___x_6760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6762_: u8 = 0;
    let mut v_a_6763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6766_: u8 = 0;
    let mut v___x_6768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6770_: u8 = 0;
    let mut v_fvarId_6771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_6772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_6774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6775_: u8 = 0;
    let mut v___x_6776_: u8 = 0;
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6785_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: u8 = 0;
    let mut v___x_6789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: u8 = 0;
    let mut v___x_6791_: usize = 0;
    let mut v___x_6792_: usize = 0;
    let mut v___x_6793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6794_: usize = 0;
    let mut v___x_6795_: usize = 0;
    let mut v___x_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6800_: u8 = 0;
    let mut v___x_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6803_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6804_: u8 = 0;
    let mut v_a_6805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6808_: u8 = 0;
    let mut v___x_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6812_: u8 = 0;
    let mut v_a_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6816_: u8 = 0;
    let mut v___x_6818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6820_: u8 = 0;
    let mut v___x_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_6822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6824_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6826_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6827_: u8 = 0;
    let mut v_val_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_6832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_6833_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_6834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_6835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_6837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6838_: u8 = 0;
    let mut v___x_6839_: u8 = 0;
    let mut v___x_6840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6850_: u8 = 0;
    let mut v_subst_6851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: u8 = 0;
    let mut v___x_6856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_6857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_6858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: u8 = 0;
    let mut v___x_6861_: usize = 0;
    let mut v___x_6862_: usize = 0;
    let mut v___x_6863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: u8 = 0;
    let mut v_a_6866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6869_: u8 = 0;
    let mut v___x_6871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6873_: u8 = 0;
    let mut v_code_6874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6878_: u8 = 0;
    let mut v_a_6879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6882_: u8 = 0;
    let mut v___x_6884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6886_: u8 = 0;
    let mut v_a_6887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6890_: u8 = 0;
    let mut v___x_6892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6894_: u8 = 0;
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6896_: u8 = 0;
    let mut v_a_6897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6900_: u8 = 0;
    let mut v___x_6902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6904_: u8 = 0;
    let mut v_fvarId_6905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_6907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6908_: u8 = 0;
    let mut v___x_6909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_6910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6914_: u8 = 0;
    let mut v___x_6915_: u8 = 0;
    let mut v___x_6917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6918_: u8 = 0;
    let mut v___x_6920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6925_: u8 = 0;
    let mut v_unused_6926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6930_: u8 = 0;
    let mut v_unused_6931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6935_: u8 = 0;
    let mut v___x_6937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6939_: u8 = 0;
    let mut v___x_6940_: u8 = 0;
    let mut v___x_6941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_6942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_6944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6945_: u8 = 0;
    let mut v___x_6946_: u8 = 0;
    let mut v___x_6947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6948_: usize = 0;
    let mut v___x_6949_: usize = 0;
    let mut v___x_6950_: u8 = 0;
    let mut v___x_6952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6953_: u8 = 0;
    let mut v___x_6955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6958_: u8 = 0;
    let mut v_unused_6959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_6961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileName_6963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_6965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6967_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_6968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6970_: *mut LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6971_: *mut LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6973_: *mut LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diag_6975_: u8 = 0;
    let mut v_cancelTk_x3f_6976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6977_: u8 = 0;
    let mut v_inheritedTraceOptions_6978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_visited_6982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: u8 = 0;
    let mut v___x_6990_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6995_: u8 = 0;
    let mut v___x_6997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6999_: u8 = 0;
    let mut v_a_7000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7003_: u8 = 0;
    let mut v___x_7005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7007_: u8 = 0;
    let mut v___x_7008_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7009_: u8 = 0;
    let mut v___x_7010_: u8 = 0;
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_6963_ = lean_ctor_get(v_a_6083_, 0);
                v_fileMap_6964_ = lean_ctor_get(v_a_6083_, 1);
                v_options_6965_ = lean_ctor_get(v_a_6083_, 2);
                v_currRecDepth_6966_ = lean_ctor_get(v_a_6083_, 3);
                v_maxRecDepth_6967_ = lean_ctor_get(v_a_6083_, 4);
                v_ref_6968_ = lean_ctor_get(v_a_6083_, 5);
                v_currNamespace_6969_ = lean_ctor_get(v_a_6083_, 6);
                v_openDecls_6970_ = lean_ctor_get(v_a_6083_, 7);
                v_initHeartbeats_6971_ = lean_ctor_get(v_a_6083_, 8);
                v_maxHeartbeats_6972_ = lean_ctor_get(v_a_6083_, 9);
                v_quotContext_6973_ = lean_ctor_get(v_a_6083_, 10);
                v_currMacroScope_6974_ = lean_ctor_get(v_a_6083_, 11);
                v_diag_6975_ = lean_ctor_get_uint8(
                    v_a_6083_,
                    (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_6976_ = lean_ctor_get(v_a_6083_, 12);
                v_suppressElabErrors_6977_ = lean_ctor_get_uint8(
                    v_a_6083_,
                    (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_6978_ = lean_ctor_get(v_a_6083_, 13);
                v___x_7008_ = lean_unsigned_to_nat(0);
                v___x_7009_ = lean_nat_dec_eq(v_maxRecDepth_6967_, v___x_7008_);
                if v___x_7009_ == 0 {
                    v___x_7010_ = lean_nat_dec_eq(v_currRecDepth_6966_, v_maxRecDepth_6967_);
                    if v___x_7010_ == 0 {
                        lean_inc_ref(v_inheritedTraceOptions_6978_);
                        lean_inc(v_cancelTk_x3f_6976_);
                        lean_inc(v_currMacroScope_6974_);
                        lean_inc(v_quotContext_6973_);
                        lean_inc(v_maxHeartbeats_6972_);
                        lean_inc(v_initHeartbeats_6971_);
                        lean_inc(v_openDecls_6970_);
                        lean_inc(v_currNamespace_6969_);
                        lean_inc(v_ref_6968_);
                        lean_inc(v_maxRecDepth_6967_);
                        lean_inc(v_currRecDepth_6966_);
                        lean_inc_ref(v_options_6965_);
                        lean_inc_ref(v_fileMap_6964_);
                        lean_inc_ref(v_fileName_6963_);
                        lean_dec_ref(v_a_6083_);
                        state = 133;
                        continue;
                    } else {
                        lean_dec_ref(v_code_6077_);
                        v___x_7011_ = l___private_Lean_Compiler_LCNF_Simp_SimpM_0__Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), v_a_6078_, v_a_6079_, v_a_6080_, v_a_6081_, v_a_6082_, v_a_6083_, v_a_6084_);
                        lean_dec_ref(v_a_6083_);
                        return v___x_7011_;
                    }
                } else {
                    lean_inc_ref(v_inheritedTraceOptions_6978_);
                    lean_inc(v_cancelTk_x3f_6976_);
                    lean_inc(v_currMacroScope_6974_);
                    lean_inc(v_quotContext_6973_);
                    lean_inc(v_maxHeartbeats_6972_);
                    lean_inc(v_initHeartbeats_6971_);
                    lean_inc(v_openDecls_6970_);
                    lean_inc(v_currNamespace_6969_);
                    lean_inc(v_ref_6968_);
                    lean_inc(v_maxRecDepth_6967_);
                    lean_inc(v_currRecDepth_6966_);
                    lean_inc_ref(v_options_6965_);
                    lean_inc_ref(v_fileMap_6964_);
                    lean_inc_ref(v_fileName_6963_);
                    lean_dec_ref(v_a_6083_);
                    state = 133;
                    continue;
                }
            }
            1 => {
                if v___y_6089_ == 0 {
                    lean_dec_ref(v_code_6077_);
                    v___x_6090_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_6090_, 0, v___y_6087_);
                    lean_ctor_set(v___x_6090_, 1, v___y_6088_);
                    v___x_6091_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6091_, 0, v___x_6090_);
                    return v___x_6091_;
                } else {
                    lean_dec_ref(v___y_6088_);
                    lean_dec_ref(v___y_6087_);
                    v___x_6092_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6092_, 0, v_code_6077_);
                    return v___x_6092_;
                }
            }
            2 => {
                if v___y_6096_ == 0 {
                    lean_dec_ref(v_code_6077_);
                    v___x_6097_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_6097_, 0, v___y_6094_);
                    lean_ctor_set(v___x_6097_, 1, v___y_6095_);
                    v___x_6098_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6098_, 0, v___x_6097_);
                    return v___x_6098_;
                } else {
                    lean_dec_ref(v___y_6095_);
                    lean_dec_ref(v___y_6094_);
                    v___x_6099_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6099_, 0, v_code_6077_);
                    return v___x_6099_;
                }
            }
            3 => match lean_obj_tag(v_code_6077_) {
                1 => {
                    v_decl_6103_ = lean_ctor_get(v_code_6077_, 0);
                    v_k_6104_ = lean_ctor_get(v_code_6077_, 1);
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
                    v_decl_6111_ = lean_ctor_get(v_code_6077_, 0);
                    v_k_6112_ = lean_ctor_get(v_code_6077_, 1);
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
                    lean_dec_ref(v___y_6102_);
                    lean_dec_ref(v___y_6101_);
                    lean_dec_ref(v_code_6077_);
                    v___x_6119_ = lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_simp___closed__3),
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_simp___closed__3_once),
                        _init_l_Lean_Compiler_LCNF_Simp_simp___closed__3,
                    );
                    v___x_6120_ =
                        l_panic___at___00Lean_Compiler_LCNF_Simp_simp_spec__3(v___x_6119_);
                    v___x_6121_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6121_, 0, v___x_6120_);
                    return v___x_6121_;
                }
            },
            4 => {
                lean_inc_ref(v___y_6131_);
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
                if lean_obj_tag(v___x_6133_) == 0 {
                    v_a_6134_ = lean_ctor_get(v___x_6133_, 0);
                    lean_inc(v_a_6134_);
                    lean_dec_ref_known(v___x_6133_, 1);
                    v_fvarId_6135_ = lean_ctor_get(v_decl_6125_, 0);
                    v___x_6136_ =
                        l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_6135_, v___y_6127_);
                    if lean_obj_tag(v___x_6136_) == 0 {
                        v_a_6137_ = lean_ctor_get(v___x_6136_, 0);
                        lean_inc(v_a_6137_);
                        lean_dec_ref_known(v___x_6136_, 1);
                        v___x_6138_ = (lean_unbox(v_a_6137_) as u8);
                        lean_dec(v_a_6137_);
                        if v___x_6138_ == 0 {
                            lean_dec_ref(v___y_6131_);
                            lean_dec_ref(v_code_6077_);
                            v___x_6139_ = l_Lean_Compiler_LCNF_Simp_eraseFunDecl___redArg(
                                v_decl_6125_,
                                v___y_6127_,
                                v___y_6130_,
                            );
                            lean_dec_ref(v_decl_6125_);
                            if lean_obj_tag(v___x_6139_) == 0 {
                                v_isSharedCheck_6146_ = (!lean_is_exclusive(v___x_6139_)) as u8;
                                if v_isSharedCheck_6146_ == 0 {
                                    v_unused_6147_ = lean_ctor_get(v___x_6139_, 0);
                                    lean_dec(v_unused_6147_);
                                    v___x_6141_ = v___x_6139_;
                                    v_isShared_6142_ = v_isSharedCheck_6146_;
                                    state = 5;
                                    continue;
                                } else {
                                    lean_dec(v___x_6139_);
                                    v___x_6141_ = lean_box(0);
                                    v_isShared_6142_ = v_isSharedCheck_6146_;
                                    state = 5;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_6134_);
                                v_a_6148_ = lean_ctor_get(v___x_6139_, 0);
                                v_isSharedCheck_6155_ = (!lean_is_exclusive(v___x_6139_)) as u8;
                                if v_isSharedCheck_6155_ == 0 {
                                    v___x_6150_ = v___x_6139_;
                                    v_isShared_6151_ = v_isSharedCheck_6155_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_6148_);
                                    lean_dec(v___x_6139_);
                                    v___x_6150_ = lean_box(0);
                                    v_isShared_6151_ = v_isSharedCheck_6155_;
                                    state = 7;
                                    continue;
                                }
                            }
                        } else {
                            if v___y_6123_ == 0 {
                                lean_dec_ref(v___y_6131_);
                                v___y_6101_ = v_decl_6125_;
                                v___y_6102_ = v_a_6134_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc_ref(v_decl_6125_);
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
                                lean_dec_ref(v___y_6131_);
                                if lean_obj_tag(v___x_6156_) == 0 {
                                    lean_dec_ref_known(v___x_6156_, 1);
                                    v___y_6101_ = v_decl_6125_;
                                    v___y_6102_ = v_a_6134_;
                                    state = 3;
                                    continue;
                                } else {
                                    lean_dec(v_a_6134_);
                                    lean_dec_ref(v_decl_6125_);
                                    lean_dec_ref(v_code_6077_);
                                    v_a_6157_ = lean_ctor_get(v___x_6156_, 0);
                                    v_isSharedCheck_6164_ = (!lean_is_exclusive(v___x_6156_)) as u8;
                                    if v_isSharedCheck_6164_ == 0 {
                                        v___x_6159_ = v___x_6156_;
                                        v_isShared_6160_ = v_isSharedCheck_6164_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6157_);
                                        lean_dec(v___x_6156_);
                                        v___x_6159_ = lean_box(0);
                                        v_isShared_6160_ = v_isSharedCheck_6164_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_6134_);
                        lean_dec_ref(v___y_6131_);
                        lean_dec_ref(v_decl_6125_);
                        lean_dec_ref(v_code_6077_);
                        v_a_6165_ = lean_ctor_get(v___x_6136_, 0);
                        v_isSharedCheck_6172_ = (!lean_is_exclusive(v___x_6136_)) as u8;
                        if v_isSharedCheck_6172_ == 0 {
                            v___x_6167_ = v___x_6136_;
                            v_isShared_6168_ = v_isSharedCheck_6172_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_6165_);
                            lean_dec(v___x_6136_);
                            v___x_6167_ = lean_box(0);
                            v_isShared_6168_ = v_isSharedCheck_6172_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6131_);
                    lean_dec_ref(v_decl_6125_);
                    lean_dec_ref(v_code_6077_);
                    return v___x_6133_;
                }
            }
            5 => {
                if v_isShared_6142_ == 0 {
                    lean_ctor_set(v___x_6141_, 0, v_a_6134_);
                    v___x_6144_ = v___x_6141_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6145_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6145_, 0, v_a_6134_);
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
                    v_reuseFailAlloc_6154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6154_, 0, v_a_6148_);
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
                    v_reuseFailAlloc_6163_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6163_, 0, v_a_6157_);
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
                    v_reuseFailAlloc_6171_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6171_, 0, v_a_6165_);
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
                if lean_obj_tag(v___x_6184_) == 0 {
                    v_a_6185_ = lean_ctor_get(v___x_6184_, 0);
                    lean_inc(v_a_6185_);
                    lean_dec_ref_known(v___x_6184_, 1);
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
                    lean_dec_ref(v___y_6182_);
                    lean_dec_ref(v___y_6175_);
                    lean_dec_ref(v_code_6077_);
                    v_a_6186_ = lean_ctor_get(v___x_6184_, 0);
                    v_isSharedCheck_6193_ = (!lean_is_exclusive(v___x_6184_)) as u8;
                    if v_isSharedCheck_6193_ == 0 {
                        v___x_6188_ = v___x_6184_;
                        v_isShared_6189_ = v_isSharedCheck_6193_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_6186_);
                        lean_dec(v___x_6184_);
                        v___x_6188_ = lean_box(0);
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
                    v_reuseFailAlloc_6192_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6192_, 0, v_a_6186_);
                    v___x_6191_ = v_reuseFailAlloc_6192_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_6191_;
            }
            16 => {
                v_fvarId_6204_ = lean_ctor_get(v_decl_6195_, 0);
                v_params_6205_ = lean_ctor_get(v_decl_6195_, 2);
                v_type_6206_ = lean_ctor_get(v_decl_6195_, 3);
                v___x_6207_ = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(
                    v_fvarId_6204_,
                    v___y_6198_,
                );
                if lean_obj_tag(v___x_6207_) == 0 {
                    v_a_6208_ = lean_ctor_get(v___x_6207_, 0);
                    lean_inc(v_a_6208_);
                    lean_dec_ref_known(v___x_6207_, 1);
                    v___x_6209_ = 0;
                    v___x_6210_ = (lean_unbox(v_a_6208_) as u8);
                    if v___x_6210_ == 0 {
                        v___x_6211_ = l_Lean_Compiler_LCNF_Code_isFun___redArg(v_code_6077_);
                        if v___x_6211_ == 0 {
                            v___x_6212_ = (lean_unbox(v_a_6208_) as u8);
                            lean_dec(v_a_6208_);
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
                            lean_inc_ref(v_type_6206_);
                            v___x_6213_ = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(
                                v_type_6206_,
                                v_params_6205_,
                            );
                            if v___x_6213_ == 0 {
                                v___x_6214_ = (lean_unbox(v_a_6208_) as u8);
                                lean_dec(v_a_6208_);
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
                                v_subst_6216_ = lean_ctor_get(v___x_6215_, 0);
                                lean_inc_ref(v_subst_6216_);
                                lean_dec(v___x_6215_);
                                v___x_6217_ = (lean_unbox(v_a_6208_) as u8);
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
                                lean_dec_ref(v_subst_6216_);
                                if lean_obj_tag(v___x_6218_) == 0 {
                                    v_a_6219_ = lean_ctor_get(v___x_6218_, 0);
                                    lean_inc(v_a_6219_);
                                    lean_dec_ref_known(v___x_6218_, 1);
                                    v___x_6220_ = l_Lean_Compiler_LCNF_FunDecl_etaExpand(
                                        v_a_6219_,
                                        v___y_6200_,
                                        v___y_6201_,
                                        v___y_6202_,
                                        v___y_6203_,
                                    );
                                    if lean_obj_tag(v___x_6220_) == 0 {
                                        v_a_6221_ = lean_ctor_get(v___x_6220_, 0);
                                        lean_inc(v_a_6221_);
                                        lean_dec_ref_known(v___x_6220_, 1);
                                        v___x_6222_ =
                                            l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(
                                                v___y_6198_,
                                            );
                                        if lean_obj_tag(v___x_6222_) == 0 {
                                            lean_dec_ref_known(v___x_6222_, 1);
                                            v___x_6223_ = (lean_unbox(v_a_6208_) as u8);
                                            lean_dec(v_a_6208_);
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
                                            lean_dec(v_a_6221_);
                                            lean_dec(v_a_6208_);
                                            lean_dec_ref(v___y_6202_);
                                            lean_dec_ref(v_k_6196_);
                                            lean_dec_ref(v_code_6077_);
                                            v_a_6224_ = lean_ctor_get(v___x_6222_, 0);
                                            v_isSharedCheck_6231_ =
                                                (!lean_is_exclusive(v___x_6222_)) as u8;
                                            if v_isSharedCheck_6231_ == 0 {
                                                v___x_6226_ = v___x_6222_;
                                                v_isShared_6227_ = v_isSharedCheck_6231_;
                                                state = 17;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6224_);
                                                lean_dec(v___x_6222_);
                                                v___x_6226_ = lean_box(0);
                                                v_isShared_6227_ = v_isSharedCheck_6231_;
                                                state = 17;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_6208_);
                                        lean_dec_ref(v___y_6202_);
                                        lean_dec_ref(v_k_6196_);
                                        lean_dec_ref(v_code_6077_);
                                        v_a_6232_ = lean_ctor_get(v___x_6220_, 0);
                                        v_isSharedCheck_6239_ =
                                            (!lean_is_exclusive(v___x_6220_)) as u8;
                                        if v_isSharedCheck_6239_ == 0 {
                                            v___x_6234_ = v___x_6220_;
                                            v_isShared_6235_ = v_isSharedCheck_6239_;
                                            state = 19;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6232_);
                                            lean_dec(v___x_6220_);
                                            v___x_6234_ = lean_box(0);
                                            v_isShared_6235_ = v_isSharedCheck_6239_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_6208_);
                                    lean_dec_ref(v___y_6202_);
                                    lean_dec_ref(v_k_6196_);
                                    lean_dec_ref(v_code_6077_);
                                    v_a_6240_ = lean_ctor_get(v___x_6218_, 0);
                                    v_isSharedCheck_6247_ = (!lean_is_exclusive(v___x_6218_)) as u8;
                                    if v_isSharedCheck_6247_ == 0 {
                                        v___x_6242_ = v___x_6218_;
                                        v_isShared_6243_ = v_isSharedCheck_6247_;
                                        state = 21;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6240_);
                                        lean_dec(v___x_6218_);
                                        v___x_6242_ = lean_box(0);
                                        v_isShared_6243_ = v_isSharedCheck_6247_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        v___x_6248_ = lean_st_ref_get(v___y_6198_);
                        v_subst_6249_ = lean_ctor_get(v___x_6248_, 0);
                        lean_inc_ref(v_subst_6249_);
                        lean_dec(v___x_6248_);
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
                        lean_dec_ref(v_subst_6249_);
                        if lean_obj_tag(v___x_6251_) == 0 {
                            v_a_6252_ = lean_ctor_get(v___x_6251_, 0);
                            lean_inc(v_a_6252_);
                            lean_dec_ref_known(v___x_6251_, 1);
                            v___x_6253_ = (lean_unbox(v_a_6208_) as u8);
                            lean_dec(v_a_6208_);
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
                            lean_dec(v_a_6208_);
                            lean_dec_ref(v___y_6202_);
                            lean_dec_ref(v_k_6196_);
                            lean_dec_ref(v_code_6077_);
                            v_a_6254_ = lean_ctor_get(v___x_6251_, 0);
                            v_isSharedCheck_6261_ = (!lean_is_exclusive(v___x_6251_)) as u8;
                            if v_isSharedCheck_6261_ == 0 {
                                v___x_6256_ = v___x_6251_;
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_6254_);
                                lean_dec(v___x_6251_);
                                v___x_6256_ = lean_box(0);
                                v_isShared_6257_ = v_isSharedCheck_6261_;
                                state = 23;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6202_);
                    lean_dec_ref(v_k_6196_);
                    lean_dec_ref(v_decl_6195_);
                    lean_dec_ref(v_code_6077_);
                    v_a_6262_ = lean_ctor_get(v___x_6207_, 0);
                    v_isSharedCheck_6269_ = (!lean_is_exclusive(v___x_6207_)) as u8;
                    if v_isSharedCheck_6269_ == 0 {
                        v___x_6264_ = v___x_6207_;
                        v_isShared_6265_ = v_isSharedCheck_6269_;
                        state = 25;
                        continue;
                    } else {
                        lean_inc(v_a_6262_);
                        lean_dec(v___x_6207_);
                        v___x_6264_ = lean_box(0);
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
                    v_reuseFailAlloc_6230_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6230_, 0, v_a_6224_);
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
                    v_reuseFailAlloc_6238_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6238_, 0, v_a_6232_);
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
                    v_reuseFailAlloc_6246_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6246_, 0, v_a_6240_);
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
                    v_reuseFailAlloc_6260_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6260_, 0, v_a_6254_);
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
                    v_reuseFailAlloc_6268_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6268_, 0, v_a_6262_);
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
                    lean_dec_ref(v_code_6077_);
                    v___x_6274_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6274_, 0, v___y_6271_);
                    lean_ctor_set(v___x_6274_, 1, v___y_6272_);
                    v___x_6275_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6275_, 0, v___x_6274_);
                    return v___x_6275_;
                } else {
                    lean_dec_ref(v___y_6272_);
                    lean_dec_ref(v___y_6271_);
                    v___x_6276_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6276_, 0, v_code_6077_);
                    return v___x_6276_;
                }
            }
            28 => {
                lean_inc_ref(v___y_6279_);
                v___x_6288_ = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(
                    v___y_6279_,
                    v___y_6285_,
                    v___y_6278_,
                    v___y_6280_,
                    v___y_6283_,
                );
                if lean_obj_tag(v___x_6288_) == 0 {
                    v_a_6289_ = lean_ctor_get(v___x_6288_, 0);
                    lean_inc(v_a_6289_);
                    lean_dec_ref_known(v___x_6288_, 1);
                    if lean_obj_tag(v_a_6289_) == 1 {
                        lean_dec_ref(v___y_6286_);
                        lean_dec_ref(v___y_6279_);
                        lean_dec_ref(v_code_6077_);
                        v_val_6290_ = lean_ctor_get(v_a_6289_, 0);
                        lean_inc(v_val_6290_);
                        lean_dec_ref_known(v_a_6289_, 1);
                        v___x_6291_ =
                            l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6281_);
                        if lean_obj_tag(v___x_6291_) == 0 {
                            lean_dec_ref_known(v___x_6291_, 1);
                            lean_inc_ref(v___y_6280_);
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
                            if lean_obj_tag(v___x_6292_) == 0 {
                                v_a_6293_ = lean_ctor_get(v___x_6292_, 0);
                                lean_inc(v_a_6293_);
                                lean_dec_ref_known(v___x_6292_, 1);
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
                                lean_dec_ref(v___y_6280_);
                                lean_dec(v_val_6290_);
                                return v___x_6294_;
                            } else {
                                lean_dec(v_val_6290_);
                                lean_dec_ref(v___y_6280_);
                                return v___x_6292_;
                            }
                        } else {
                            lean_dec(v_val_6290_);
                            lean_dec_ref(v___y_6287_);
                            lean_dec_ref(v___y_6280_);
                            v_a_6295_ = lean_ctor_get(v___x_6291_, 0);
                            v_isSharedCheck_6302_ = (!lean_is_exclusive(v___x_6291_)) as u8;
                            if v_isSharedCheck_6302_ == 0 {
                                v___x_6297_ = v___x_6291_;
                                v_isShared_6298_ = v_isSharedCheck_6302_;
                                state = 29;
                                continue;
                            } else {
                                lean_inc(v_a_6295_);
                                lean_dec(v___x_6291_);
                                v___x_6297_ = lean_box(0);
                                v_isShared_6298_ = v_isSharedCheck_6302_;
                                state = 29;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_6289_);
                        lean_inc_ref(v___y_6279_);
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
                        if lean_obj_tag(v___x_6303_) == 0 {
                            v_a_6304_ = lean_ctor_get(v___x_6303_, 0);
                            lean_inc(v_a_6304_);
                            lean_dec_ref_known(v___x_6303_, 1);
                            if lean_obj_tag(v_a_6304_) == 1 {
                                lean_dec_ref(v___y_6286_);
                                lean_dec_ref(v___y_6279_);
                                lean_dec_ref(v_code_6077_);
                                v_val_6305_ = lean_ctor_get(v_a_6304_, 0);
                                lean_inc(v_val_6305_);
                                lean_dec_ref_known(v_a_6304_, 1);
                                v___x_6306_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_6306_, 0, v_val_6305_);
                                lean_ctor_set(v___x_6306_, 1, v___y_6287_);
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
                                lean_dec(v_a_6304_);
                                v_fvarId_6308_ = lean_ctor_get(v___y_6279_, 0);
                                v_value_6309_ = lean_ctor_get(v___y_6279_, 3);
                                v___x_6310_ =
                                    l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(v_value_6309_);
                                if lean_obj_tag(v___x_6310_) == 0 {
                                    v_a_6311_ = lean_ctor_get(v___x_6310_, 0);
                                    lean_inc(v_a_6311_);
                                    lean_dec_ref_known(v___x_6310_, 1);
                                    if lean_obj_tag(v_a_6311_) == 1 {
                                        lean_dec_ref(v___y_6286_);
                                        lean_dec_ref(v_code_6077_);
                                        v_val_6312_ = lean_ctor_get(v_a_6311_, 0);
                                        lean_inc(v_val_6312_);
                                        lean_dec_ref_known(v_a_6311_, 1);
                                        lean_inc(v_fvarId_6308_);
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
                                        if lean_obj_tag(v___x_6313_) == 0 {
                                            lean_dec_ref_known(v___x_6313_, 1);
                                            v___x_6314_ =
                                                l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
                                                    v___y_6279_,
                                                    v___y_6281_,
                                                    v___y_6278_,
                                                );
                                            lean_dec_ref(v___y_6279_);
                                            if lean_obj_tag(v___x_6314_) == 0 {
                                                lean_dec_ref_known(v___x_6314_, 1);
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
                                                lean_dec_ref(v___y_6287_);
                                                lean_dec_ref(v___y_6280_);
                                                v_a_6316_ = lean_ctor_get(v___x_6314_, 0);
                                                v_isSharedCheck_6323_ =
                                                    (!lean_is_exclusive(v___x_6314_)) as u8;
                                                if v_isSharedCheck_6323_ == 0 {
                                                    v___x_6318_ = v___x_6314_;
                                                    v_isShared_6319_ = v_isSharedCheck_6323_;
                                                    state = 31;
                                                    continue;
                                                } else {
                                                    lean_inc(v_a_6316_);
                                                    lean_dec(v___x_6314_);
                                                    v___x_6318_ = lean_box(0);
                                                    v_isShared_6319_ = v_isSharedCheck_6323_;
                                                    state = 31;
                                                    continue;
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___y_6287_);
                                            lean_dec_ref(v___y_6280_);
                                            lean_dec_ref(v___y_6279_);
                                            v_a_6324_ = lean_ctor_get(v___x_6313_, 0);
                                            v_isSharedCheck_6331_ =
                                                (!lean_is_exclusive(v___x_6313_)) as u8;
                                            if v_isSharedCheck_6331_ == 0 {
                                                v___x_6326_ = v___x_6313_;
                                                v_isShared_6327_ = v_isSharedCheck_6331_;
                                                state = 33;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6324_);
                                                lean_dec(v___x_6313_);
                                                v___x_6326_ = lean_box(0);
                                                v_isShared_6327_ = v_isSharedCheck_6331_;
                                                state = 33;
                                                continue;
                                            }
                                        }
                                    } else {
                                        lean_dec(v_a_6311_);
                                        lean_inc_ref(v___y_6287_);
                                        lean_inc_ref(v___y_6279_);
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
                                        if lean_obj_tag(v___x_6332_) == 0 {
                                            v_a_6333_ = lean_ctor_get(v___x_6332_, 0);
                                            lean_inc(v_a_6333_);
                                            lean_dec_ref_known(v___x_6332_, 1);
                                            if lean_obj_tag(v_a_6333_) == 1 {
                                                lean_dec_ref(v___y_6287_);
                                                lean_dec_ref(v___y_6286_);
                                                lean_dec_ref(v___y_6280_);
                                                lean_dec_ref(v_code_6077_);
                                                v_val_6334_ = lean_ctor_get(v_a_6333_, 0);
                                                lean_inc(v_val_6334_);
                                                lean_dec_ref_known(v_a_6333_, 1);
                                                v___x_6335_ =
                                                    l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(
                                                        v___y_6279_,
                                                        v___y_6281_,
                                                        v___y_6278_,
                                                    );
                                                lean_dec_ref(v___y_6279_);
                                                if lean_obj_tag(v___x_6335_) == 0 {
                                                    v_isSharedCheck_6342_ =
                                                        (!lean_is_exclusive(v___x_6335_)) as u8;
                                                    if v_isSharedCheck_6342_ == 0 {
                                                        v_unused_6343_ =
                                                            lean_ctor_get(v___x_6335_, 0);
                                                        lean_dec(v_unused_6343_);
                                                        v___x_6337_ = v___x_6335_;
                                                        v_isShared_6338_ = v_isSharedCheck_6342_;
                                                        state = 35;
                                                        continue;
                                                    } else {
                                                        lean_dec(v___x_6335_);
                                                        v___x_6337_ = lean_box(0);
                                                        v_isShared_6338_ = v_isSharedCheck_6342_;
                                                        state = 35;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v_val_6334_);
                                                    v_a_6344_ = lean_ctor_get(v___x_6335_, 0);
                                                    v_isSharedCheck_6351_ =
                                                        (!lean_is_exclusive(v___x_6335_)) as u8;
                                                    if v_isSharedCheck_6351_ == 0 {
                                                        v___x_6346_ = v___x_6335_;
                                                        v_isShared_6347_ = v_isSharedCheck_6351_;
                                                        state = 37;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_6344_);
                                                        lean_dec(v___x_6335_);
                                                        v___x_6346_ = lean_box(0);
                                                        v_isShared_6347_ = v_isSharedCheck_6351_;
                                                        state = 37;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec(v_a_6333_);
                                                lean_inc(v_value_6309_);
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
                                                if lean_obj_tag(v___x_6352_) == 0 {
                                                    v_a_6353_ = lean_ctor_get(v___x_6352_, 0);
                                                    lean_inc(v_a_6353_);
                                                    lean_dec_ref_known(v___x_6352_, 1);
                                                    if lean_obj_tag(v_a_6353_) == 1 {
                                                        lean_dec_ref(v___y_6286_);
                                                        lean_dec_ref(v_code_6077_);
                                                        v_val_6354_ = lean_ctor_get(v_a_6353_, 0);
                                                        lean_inc(v_val_6354_);
                                                        lean_dec_ref_known(v_a_6353_, 1);
                                                        v_fst_6355_ = lean_ctor_get(v_val_6354_, 0);
                                                        lean_inc(v_fst_6355_);
                                                        v_snd_6356_ = lean_ctor_get(v_val_6354_, 1);
                                                        lean_inc(v_snd_6356_);
                                                        lean_dec(v_val_6354_);
                                                        lean_inc(v_fvarId_6308_);
                                                        v___x_6357_ = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(v_fvarId_6308_, v_snd_6356_, v___y_6281_, v___y_6285_, v___y_6278_, v___y_6280_, v___y_6283_);
                                                        if lean_obj_tag(v___x_6357_) == 0 {
                                                            lean_dec_ref_known(v___x_6357_, 1);
                                                            v___x_6358_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_6279_, v___y_6281_, v___y_6278_);
                                                            lean_dec_ref(v___y_6279_);
                                                            if lean_obj_tag(v___x_6358_) == 0 {
                                                                lean_dec_ref_known(v___x_6358_, 1);
                                                                lean_inc_ref(v___y_6280_);
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
                                                                if lean_obj_tag(v___x_6359_) == 0 {
                                                                    v_a_6360_ = lean_ctor_get(
                                                                        v___x_6359_,
                                                                        0,
                                                                    );
                                                                    lean_inc(v_a_6360_);
                                                                    lean_dec_ref_known(
                                                                        v___x_6359_,
                                                                        1,
                                                                    );
                                                                    v___x_6361_ = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(v_fst_6355_, v_a_6360_, v___y_6282_, v___y_6281_, v___y_6284_, v___y_6285_, v___y_6278_, v___y_6280_, v___y_6283_);
                                                                    lean_dec_ref(v___y_6280_);
                                                                    lean_dec(v_fst_6355_);
                                                                    return v___x_6361_;
                                                                } else {
                                                                    lean_dec(v_fst_6355_);
                                                                    lean_dec_ref(v___y_6280_);
                                                                    return v___x_6359_;
                                                                }
                                                            } else {
                                                                lean_dec(v_fst_6355_);
                                                                lean_dec_ref(v___y_6287_);
                                                                lean_dec_ref(v___y_6280_);
                                                                v_a_6362_ =
                                                                    lean_ctor_get(v___x_6358_, 0);
                                                                v_isSharedCheck_6369_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_6358_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_6369_ == 0 {
                                                                    v___x_6364_ = v___x_6358_;
                                                                    v_isShared_6365_ =
                                                                        v_isSharedCheck_6369_;
                                                                    state = 39;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_6362_);
                                                                    lean_dec(v___x_6358_);
                                                                    v___x_6364_ = lean_box(0);
                                                                    v_isShared_6365_ =
                                                                        v_isSharedCheck_6369_;
                                                                    state = 39;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec(v_fst_6355_);
                                                            lean_dec_ref(v___y_6287_);
                                                            lean_dec_ref(v___y_6280_);
                                                            lean_dec_ref(v___y_6279_);
                                                            v_a_6370_ =
                                                                lean_ctor_get(v___x_6357_, 0);
                                                            v_isSharedCheck_6377_ =
                                                                (!lean_is_exclusive(v___x_6357_))
                                                                    as u8;
                                                            if v_isSharedCheck_6377_ == 0 {
                                                                v___x_6372_ = v___x_6357_;
                                                                v_isShared_6373_ =
                                                                    v_isSharedCheck_6377_;
                                                                state = 41;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_6370_);
                                                                lean_dec(v___x_6357_);
                                                                v___x_6372_ = lean_box(0);
                                                                v_isShared_6373_ =
                                                                    v_isSharedCheck_6377_;
                                                                state = 41;
                                                                continue;
                                                            }
                                                        }
                                                    } else {
                                                        lean_dec(v_a_6353_);
                                                        lean_inc_ref(v___y_6280_);
                                                        lean_inc_ref(v___y_6287_);
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
                                                        if lean_obj_tag(v___x_6378_) == 0 {
                                                            v_a_6379_ =
                                                                lean_ctor_get(v___x_6378_, 0);
                                                            lean_inc(v_a_6379_);
                                                            lean_dec_ref_known(v___x_6378_, 1);
                                                            v___x_6380_ = l_Lean_Compiler_LCNF_Simp_isUsed___redArg(v_fvarId_6308_, v___y_6281_);
                                                            if lean_obj_tag(v___x_6380_) == 0 {
                                                                v_a_6381_ =
                                                                    lean_ctor_get(v___x_6380_, 0);
                                                                lean_inc(v_a_6381_);
                                                                lean_dec_ref_known(v___x_6380_, 1);
                                                                v___x_6382_ =
                                                                    (lean_unbox(v_a_6381_) as u8);
                                                                lean_dec(v_a_6381_);
                                                                if v___x_6382_ == 0 {
                                                                    lean_dec_ref(v___y_6287_);
                                                                    lean_dec_ref(v___y_6286_);
                                                                    lean_dec_ref(v___y_6280_);
                                                                    lean_dec_ref(v_code_6077_);
                                                                    v___x_6383_ = l_Lean_Compiler_LCNF_Simp_eraseLetDecl___redArg(v___y_6279_, v___y_6281_, v___y_6278_);
                                                                    lean_dec_ref(v___y_6279_);
                                                                    if lean_obj_tag(v___x_6383_)
                                                                        == 0
                                                                    {
                                                                        v_isSharedCheck_6390_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_6383_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_6390_
                                                                            == 0
                                                                        {
                                                                            v_unused_6391_ =
                                                                                lean_ctor_get(
                                                                                    v___x_6383_,
                                                                                    0,
                                                                                );
                                                                            lean_dec(
                                                                                v_unused_6391_,
                                                                            );
                                                                            v___x_6385_ =
                                                                                v___x_6383_;
                                                                            v_isShared_6386_ = v_isSharedCheck_6390_;
                                                                            state = 43;
                                                                            continue;
                                                                        } else {
                                                                            lean_dec(v___x_6383_);
                                                                            v___x_6385_ =
                                                                                lean_box(0);
                                                                            v_isShared_6386_ = v_isSharedCheck_6390_;
                                                                            state = 43;
                                                                            continue;
                                                                        }
                                                                    } else {
                                                                        lean_dec(v_a_6379_);
                                                                        v_a_6392_ = lean_ctor_get(
                                                                            v___x_6383_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_6399_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_6383_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_6399_
                                                                            == 0
                                                                        {
                                                                            v___x_6394_ =
                                                                                v___x_6383_;
                                                                            v_isShared_6395_ = v_isSharedCheck_6399_;
                                                                            state = 45;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_6392_);
                                                                            lean_dec(v___x_6383_);
                                                                            v___x_6394_ =
                                                                                lean_box(0);
                                                                            v_isShared_6395_ = v_isSharedCheck_6399_;
                                                                            state = 45;
                                                                            continue;
                                                                        }
                                                                    }
                                                                } else {
                                                                    lean_inc_ref(v___y_6279_);
                                                                    v___x_6400_ = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(v___y_6279_, v___y_6282_, v___y_6281_, v___y_6284_, v___y_6285_, v___y_6278_, v___y_6280_, v___y_6283_);
                                                                    lean_dec_ref(v___y_6280_);
                                                                    if lean_obj_tag(v___x_6400_)
                                                                        == 0
                                                                    {
                                                                        lean_dec_ref_known(
                                                                            v___x_6400_,
                                                                            1,
                                                                        );
                                                                        v___x_6401_ = lean_ptr_addr(
                                                                            v___y_6287_,
                                                                        );
                                                                        lean_dec_ref(v___y_6287_);
                                                                        v___x_6402_ = lean_ptr_addr(
                                                                            v_a_6379_,
                                                                        );
                                                                        v___x_6403_ =
                                                                            lean_usize_dec_eq(
                                                                                v___x_6401_,
                                                                                v___x_6402_,
                                                                            );
                                                                        if v___x_6403_ == 0 {
                                                                            lean_dec_ref(
                                                                                v___y_6286_,
                                                                            );
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
                                                                            lean_dec_ref(
                                                                                v___y_6286_,
                                                                            );
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
                                                                        lean_dec(v_a_6379_);
                                                                        lean_dec_ref(v___y_6287_);
                                                                        lean_dec_ref(v___y_6286_);
                                                                        lean_dec_ref(v___y_6279_);
                                                                        lean_dec_ref(v_code_6077_);
                                                                        v_a_6407_ = lean_ctor_get(
                                                                            v___x_6400_,
                                                                            0,
                                                                        );
                                                                        v_isSharedCheck_6414_ =
                                                                            (!lean_is_exclusive(
                                                                                v___x_6400_,
                                                                            ))
                                                                                as u8;
                                                                        if v_isSharedCheck_6414_
                                                                            == 0
                                                                        {
                                                                            v___x_6409_ =
                                                                                v___x_6400_;
                                                                            v_isShared_6410_ = v_isSharedCheck_6414_;
                                                                            state = 47;
                                                                            continue;
                                                                        } else {
                                                                            lean_inc(v_a_6407_);
                                                                            lean_dec(v___x_6400_);
                                                                            v___x_6409_ =
                                                                                lean_box(0);
                                                                            v_isShared_6410_ = v_isSharedCheck_6414_;
                                                                            state = 47;
                                                                            continue;
                                                                        }
                                                                    }
                                                                }
                                                            } else {
                                                                lean_dec(v_a_6379_);
                                                                lean_dec_ref(v___y_6287_);
                                                                lean_dec_ref(v___y_6286_);
                                                                lean_dec_ref(v___y_6280_);
                                                                lean_dec_ref(v___y_6279_);
                                                                lean_dec_ref(v_code_6077_);
                                                                v_a_6415_ =
                                                                    lean_ctor_get(v___x_6380_, 0);
                                                                v_isSharedCheck_6422_ =
                                                                    (!lean_is_exclusive(
                                                                        v___x_6380_,
                                                                    ))
                                                                        as u8;
                                                                if v_isSharedCheck_6422_ == 0 {
                                                                    v___x_6417_ = v___x_6380_;
                                                                    v_isShared_6418_ =
                                                                        v_isSharedCheck_6422_;
                                                                    state = 49;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_a_6415_);
                                                                    lean_dec(v___x_6380_);
                                                                    v___x_6417_ = lean_box(0);
                                                                    v_isShared_6418_ =
                                                                        v_isSharedCheck_6422_;
                                                                    state = 49;
                                                                    continue;
                                                                }
                                                            }
                                                        } else {
                                                            lean_dec_ref(v___y_6287_);
                                                            lean_dec_ref(v___y_6286_);
                                                            lean_dec_ref(v___y_6280_);
                                                            lean_dec_ref(v___y_6279_);
                                                            lean_dec_ref(v_code_6077_);
                                                            return v___x_6378_;
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___y_6287_);
                                                    lean_dec_ref(v___y_6286_);
                                                    lean_dec_ref(v___y_6280_);
                                                    lean_dec_ref(v___y_6279_);
                                                    lean_dec_ref(v_code_6077_);
                                                    v_a_6423_ = lean_ctor_get(v___x_6352_, 0);
                                                    v_isSharedCheck_6430_ =
                                                        (!lean_is_exclusive(v___x_6352_)) as u8;
                                                    if v_isSharedCheck_6430_ == 0 {
                                                        v___x_6425_ = v___x_6352_;
                                                        v_isShared_6426_ = v_isSharedCheck_6430_;
                                                        state = 51;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_6423_);
                                                        lean_dec(v___x_6352_);
                                                        v___x_6425_ = lean_box(0);
                                                        v_isShared_6426_ = v_isSharedCheck_6430_;
                                                        state = 51;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v___y_6287_);
                                            lean_dec_ref(v___y_6286_);
                                            lean_dec_ref(v___y_6280_);
                                            lean_dec_ref(v___y_6279_);
                                            lean_dec_ref(v_code_6077_);
                                            v_a_6431_ = lean_ctor_get(v___x_6332_, 0);
                                            v_isSharedCheck_6438_ =
                                                (!lean_is_exclusive(v___x_6332_)) as u8;
                                            if v_isSharedCheck_6438_ == 0 {
                                                v___x_6433_ = v___x_6332_;
                                                v_isShared_6434_ = v_isSharedCheck_6438_;
                                                state = 53;
                                                continue;
                                            } else {
                                                lean_inc(v_a_6431_);
                                                lean_dec(v___x_6332_);
                                                v___x_6433_ = lean_box(0);
                                                v_isShared_6434_ = v_isSharedCheck_6438_;
                                                state = 53;
                                                continue;
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___y_6287_);
                                    lean_dec_ref(v___y_6286_);
                                    lean_dec_ref(v___y_6280_);
                                    lean_dec_ref(v___y_6279_);
                                    lean_dec_ref(v_code_6077_);
                                    v_a_6439_ = lean_ctor_get(v___x_6310_, 0);
                                    v_isSharedCheck_6446_ = (!lean_is_exclusive(v___x_6310_)) as u8;
                                    if v_isSharedCheck_6446_ == 0 {
                                        v___x_6441_ = v___x_6310_;
                                        v_isShared_6442_ = v_isSharedCheck_6446_;
                                        state = 55;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6439_);
                                        lean_dec(v___x_6310_);
                                        v___x_6441_ = lean_box(0);
                                        v_isShared_6442_ = v_isSharedCheck_6446_;
                                        state = 55;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___y_6287_);
                            lean_dec_ref(v___y_6286_);
                            lean_dec_ref(v___y_6280_);
                            lean_dec_ref(v___y_6279_);
                            lean_dec_ref(v_code_6077_);
                            v_a_6447_ = lean_ctor_get(v___x_6303_, 0);
                            v_isSharedCheck_6454_ = (!lean_is_exclusive(v___x_6303_)) as u8;
                            if v_isSharedCheck_6454_ == 0 {
                                v___x_6449_ = v___x_6303_;
                                v_isShared_6450_ = v_isSharedCheck_6454_;
                                state = 57;
                                continue;
                            } else {
                                lean_inc(v_a_6447_);
                                lean_dec(v___x_6303_);
                                v___x_6449_ = lean_box(0);
                                v_isShared_6450_ = v_isSharedCheck_6454_;
                                state = 57;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v___y_6287_);
                    lean_dec_ref(v___y_6286_);
                    lean_dec_ref(v___y_6280_);
                    lean_dec_ref(v___y_6279_);
                    lean_dec_ref(v_code_6077_);
                    v_a_6455_ = lean_ctor_get(v___x_6288_, 0);
                    v_isSharedCheck_6462_ = (!lean_is_exclusive(v___x_6288_)) as u8;
                    if v_isSharedCheck_6462_ == 0 {
                        v___x_6457_ = v___x_6288_;
                        v_isShared_6458_ = v_isSharedCheck_6462_;
                        state = 59;
                        continue;
                    } else {
                        lean_inc(v_a_6455_);
                        lean_dec(v___x_6288_);
                        v___x_6457_ = lean_box(0);
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
                    v_reuseFailAlloc_6301_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6301_, 0, v_a_6295_);
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
                    v_reuseFailAlloc_6322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6322_, 0, v_a_6316_);
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
                    v_reuseFailAlloc_6330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6330_, 0, v_a_6324_);
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
                    lean_ctor_set(v___x_6337_, 0, v_val_6334_);
                    v___x_6340_ = v___x_6337_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_6341_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6341_, 0, v_val_6334_);
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
                    v_reuseFailAlloc_6350_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6350_, 0, v_a_6344_);
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
                    v_reuseFailAlloc_6368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6368_, 0, v_a_6362_);
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
                    v_reuseFailAlloc_6376_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6376_, 0, v_a_6370_);
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
                    lean_ctor_set(v___x_6385_, 0, v_a_6379_);
                    v___x_6388_ = v___x_6385_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_6389_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6389_, 0, v_a_6379_);
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
                    v_reuseFailAlloc_6398_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6398_, 0, v_a_6392_);
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
                    v_reuseFailAlloc_6413_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6413_, 0, v_a_6407_);
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
                    v_reuseFailAlloc_6421_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6421_, 0, v_a_6415_);
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
                    v_reuseFailAlloc_6429_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6429_, 0, v_a_6423_);
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
                    v_reuseFailAlloc_6437_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6437_, 0, v_a_6431_);
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
                    v_reuseFailAlloc_6445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6445_, 0, v_a_6439_);
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
                    v_reuseFailAlloc_6453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6453_, 0, v_a_6447_);
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
                    v_reuseFailAlloc_6461_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6461_, 0, v_a_6455_);
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
                lean_dec_ref(v_type_6469_);
                if v___x_6478_ == 0 {
                    lean_dec(v_value_6470_);
                    lean_dec(v_fvarId_6468_);
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
                    v___x_6479_ = lean_box(1);
                    v___x_6480_ = l_Lean_Compiler_LCNF_instBEqLetValue_beq(
                        v___y_6464_,
                        v_value_6470_,
                        v___x_6479_,
                    );
                    lean_dec(v_value_6470_);
                    if v___x_6480_ == 0 {
                        if v___x_6478_ == 0 {
                            lean_dec(v_fvarId_6468_);
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
                            lean_dec_ref(v___y_6466_);
                            lean_dec_ref(v_code_6077_);
                            v___x_6481_ = lean_st_ref_take(v___y_6472_);
                            v_subst_6482_ = lean_ctor_get(v___x_6481_, 0);
                            v_used_6483_ = lean_ctor_get(v___x_6481_, 1);
                            v_binderRenaming_6484_ = lean_ctor_get(v___x_6481_, 2);
                            v_funDeclInfoMap_6485_ = lean_ctor_get(v___x_6481_, 3);
                            v_simplified_6486_ = lean_ctor_get_uint8(
                                v___x_6481_,
                                (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
                            );
                            v_visited_6487_ = lean_ctor_get(v___x_6481_, 4);
                            v_inline_6488_ = lean_ctor_get(v___x_6481_, 5);
                            v_inlineLocal_6489_ = lean_ctor_get(v___x_6481_, 6);
                            v_isSharedCheck_6509_ = (!lean_is_exclusive(v___x_6481_)) as u8;
                            if v_isSharedCheck_6509_ == 0 {
                                v___x_6491_ = v___x_6481_;
                                v_isShared_6492_ = v_isSharedCheck_6509_;
                                state = 62;
                                continue;
                            } else {
                                lean_inc(v_inlineLocal_6489_);
                                lean_inc(v_inline_6488_);
                                lean_inc(v_visited_6487_);
                                lean_inc(v_funDeclInfoMap_6485_);
                                lean_inc(v_binderRenaming_6484_);
                                lean_inc(v_used_6483_);
                                lean_inc(v_subst_6482_);
                                lean_dec(v___x_6481_);
                                v___x_6491_ = lean_box(0);
                                v_isShared_6492_ = v_isSharedCheck_6509_;
                                state = 62;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_fvarId_6468_);
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
                v___x_6493_ = lean_box(0);
                v___x_6494_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(v_subst_6482_, v_fvarId_6468_, v___x_6493_);
                if v_isShared_6492_ == 0 {
                    lean_ctor_set(v___x_6491_, 0, v___x_6494_);
                    v___x_6496_ = v___x_6491_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_6508_ = lean_alloc_ctor(0, 7, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 0, v___x_6494_);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 1, v_used_6483_);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 2, v_binderRenaming_6484_);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 3, v_funDeclInfoMap_6485_);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 4, v_visited_6487_);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 5, v_inline_6488_);
                    lean_ctor_set(v_reuseFailAlloc_6508_, 6, v_inlineLocal_6489_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_6508_,
                        (core::mem::size_of::<*mut LeanObject>() * 7) as u32,
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
                lean_dec_ref(v_decl_6467_);
                if lean_obj_tag(v___x_6498_) == 0 {
                    lean_dec_ref_known(v___x_6498_, 1);
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
                    lean_dec_ref(v___y_6476_);
                    lean_dec_ref(v___y_6465_);
                    v_a_6500_ = lean_ctor_get(v___x_6498_, 0);
                    v_isSharedCheck_6507_ = (!lean_is_exclusive(v___x_6498_)) as u8;
                    if v_isSharedCheck_6507_ == 0 {
                        v___x_6502_ = v___x_6498_;
                        v_isShared_6503_ = v_isSharedCheck_6507_;
                        state = 64;
                        continue;
                    } else {
                        lean_inc(v_a_6500_);
                        lean_dec(v___x_6498_);
                        v___x_6502_ = lean_box(0);
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
                    v_reuseFailAlloc_6506_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6506_, 0, v_a_6500_);
                    v___x_6505_ = v_reuseFailAlloc_6506_;
                    state = 65;
                    continue;
                }
            }
            65 => {
                return v___x_6505_;
            }
            66 => {
                v_fvarId_6522_ = lean_ctor_get(v___y_6514_, 0);
                v_type_6523_ = lean_ctor_get(v___y_6514_, 2);
                v_value_6524_ = lean_ctor_get(v___y_6514_, 3);
                lean_inc(v_value_6524_);
                v___x_6525_ = l_Lean_Compiler_LCNF_Simp_simpValue_x3f___redArg(
                    v_value_6524_,
                    v___y_6515_,
                    v___y_6517_,
                    v___y_6518_,
                    v___y_6519_,
                    v___y_6520_,
                    v___y_6521_,
                );
                if lean_obj_tag(v___x_6525_) == 0 {
                    v_a_6526_ = lean_ctor_get(v___x_6525_, 0);
                    lean_inc(v_a_6526_);
                    lean_dec_ref_known(v___x_6525_, 1);
                    if lean_obj_tag(v_a_6526_) == 1 {
                        v_val_6527_ = lean_ctor_get(v_a_6526_, 0);
                        lean_inc(v_val_6527_);
                        lean_dec_ref_known(v_a_6526_, 1);
                        v___x_6528_ =
                            l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6516_);
                        if lean_obj_tag(v___x_6528_) == 0 {
                            lean_dec_ref_known(v___x_6528_, 1);
                            v___x_6529_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                v___y_6511_,
                                v___y_6514_,
                                v_val_6527_,
                                v___y_6519_,
                            );
                            if lean_obj_tag(v___x_6529_) == 0 {
                                v_a_6530_ = lean_ctor_get(v___x_6529_, 0);
                                lean_inc(v_a_6530_);
                                lean_dec_ref_known(v___x_6529_, 1);
                                v_fvarId_6531_ = lean_ctor_get(v_a_6530_, 0);
                                lean_inc(v_fvarId_6531_);
                                v_type_6532_ = lean_ctor_get(v_a_6530_, 2);
                                lean_inc_ref(v_type_6532_);
                                v_value_6533_ = lean_ctor_get(v_a_6530_, 3);
                                lean_inc(v_value_6533_);
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
                                lean_dec_ref(v___y_6520_);
                                lean_dec_ref(v___y_6513_);
                                lean_dec_ref(v___y_6512_);
                                lean_dec_ref(v_code_6077_);
                                v_a_6534_ = lean_ctor_get(v___x_6529_, 0);
                                v_isSharedCheck_6541_ = (!lean_is_exclusive(v___x_6529_)) as u8;
                                if v_isSharedCheck_6541_ == 0 {
                                    v___x_6536_ = v___x_6529_;
                                    v_isShared_6537_ = v_isSharedCheck_6541_;
                                    state = 67;
                                    continue;
                                } else {
                                    lean_inc(v_a_6534_);
                                    lean_dec(v___x_6529_);
                                    v___x_6536_ = lean_box(0);
                                    v_isShared_6537_ = v_isSharedCheck_6541_;
                                    state = 67;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_val_6527_);
                            lean_dec_ref(v___y_6520_);
                            lean_dec_ref(v___y_6514_);
                            lean_dec_ref(v___y_6513_);
                            lean_dec_ref(v___y_6512_);
                            lean_dec_ref(v_code_6077_);
                            v_a_6542_ = lean_ctor_get(v___x_6528_, 0);
                            v_isSharedCheck_6549_ = (!lean_is_exclusive(v___x_6528_)) as u8;
                            if v_isSharedCheck_6549_ == 0 {
                                v___x_6544_ = v___x_6528_;
                                v_isShared_6545_ = v_isSharedCheck_6549_;
                                state = 69;
                                continue;
                            } else {
                                lean_inc(v_a_6542_);
                                lean_dec(v___x_6528_);
                                v___x_6544_ = lean_box(0);
                                v_isShared_6545_ = v_isSharedCheck_6549_;
                                state = 69;
                                continue;
                            }
                        }
                    } else {
                        lean_inc(v_value_6524_);
                        lean_inc_ref(v_type_6523_);
                        lean_inc(v_fvarId_6522_);
                        lean_dec(v_a_6526_);
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
                    lean_dec_ref(v___y_6520_);
                    lean_dec_ref(v___y_6514_);
                    lean_dec_ref(v___y_6513_);
                    lean_dec_ref(v___y_6512_);
                    lean_dec_ref(v_code_6077_);
                    v_a_6550_ = lean_ctor_get(v___x_6525_, 0);
                    v_isSharedCheck_6557_ = (!lean_is_exclusive(v___x_6525_)) as u8;
                    if v_isSharedCheck_6557_ == 0 {
                        v___x_6552_ = v___x_6525_;
                        v_isShared_6553_ = v_isSharedCheck_6557_;
                        state = 71;
                        continue;
                    } else {
                        lean_inc(v_a_6550_);
                        lean_dec(v___x_6525_);
                        v___x_6552_ = lean_box(0);
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
                    v_reuseFailAlloc_6540_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6540_, 0, v_a_6534_);
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
                    v_reuseFailAlloc_6548_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6548_, 0, v_a_6542_);
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
                    v_reuseFailAlloc_6556_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6556_, 0, v_a_6550_);
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
                    lean_dec_ref(v_code_6077_);
                    v___x_6562_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v___x_6562_, 0, v___y_6559_);
                    lean_ctor_set(v___x_6562_, 1, v___y_6560_);
                    v___x_6563_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6563_, 0, v___x_6562_);
                    return v___x_6563_;
                } else {
                    lean_dec_ref(v___y_6560_);
                    lean_dec(v___y_6559_);
                    v___x_6564_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6564_, 0, v_code_6077_);
                    return v___x_6564_;
                }
            }
            74 => {
                v___x_6570_ = l_Lean_instBEqFVarId_beq(v___y_6566_, v___y_6568_);
                lean_dec(v___y_6566_);
                if v___x_6570_ == 0 {
                    lean_dec_ref(v___y_6567_);
                    v___y_6559_ = v___y_6568_;
                    v___y_6560_ = v___y_6569_;
                    v___y_6561_ = v___x_6570_;
                    state = 73;
                    continue;
                } else {
                    v___x_6571_ = lean_ptr_addr(v___y_6567_);
                    lean_dec_ref(v___y_6567_);
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
                if lean_obj_tag(v___y_6579_) == 0 {
                    lean_dec_ref_known(v___y_6579_, 1);
                    v___y_6566_ = v___y_6575_;
                    v___y_6567_ = v___y_6576_;
                    v___y_6568_ = v___y_6577_;
                    v___y_6569_ = v___y_6578_;
                    state = 74;
                    continue;
                } else {
                    lean_dec_ref(v___y_6578_);
                    lean_dec(v___y_6577_);
                    lean_dec_ref(v___y_6576_);
                    lean_dec(v___y_6575_);
                    lean_dec_ref(v_code_6077_);
                    v_a_6580_ = lean_ctor_get(v___y_6579_, 0);
                    v_isSharedCheck_6587_ = (!lean_is_exclusive(v___y_6579_)) as u8;
                    if v_isSharedCheck_6587_ == 0 {
                        v___x_6582_ = v___y_6579_;
                        v_isShared_6583_ = v_isSharedCheck_6587_;
                        state = 76;
                        continue;
                    } else {
                        lean_inc(v_a_6580_);
                        lean_dec(v___y_6579_);
                        v___x_6582_ = lean_box(0);
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
                    v_reuseFailAlloc_6586_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6586_, 0, v_a_6580_);
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
                if lean_obj_tag(v___x_6591_) == 0 {
                    v_isSharedCheck_6599_ = (!lean_is_exclusive(v___x_6591_)) as u8;
                    if v_isSharedCheck_6599_ == 0 {
                        v_unused_6600_ = lean_ctor_get(v___x_6591_, 0);
                        lean_dec(v_unused_6600_);
                        v___x_6593_ = v___x_6591_;
                        v_isShared_6594_ = v_isSharedCheck_6599_;
                        state = 79;
                        continue;
                    } else {
                        lean_dec(v___x_6591_);
                        v___x_6593_ = lean_box(0);
                        v_isShared_6594_ = v_isSharedCheck_6599_;
                        state = 79;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_6590_);
                    v_a_6601_ = lean_ctor_get(v___x_6591_, 0);
                    v_isSharedCheck_6608_ = (!lean_is_exclusive(v___x_6591_)) as u8;
                    if v_isSharedCheck_6608_ == 0 {
                        v___x_6603_ = v___x_6591_;
                        v_isShared_6604_ = v_isSharedCheck_6608_;
                        state = 81;
                        continue;
                    } else {
                        lean_inc(v_a_6601_);
                        lean_dec(v___x_6591_);
                        v___x_6603_ = lean_box(0);
                        v_isShared_6604_ = v_isSharedCheck_6608_;
                        state = 81;
                        continue;
                    }
                }
            }
            79 => {
                v___x_6595_ = lean_alloc_ctor(6, 1, (0) as u32);
                lean_ctor_set(v___x_6595_, 0, v___y_6590_);
                if v_isShared_6594_ == 0 {
                    lean_ctor_set(v___x_6593_, 0, v___x_6595_);
                    v___x_6597_ = v___x_6593_;
                    state = 80;
                    continue;
                } else {
                    v_reuseFailAlloc_6598_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6598_, 0, v___x_6595_);
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
                    v_reuseFailAlloc_6607_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6607_, 0, v_a_6601_);
                    v___x_6606_ = v_reuseFailAlloc_6607_;
                    state = 82;
                    continue;
                }
            }
            82 => {
                return v___x_6606_;
            }
            83 => {
                if lean_obj_tag(v___y_6612_) == 0 {
                    lean_dec_ref_known(v___y_6612_, 1);
                    v___y_6589_ = v___y_6610_;
                    v___y_6590_ = v___y_6611_;
                    state = 78;
                    continue;
                } else {
                    lean_dec_ref(v___y_6611_);
                    v_a_6613_ = lean_ctor_get(v___y_6612_, 0);
                    v_isSharedCheck_6620_ = (!lean_is_exclusive(v___y_6612_)) as u8;
                    if v_isSharedCheck_6620_ == 0 {
                        v___x_6615_ = v___y_6612_;
                        v_isShared_6616_ = v_isSharedCheck_6620_;
                        state = 84;
                        continue;
                    } else {
                        lean_inc(v_a_6613_);
                        lean_dec(v___y_6612_);
                        v___x_6615_ = lean_box(0);
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
                    v_reuseFailAlloc_6619_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6619_, 0, v_a_6613_);
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
                lean_dec(v___y_6628_);
                if v___x_6631_ == 0 {
                    lean_dec_ref(v___y_6630_);
                    lean_dec_ref(v___y_6624_);
                    lean_dec(v___y_6622_);
                    v___y_6589_ = v___y_6623_;
                    v___y_6590_ = v___y_6626_;
                    state = 78;
                    continue;
                } else {
                    v___x_6632_ = lean_box(0);
                    v___x_6633_ = lean_nat_dec_le(v___y_6622_, v___y_6622_);
                    if v___x_6633_ == 0 {
                        if v___x_6631_ == 0 {
                            lean_dec_ref(v___y_6630_);
                            lean_dec_ref(v___y_6624_);
                            lean_dec(v___y_6622_);
                            v___y_6589_ = v___y_6623_;
                            v___y_6590_ = v___y_6626_;
                            state = 78;
                            continue;
                        } else {
                            v___x_6634_ = 0usize;
                            v___x_6635_ = lean_usize_of_nat(v___y_6622_);
                            lean_dec(v___y_6622_);
                            v___x_6636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_6624_, v___x_6634_, v___x_6635_, v___x_6632_, v___y_6627_, v___y_6625_, v___y_6630_, v___y_6629_);
                            lean_dec_ref(v___y_6630_);
                            lean_dec_ref(v___y_6624_);
                            v___y_6610_ = v___y_6623_;
                            v___y_6611_ = v___y_6626_;
                            v___y_6612_ = v___x_6636_;
                            state = 83;
                            continue;
                        }
                    } else {
                        v___x_6637_ = 0usize;
                        v___x_6638_ = lean_usize_of_nat(v___y_6622_);
                        lean_dec(v___y_6622_);
                        v___x_6639_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v___y_6624_, v___x_6637_, v___x_6638_, v___x_6632_, v___y_6627_, v___y_6625_, v___y_6630_, v___y_6629_);
                        lean_dec_ref(v___y_6630_);
                        lean_dec_ref(v___y_6624_);
                        v___y_6610_ = v___y_6623_;
                        v___y_6611_ = v___y_6626_;
                        v___y_6612_ = v___x_6639_;
                        state = 83;
                        continue;
                    }
                }
            }
            87 => {
                v___x_6645_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_6645_, 0, v___y_6643_);
                lean_ctor_set(v___x_6645_, 1, v___y_6644_);
                lean_ctor_set(v___x_6645_, 2, v___y_6641_);
                lean_ctor_set(v___x_6645_, 3, v___y_6642_);
                v___x_6646_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_6646_, 0, v___x_6645_);
                v___x_6647_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6647_, 0, v___x_6646_);
                return v___x_6647_;
            }
            88 => {
                if v___y_6654_ == 0 {
                    lean_dec(v___y_6649_);
                    lean_dec_ref(v_code_6077_);
                    v___y_6641_ = v___y_6650_;
                    v___y_6642_ = v___y_6651_;
                    v___y_6643_ = v___y_6652_;
                    v___y_6644_ = v___y_6653_;
                    state = 87;
                    continue;
                } else {
                    v___x_6655_ = l_Lean_instBEqFVarId_beq(v___y_6649_, v___y_6650_);
                    lean_dec(v___y_6649_);
                    if v___x_6655_ == 0 {
                        lean_dec_ref(v_code_6077_);
                        v___y_6641_ = v___y_6650_;
                        v___y_6642_ = v___y_6651_;
                        v___y_6643_ = v___y_6652_;
                        v___y_6644_ = v___y_6653_;
                        state = 87;
                        continue;
                    } else {
                        lean_dec_ref(v___y_6653_);
                        lean_dec(v___y_6652_);
                        lean_dec_ref(v___y_6651_);
                        lean_dec(v___y_6650_);
                        v___x_6656_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6656_, 0, v_code_6077_);
                        return v___x_6656_;
                    }
                }
            }
            89 => {
                v___x_6671_ = lean_array_get_size(v___y_6660_);
                v___x_6672_ = lean_nat_dec_lt(v___y_6665_, v___x_6671_);
                if v___x_6672_ == 0 {
                    lean_dec_ref(v___y_6664_);
                    lean_dec(v___y_6662_);
                    lean_dec_ref(v___y_6661_);
                    lean_dec(v___y_6659_);
                    lean_dec(v___y_6658_);
                    lean_dec_ref(v_code_6077_);
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
                        lean_dec_ref(v___y_6664_);
                        lean_dec(v___y_6662_);
                        lean_dec_ref(v___y_6661_);
                        lean_dec(v___y_6659_);
                        lean_dec(v___y_6658_);
                        lean_dec_ref(v_code_6077_);
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
                            lean_dec_ref(v___y_6664_);
                            lean_dec(v___y_6662_);
                            lean_dec_ref(v___y_6661_);
                            lean_dec(v___y_6659_);
                            lean_dec(v___y_6658_);
                            lean_dec_ref(v_code_6077_);
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
                            lean_dec_ref(v___y_6669_);
                            lean_dec(v___y_6665_);
                            lean_inc(v___y_6659_);
                            v___x_6676_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(
                                v___y_6659_,
                                v___y_6666_,
                            );
                            if lean_obj_tag(v___x_6676_) == 0 {
                                lean_dec_ref_known(v___x_6676_, 1);
                                v___x_6677_ = lean_ptr_addr(v___y_6664_);
                                lean_dec_ref(v___y_6664_);
                                v___x_6678_ = lean_ptr_addr(v___y_6660_);
                                v___x_6679_ = lean_usize_dec_eq(v___x_6677_, v___x_6678_);
                                if v___x_6679_ == 0 {
                                    lean_dec_ref(v___y_6661_);
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
                                    lean_dec_ref(v___y_6661_);
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
                                lean_dec_ref(v___y_6664_);
                                lean_dec_ref(v___y_6663_);
                                lean_dec(v___y_6662_);
                                lean_dec_ref(v___y_6661_);
                                lean_dec_ref(v___y_6660_);
                                lean_dec(v___y_6659_);
                                lean_dec(v___y_6658_);
                                lean_dec_ref(v_code_6077_);
                                v_a_6683_ = lean_ctor_get(v___x_6676_, 0);
                                v_isSharedCheck_6690_ = (!lean_is_exclusive(v___x_6676_)) as u8;
                                if v_isSharedCheck_6690_ == 0 {
                                    v___x_6685_ = v___x_6676_;
                                    v_isShared_6686_ = v_isSharedCheck_6690_;
                                    state = 90;
                                    continue;
                                } else {
                                    lean_inc(v_a_6683_);
                                    lean_dec(v___x_6676_);
                                    v___x_6685_ = lean_box(0);
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
                    v_reuseFailAlloc_6689_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6689_, 0, v_a_6683_);
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
                if lean_obj_tag(v___x_6694_) == 0 {
                    v_isSharedCheck_6701_ = (!lean_is_exclusive(v___x_6694_)) as u8;
                    if v_isSharedCheck_6701_ == 0 {
                        v_unused_6702_ = lean_ctor_get(v___x_6694_, 0);
                        lean_dec(v_unused_6702_);
                        v___x_6696_ = v___x_6694_;
                        v_isShared_6697_ = v_isSharedCheck_6701_;
                        state = 93;
                        continue;
                    } else {
                        lean_dec(v___x_6694_);
                        v___x_6696_ = lean_box(0);
                        v_isShared_6697_ = v_isSharedCheck_6701_;
                        state = 93;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_6693_);
                    v_a_6703_ = lean_ctor_get(v___x_6694_, 0);
                    v_isSharedCheck_6710_ = (!lean_is_exclusive(v___x_6694_)) as u8;
                    if v_isSharedCheck_6710_ == 0 {
                        v___x_6705_ = v___x_6694_;
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 95;
                        continue;
                    } else {
                        lean_inc(v_a_6703_);
                        lean_dec(v___x_6694_);
                        v___x_6705_ = lean_box(0);
                        v_isShared_6706_ = v_isSharedCheck_6710_;
                        state = 95;
                        continue;
                    }
                }
            }
            93 => {
                if v_isShared_6697_ == 0 {
                    lean_ctor_set(v___x_6696_, 0, v___y_6693_);
                    v___x_6699_ = v___x_6696_;
                    state = 94;
                    continue;
                } else {
                    v_reuseFailAlloc_6700_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6700_, 0, v___y_6693_);
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
                    v_reuseFailAlloc_6709_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6709_, 0, v_a_6703_);
                    v___x_6708_ = v_reuseFailAlloc_6709_;
                    state = 96;
                    continue;
                }
            }
            96 => {
                return v___x_6708_;
            }
            97 => {
                if lean_obj_tag(v___y_6714_) == 0 {
                    lean_dec_ref_known(v___y_6714_, 1);
                    v___y_6692_ = v___y_6712_;
                    v___y_6693_ = v___y_6713_;
                    state = 92;
                    continue;
                } else {
                    lean_dec_ref(v___y_6713_);
                    v_a_6715_ = lean_ctor_get(v___y_6714_, 0);
                    v_isSharedCheck_6722_ = (!lean_is_exclusive(v___y_6714_)) as u8;
                    if v_isSharedCheck_6722_ == 0 {
                        v___x_6717_ = v___y_6714_;
                        v_isShared_6718_ = v_isSharedCheck_6722_;
                        state = 98;
                        continue;
                    } else {
                        lean_inc(v_a_6715_);
                        lean_dec(v___y_6714_);
                        v___x_6717_ = lean_box(0);
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
                    v_reuseFailAlloc_6721_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6721_, 0, v_a_6715_);
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
                lean_dec(v___y_6729_);
                if v___x_6730_ == 0 {
                    lean_dec_ref(v___y_6726_);
                    lean_dec(v___y_6725_);
                    v___y_6692_ = v___y_6724_;
                    v___y_6693_ = v___y_6727_;
                    state = 92;
                    continue;
                } else {
                    v___x_6731_ = lean_box(0);
                    v___x_6732_ = lean_nat_dec_le(v___y_6725_, v___y_6725_);
                    if v___x_6732_ == 0 {
                        if v___x_6730_ == 0 {
                            lean_dec_ref(v___y_6726_);
                            lean_dec(v___y_6725_);
                            v___y_6692_ = v___y_6724_;
                            v___y_6693_ = v___y_6727_;
                            state = 92;
                            continue;
                        } else {
                            v___x_6733_ = 0usize;
                            v___x_6734_ = lean_usize_of_nat(v___y_6725_);
                            lean_dec(v___y_6725_);
                            v___x_6735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_6726_, v___x_6733_, v___x_6734_, v___x_6731_, v___y_6728_);
                            lean_dec_ref(v___y_6726_);
                            v___y_6712_ = v___y_6724_;
                            v___y_6713_ = v___y_6727_;
                            v___y_6714_ = v___x_6735_;
                            state = 97;
                            continue;
                        }
                    } else {
                        v___x_6736_ = 0usize;
                        v___x_6737_ = lean_usize_of_nat(v___y_6725_);
                        lean_dec(v___y_6725_);
                        v___x_6738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v___y_6726_, v___x_6736_, v___x_6737_, v___x_6731_, v___y_6728_);
                        lean_dec_ref(v___y_6726_);
                        v___y_6712_ = v___y_6724_;
                        v___y_6713_ = v___y_6727_;
                        v___y_6714_ = v___x_6738_;
                        state = 97;
                        continue;
                    }
                }
            }
            101 => match lean_obj_tag(v_code_6077_) {
                0 => {
                    v_decl_6747_ = lean_ctor_get(v_code_6077_, 0);
                    v_k_6748_ = lean_ctor_get(v_code_6077_, 1);
                    v___x_6749_ = 0;
                    v___x_6750_ = 0;
                    lean_inc_ref(v_decl_6747_);
                    v___x_6751_ = l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4___redArg(v___x_6749_, v___x_6750_, v_decl_6747_, v___y_6741_, v___y_6744_);
                    if lean_obj_tag(v___x_6751_) == 0 {
                        v_a_6752_ = lean_ctor_get(v___x_6751_, 0);
                        lean_inc(v_a_6752_);
                        lean_dec_ref_known(v___x_6751_, 1);
                        v___x_6753_ = l_Lean_Compiler_LCNF_instBEqLetDecl_beq(
                            v___x_6749_,
                            v_decl_6747_,
                            v_a_6752_,
                        );
                        if v___x_6753_ == 0 {
                            v___x_6754_ =
                                l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(v___y_6741_);
                            if lean_obj_tag(v___x_6754_) == 0 {
                                lean_dec_ref_known(v___x_6754_, 1);
                                lean_inc_ref(v_k_6748_);
                                lean_inc_ref(v_decl_6747_);
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
                                lean_dec(v_a_6752_);
                                lean_dec_ref_known(v_code_6077_, 2);
                                lean_dec_ref(v___y_6745_);
                                v_a_6755_ = lean_ctor_get(v___x_6754_, 0);
                                v_isSharedCheck_6762_ = (!lean_is_exclusive(v___x_6754_)) as u8;
                                if v_isSharedCheck_6762_ == 0 {
                                    v___x_6757_ = v___x_6754_;
                                    v_isShared_6758_ = v_isSharedCheck_6762_;
                                    state = 102;
                                    continue;
                                } else {
                                    lean_inc(v_a_6755_);
                                    lean_dec(v___x_6754_);
                                    v___x_6757_ = lean_box(0);
                                    v_isShared_6758_ = v_isSharedCheck_6762_;
                                    state = 102;
                                    continue;
                                }
                            }
                        } else {
                            lean_inc_ref(v_k_6748_);
                            lean_inc_ref(v_decl_6747_);
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
                        lean_dec_ref_known(v_code_6077_, 2);
                        lean_dec_ref(v___y_6745_);
                        v_a_6763_ = lean_ctor_get(v___x_6751_, 0);
                        v_isSharedCheck_6770_ = (!lean_is_exclusive(v___x_6751_)) as u8;
                        if v_isSharedCheck_6770_ == 0 {
                            v___x_6765_ = v___x_6751_;
                            v_isShared_6766_ = v_isSharedCheck_6770_;
                            state = 104;
                            continue;
                        } else {
                            lean_inc(v_a_6763_);
                            lean_dec(v___x_6751_);
                            v___x_6765_ = lean_box(0);
                            v_isShared_6766_ = v_isSharedCheck_6770_;
                            state = 104;
                            continue;
                        }
                    }
                }
                3 => {
                    v_fvarId_6771_ = lean_ctor_get(v_code_6077_, 0);
                    v_args_6772_ = lean_ctor_get(v_code_6077_, 1);
                    v___x_6773_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6774_ = lean_ctor_get(v___x_6773_, 0);
                    lean_inc_ref(v_subst_6774_);
                    lean_dec(v___x_6773_);
                    v___x_6775_ = 0;
                    v___x_6776_ = 0;
                    lean_inc(v_fvarId_6771_);
                    v___x_6777_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_subst_6774_,
                        v_fvarId_6771_,
                        v___x_6776_,
                    );
                    lean_dec_ref(v_subst_6774_);
                    if lean_obj_tag(v___x_6777_) == 0 {
                        v_fvarId_6778_ = lean_ctor_get(v___x_6777_, 0);
                        lean_inc(v_fvarId_6778_);
                        lean_dec_ref_known(v___x_6777_, 1);
                        lean_inc_ref(v_args_6772_);
                        v___x_6779_ = l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5___redArg(v___x_6775_, v___x_6776_, v_args_6772_, v___y_6741_);
                        if lean_obj_tag(v___x_6779_) == 0 {
                            v_a_6780_ = lean_ctor_get(v___x_6779_, 0);
                            lean_inc_n(v_a_6780_, 2);
                            lean_dec_ref_known(v___x_6779_, 1);
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
                            if lean_obj_tag(v___x_6781_) == 0 {
                                v_a_6782_ = lean_ctor_get(v___x_6781_, 0);
                                lean_inc(v_a_6782_);
                                lean_dec_ref_known(v___x_6781_, 1);
                                if lean_obj_tag(v_a_6782_) == 1 {
                                    lean_dec(v_a_6780_);
                                    lean_dec(v_fvarId_6778_);
                                    lean_dec_ref_known(v_code_6077_, 2);
                                    v_val_6783_ = lean_ctor_get(v_a_6782_, 0);
                                    lean_inc(v_val_6783_);
                                    lean_dec_ref_known(v_a_6782_, 1);
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
                                    lean_dec(v_a_6782_);
                                    lean_dec_ref(v___y_6745_);
                                    lean_inc(v_fvarId_6778_);
                                    v___x_6785_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(
                                        v_fvarId_6778_,
                                        v___y_6741_,
                                    );
                                    if lean_obj_tag(v___x_6785_) == 0 {
                                        lean_dec_ref_known(v___x_6785_, 1);
                                        v___x_6786_ = lean_unsigned_to_nat(0);
                                        v___x_6787_ = lean_array_get_size(v_a_6780_);
                                        v___x_6788_ = lean_nat_dec_lt(v___x_6786_, v___x_6787_);
                                        if v___x_6788_ == 0 {
                                            lean_inc_ref(v_args_6772_);
                                            lean_inc(v_fvarId_6771_);
                                            v___y_6566_ = v_fvarId_6771_;
                                            v___y_6567_ = v_args_6772_;
                                            v___y_6568_ = v_fvarId_6778_;
                                            v___y_6569_ = v_a_6780_;
                                            state = 74;
                                            continue;
                                        } else {
                                            v___x_6789_ = lean_box(0);
                                            v___x_6790_ = lean_nat_dec_le(v___x_6787_, v___x_6787_);
                                            if v___x_6790_ == 0 {
                                                if v___x_6788_ == 0 {
                                                    lean_inc_ref(v_args_6772_);
                                                    lean_inc(v_fvarId_6771_);
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
                                                    lean_inc_ref(v_args_6772_);
                                                    lean_inc(v_fvarId_6771_);
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
                                                lean_inc_ref(v_args_6772_);
                                                lean_inc(v_fvarId_6771_);
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
                                        lean_dec(v_a_6780_);
                                        lean_dec(v_fvarId_6778_);
                                        lean_dec_ref_known(v_code_6077_, 2);
                                        v_a_6797_ = lean_ctor_get(v___x_6785_, 0);
                                        v_isSharedCheck_6804_ =
                                            (!lean_is_exclusive(v___x_6785_)) as u8;
                                        if v_isSharedCheck_6804_ == 0 {
                                            v___x_6799_ = v___x_6785_;
                                            v_isShared_6800_ = v_isSharedCheck_6804_;
                                            state = 106;
                                            continue;
                                        } else {
                                            lean_inc(v_a_6797_);
                                            lean_dec(v___x_6785_);
                                            v___x_6799_ = lean_box(0);
                                            v_isShared_6800_ = v_isSharedCheck_6804_;
                                            state = 106;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_a_6780_);
                                lean_dec(v_fvarId_6778_);
                                lean_dec_ref_known(v_code_6077_, 2);
                                lean_dec_ref(v___y_6745_);
                                v_a_6805_ = lean_ctor_get(v___x_6781_, 0);
                                v_isSharedCheck_6812_ = (!lean_is_exclusive(v___x_6781_)) as u8;
                                if v_isSharedCheck_6812_ == 0 {
                                    v___x_6807_ = v___x_6781_;
                                    v_isShared_6808_ = v_isSharedCheck_6812_;
                                    state = 108;
                                    continue;
                                } else {
                                    lean_inc(v_a_6805_);
                                    lean_dec(v___x_6781_);
                                    v___x_6807_ = lean_box(0);
                                    v_isShared_6808_ = v_isSharedCheck_6812_;
                                    state = 108;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_fvarId_6778_);
                            lean_dec_ref_known(v_code_6077_, 2);
                            lean_dec_ref(v___y_6745_);
                            v_a_6813_ = lean_ctor_get(v___x_6779_, 0);
                            v_isSharedCheck_6820_ = (!lean_is_exclusive(v___x_6779_)) as u8;
                            if v_isSharedCheck_6820_ == 0 {
                                v___x_6815_ = v___x_6779_;
                                v_isShared_6816_ = v_isSharedCheck_6820_;
                                state = 110;
                                continue;
                            } else {
                                lean_inc(v_a_6813_);
                                lean_dec(v___x_6779_);
                                v___x_6815_ = lean_box(0);
                                v_isShared_6816_ = v_isSharedCheck_6820_;
                                state = 110;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_6077_, 2);
                        v___x_6821_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v___x_6775_,
                            v___y_6743_,
                            v___y_6744_,
                            v___y_6745_,
                            v___y_6746_,
                        );
                        lean_dec_ref(v___y_6745_);
                        return v___x_6821_;
                    }
                }
                4 => {
                    v_cases_6822_ = lean_ctor_get(v_code_6077_, 0);
                    lean_inc_ref(v_cases_6822_);
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
                    if lean_obj_tag(v___x_6823_) == 0 {
                        v_a_6824_ = lean_ctor_get(v___x_6823_, 0);
                        v_isSharedCheck_6896_ = (!lean_is_exclusive(v___x_6823_)) as u8;
                        if v_isSharedCheck_6896_ == 0 {
                            v___x_6826_ = v___x_6823_;
                            v_isShared_6827_ = v_isSharedCheck_6896_;
                            state = 112;
                            continue;
                        } else {
                            lean_inc(v_a_6824_);
                            lean_dec(v___x_6823_);
                            v___x_6826_ = lean_box(0);
                            v_isShared_6827_ = v_isSharedCheck_6896_;
                            state = 112;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_6077_, 1);
                        lean_dec_ref(v___y_6745_);
                        v_a_6897_ = lean_ctor_get(v___x_6823_, 0);
                        v_isSharedCheck_6904_ = (!lean_is_exclusive(v___x_6823_)) as u8;
                        if v_isSharedCheck_6904_ == 0 {
                            v___x_6899_ = v___x_6823_;
                            v_isShared_6900_ = v_isSharedCheck_6904_;
                            state = 122;
                            continue;
                        } else {
                            lean_inc(v_a_6897_);
                            lean_dec(v___x_6823_);
                            v___x_6899_ = lean_box(0);
                            v_isShared_6900_ = v_isSharedCheck_6904_;
                            state = 122;
                            continue;
                        }
                    }
                }
                5 => {
                    v_fvarId_6905_ = lean_ctor_get(v_code_6077_, 0);
                    v___x_6906_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6907_ = lean_ctor_get(v___x_6906_, 0);
                    lean_inc_ref(v_subst_6907_);
                    lean_dec(v___x_6906_);
                    v___x_6908_ = 0;
                    lean_inc(v_fvarId_6905_);
                    v___x_6909_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_subst_6907_,
                        v_fvarId_6905_,
                        v___x_6908_,
                    );
                    lean_dec_ref(v_subst_6907_);
                    if lean_obj_tag(v___x_6909_) == 0 {
                        lean_dec_ref(v___y_6745_);
                        v_fvarId_6910_ = lean_ctor_get(v___x_6909_, 0);
                        lean_inc_n(v_fvarId_6910_, 2);
                        lean_dec_ref_known(v___x_6909_, 1);
                        v___x_6911_ = l_Lean_Compiler_LCNF_Simp_markUsedFVar___redArg(
                            v_fvarId_6910_,
                            v___y_6741_,
                        );
                        if lean_obj_tag(v___x_6911_) == 0 {
                            v_isSharedCheck_6930_ = (!lean_is_exclusive(v___x_6911_)) as u8;
                            if v_isSharedCheck_6930_ == 0 {
                                v_unused_6931_ = lean_ctor_get(v___x_6911_, 0);
                                lean_dec(v_unused_6931_);
                                v___x_6913_ = v___x_6911_;
                                v_isShared_6914_ = v_isSharedCheck_6930_;
                                state = 124;
                                continue;
                            } else {
                                lean_dec(v___x_6911_);
                                v___x_6913_ = lean_box(0);
                                v_isShared_6914_ = v_isSharedCheck_6930_;
                                state = 124;
                                continue;
                            }
                        } else {
                            lean_dec(v_fvarId_6910_);
                            lean_dec_ref_known(v_code_6077_, 1);
                            v_a_6932_ = lean_ctor_get(v___x_6911_, 0);
                            v_isSharedCheck_6939_ = (!lean_is_exclusive(v___x_6911_)) as u8;
                            if v_isSharedCheck_6939_ == 0 {
                                v___x_6934_ = v___x_6911_;
                                v_isShared_6935_ = v_isSharedCheck_6939_;
                                state = 129;
                                continue;
                            } else {
                                lean_inc(v_a_6932_);
                                lean_dec(v___x_6911_);
                                v___x_6934_ = lean_box(0);
                                v_isShared_6935_ = v_isSharedCheck_6939_;
                                state = 129;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_6077_, 1);
                        v___x_6940_ = 0;
                        v___x_6941_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v___x_6940_,
                            v___y_6743_,
                            v___y_6744_,
                            v___y_6745_,
                            v___y_6746_,
                        );
                        lean_dec_ref(v___y_6745_);
                        return v___x_6941_;
                    }
                }
                6 => {
                    lean_dec_ref(v___y_6745_);
                    v_type_6942_ = lean_ctor_get(v_code_6077_, 0);
                    v___x_6943_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6944_ = lean_ctor_get(v___x_6943_, 0);
                    lean_inc_ref(v_subst_6944_);
                    lean_dec(v___x_6943_);
                    v___x_6945_ = 0;
                    v___x_6946_ = 0;
                    lean_inc_ref(v_type_6942_);
                    v___x_6947_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(v___x_6945_, v_subst_6944_, v___x_6946_, v_type_6942_);
                    lean_dec_ref(v_subst_6944_);
                    v___x_6948_ = lean_ptr_addr(v_type_6942_);
                    v___x_6949_ = lean_ptr_addr(v___x_6947_);
                    v___x_6950_ = lean_usize_dec_eq(v___x_6948_, v___x_6949_);
                    if v___x_6950_ == 0 {
                        v_isSharedCheck_6958_ = (!lean_is_exclusive(v_code_6077_)) as u8;
                        if v_isSharedCheck_6958_ == 0 {
                            v_unused_6959_ = lean_ctor_get(v_code_6077_, 0);
                            lean_dec(v_unused_6959_);
                            v___x_6952_ = v_code_6077_;
                            v_isShared_6953_ = v_isSharedCheck_6958_;
                            state = 131;
                            continue;
                        } else {
                            lean_dec(v_code_6077_);
                            v___x_6952_ = lean_box(0);
                            v_isShared_6953_ = v_isSharedCheck_6958_;
                            state = 131;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v___x_6947_);
                        v___x_6960_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_6960_, 0, v_code_6077_);
                        return v___x_6960_;
                    }
                }
                _ => {
                    v_decl_6961_ = lean_ctor_get(v_code_6077_, 0);
                    v_k_6962_ = lean_ctor_get(v_code_6077_, 1);
                    lean_inc_ref(v_k_6962_);
                    lean_inc_ref(v_decl_6961_);
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
                    v_reuseFailAlloc_6761_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6761_, 0, v_a_6755_);
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
                    v_reuseFailAlloc_6769_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6769_, 0, v_a_6763_);
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
                    v_reuseFailAlloc_6803_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6803_, 0, v_a_6797_);
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
                    v_reuseFailAlloc_6811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6811_, 0, v_a_6805_);
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
                    v_reuseFailAlloc_6819_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6819_, 0, v_a_6813_);
                    v___x_6818_ = v_reuseFailAlloc_6819_;
                    state = 111;
                    continue;
                }
            }
            111 => {
                return v___x_6818_;
            }
            112 => {
                if lean_obj_tag(v_a_6824_) == 1 {
                    lean_dec_ref_known(v_code_6077_, 1);
                    lean_dec_ref(v___y_6745_);
                    v_val_6828_ = lean_ctor_get(v_a_6824_, 0);
                    lean_inc(v_val_6828_);
                    lean_dec_ref_known(v_a_6824_, 1);
                    if v_isShared_6827_ == 0 {
                        lean_ctor_set(v___x_6826_, 0, v_val_6828_);
                        v___x_6830_ = v___x_6826_;
                        state = 113;
                        continue;
                    } else {
                        v_reuseFailAlloc_6831_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6831_, 0, v_val_6828_);
                        v___x_6830_ = v_reuseFailAlloc_6831_;
                        state = 113;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6826_);
                    lean_dec(v_a_6824_);
                    v_typeName_6832_ = lean_ctor_get(v_cases_6822_, 0);
                    v_resultType_6833_ = lean_ctor_get(v_cases_6822_, 1);
                    v_discr_6834_ = lean_ctor_get(v_cases_6822_, 2);
                    v_alts_6835_ = lean_ctor_get(v_cases_6822_, 3);
                    v___x_6836_ = lean_st_ref_get(v___y_6741_);
                    v_subst_6837_ = lean_ctor_get(v___x_6836_, 0);
                    lean_inc_ref(v_subst_6837_);
                    lean_dec(v___x_6836_);
                    v___x_6838_ = 0;
                    v___x_6839_ = 0;
                    lean_inc(v_discr_6834_);
                    v___x_6840_ = l_Lean_Compiler_LCNF_normFVarImp___redArg(
                        v_subst_6837_,
                        v_discr_6834_,
                        v___x_6839_,
                    );
                    lean_dec_ref(v_subst_6837_);
                    if lean_obj_tag(v___x_6840_) == 0 {
                        v_fvarId_6841_ = lean_ctor_get(v___x_6840_, 0);
                        lean_inc_n(v_fvarId_6841_, 2);
                        lean_dec_ref_known(v___x_6840_, 1);
                        v___x_6842_ = lean_st_ref_get(v___y_6741_);
                        v___x_6843_ = lean_unsigned_to_nat(0);
                        lean_inc_ref(v_alts_6835_);
                        v___x_6844_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_6841_, v___x_6843_, v_alts_6835_, v___y_6740_, v___y_6741_, v___y_6742_, v___y_6743_, v___y_6744_, v___y_6745_, v___y_6746_);
                        if lean_obj_tag(v___x_6844_) == 0 {
                            v_a_6845_ = lean_ctor_get(v___x_6844_, 0);
                            lean_inc(v_a_6845_);
                            lean_dec_ref_known(v___x_6844_, 1);
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
                            if lean_obj_tag(v___x_6846_) == 0 {
                                v_a_6847_ = lean_ctor_get(v___x_6846_, 0);
                                v_isSharedCheck_6878_ = (!lean_is_exclusive(v___x_6846_)) as u8;
                                if v_isSharedCheck_6878_ == 0 {
                                    v___x_6849_ = v___x_6846_;
                                    v_isShared_6850_ = v_isSharedCheck_6878_;
                                    state = 114;
                                    continue;
                                } else {
                                    lean_inc(v_a_6847_);
                                    lean_dec(v___x_6846_);
                                    v___x_6849_ = lean_box(0);
                                    v_isShared_6850_ = v_isSharedCheck_6878_;
                                    state = 114;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_6842_);
                                lean_dec(v_fvarId_6841_);
                                lean_dec_ref_known(v_code_6077_, 1);
                                lean_dec_ref(v___y_6745_);
                                v_a_6879_ = lean_ctor_get(v___x_6846_, 0);
                                v_isSharedCheck_6886_ = (!lean_is_exclusive(v___x_6846_)) as u8;
                                if v_isSharedCheck_6886_ == 0 {
                                    v___x_6881_ = v___x_6846_;
                                    v_isShared_6882_ = v_isSharedCheck_6886_;
                                    state = 118;
                                    continue;
                                } else {
                                    lean_inc(v_a_6879_);
                                    lean_dec(v___x_6846_);
                                    v___x_6881_ = lean_box(0);
                                    v_isShared_6882_ = v_isSharedCheck_6886_;
                                    state = 118;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_6842_);
                            lean_dec(v_fvarId_6841_);
                            lean_dec_ref_known(v_code_6077_, 1);
                            lean_dec_ref(v___y_6745_);
                            v_a_6887_ = lean_ctor_get(v___x_6844_, 0);
                            v_isSharedCheck_6894_ = (!lean_is_exclusive(v___x_6844_)) as u8;
                            if v_isSharedCheck_6894_ == 0 {
                                v___x_6889_ = v___x_6844_;
                                v_isShared_6890_ = v_isSharedCheck_6894_;
                                state = 120;
                                continue;
                            } else {
                                lean_inc(v_a_6887_);
                                lean_dec(v___x_6844_);
                                v___x_6889_ = lean_box(0);
                                v_isShared_6890_ = v_isSharedCheck_6894_;
                                state = 120;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_6077_, 1);
                        v___x_6895_ = l_Lean_Compiler_LCNF_mkReturnErased(
                            v___x_6838_,
                            v___y_6743_,
                            v___y_6744_,
                            v___y_6745_,
                            v___y_6746_,
                        );
                        lean_dec_ref(v___y_6745_);
                        return v___x_6895_;
                    }
                }
            }
            113 => {
                return v___x_6830_;
            }
            114 => {
                v_subst_6851_ = lean_ctor_get(v___x_6842_, 0);
                lean_inc_ref(v_subst_6851_);
                lean_dec(v___x_6842_);
                lean_inc_ref(v_resultType_6833_);
                v___x_6852_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v___x_6838_,
                        v_subst_6851_,
                        v___x_6839_,
                        v_resultType_6833_,
                    );
                lean_dec_ref(v_subst_6851_);
                v___x_6853_ = lean_array_get_size(v_a_6847_);
                v___x_6854_ = lean_unsigned_to_nat(1);
                v___x_6855_ = lean_nat_dec_eq(v___x_6853_, v___x_6854_);
                if v___x_6855_ == 0 {
                    lean_del_object(v___x_6849_);
                    lean_inc_ref(v_alts_6835_);
                    lean_inc(v_typeName_6832_);
                    lean_inc_ref(v_resultType_6833_);
                    lean_inc(v_discr_6834_);
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
                    if lean_obj_tag(v___x_6856_) == 0 {
                        lean_del_object(v___x_6849_);
                        v_params_6857_ = lean_ctor_get(v___x_6856_, 1);
                        v_code_6858_ = lean_ctor_get(v___x_6856_, 2);
                        v___x_6859_ = lean_array_get_size(v_params_6857_);
                        v___x_6860_ = lean_nat_dec_lt(v___x_6843_, v___x_6859_);
                        if v___x_6860_ == 0 {
                            lean_inc_ref(v_code_6858_);
                            lean_inc_ref(v_params_6857_);
                            lean_dec_ref(v___x_6852_);
                            lean_dec(v_a_6847_);
                            lean_dec(v_fvarId_6841_);
                            lean_dec_ref_known(v_code_6077_, 1);
                            lean_dec_ref(v___y_6745_);
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
                                lean_inc_ref(v_code_6858_);
                                lean_inc_ref(v_params_6857_);
                                lean_dec_ref(v___x_6852_);
                                lean_dec(v_a_6847_);
                                lean_dec(v_fvarId_6841_);
                                lean_dec_ref_known(v_code_6077_, 1);
                                lean_dec_ref(v___y_6745_);
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
                                if lean_obj_tag(v___x_6863_) == 0 {
                                    v_a_6864_ = lean_ctor_get(v___x_6863_, 0);
                                    lean_inc(v_a_6864_);
                                    lean_dec_ref_known(v___x_6863_, 1);
                                    v___x_6865_ = (lean_unbox(v_a_6864_) as u8);
                                    lean_dec(v_a_6864_);
                                    if v___x_6865_ == 0 {
                                        lean_inc_ref(v_code_6858_);
                                        lean_inc_ref(v_params_6857_);
                                        lean_dec_ref(v___x_6852_);
                                        lean_dec(v_a_6847_);
                                        lean_dec(v_fvarId_6841_);
                                        lean_dec_ref_known(v_code_6077_, 1);
                                        lean_dec_ref(v___y_6745_);
                                        v___y_6724_ = v___y_6741_;
                                        v___y_6725_ = v___x_6859_;
                                        v___y_6726_ = v_params_6857_;
                                        v___y_6727_ = v_code_6858_;
                                        v___y_6728_ = v___y_6744_;
                                        v___y_6729_ = v___x_6843_;
                                        state = 100;
                                        continue;
                                    } else {
                                        lean_inc_ref(v_alts_6835_);
                                        lean_inc(v_typeName_6832_);
                                        lean_inc_ref(v_resultType_6833_);
                                        lean_inc(v_discr_6834_);
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
                                    lean_dec_ref(v___x_6852_);
                                    lean_dec(v_a_6847_);
                                    lean_dec(v_fvarId_6841_);
                                    lean_dec_ref_known(v_code_6077_, 1);
                                    lean_dec_ref(v___y_6745_);
                                    v_a_6866_ = lean_ctor_get(v___x_6863_, 0);
                                    v_isSharedCheck_6873_ = (!lean_is_exclusive(v___x_6863_)) as u8;
                                    if v_isSharedCheck_6873_ == 0 {
                                        v___x_6868_ = v___x_6863_;
                                        v_isShared_6869_ = v_isSharedCheck_6873_;
                                        state = 115;
                                        continue;
                                    } else {
                                        lean_inc(v_a_6866_);
                                        lean_dec(v___x_6863_);
                                        v___x_6868_ = lean_box(0);
                                        v_isShared_6869_ = v_isSharedCheck_6873_;
                                        state = 115;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        lean_inc_ref(v___x_6856_);
                        lean_dec_ref(v___x_6852_);
                        lean_dec(v_a_6847_);
                        lean_dec(v_fvarId_6841_);
                        lean_dec_ref_known(v_code_6077_, 1);
                        lean_dec_ref(v___y_6745_);
                        v_code_6874_ = lean_ctor_get(v___x_6856_, 0);
                        lean_inc_ref(v_code_6874_);
                        lean_dec_ref_known(v___x_6856_, 1);
                        if v_isShared_6850_ == 0 {
                            lean_ctor_set(v___x_6849_, 0, v_code_6874_);
                            v___x_6876_ = v___x_6849_;
                            state = 117;
                            continue;
                        } else {
                            v_reuseFailAlloc_6877_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_6877_, 0, v_code_6874_);
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
                    v_reuseFailAlloc_6872_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6872_, 0, v_a_6866_);
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
                    v_reuseFailAlloc_6885_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6885_, 0, v_a_6879_);
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
                    v_reuseFailAlloc_6893_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6893_, 0, v_a_6887_);
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
                    v_reuseFailAlloc_6903_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6903_, 0, v_a_6897_);
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
                    v_isSharedCheck_6925_ = (!lean_is_exclusive(v_code_6077_)) as u8;
                    if v_isSharedCheck_6925_ == 0 {
                        v_unused_6926_ = lean_ctor_get(v_code_6077_, 0);
                        lean_dec(v_unused_6926_);
                        v___x_6917_ = v_code_6077_;
                        v_isShared_6918_ = v_isSharedCheck_6925_;
                        state = 125;
                        continue;
                    } else {
                        lean_dec(v_code_6077_);
                        v___x_6917_ = lean_box(0);
                        v_isShared_6918_ = v_isSharedCheck_6925_;
                        state = 125;
                        continue;
                    }
                } else {
                    lean_dec(v_fvarId_6910_);
                    if v_isShared_6914_ == 0 {
                        lean_ctor_set(v___x_6913_, 0, v_code_6077_);
                        v___x_6928_ = v___x_6913_;
                        state = 128;
                        continue;
                    } else {
                        v_reuseFailAlloc_6929_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6929_, 0, v_code_6077_);
                        v___x_6928_ = v_reuseFailAlloc_6929_;
                        state = 128;
                        continue;
                    }
                }
            }
            125 => {
                if v_isShared_6918_ == 0 {
                    lean_ctor_set(v___x_6917_, 0, v_fvarId_6910_);
                    v___x_6920_ = v___x_6917_;
                    state = 126;
                    continue;
                } else {
                    v_reuseFailAlloc_6924_ = lean_alloc_ctor(5, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6924_, 0, v_fvarId_6910_);
                    v___x_6920_ = v_reuseFailAlloc_6924_;
                    state = 126;
                    continue;
                }
            }
            126 => {
                if v_isShared_6914_ == 0 {
                    lean_ctor_set(v___x_6913_, 0, v___x_6920_);
                    v___x_6922_ = v___x_6913_;
                    state = 127;
                    continue;
                } else {
                    v_reuseFailAlloc_6923_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6923_, 0, v___x_6920_);
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
                    v_reuseFailAlloc_6938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6938_, 0, v_a_6932_);
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
                    lean_ctor_set(v___x_6952_, 0, v___x_6947_);
                    v___x_6955_ = v___x_6952_;
                    state = 132;
                    continue;
                } else {
                    v_reuseFailAlloc_6957_ = lean_alloc_ctor(6, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6957_, 0, v___x_6947_);
                    v___x_6955_ = v_reuseFailAlloc_6957_;
                    state = 132;
                    continue;
                }
            }
            132 => {
                v___x_6956_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6956_, 0, v___x_6955_);
                return v___x_6956_;
            }
            133 => {
                v___x_6980_ = l_Lean_Compiler_LCNF_Simp_incVisited___redArg(v_a_6079_);
                if lean_obj_tag(v___x_6980_) == 0 {
                    lean_dec_ref_known(v___x_6980_, 1);
                    v___x_6981_ = lean_st_ref_get(v_a_6079_);
                    v_visited_6982_ = lean_ctor_get(v___x_6981_, 4);
                    lean_inc(v_visited_6982_);
                    lean_dec(v___x_6981_);
                    v___x_6983_ = lean_unsigned_to_nat(1);
                    v___x_6984_ = lean_nat_add(v_currRecDepth_6966_, v___x_6983_);
                    lean_dec(v_currRecDepth_6966_);
                    v___x_6985_ = lean_alloc_ctor(0, 14, (2) as u32);
                    lean_ctor_set(v___x_6985_, 0, v_fileName_6963_);
                    lean_ctor_set(v___x_6985_, 1, v_fileMap_6964_);
                    lean_ctor_set(v___x_6985_, 2, v_options_6965_);
                    lean_ctor_set(v___x_6985_, 3, v___x_6984_);
                    lean_ctor_set(v___x_6985_, 4, v_maxRecDepth_6967_);
                    lean_ctor_set(v___x_6985_, 5, v_ref_6968_);
                    lean_ctor_set(v___x_6985_, 6, v_currNamespace_6969_);
                    lean_ctor_set(v___x_6985_, 7, v_openDecls_6970_);
                    lean_ctor_set(v___x_6985_, 8, v_initHeartbeats_6971_);
                    lean_ctor_set(v___x_6985_, 9, v_maxHeartbeats_6972_);
                    lean_ctor_set(v___x_6985_, 10, v_quotContext_6973_);
                    lean_ctor_set(v___x_6985_, 11, v_currMacroScope_6974_);
                    lean_ctor_set(v___x_6985_, 12, v_cancelTk_x3f_6976_);
                    lean_ctor_set(v___x_6985_, 13, v_inheritedTraceOptions_6978_);
                    lean_ctor_set_uint8(
                        v___x_6985_,
                        (core::mem::size_of::<*mut LeanObject>() * 14) as u32,
                        v_diag_6975_,
                    );
                    lean_ctor_set_uint8(
                        v___x_6985_,
                        (core::mem::size_of::<*mut LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_6977_,
                    );
                    v___x_6986_ = lean_unsigned_to_nat(128);
                    v___x_6987_ = lean_nat_mod(v_visited_6982_, v___x_6986_);
                    lean_dec(v_visited_6982_);
                    v___x_6988_ = lean_unsigned_to_nat(0);
                    v___x_6989_ = lean_nat_dec_eq(v___x_6987_, v___x_6988_);
                    lean_dec(v___x_6987_);
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
                        if lean_obj_tag(v___x_6991_) == 0 {
                            lean_dec_ref_known(v___x_6991_, 1);
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
                            lean_dec_ref_known(v___x_6985_, 14);
                            lean_dec_ref(v_code_6077_);
                            v_a_6992_ = lean_ctor_get(v___x_6991_, 0);
                            v_isSharedCheck_6999_ = (!lean_is_exclusive(v___x_6991_)) as u8;
                            if v_isSharedCheck_6999_ == 0 {
                                v___x_6994_ = v___x_6991_;
                                v_isShared_6995_ = v_isSharedCheck_6999_;
                                state = 134;
                                continue;
                            } else {
                                lean_inc(v_a_6992_);
                                lean_dec(v___x_6991_);
                                v___x_6994_ = lean_box(0);
                                v_isShared_6995_ = v_isSharedCheck_6999_;
                                state = 134;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_inheritedTraceOptions_6978_);
                    lean_dec(v_cancelTk_x3f_6976_);
                    lean_dec(v_currMacroScope_6974_);
                    lean_dec(v_quotContext_6973_);
                    lean_dec(v_maxHeartbeats_6972_);
                    lean_dec(v_initHeartbeats_6971_);
                    lean_dec(v_openDecls_6970_);
                    lean_dec(v_currNamespace_6969_);
                    lean_dec(v_ref_6968_);
                    lean_dec(v_maxRecDepth_6967_);
                    lean_dec(v_currRecDepth_6966_);
                    lean_dec_ref(v_options_6965_);
                    lean_dec_ref(v_fileMap_6964_);
                    lean_dec_ref(v_fileName_6963_);
                    lean_dec_ref(v_code_6077_);
                    v_a_7000_ = lean_ctor_get(v___x_6980_, 0);
                    v_isSharedCheck_7007_ = (!lean_is_exclusive(v___x_6980_)) as u8;
                    if v_isSharedCheck_7007_ == 0 {
                        v___x_7002_ = v___x_6980_;
                        v_isShared_7003_ = v_isSharedCheck_7007_;
                        state = 136;
                        continue;
                    } else {
                        lean_inc(v_a_7000_);
                        lean_dec(v___x_6980_);
                        v___x_7002_ = lean_box(0);
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
                    v_reuseFailAlloc_6998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6998_, 0, v_a_6992_);
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
                    v_reuseFailAlloc_7006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7006_, 0, v_a_7000_);
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
    mut v_decl_7012_: *mut LeanObject,
    mut v_a_7013_: *mut LeanObject,
    mut v_a_7014_: *mut LeanObject,
    mut v_a_7015_: *mut LeanObject,
    mut v_a_7016_: *mut LeanObject,
    mut v_a_7017_: *mut LeanObject,
    mut v_a_7018_: *mut LeanObject,
    mut v_a_7019_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_7021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_7022_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_7023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_subst_7025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7026_: u8 = 0;
    let mut v___x_7027_: u8 = 0;
    let mut v___x_7028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7037_: u8 = 0;
    let mut v___x_7039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7041_: u8 = 0;
    let mut v_a_7042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7045_: u8 = 0;
    let mut v___x_7047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7048_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7049_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_7021_ = lean_ctor_get(v_decl_7012_, 2);
                v_type_7022_ = lean_ctor_get(v_decl_7012_, 3);
                v_value_7023_ = lean_ctor_get(v_decl_7012_, 4);
                v___x_7024_ = lean_st_ref_get(v_a_7014_);
                v_subst_7025_ = lean_ctor_get(v___x_7024_, 0);
                lean_inc_ref(v_subst_7025_);
                lean_dec(v___x_7024_);
                v___x_7026_ = 0;
                v___x_7027_ = 0;
                lean_inc_ref(v_type_7022_);
                v___x_7028_ =
                    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(
                        v___x_7026_,
                        v_subst_7025_,
                        v___x_7027_,
                        v_type_7022_,
                    );
                lean_dec_ref(v_subst_7025_);
                lean_inc_ref(v_params_7021_);
                v___x_7029_ = l_Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17(v___x_7026_, v___x_7027_, v_params_7021_, v_a_7013_, v_a_7014_, v_a_7015_, v_a_7016_, v_a_7017_, v_a_7018_, v_a_7019_);
                if lean_obj_tag(v___x_7029_) == 0 {
                    v_a_7030_ = lean_ctor_get(v___x_7029_, 0);
                    lean_inc(v_a_7030_);
                    lean_dec_ref_known(v___x_7029_, 1);
                    lean_inc_ref(v_a_7018_);
                    lean_inc_ref(v_value_7023_);
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
                    if lean_obj_tag(v___x_7031_) == 0 {
                        v_a_7032_ = lean_ctor_get(v___x_7031_, 0);
                        lean_inc(v_a_7032_);
                        lean_dec_ref_known(v___x_7031_, 1);
                        v___x_7033_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_7026_, v_decl_7012_, v___x_7028_, v_a_7030_, v_a_7032_, v_a_7017_);
                        return v___x_7033_;
                    } else {
                        lean_dec(v_a_7030_);
                        lean_dec_ref(v___x_7028_);
                        lean_dec_ref(v_decl_7012_);
                        v_a_7034_ = lean_ctor_get(v___x_7031_, 0);
                        v_isSharedCheck_7041_ = (!lean_is_exclusive(v___x_7031_)) as u8;
                        if v_isSharedCheck_7041_ == 0 {
                            v___x_7036_ = v___x_7031_;
                            v_isShared_7037_ = v_isSharedCheck_7041_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_7034_);
                            lean_dec(v___x_7031_);
                            v___x_7036_ = lean_box(0);
                            v_isShared_7037_ = v_isSharedCheck_7041_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v___x_7028_);
                    lean_dec_ref(v_decl_7012_);
                    v_a_7042_ = lean_ctor_get(v___x_7029_, 0);
                    v_isSharedCheck_7049_ = (!lean_is_exclusive(v___x_7029_)) as u8;
                    if v_isSharedCheck_7049_ == 0 {
                        v___x_7044_ = v___x_7029_;
                        v_isShared_7045_ = v_isSharedCheck_7049_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_7042_);
                        lean_dec(v___x_7029_);
                        v___x_7044_ = lean_box(0);
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
                    v_reuseFailAlloc_7040_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7040_, 0, v_a_7034_);
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
                    v_reuseFailAlloc_7048_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7048_, 0, v_a_7042_);
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
    mut v_decl_7050_: *mut LeanObject,
    mut v_a_7051_: *mut LeanObject,
    mut v_a_7052_: *mut LeanObject,
    mut v_a_7053_: *mut LeanObject,
    mut v_a_7054_: *mut LeanObject,
    mut v_a_7055_: *mut LeanObject,
    mut v_a_7056_: *mut LeanObject,
    mut v_a_7057_: *mut LeanObject,
    mut v_a_7058_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7059_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_7057_);
    lean_dec_ref(v_a_7056_);
    lean_dec(v_a_7055_);
    lean_dec_ref(v_a_7054_);
    lean_dec_ref(v_a_7053_);
    lean_dec(v_a_7052_);
    lean_dec_ref(v_a_7051_);
    return v_res_7059_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8___boxed(
    mut v_fvarId_7060_: *mut LeanObject,
    mut v_i_7061_: *mut LeanObject,
    mut v_as_7062_: *mut LeanObject,
    mut v___y_7063_: *mut LeanObject,
    mut v___y_7064_: *mut LeanObject,
    mut v___y_7065_: *mut LeanObject,
    mut v___y_7066_: *mut LeanObject,
    mut v___y_7067_: *mut LeanObject,
    mut v___y_7068_: *mut LeanObject,
    mut v___y_7069_: *mut LeanObject,
    mut v___y_7070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7071_: *mut LeanObject = core::ptr::null_mut();
    v_res_7071_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_Simp_simp_spec__8(v_fvarId_7060_, v_i_7061_, v_as_7062_, v___y_7063_, v___y_7064_, v___y_7065_, v___y_7066_, v___y_7067_, v___y_7068_, v___y_7069_);
    lean_dec(v___y_7069_);
    lean_dec_ref(v___y_7068_);
    lean_dec(v___y_7067_);
    lean_dec_ref(v___y_7066_);
    lean_dec_ref(v___y_7065_);
    lean_dec(v___y_7064_);
    lean_dec_ref(v___y_7063_);
    return v_res_7071_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f___boxed(
    mut v_cases_7072_: *mut LeanObject,
    mut v_a_7073_: *mut LeanObject,
    mut v_a_7074_: *mut LeanObject,
    mut v_a_7075_: *mut LeanObject,
    mut v_a_7076_: *mut LeanObject,
    mut v_a_7077_: *mut LeanObject,
    mut v_a_7078_: *mut LeanObject,
    mut v_a_7079_: *mut LeanObject,
    mut v_a_7080_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7081_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_7079_);
    lean_dec_ref(v_a_7078_);
    lean_dec(v_a_7077_);
    lean_dec_ref(v_a_7076_);
    lean_dec_ref(v_a_7075_);
    lean_dec(v_a_7074_);
    lean_dec_ref(v_a_7073_);
    return v_res_7081_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___boxed(
    mut v_letDecl_7082_: *mut LeanObject,
    mut v_k_7083_: *mut LeanObject,
    mut v_a_7084_: *mut LeanObject,
    mut v_a_7085_: *mut LeanObject,
    mut v_a_7086_: *mut LeanObject,
    mut v_a_7087_: *mut LeanObject,
    mut v_a_7088_: *mut LeanObject,
    mut v_a_7089_: *mut LeanObject,
    mut v_a_7090_: *mut LeanObject,
    mut v_a_7091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7092_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_7090_);
    lean_dec_ref(v_a_7089_);
    lean_dec(v_a_7088_);
    lean_dec_ref(v_a_7087_);
    lean_dec_ref(v_a_7086_);
    lean_dec(v_a_7085_);
    lean_dec_ref(v_a_7084_);
    return v_res_7092_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simp___boxed(
    mut v_code_7093_: *mut LeanObject,
    mut v_a_7094_: *mut LeanObject,
    mut v_a_7095_: *mut LeanObject,
    mut v_a_7096_: *mut LeanObject,
    mut v_a_7097_: *mut LeanObject,
    mut v_a_7098_: *mut LeanObject,
    mut v_a_7099_: *mut LeanObject,
    mut v_a_7100_: *mut LeanObject,
    mut v_a_7101_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7102_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_7100_);
    lean_dec(v_a_7098_);
    lean_dec_ref(v_a_7097_);
    lean_dec_ref(v_a_7096_);
    lean_dec(v_a_7095_);
    lean_dec_ref(v_a_7094_);
    return v_res_7102_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normLetDecl___at___00Lean_Compiler_LCNF_Simp_simp_spec__4(
    mut v_pu_7103_: u8,
    mut v_t_7104_: u8,
    mut v_decl_7105_: *mut LeanObject,
    mut v___y_7106_: *mut LeanObject,
    mut v___y_7107_: *mut LeanObject,
    mut v___y_7108_: *mut LeanObject,
    mut v___y_7109_: *mut LeanObject,
    mut v___y_7110_: *mut LeanObject,
    mut v___y_7111_: *mut LeanObject,
    mut v___y_7112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_7115_: *mut LeanObject,
    mut v_t_7116_: *mut LeanObject,
    mut v_decl_7117_: *mut LeanObject,
    mut v___y_7118_: *mut LeanObject,
    mut v___y_7119_: *mut LeanObject,
    mut v___y_7120_: *mut LeanObject,
    mut v___y_7121_: *mut LeanObject,
    mut v___y_7122_: *mut LeanObject,
    mut v___y_7123_: *mut LeanObject,
    mut v___y_7124_: *mut LeanObject,
    mut v___y_7125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7126_: u8 = 0;
    let mut v_t_boxed_7127_: u8 = 0;
    let mut v_res_7128_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7126_ = (lean_unbox(v_pu_7115_) as u8);
    v_t_boxed_7127_ = (lean_unbox(v_t_7116_) as u8);
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
    lean_dec(v___y_7124_);
    lean_dec_ref(v___y_7123_);
    lean_dec(v___y_7122_);
    lean_dec_ref(v___y_7121_);
    lean_dec_ref(v___y_7120_);
    lean_dec(v___y_7119_);
    lean_dec_ref(v___y_7118_);
    return v_res_7128_;
}
pub unsafe fn l_Lean_Compiler_LCNF_normArgs___at___00Lean_Compiler_LCNF_Simp_simp_spec__5(
    mut v_pu_7129_: u8,
    mut v_t_7130_: u8,
    mut v_args_7131_: *mut LeanObject,
    mut v___y_7132_: *mut LeanObject,
    mut v___y_7133_: *mut LeanObject,
    mut v___y_7134_: *mut LeanObject,
    mut v___y_7135_: *mut LeanObject,
    mut v___y_7136_: *mut LeanObject,
    mut v___y_7137_: *mut LeanObject,
    mut v___y_7138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7140_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_pu_7141_: *mut LeanObject,
    mut v_t_7142_: *mut LeanObject,
    mut v_args_7143_: *mut LeanObject,
    mut v___y_7144_: *mut LeanObject,
    mut v___y_7145_: *mut LeanObject,
    mut v___y_7146_: *mut LeanObject,
    mut v___y_7147_: *mut LeanObject,
    mut v___y_7148_: *mut LeanObject,
    mut v___y_7149_: *mut LeanObject,
    mut v___y_7150_: *mut LeanObject,
    mut v___y_7151_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7152_: u8 = 0;
    let mut v_t_boxed_7153_: u8 = 0;
    let mut v_res_7154_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7152_ = (lean_unbox(v_pu_7141_) as u8);
    v_t_boxed_7153_ = (lean_unbox(v_t_7142_) as u8);
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
    lean_dec(v___y_7150_);
    lean_dec_ref(v___y_7149_);
    lean_dec(v___y_7148_);
    lean_dec_ref(v___y_7147_);
    lean_dec_ref(v___y_7146_);
    lean_dec(v___y_7145_);
    lean_dec_ref(v___y_7144_);
    return v_res_7154_;
}
pub unsafe fn l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0(
    mut v_inst_7155_: *mut LeanObject,
    mut v_R_7156_: *mut LeanObject,
    mut v_a_7157_: *mut LeanObject,
    mut v_b_7158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7159_: *mut LeanObject = core::ptr::null_mut();
    v___x_7159_ = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__0___redArg(v_a_7157_, v_b_7158_);
    return v___x_7159_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1(
    mut v_00_u03b2_7160_: *mut LeanObject,
    mut v_x_7161_: *mut LeanObject,
    mut v_x_7162_: *mut LeanObject,
    mut v_x_7163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7164_: *mut LeanObject = core::ptr::null_mut();
    v___x_7164_ = l_Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1___redArg(v_x_7161_, v_x_7162_, v_x_7163_);
    return v___x_7164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(
    mut v_as_7165_: *mut LeanObject,
    mut v_i_7166_: usize,
    mut v_stop_7167_: usize,
    mut v_b_7168_: *mut LeanObject,
    mut v___y_7169_: *mut LeanObject,
    mut v___y_7170_: *mut LeanObject,
    mut v___y_7171_: *mut LeanObject,
    mut v___y_7172_: *mut LeanObject,
    mut v___y_7173_: *mut LeanObject,
    mut v___y_7174_: *mut LeanObject,
    mut v___y_7175_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
    v___x_7177_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___redArg(v_as_7165_, v_i_7166_, v_stop_7167_, v_b_7168_, v___y_7170_);
    return v___x_7177_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6___boxed(
    mut v_as_7178_: *mut LeanObject,
    mut v_i_7179_: *mut LeanObject,
    mut v_stop_7180_: *mut LeanObject,
    mut v_b_7181_: *mut LeanObject,
    mut v___y_7182_: *mut LeanObject,
    mut v___y_7183_: *mut LeanObject,
    mut v___y_7184_: *mut LeanObject,
    mut v___y_7185_: *mut LeanObject,
    mut v___y_7186_: *mut LeanObject,
    mut v___y_7187_: *mut LeanObject,
    mut v___y_7188_: *mut LeanObject,
    mut v___y_7189_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7190_: usize = 0;
    let mut v_stop_boxed_7191_: usize = 0;
    let mut v_res_7192_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7190_ = lean_unbox_usize(v_i_7179_);
    lean_dec(v_i_7179_);
    v_stop_boxed_7191_ = lean_unbox_usize(v_stop_7180_);
    lean_dec(v_stop_7180_);
    v_res_7192_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__6(v_as_7178_, v_i_boxed_7190_, v_stop_boxed_7191_, v_b_7181_, v___y_7182_, v___y_7183_, v___y_7184_, v___y_7185_, v___y_7186_, v___y_7187_, v___y_7188_);
    lean_dec(v___y_7188_);
    lean_dec_ref(v___y_7187_);
    lean_dec(v___y_7186_);
    lean_dec_ref(v___y_7185_);
    lean_dec_ref(v___y_7184_);
    lean_dec(v___y_7183_);
    lean_dec_ref(v___y_7182_);
    lean_dec_ref(v_as_7178_);
    return v_res_7192_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(
    mut v_as_7193_: *mut LeanObject,
    mut v_i_7194_: usize,
    mut v_stop_7195_: usize,
    mut v___y_7196_: *mut LeanObject,
    mut v___y_7197_: *mut LeanObject,
    mut v___y_7198_: *mut LeanObject,
    mut v___y_7199_: *mut LeanObject,
    mut v___y_7200_: *mut LeanObject,
    mut v___y_7201_: *mut LeanObject,
    mut v___y_7202_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7204_: *mut LeanObject = core::ptr::null_mut();
    v___x_7204_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___redArg(v_as_7193_, v_i_7194_, v_stop_7195_, v___y_7202_);
    return v___x_7204_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7___boxed(
    mut v_as_7205_: *mut LeanObject,
    mut v_i_7206_: *mut LeanObject,
    mut v_stop_7207_: *mut LeanObject,
    mut v___y_7208_: *mut LeanObject,
    mut v___y_7209_: *mut LeanObject,
    mut v___y_7210_: *mut LeanObject,
    mut v___y_7211_: *mut LeanObject,
    mut v___y_7212_: *mut LeanObject,
    mut v___y_7213_: *mut LeanObject,
    mut v___y_7214_: *mut LeanObject,
    mut v___y_7215_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7216_: usize = 0;
    let mut v_stop_boxed_7217_: usize = 0;
    let mut v_res_7218_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7216_ = lean_unbox_usize(v_i_7206_);
    lean_dec(v_i_7206_);
    v_stop_boxed_7217_ = lean_unbox_usize(v_stop_7207_);
    lean_dec(v_stop_7207_);
    v_res_7218_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__7(v_as_7205_, v_i_boxed_7216_, v_stop_boxed_7217_, v___y_7208_, v___y_7209_, v___y_7210_, v___y_7211_, v___y_7212_, v___y_7213_, v___y_7214_);
    lean_dec(v___y_7214_);
    lean_dec_ref(v___y_7213_);
    lean_dec(v___y_7212_);
    lean_dec_ref(v___y_7211_);
    lean_dec_ref(v___y_7210_);
    lean_dec(v___y_7209_);
    lean_dec_ref(v___y_7208_);
    lean_dec_ref(v_as_7205_);
    return v_res_7218_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(
    mut v_as_7219_: *mut LeanObject,
    mut v_i_7220_: usize,
    mut v_stop_7221_: usize,
    mut v_b_7222_: *mut LeanObject,
    mut v___y_7223_: *mut LeanObject,
    mut v___y_7224_: *mut LeanObject,
    mut v___y_7225_: *mut LeanObject,
    mut v___y_7226_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7228_: *mut LeanObject = core::ptr::null_mut();
    v___x_7228_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___redArg(v_as_7219_, v_i_7220_, v_stop_7221_, v_b_7222_, v___y_7224_);
    return v___x_7228_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9___boxed(
    mut v_as_7229_: *mut LeanObject,
    mut v_i_7230_: *mut LeanObject,
    mut v_stop_7231_: *mut LeanObject,
    mut v_b_7232_: *mut LeanObject,
    mut v___y_7233_: *mut LeanObject,
    mut v___y_7234_: *mut LeanObject,
    mut v___y_7235_: *mut LeanObject,
    mut v___y_7236_: *mut LeanObject,
    mut v___y_7237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7238_: usize = 0;
    let mut v_stop_boxed_7239_: usize = 0;
    let mut v_res_7240_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7238_ = lean_unbox_usize(v_i_7230_);
    lean_dec(v_i_7230_);
    v_stop_boxed_7239_ = lean_unbox_usize(v_stop_7231_);
    lean_dec(v_stop_7231_);
    v_res_7240_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__9(v_as_7229_, v_i_boxed_7238_, v_stop_boxed_7239_, v_b_7232_, v___y_7233_, v___y_7234_, v___y_7235_, v___y_7236_);
    lean_dec(v___y_7236_);
    lean_dec_ref(v___y_7235_);
    lean_dec(v___y_7234_);
    lean_dec_ref(v___y_7233_);
    lean_dec_ref(v_as_7229_);
    return v_res_7240_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(
    mut v_as_7241_: *mut LeanObject,
    mut v_i_7242_: usize,
    mut v_stop_7243_: usize,
    mut v_b_7244_: *mut LeanObject,
    mut v___y_7245_: *mut LeanObject,
    mut v___y_7246_: *mut LeanObject,
    mut v___y_7247_: *mut LeanObject,
    mut v___y_7248_: *mut LeanObject,
    mut v___y_7249_: *mut LeanObject,
    mut v___y_7250_: *mut LeanObject,
    mut v___y_7251_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7253_: *mut LeanObject = core::ptr::null_mut();
    v___x_7253_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___redArg(v_as_7241_, v_i_7242_, v_stop_7243_, v_b_7244_, v___y_7248_, v___y_7249_, v___y_7250_, v___y_7251_);
    return v___x_7253_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10___boxed(
    mut v_as_7254_: *mut LeanObject,
    mut v_i_7255_: *mut LeanObject,
    mut v_stop_7256_: *mut LeanObject,
    mut v_b_7257_: *mut LeanObject,
    mut v___y_7258_: *mut LeanObject,
    mut v___y_7259_: *mut LeanObject,
    mut v___y_7260_: *mut LeanObject,
    mut v___y_7261_: *mut LeanObject,
    mut v___y_7262_: *mut LeanObject,
    mut v___y_7263_: *mut LeanObject,
    mut v___y_7264_: *mut LeanObject,
    mut v___y_7265_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7266_: usize = 0;
    let mut v_stop_boxed_7267_: usize = 0;
    let mut v_res_7268_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7266_ = lean_unbox_usize(v_i_7255_);
    lean_dec(v_i_7255_);
    v_stop_boxed_7267_ = lean_unbox_usize(v_stop_7256_);
    lean_dec(v_stop_7256_);
    v_res_7268_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__10(v_as_7254_, v_i_boxed_7266_, v_stop_boxed_7267_, v_b_7257_, v___y_7258_, v___y_7259_, v___y_7260_, v___y_7261_, v___y_7262_, v___y_7263_, v___y_7264_);
    lean_dec(v___y_7264_);
    lean_dec_ref(v___y_7263_);
    lean_dec(v___y_7262_);
    lean_dec_ref(v___y_7261_);
    lean_dec_ref(v___y_7260_);
    lean_dec(v___y_7259_);
    lean_dec_ref(v___y_7258_);
    lean_dec_ref(v_as_7254_);
    return v_res_7268_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(
    mut v_as_7269_: *mut LeanObject,
    mut v_i_7270_: usize,
    mut v_stop_7271_: usize,
    mut v_b_7272_: *mut LeanObject,
    mut v___y_7273_: *mut LeanObject,
    mut v___y_7274_: *mut LeanObject,
    mut v___y_7275_: *mut LeanObject,
    mut v___y_7276_: *mut LeanObject,
    mut v___y_7277_: *mut LeanObject,
    mut v___y_7278_: *mut LeanObject,
    mut v___y_7279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7281_: *mut LeanObject = core::ptr::null_mut();
    v___x_7281_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___redArg(v_as_7269_, v_i_7270_, v_stop_7271_, v_b_7272_, v___y_7277_);
    return v___x_7281_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12___boxed(
    mut v_as_7282_: *mut LeanObject,
    mut v_i_7283_: *mut LeanObject,
    mut v_stop_7284_: *mut LeanObject,
    mut v_b_7285_: *mut LeanObject,
    mut v___y_7286_: *mut LeanObject,
    mut v___y_7287_: *mut LeanObject,
    mut v___y_7288_: *mut LeanObject,
    mut v___y_7289_: *mut LeanObject,
    mut v___y_7290_: *mut LeanObject,
    mut v___y_7291_: *mut LeanObject,
    mut v___y_7292_: *mut LeanObject,
    mut v___y_7293_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7294_: usize = 0;
    let mut v_stop_boxed_7295_: usize = 0;
    let mut v_res_7296_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7294_ = lean_unbox_usize(v_i_7283_);
    lean_dec(v_i_7283_);
    v_stop_boxed_7295_ = lean_unbox_usize(v_stop_7284_);
    lean_dec(v_stop_7284_);
    v_res_7296_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Simp_simp_spec__12(v_as_7282_, v_i_boxed_7294_, v_stop_boxed_7295_, v_b_7285_, v___y_7286_, v___y_7287_, v___y_7288_, v___y_7289_, v___y_7290_, v___y_7291_, v___y_7292_);
    lean_dec(v___y_7292_);
    lean_dec_ref(v___y_7291_);
    lean_dec(v___y_7290_);
    lean_dec_ref(v___y_7289_);
    lean_dec_ref(v___y_7288_);
    lean_dec(v___y_7287_);
    lean_dec_ref(v___y_7286_);
    lean_dec_ref(v_as_7282_);
    return v_res_7296_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(
    mut v_as_7297_: *mut LeanObject,
    mut v_i_7298_: usize,
    mut v_stop_7299_: usize,
    mut v___y_7300_: *mut LeanObject,
    mut v___y_7301_: *mut LeanObject,
    mut v___y_7302_: *mut LeanObject,
    mut v___y_7303_: *mut LeanObject,
    mut v___y_7304_: *mut LeanObject,
    mut v___y_7305_: *mut LeanObject,
    mut v___y_7306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7308_: *mut LeanObject = core::ptr::null_mut();
    v___x_7308_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___redArg(v_as_7297_, v_i_7298_, v_stop_7299_, v___y_7301_);
    return v___x_7308_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13___boxed(
    mut v_as_7309_: *mut LeanObject,
    mut v_i_7310_: *mut LeanObject,
    mut v_stop_7311_: *mut LeanObject,
    mut v___y_7312_: *mut LeanObject,
    mut v___y_7313_: *mut LeanObject,
    mut v___y_7314_: *mut LeanObject,
    mut v___y_7315_: *mut LeanObject,
    mut v___y_7316_: *mut LeanObject,
    mut v___y_7317_: *mut LeanObject,
    mut v___y_7318_: *mut LeanObject,
    mut v___y_7319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_7320_: usize = 0;
    let mut v_stop_boxed_7321_: usize = 0;
    let mut v_res_7322_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7320_ = lean_unbox_usize(v_i_7310_);
    lean_dec(v_i_7310_);
    v_stop_boxed_7321_ = lean_unbox_usize(v_stop_7311_);
    lean_dec(v_stop_7311_);
    v_res_7322_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_Simp_simp_spec__13(v_as_7309_, v_i_boxed_7320_, v_stop_boxed_7321_, v___y_7312_, v___y_7313_, v___y_7314_, v___y_7315_, v___y_7316_, v___y_7317_, v___y_7318_);
    lean_dec(v___y_7318_);
    lean_dec_ref(v___y_7317_);
    lean_dec(v___y_7316_);
    lean_dec_ref(v___y_7315_);
    lean_dec_ref(v___y_7314_);
    lean_dec(v___y_7313_);
    lean_dec_ref(v___y_7312_);
    lean_dec_ref(v_as_7309_);
    return v_res_7322_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(
    mut v_as_7323_: *mut LeanObject,
    mut v_sz_7324_: usize,
    mut v_i_7325_: usize,
    mut v_b_7326_: *mut LeanObject,
    mut v___y_7327_: *mut LeanObject,
    mut v___y_7328_: *mut LeanObject,
    mut v___y_7329_: *mut LeanObject,
    mut v___y_7330_: *mut LeanObject,
    mut v___y_7331_: *mut LeanObject,
    mut v___y_7332_: *mut LeanObject,
    mut v___y_7333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7335_: *mut LeanObject = core::ptr::null_mut();
    v___x_7335_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___redArg(v_as_7323_, v_sz_7324_, v_i_7325_, v_b_7326_, v___y_7328_);
    return v___x_7335_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15___boxed(
    mut v_as_7336_: *mut LeanObject,
    mut v_sz_7337_: *mut LeanObject,
    mut v_i_7338_: *mut LeanObject,
    mut v_b_7339_: *mut LeanObject,
    mut v___y_7340_: *mut LeanObject,
    mut v___y_7341_: *mut LeanObject,
    mut v___y_7342_: *mut LeanObject,
    mut v___y_7343_: *mut LeanObject,
    mut v___y_7344_: *mut LeanObject,
    mut v___y_7345_: *mut LeanObject,
    mut v___y_7346_: *mut LeanObject,
    mut v___y_7347_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_7348_: usize = 0;
    let mut v_i_boxed_7349_: usize = 0;
    let mut v_res_7350_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_7348_ = lean_unbox_usize(v_sz_7337_);
    lean_dec(v_sz_7337_);
    v_i_boxed_7349_ = lean_unbox_usize(v_i_7338_);
    lean_dec(v_i_7338_);
    v_res_7350_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__15(v_as_7336_, v_sz_boxed_7348_, v_i_boxed_7349_, v_b_7339_, v___y_7340_, v___y_7341_, v___y_7342_, v___y_7343_, v___y_7344_, v___y_7345_, v___y_7346_);
    lean_dec(v___y_7346_);
    lean_dec_ref(v___y_7345_);
    lean_dec(v___y_7344_);
    lean_dec_ref(v___y_7343_);
    lean_dec_ref(v___y_7342_);
    lean_dec(v___y_7341_);
    lean_dec_ref(v___y_7340_);
    lean_dec_ref(v_as_7336_);
    return v_res_7350_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(
    mut v_00_u03b2_7351_: *mut LeanObject,
    mut v_x_7352_: *mut LeanObject,
    mut v_x_7353_: usize,
    mut v_x_7354_: usize,
    mut v_x_7355_: *mut LeanObject,
    mut v_x_7356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7357_: *mut LeanObject = core::ptr::null_mut();
    v___x_7357_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___redArg(v_x_7352_, v_x_7353_, v_x_7354_, v_x_7355_, v_x_7356_);
    return v___x_7357_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_7358_: *mut LeanObject,
    mut v_x_7359_: *mut LeanObject,
    mut v_x_7360_: *mut LeanObject,
    mut v_x_7361_: *mut LeanObject,
    mut v_x_7362_: *mut LeanObject,
    mut v_x_7363_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_51443__boxed_7364_: usize = 0;
    let mut v_x_51444__boxed_7365_: usize = 0;
    let mut v_res_7366_: *mut LeanObject = core::ptr::null_mut();
    v_x_51443__boxed_7364_ = lean_unbox_usize(v_x_7360_);
    lean_dec(v_x_7360_);
    v_x_51444__boxed_7365_ = lean_unbox_usize(v_x_7361_);
    lean_dec(v_x_7361_);
    v_res_7366_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1(v_00_u03b2_7358_, v_x_7359_, v_x_51443__boxed_7364_, v_x_51444__boxed_7365_, v_x_7362_, v_x_7363_);
    return v_res_7366_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(
    mut v_pu_7367_: u8,
    mut v_t_7368_: u8,
    mut v_i_7369_: *mut LeanObject,
    mut v_as_7370_: *mut LeanObject,
    mut v___y_7371_: *mut LeanObject,
    mut v___y_7372_: *mut LeanObject,
    mut v___y_7373_: *mut LeanObject,
    mut v___y_7374_: *mut LeanObject,
    mut v___y_7375_: *mut LeanObject,
    mut v___y_7376_: *mut LeanObject,
    mut v___y_7377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7379_: *mut LeanObject = core::ptr::null_mut();
    v___x_7379_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___redArg(v_pu_7367_, v_t_7368_, v_i_7369_, v_as_7370_, v___y_7372_, v___y_7375_);
    return v___x_7379_;
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18___boxed(
    mut v_pu_7380_: *mut LeanObject,
    mut v_t_7381_: *mut LeanObject,
    mut v_i_7382_: *mut LeanObject,
    mut v_as_7383_: *mut LeanObject,
    mut v___y_7384_: *mut LeanObject,
    mut v___y_7385_: *mut LeanObject,
    mut v___y_7386_: *mut LeanObject,
    mut v___y_7387_: *mut LeanObject,
    mut v___y_7388_: *mut LeanObject,
    mut v___y_7389_: *mut LeanObject,
    mut v___y_7390_: *mut LeanObject,
    mut v___y_7391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_7392_: u8 = 0;
    let mut v_t_boxed_7393_: u8 = 0;
    let mut v_res_7394_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_7392_ = (lean_unbox(v_pu_7380_) as u8);
    v_t_boxed_7393_ = (lean_unbox(v_t_7381_) as u8);
    v_res_7394_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_normParams___at___00Lean_Compiler_LCNF_Simp_simpFunDecl_spec__17_spec__18(v_pu_boxed_7392_, v_t_boxed_7393_, v_i_7382_, v_as_7383_, v___y_7384_, v___y_7385_, v___y_7386_, v___y_7387_, v___y_7388_, v___y_7389_, v___y_7390_);
    lean_dec(v___y_7390_);
    lean_dec_ref(v___y_7389_);
    lean_dec(v___y_7388_);
    lean_dec_ref(v___y_7387_);
    lean_dec_ref(v___y_7386_);
    lean_dec(v___y_7385_);
    lean_dec_ref(v___y_7384_);
    return v_res_7394_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8(
    mut v_00_u03b2_7395_: *mut LeanObject,
    mut v_n_7396_: *mut LeanObject,
    mut v_k_7397_: *mut LeanObject,
    mut v_v_7398_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7399_: *mut LeanObject = core::ptr::null_mut();
    v___x_7399_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8___redArg(v_n_7396_, v_k_7397_, v_v_7398_);
    return v___x_7399_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(
    mut v_00_u03b2_7400_: *mut LeanObject,
    mut v_depth_7401_: usize,
    mut v_keys_7402_: *mut LeanObject,
    mut v_vals_7403_: *mut LeanObject,
    mut v_heq_7404_: *mut LeanObject,
    mut v_i_7405_: *mut LeanObject,
    mut v_entries_7406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7407_: *mut LeanObject = core::ptr::null_mut();
    v___x_7407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___redArg(v_depth_7401_, v_keys_7402_, v_vals_7403_, v_i_7405_, v_entries_7406_);
    return v___x_7407_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9___boxed(
    mut v_00_u03b2_7408_: *mut LeanObject,
    mut v_depth_7409_: *mut LeanObject,
    mut v_keys_7410_: *mut LeanObject,
    mut v_vals_7411_: *mut LeanObject,
    mut v_heq_7412_: *mut LeanObject,
    mut v_i_7413_: *mut LeanObject,
    mut v_entries_7414_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_7415_: usize = 0;
    let mut v_res_7416_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_7415_ = lean_unbox_usize(v_depth_7409_);
    lean_dec(v_depth_7409_);
    v_res_7416_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__9(v_00_u03b2_7408_, v_depth_boxed_7415_, v_keys_7410_, v_vals_7411_, v_heq_7412_, v_i_7413_, v_entries_7414_);
    lean_dec_ref(v_vals_7411_);
    lean_dec_ref(v_keys_7410_);
    return v_res_7416_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19(
    mut v_00_u03b2_7417_: *mut LeanObject,
    mut v_x_7418_: *mut LeanObject,
    mut v_x_7419_: *mut LeanObject,
    mut v_x_7420_: *mut LeanObject,
    mut v_x_7421_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7422_: *mut LeanObject = core::ptr::null_mut();
    v___x_7422_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Compiler_LCNF_Simp_inlineApp_x3f_spec__1_spec__1_spec__8_spec__19___redArg(v_x_7418_, v_x_7419_, v_x_7420_, v_x_7421_);
    return v___x_7422_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_Main(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
}
