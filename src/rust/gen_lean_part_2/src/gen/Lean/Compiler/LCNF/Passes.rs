// Lean compiler output
// Module: Lean.Compiler.LCNF.Passes
// Imports: Lean.Compiler.LCNF.PullLetDecls Lean.Compiler.LCNF.CSE Lean.Compiler.LCNF.JoinPoints Lean.Compiler.LCNF.Specialize Lean.Compiler.LCNF.ToMono Lean.Compiler.LCNF.LambdaLifting Lean.Compiler.LCNF.FloatLetIn Lean.Compiler.LCNF.ReduceArity Lean.Compiler.LCNF.ElimDeadBranches Lean.Compiler.LCNF.StructProjCases Lean.Compiler.LCNF.ExtractClosed Lean.Compiler.LCNF.Visibility Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.ToImpure Lean.Compiler.LCNF.PushProj Lean.Compiler.LCNF.ResetReuse Lean.Compiler.LCNF.SimpCase Lean.Compiler.LCNF.InferBorrow Lean.Compiler.LCNF.ExplicitBoxing Lean.Compiler.LCNF.ExplicitRC Lean.Compiler.LCNF.CoalesceRC Lean.Compiler.LCNF.Toposort Lean.Compiler.LCNF.ExpandResetReuse Lean.Compiler.LCNF.SimpleGroundExpr
use crate::ffi::{
    lean_array_get, lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_mk_empty_array_with_capacity,
    lean_nat_dec_le, lean_nat_dec_lt, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
    lean_string_dec_eq, lean_usize_add, lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_num___override, l_Lean_Name_str___override, l_Lean_replaceRef,
};
use crate::r#gen::Lean::Attributes::{
    l_Lean_Attribute_Builtin_ensureNoArgs, l_Lean_ensureAttrDeclIsMeta,
    l_Lean_instBEqAttributeKind_beq, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::LCNF::CSE::{
    initialize_Lean_Compiler_LCNF_CSE, l_Lean_Compiler_LCNF_cse,
    runtime_initialize_Lean_Compiler_LCNF_CSE,
};
use crate::r#gen::Lean::Compiler::LCNF::CoalesceRC::{
    initialize_Lean_Compiler_LCNF_CoalesceRC, l_Lean_Compiler_LCNF_coalesceRC,
    runtime_initialize_Lean_Compiler_LCNF_CoalesceRC,
};
use crate::r#gen::Lean::Compiler::LCNF::ElimDead::l_Lean_Compiler_LCNF_elimDeadVars;
use crate::r#gen::Lean::Compiler::LCNF::ElimDeadBranches::{
    initialize_Lean_Compiler_LCNF_ElimDeadBranches, l_Lean_Compiler_LCNF_elimDeadBranches,
    runtime_initialize_Lean_Compiler_LCNF_ElimDeadBranches,
};
use crate::r#gen::Lean::Compiler::LCNF::ExpandResetReuse::{
    initialize_Lean_Compiler_LCNF_ExpandResetReuse, l_Lean_Compiler_LCNF_expandResetReuse,
    runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse,
};
use crate::r#gen::Lean::Compiler::LCNF::ExplicitBoxing::{
    initialize_Lean_Compiler_LCNF_ExplicitBoxing, l_Lean_Compiler_LCNF_explicitBoxing,
    runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing,
};
use crate::r#gen::Lean::Compiler::LCNF::ExplicitRC::{
    initialize_Lean_Compiler_LCNF_ExplicitRC, l_Lean_Compiler_LCNF_explicitRc,
    runtime_initialize_Lean_Compiler_LCNF_ExplicitRC,
};
use crate::r#gen::Lean::Compiler::LCNF::ExtractClosed::{
    initialize_Lean_Compiler_LCNF_ExtractClosed, l_Lean_Compiler_LCNF_extractClosed,
    runtime_initialize_Lean_Compiler_LCNF_ExtractClosed,
};
use crate::r#gen::Lean::Compiler::LCNF::FloatLetIn::{
    initialize_Lean_Compiler_LCNF_FloatLetIn, l_Lean_Compiler_LCNF_floatLetIn,
    runtime_initialize_Lean_Compiler_LCNF_FloatLetIn,
};
use crate::r#gen::Lean::Compiler::LCNF::InferBorrow::{
    initialize_Lean_Compiler_LCNF_InferBorrow, l_Lean_Compiler_LCNF_inferBorrow,
    runtime_initialize_Lean_Compiler_LCNF_InferBorrow,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::l_Lean_Compiler_LCNF_normalizeFVarIds;
use crate::r#gen::Lean::Compiler::LCNF::JoinPoints::{
    initialize_Lean_Compiler_LCNF_JoinPoints, l_Lean_Compiler_LCNF_commonJoinPointArgs,
    l_Lean_Compiler_LCNF_extendJoinPointContext___redArg, l_Lean_Compiler_LCNF_findJoinPoints,
    runtime_initialize_Lean_Compiler_LCNF_JoinPoints,
};
use crate::r#gen::Lean::Compiler::LCNF::LambdaLifting::{
    initialize_Lean_Compiler_LCNF_LambdaLifting, l_Lean_Compiler_LCNF_eagerLambdaLifting,
    l_Lean_Compiler_LCNF_lambdaLifting, runtime_initialize_Lean_Compiler_LCNF_LambdaLifting,
};
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    l_Lean_Compiler_LCNF_PassInstaller_runFromDecl,
    l_Lean_Compiler_LCNF_instInhabitedPassManager_default,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    l_Lean_Compiler_LCNF_Decl_saveBase___redArg, l_Lean_Compiler_LCNF_Decl_saveImpure___redArg,
    l_Lean_Compiler_LCNF_Decl_saveMono___redArg, l_Lean_Compiler_LCNF_recordFinalImpureDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::PullFunDecls::l_Lean_Compiler_LCNF_pullFunDecls;
use crate::r#gen::Lean::Compiler::LCNF::PullLetDecls::{
    initialize_Lean_Compiler_LCNF_PullLetDecls, l_Lean_Compiler_LCNF_pullInstances,
    runtime_initialize_Lean_Compiler_LCNF_PullLetDecls,
};
use crate::r#gen::Lean::Compiler::LCNF::PushProj::{
    initialize_Lean_Compiler_LCNF_PushProj, l_Lean_Compiler_LCNF_pushProj,
    runtime_initialize_Lean_Compiler_LCNF_PushProj,
};
use crate::r#gen::Lean::Compiler::LCNF::ReduceArity::{
    initialize_Lean_Compiler_LCNF_ReduceArity, l_Lean_Compiler_LCNF_reduceArity,
    runtime_initialize_Lean_Compiler_LCNF_ReduceArity,
};
use crate::r#gen::Lean::Compiler::LCNF::ReduceJpArity::l_Lean_Compiler_LCNF_reduceJpArity;
use crate::r#gen::Lean::Compiler::LCNF::ResetReuse::{
    initialize_Lean_Compiler_LCNF_ResetReuse, l_Lean_Compiler_LCNF_insertResetReuse,
    runtime_initialize_Lean_Compiler_LCNF_ResetReuse,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::{
    initialize_Lean_Compiler_LCNF_Simp, l_Lean_Compiler_LCNF_simp,
    runtime_initialize_Lean_Compiler_LCNF_Simp,
};
use crate::r#gen::Lean::Compiler::LCNF::SimpCase::{
    initialize_Lean_Compiler_LCNF_SimpCase, l_Lean_Compiler_LCNF_simpCase,
    runtime_initialize_Lean_Compiler_LCNF_SimpCase,
};
use crate::r#gen::Lean::Compiler::LCNF::SimpleGroundExpr::{
    initialize_Lean_Compiler_LCNF_SimpleGroundExpr, l_Lean_Compiler_LCNF_detectSimpleGround,
    runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr,
};
use crate::r#gen::Lean::Compiler::LCNF::Specialize::{
    initialize_Lean_Compiler_LCNF_Specialize, l_Lean_Compiler_LCNF_specialize,
    runtime_initialize_Lean_Compiler_LCNF_Specialize,
};
use crate::r#gen::Lean::Compiler::LCNF::StructProjCases::{
    initialize_Lean_Compiler_LCNF_StructProjCases, l_Lean_Compiler_LCNF_structProjCases,
    runtime_initialize_Lean_Compiler_LCNF_StructProjCases,
};
use crate::r#gen::Lean::Compiler::LCNF::ToImpure::{
    initialize_Lean_Compiler_LCNF_ToImpure, l_Lean_Compiler_LCNF_toImpure,
    runtime_initialize_Lean_Compiler_LCNF_ToImpure,
};
use crate::r#gen::Lean::Compiler::LCNF::ToMono::{
    initialize_Lean_Compiler_LCNF_ToMono, l_Lean_Compiler_LCNF_toMono,
    runtime_initialize_Lean_Compiler_LCNF_ToMono,
};
use crate::r#gen::Lean::Compiler::LCNF::Toposort::{
    initialize_Lean_Compiler_LCNF_Toposort, l_Lean_Compiler_LCNF_toposortPass,
    runtime_initialize_Lean_Compiler_LCNF_Toposort,
};
use crate::r#gen::Lean::Compiler::LCNF::Visibility::{
    initialize_Lean_Compiler_LCNF_Visibility, l_Lean_Compiler_LCNF_checkTemplateVisibility,
    l_Lean_Compiler_LCNF_inferVisibility, runtime_initialize_Lean_Compiler_LCNF_Visibility,
};
use crate::r#gen::Lean::CoreM::l_Lean_ImportM_runCoreM___redArg;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_isAnonymous;
use crate::r#gen::Lean::Data::Options::l_Lean_Options_empty;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_contains, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f, l_Lean_Environment_header,
    l_Lean_Environment_setExporting, l_Lean_EnvironmentHeader_moduleNames,
    l_Lean_PersistentEnvExtension_addEntry___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_unknownIdentifierMessageTag;
use crate::r#gen::Lean::Expr::l_Lean_mkConst;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_note, l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat,
    l_Lean_MessageData_ofName, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::PrivateName::l_Lean_isPrivateName;
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
pub static l_Lean_Compiler_LCNF_Pass_init___closed__0_value: leanh::LeanClosureObject<1> =
    leanh::LeanClosureObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_Pass_init___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut leanh::LeanObject],
    };
static mut l_Lean_Compiler_LCNF_Pass_init___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_init___closed__1_value: leanh::LeanStringObject<5> =
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
        m_data: [105, 110, 105, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_Pass_init___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_init___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__1_value)
                as *mut leanh::LeanObject,
            15209775132330820936 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_init___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_init___closed__3_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__0_value)
                as *mut leanh::LeanObject,
            65536 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_init___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Pass_init: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_init___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_trace___closed__0_value: leanh::LeanClosureObject<0> =
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
        m_fun: l_Lean_Compiler_LCNF_Pass_trace___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 6,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_Pass_trace___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_trace___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_trace___closed__1_value: leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Pass_trace___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_trace___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_trace___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_trace___closed__1_value)
                as *mut leanh::LeanObject,
            14231257465488249300 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_trace___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_trace___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveBase___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Pass_saveBase___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Pass_saveBase___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 97, 118, 101, 66, 97, 115, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveBase___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveBase___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value)
                as *mut leanh::LeanObject,
            6295427711831148428 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveBase___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveBase___closed__3_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__0_value)
                as *mut leanh::LeanObject,
            65536 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveBase___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Pass_saveBase: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveMono___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Pass_saveMono___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Pass_saveMono___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value: leanh::LeanStringObject<9> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [115, 97, 118, 101, 77, 111, 110, 111, 0],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveMono___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveMono___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value)
                as *mut leanh::LeanObject,
            13280578357788257162 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveMono___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveMono___closed__3_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__0_value)
                as *mut leanh::LeanObject,
            65793 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveMono___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Pass_saveMono: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__3_value)
        as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0_value: leanh::LeanClosureObject<
    0,
> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 6,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value: leanh::LeanStringObject<
    11,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 97, 118, 101, 73, 109, 112, 117, 114, 101, 0],
};
static mut l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value)
                as *mut leanh::LeanObject,
            15070305261751155215 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3_value: leanh::LeanCtorObject<4> =
    leanh::LeanCtorObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<leanh::LeanObject>()
                + core::mem::size_of::<*mut leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__2_value)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__0_value)
                as *mut leanh::LeanObject,
            66050 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_Pass_saveImpure: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_builtinPassManager___closed__1_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16777216 as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinPassManager___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_builtinPassManager___closed__6_value: leanh::LeanCtorObject<
    1,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [16843009 as *mut leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_builtinPassManager___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__8_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__10_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__10: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__12_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__12: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__14_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__14: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__16_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__16: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__18_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__18: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__20_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__20: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__22_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__22: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__25_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__25: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__27_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__27: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__29_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__29: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_builtinPassManager___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_builtinPassManager: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanStringObject<15> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [112, 97, 115, 115, 77, 97, 110, 97, 103, 101, 114, 69, 120, 116, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10566170867809201782 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 1, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_passManagerExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [67, 97, 110, 110, 111, 116, 32, 97, 100, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2_value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [93, 96, 58, 32, 68, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4_value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [96, 32, 104, 97, 115, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [10, 98, 117, 116, 32, 96, 91, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8_value: leanh::LeanStringObject<45> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [93, 96, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 97, 100, 100, 101, 100, 32, 116, 111, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 115, 32, 111, 102, 32, 116, 121, 112, 101, 0]};
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0_value: leanh::LeanStringObject<24> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 24, m_capacity: 24, m_length: 23, m_data: [65, 32, 112, 114, 105, 118, 97, 116, 101, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2_value: leanh::LeanStringObject<79> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 79, m_capacity: 79, m_length: 78, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 116, 104, 101, 32, 99, 117, 114, 114, 101, 110, 116, 32, 109, 111, 100, 117, 108, 101, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4_value: leanh::LeanStringObject<23> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 23, m_capacity: 23, m_length: 22, m_data: [65, 32, 112, 117, 98, 108, 105, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6_value: leanh::LeanStringObject<68> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 68, m_capacity: 68, m_length: 67, m_data: [96, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 105, 115, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 112, 114, 105, 118, 97, 116, 101, 108, 121, 59, 32, 99, 111, 110, 115, 105, 100, 101, 114, 32, 97, 100, 100, 105, 110, 103, 32, 96, 112, 117, 98, 108, 105, 99, 32, 105, 109, 112, 111, 114, 116, 32, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [96, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [96, 32, 40, 102, 114, 111, 109, 32, 96, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [96, 41, 32, 101, 120, 105, 115, 116, 115, 32, 98, 117, 116, 32, 119, 111, 117, 108, 100, 32, 110, 101, 101, 100, 32, 116, 111, 32, 98, 101, 32, 112, 117, 98, 108, 105, 99, 32, 116, 111, 32, 97, 99, 99, 101, 115, 115, 32, 104, 101, 114, 101, 46, 0]};
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12_value) as *mut leanh::LeanObject;
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0_value: leanh::LeanStringObject<19> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 19, m_capacity: 19, m_length: 18, m_data: [85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [96, 0]};
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_addPass___closed__0_value: leanh::LeanStringObject<6> =
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
        m_data: [99, 112, 97, 115, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_addPass___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_addPass___closed__1_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__0_value)
                as *mut leanh::LeanObject,
            3403072253734312453 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_addPass___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_addPass___closed__2_value: leanh::LeanStringObject<14> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            80, 97, 115, 115, 73, 110, 115, 116, 97, 108, 108, 101, 114, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_addPass___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__2_value)
        as *mut leanh::LeanObject;
static l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,8543197020067251012 as *mut leanh::LeanObject] };
static l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13270991020494245093 as *mut leanh::LeanObject] };
pub static l_Lean_Compiler_LCNF_addPass___closed__3_value: leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__3_value_aux_2)
                as *mut leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__2_value)
                as *mut leanh::LeanObject,
            15533063730467035502 as *mut leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_addPass___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_addPass___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_addPass___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [73, 110, 118, 97, 108, 105, 100, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 32, 115, 99, 111, 112, 101, 58, 32, 65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [93, 96, 32, 109, 117, 115, 116, 32, 98, 101, 32, 103, 108, 111, 98, 97, 108, 44, 32, 110, 111, 116, 32, 96, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [103, 108, 111, 98, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [108, 111, 99, 97, 108, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5_value) as *mut leanh::LeanObject;
pub static l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [115, 99, 111, 112, 101, 100, 0]};
static mut l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<13> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 13, m_capacity: 13, m_length: 12, m_data: [65, 116, 116, 114, 105, 98, 117, 116, 101, 32, 96, 91, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<20> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 20, m_capacity: 20, m_length: 19, m_data: [93, 96, 32, 99, 97, 110, 110, 111, 116, 32, 98, 101, 32, 101, 114, 97, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1501781890156459336 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4203849195465939425 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [80, 97, 115, 115, 101, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,17996924070737595067 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,7675110797189797830 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2423708163239028943 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12211570766922508033 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15960596544129868516 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10623933460421997313 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6958703827996757580 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2976284203647212237 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,4473104031757603883 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,13995198488201007190 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9584598005026504984 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 7, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 5, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l_Lean_Compiler_LCNF_addPass___closed__1_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value: leanh::LeanStringObject<39> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 39, m_capacity: 39, m_length: 38, m_data: [99, 111, 109, 112, 105, 108, 101, 114, 32, 112, 97, 115, 115, 101, 115, 32, 102, 111, 114, 32, 116, 104, 101, 32, 99, 111, 100, 101, 32, 103, 101, 110, 101, 114, 97, 116, 111, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveBase___closed__1_value) as *mut leanh::LeanObject,3232676647644034082 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 1750802602 as usize) << 1) | 1) as *mut leanh::LeanObject,9945461289250218406 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,16850540996416188641 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5448154622094748505 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,3914290436335877764 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveMono___closed__1_value) as *mut leanh::LeanObject,4830016804103126644 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_saveImpure___closed__1_value) as *mut leanh::LeanObject,17749604174927484793 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__value) as *mut leanh::LeanObject,2042452093243897853 as *mut leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Pass_trace___closed__1_value) as *mut leanh::LeanObject,16614278374364143338 as *mut leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(
    mut v_as_1575_: *mut leanh::LeanObject,
    mut v_i_1576_: usize,
    mut v_stop_1577_: usize,
    mut v_b_1578_: *mut leanh::LeanObject,
    mut v___y_1579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1581_: u8 = 0;
    let mut v___x_1582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1585_: usize = 0;
    let mut v___x_1586_: usize = 0;
    let mut v___x_1588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1581_ = lean_usize_dec_eq(v_i_1576_, v_stop_1577_);
                if v___x_1581_ == 0 {
                    v___x_1582_ = lean_array_uget_borrowed(v_as_1575_, v_i_1576_);
                    leanh::lean_inc(v___x_1582_);
                    v___x_1583_ =
                        l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v___x_1582_, v___y_1579_);
                    if leanh::lean_obj_tag(v___x_1583_) == 0 {
                        v_a_1584_ = leanh::lean_ctor_get(v___x_1583_, 0);
                        leanh::lean_inc(v_a_1584_);
                        leanh::lean_dec_ref_known(v___x_1583_, 1);
                        v___x_1585_ = 1usize;
                        v___x_1586_ = lean_usize_add(v_i_1576_, v___x_1585_);
                        v_i_1576_ = v___x_1586_;
                        v_b_1578_ = v_a_1584_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_1583_;
                    }
                } else {
                    v___x_1588_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1588_, 0, v_b_1578_);
                    return v___x_1588_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg___boxed(
    mut v_as_1589_: *mut leanh::LeanObject,
    mut v_i_1590_: *mut leanh::LeanObject,
    mut v_stop_1591_: *mut leanh::LeanObject,
    mut v_b_1592_: *mut leanh::LeanObject,
    mut v___y_1593_: *mut leanh::LeanObject,
    mut v___y_1594_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1595_: usize = 0;
    let mut v_stop_boxed_1596_: usize = 0;
    let mut v_res_1597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1595_ = leanh::lean_unbox_usize(v_i_1590_);
    leanh::lean_dec(v_i_1590_);
    v_stop_boxed_1596_ = leanh::lean_unbox_usize(v_stop_1591_);
    leanh::lean_dec(v_stop_1591_);
    v_res_1597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_as_1589_, v_i_boxed_1595_, v_stop_boxed_1596_, v_b_1592_, v___y_1593_);
    leanh::lean_dec(v___y_1593_);
    leanh::lean_dec_ref(v_as_1589_);
    return v_res_1597_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_init___lam__0(
    mut v___x_1598_: *mut leanh::LeanObject,
    mut v_decls_1599_: *mut leanh::LeanObject,
    mut v___y_1600_: *mut leanh::LeanObject,
    mut v___y_1601_: *mut leanh::LeanObject,
    mut v___y_1602_: *mut leanh::LeanObject,
    mut v___y_1603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_1606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1609_: u8 = 0;
    let mut v___x_1611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1613_: u8 = 0;
    let mut v_unused_1614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1618_: u8 = 0;
    let mut v___x_1620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1622_: u8 = 0;
    let mut v___x_1623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1624_: u8 = 0;
    let mut v___x_1625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: u8 = 0;
    let mut v___x_1628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: usize = 0;
    let mut v___x_1630_: usize = 0;
    let mut v___x_1631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1632_: usize = 0;
    let mut v___x_1633_: usize = 0;
    let mut v___x_1634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1623_ = lean_array_get_size(v_decls_1599_);
                v___x_1624_ = lean_nat_dec_lt(v___x_1598_, v___x_1623_);
                if v___x_1624_ == 0 {
                    v___x_1625_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1625_, 0, v_decls_1599_);
                    return v___x_1625_;
                } else {
                    v___x_1626_ = leanh::lean_box(0);
                    v___x_1627_ = lean_nat_dec_le(v___x_1623_, v___x_1623_);
                    if v___x_1627_ == 0 {
                        if v___x_1624_ == 0 {
                            v___x_1628_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_1628_, 0, v_decls_1599_);
                            return v___x_1628_;
                        } else {
                            v___x_1629_ = 0usize;
                            v___x_1630_ = lean_usize_of_nat(v___x_1623_);
                            v___x_1631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_decls_1599_, v___x_1629_, v___x_1630_, v___x_1626_, v___y_1603_);
                            v___y_1606_ = v___x_1631_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_1632_ = 0usize;
                        v___x_1633_ = lean_usize_of_nat(v___x_1623_);
                        v___x_1634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_decls_1599_, v___x_1632_, v___x_1633_, v___x_1626_, v___y_1603_);
                        v___y_1606_ = v___x_1634_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v___y_1606_) == 0 {
                    v_isSharedCheck_1613_ = (!leanh::lean_is_exclusive(v___y_1606_)) as u8;
                    if v_isSharedCheck_1613_ == 0 {
                        v_unused_1614_ = leanh::lean_ctor_get(v___y_1606_, 0);
                        leanh::lean_dec(v_unused_1614_);
                        v___x_1608_ = v___y_1606_;
                        v_isShared_1609_ = v_isSharedCheck_1613_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec(v___y_1606_);
                        v___x_1608_ = leanh::lean_box(0);
                        v_isShared_1609_ = v_isSharedCheck_1613_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_decls_1599_);
                    v_a_1615_ = leanh::lean_ctor_get(v___y_1606_, 0);
                    v_isSharedCheck_1622_ = (!leanh::lean_is_exclusive(v___y_1606_)) as u8;
                    if v_isSharedCheck_1622_ == 0 {
                        v___x_1617_ = v___y_1606_;
                        v_isShared_1618_ = v_isSharedCheck_1622_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_1615_);
                        leanh::lean_dec(v___y_1606_);
                        v___x_1617_ = leanh::lean_box(0);
                        v_isShared_1618_ = v_isSharedCheck_1622_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1609_ == 0 {
                    leanh::lean_ctor_set(v___x_1608_, 0, v_decls_1599_);
                    v___x_1611_ = v___x_1608_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1612_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1612_, 0, v_decls_1599_);
                    v___x_1611_ = v_reuseFailAlloc_1612_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1611_;
            }
            4 => {
                if v_isShared_1618_ == 0 {
                    v___x_1620_ = v___x_1617_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1621_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1621_, 0, v_a_1615_);
                    v___x_1620_ = v_reuseFailAlloc_1621_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1620_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_init___lam__0___boxed(
    mut v___x_1635_: *mut leanh::LeanObject,
    mut v_decls_1636_: *mut leanh::LeanObject,
    mut v___y_1637_: *mut leanh::LeanObject,
    mut v___y_1638_: *mut leanh::LeanObject,
    mut v___y_1639_: *mut leanh::LeanObject,
    mut v___y_1640_: *mut leanh::LeanObject,
    mut v___y_1641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1642_ = l_Lean_Compiler_LCNF_Pass_init___lam__0(
        v___x_1635_,
        v_decls_1636_,
        v___y_1637_,
        v___y_1638_,
        v___y_1639_,
        v___y_1640_,
    );
    leanh::lean_dec(v___y_1640_);
    leanh::lean_dec_ref(v___y_1639_);
    leanh::lean_dec(v___y_1638_);
    leanh::lean_dec_ref(v___y_1637_);
    leanh::lean_dec(v___x_1635_);
    return v_res_1642_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0(
    mut v_as_1655_: *mut leanh::LeanObject,
    mut v_i_1656_: usize,
    mut v_stop_1657_: usize,
    mut v_b_1658_: *mut leanh::LeanObject,
    mut v___y_1659_: *mut leanh::LeanObject,
    mut v___y_1660_: *mut leanh::LeanObject,
    mut v___y_1661_: *mut leanh::LeanObject,
    mut v___y_1662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1664_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___redArg(v_as_1655_, v_i_1656_, v_stop_1657_, v_b_1658_, v___y_1662_);
    return v___x_1664_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0___boxed(
    mut v_as_1665_: *mut leanh::LeanObject,
    mut v_i_1666_: *mut leanh::LeanObject,
    mut v_stop_1667_: *mut leanh::LeanObject,
    mut v_b_1668_: *mut leanh::LeanObject,
    mut v___y_1669_: *mut leanh::LeanObject,
    mut v___y_1670_: *mut leanh::LeanObject,
    mut v___y_1671_: *mut leanh::LeanObject,
    mut v___y_1672_: *mut leanh::LeanObject,
    mut v___y_1673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_1674_: usize = 0;
    let mut v_stop_boxed_1675_: usize = 0;
    let mut v_res_1676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_1674_ = leanh::lean_unbox_usize(v_i_1666_);
    leanh::lean_dec(v_i_1666_);
    v_stop_boxed_1675_ = leanh::lean_unbox_usize(v_stop_1667_);
    leanh::lean_dec(v_stop_1667_);
    v_res_1676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Pass_init_spec__0(v_as_1665_, v_i_boxed_1674_, v_stop_boxed_1675_, v_b_1668_, v___y_1669_, v___y_1670_, v___y_1671_, v___y_1672_);
    leanh::lean_dec(v___y_1672_);
    leanh::lean_dec_ref(v___y_1671_);
    leanh::lean_dec(v___y_1670_);
    leanh::lean_dec_ref(v___y_1669_);
    leanh::lean_dec_ref(v_as_1665_);
    return v_res_1676_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_trace___lam__0(
    mut v___y_1677_: *mut leanh::LeanObject,
    mut v___y_1678_: *mut leanh::LeanObject,
    mut v___y_1679_: *mut leanh::LeanObject,
    mut v___y_1680_: *mut leanh::LeanObject,
    mut v___y_1681_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1683_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1683_, 0, v___y_1677_);
    return v___x_1683_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_trace___lam__0___boxed(
    mut v___y_1684_: *mut leanh::LeanObject,
    mut v___y_1685_: *mut leanh::LeanObject,
    mut v___y_1686_: *mut leanh::LeanObject,
    mut v___y_1687_: *mut leanh::LeanObject,
    mut v___y_1688_: *mut leanh::LeanObject,
    mut v___y_1689_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1690_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1690_ = l_Lean_Compiler_LCNF_Pass_trace___lam__0(
        v___y_1684_,
        v___y_1685_,
        v___y_1686_,
        v___y_1687_,
        v___y_1688_,
    );
    leanh::lean_dec(v___y_1688_);
    leanh::lean_dec_ref(v___y_1687_);
    leanh::lean_dec(v___y_1686_);
    leanh::lean_dec_ref(v___y_1685_);
    return v_res_1690_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_trace(
    mut v_phase_1695_: u8,
) -> *mut leanh::LeanObject {
    let mut v___f_1696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1698_: u8 = 0;
    let mut v___x_1699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_1696_ = l_Lean_Compiler_LCNF_Pass_trace___closed__0;
    v___x_1697_ = leanh::lean_unsigned_to_nat(0);
    v___x_1698_ = 0;
    v___x_1699_ = l_Lean_Compiler_LCNF_Pass_trace___closed__2;
    v___x_1700_ = leanh::lean_alloc_ctor(0, 3, (3) as u32);
    leanh::lean_ctor_set(v___x_1700_, 0, v___x_1697_);
    leanh::lean_ctor_set(v___x_1700_, 1, v___x_1699_);
    leanh::lean_ctor_set(v___x_1700_, 2, v___f_1696_);
    leanh::lean_ctor_set_uint8(
        v___x_1700_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v_phase_1695_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1700_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 1) as u32,
        v_phase_1695_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_1700_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 2) as u32,
        v___x_1698_,
    );
    return v___x_1700_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_trace___boxed(
    mut v_phase_1701_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_1702_: u8 = 0;
    let mut v_res_1703_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1702_ = (leanh::lean_unbox(v_phase_1701_) as u8);
    v_res_1703_ = l_Lean_Compiler_LCNF_Pass_trace(v_phase_boxed_1702_);
    return v_res_1703_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(
    mut v_sz_1704_: usize,
    mut v_i_1705_: usize,
    mut v_bs_1706_: *mut leanh::LeanObject,
    mut v___y_1707_: *mut leanh::LeanObject,
    mut v___y_1708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1710_: u8 = 0;
    let mut v___x_1711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1717_: usize = 0;
    let mut v___x_1718_: usize = 0;
    let mut v___x_1719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1721_: u8 = 0;
    let mut v___x_1722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1728_: u8 = 0;
    let mut v___x_1730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1732_: u8 = 0;
    let mut v_a_1733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1737_: u8 = 0;
    let mut v___x_1739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1741_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1710_ = lean_usize_dec_lt(v_i_1705_, v_sz_1704_);
                if v___x_1710_ == 0 {
                    v___x_1711_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1711_, 0, v_bs_1706_);
                    return v___x_1711_;
                } else {
                    v_v_1712_ = lean_array_uget(v_bs_1706_, v_i_1705_);
                    v___x_1713_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1714_ = lean_array_uset(v_bs_1706_, v_i_1705_, v___x_1713_);
                    v___x_1721_ = 0;
                    leanh::lean_inc(v_v_1712_);
                    v___x_1722_ = l_Lean_Compiler_LCNF_normalizeFVarIds(
                        v___x_1721_,
                        v_v_1712_,
                        v___y_1707_,
                        v___y_1708_,
                    );
                    if leanh::lean_obj_tag(v___x_1722_) == 0 {
                        v_a_1723_ = leanh::lean_ctor_get(v___x_1722_, 0);
                        leanh::lean_inc(v_a_1723_);
                        leanh::lean_dec_ref_known(v___x_1722_, 1);
                        v___x_1724_ =
                            l_Lean_Compiler_LCNF_Decl_saveBase___redArg(v_a_1723_, v___y_1708_);
                        if leanh::lean_obj_tag(v___x_1724_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1724_, 1);
                            v_a_1716_ = v_v_1712_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_bs_x27_1714_);
                            leanh::lean_dec(v_v_1712_);
                            v_a_1725_ = leanh::lean_ctor_get(v___x_1724_, 0);
                            v_isSharedCheck_1732_ =
                                (!leanh::lean_is_exclusive(v___x_1724_)) as u8;
                            if v_isSharedCheck_1732_ == 0 {
                                v___x_1727_ = v___x_1724_;
                                v_isShared_1728_ = v_isSharedCheck_1732_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1725_);
                                leanh::lean_dec(v___x_1724_);
                                v___x_1727_ = leanh::lean_box(0);
                                v_isShared_1728_ = v_isSharedCheck_1732_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_1712_);
                        if leanh::lean_obj_tag(v___x_1722_) == 0 {
                            v_a_1733_ = leanh::lean_ctor_get(v___x_1722_, 0);
                            leanh::lean_inc(v_a_1733_);
                            leanh::lean_dec_ref_known(v___x_1722_, 1);
                            v_a_1716_ = v_a_1733_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_bs_x27_1714_);
                            v_a_1734_ = leanh::lean_ctor_get(v___x_1722_, 0);
                            v_isSharedCheck_1741_ =
                                (!leanh::lean_is_exclusive(v___x_1722_)) as u8;
                            if v_isSharedCheck_1741_ == 0 {
                                v___x_1736_ = v___x_1722_;
                                v_isShared_1737_ = v_isSharedCheck_1741_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1734_);
                                leanh::lean_dec(v___x_1722_);
                                v___x_1736_ = leanh::lean_box(0);
                                v_isShared_1737_ = v_isSharedCheck_1741_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1717_ = 1usize;
                v___x_1718_ = lean_usize_add(v_i_1705_, v___x_1717_);
                v___x_1719_ = lean_array_uset(v_bs_x27_1714_, v_i_1705_, v_a_1716_);
                v_i_1705_ = v___x_1718_;
                v_bs_1706_ = v___x_1719_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1728_ == 0 {
                    v___x_1730_ = v___x_1727_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1731_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1731_, 0, v_a_1725_);
                    v___x_1730_ = v_reuseFailAlloc_1731_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1730_;
            }
            4 => {
                if v_isShared_1737_ == 0 {
                    v___x_1739_ = v___x_1736_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1740_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_a_1734_);
                    v___x_1739_ = v_reuseFailAlloc_1740_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1739_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg___boxed(
    mut v_sz_1742_: *mut leanh::LeanObject,
    mut v_i_1743_: *mut leanh::LeanObject,
    mut v_bs_1744_: *mut leanh::LeanObject,
    mut v___y_1745_: *mut leanh::LeanObject,
    mut v___y_1746_: *mut leanh::LeanObject,
    mut v___y_1747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1748_: usize = 0;
    let mut v_i_boxed_1749_: usize = 0;
    let mut v_res_1750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1748_ = leanh::lean_unbox_usize(v_sz_1742_);
    leanh::lean_dec(v_sz_1742_);
    v_i_boxed_1749_ = leanh::lean_unbox_usize(v_i_1743_);
    leanh::lean_dec(v_i_1743_);
    v_res_1750_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_boxed_1748_, v_i_boxed_1749_, v_bs_1744_, v___y_1745_, v___y_1746_);
    leanh::lean_dec(v___y_1746_);
    leanh::lean_dec_ref(v___y_1745_);
    return v_res_1750_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_saveBase___lam__0(
    mut v_decls_1751_: *mut leanh::LeanObject,
    mut v___y_1752_: *mut leanh::LeanObject,
    mut v___y_1753_: *mut leanh::LeanObject,
    mut v___y_1754_: *mut leanh::LeanObject,
    mut v___y_1755_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1757_: usize = 0;
    let mut v___x_1758_: usize = 0;
    let mut v___x_1759_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1757_ = lean_array_size(v_decls_1751_);
    v___x_1758_ = 0usize;
    v___x_1759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_1757_, v___x_1758_, v_decls_1751_, v___y_1754_, v___y_1755_);
    return v___x_1759_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_saveBase___lam__0___boxed(
    mut v_decls_1760_: *mut leanh::LeanObject,
    mut v___y_1761_: *mut leanh::LeanObject,
    mut v___y_1762_: *mut leanh::LeanObject,
    mut v___y_1763_: *mut leanh::LeanObject,
    mut v___y_1764_: *mut leanh::LeanObject,
    mut v___y_1765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1766_ = l_Lean_Compiler_LCNF_Pass_saveBase___lam__0(
        v_decls_1760_,
        v___y_1761_,
        v___y_1762_,
        v___y_1763_,
        v___y_1764_,
    );
    leanh::lean_dec(v___y_1764_);
    leanh::lean_dec_ref(v___y_1763_);
    leanh::lean_dec(v___y_1762_);
    leanh::lean_dec_ref(v___y_1761_);
    return v_res_1766_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0(
    mut v_sz_1778_: usize,
    mut v_i_1779_: usize,
    mut v_bs_1780_: *mut leanh::LeanObject,
    mut v___y_1781_: *mut leanh::LeanObject,
    mut v___y_1782_: *mut leanh::LeanObject,
    mut v___y_1783_: *mut leanh::LeanObject,
    mut v___y_1784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1786_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___redArg(v_sz_1778_, v_i_1779_, v_bs_1780_, v___y_1783_, v___y_1784_);
    return v___x_1786_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0___boxed(
    mut v_sz_1787_: *mut leanh::LeanObject,
    mut v_i_1788_: *mut leanh::LeanObject,
    mut v_bs_1789_: *mut leanh::LeanObject,
    mut v___y_1790_: *mut leanh::LeanObject,
    mut v___y_1791_: *mut leanh::LeanObject,
    mut v___y_1792_: *mut leanh::LeanObject,
    mut v___y_1793_: *mut leanh::LeanObject,
    mut v___y_1794_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1795_: usize = 0;
    let mut v_i_boxed_1796_: usize = 0;
    let mut v_res_1797_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1795_ = leanh::lean_unbox_usize(v_sz_1787_);
    leanh::lean_dec(v_sz_1787_);
    v_i_boxed_1796_ = leanh::lean_unbox_usize(v_i_1788_);
    leanh::lean_dec(v_i_1788_);
    v_res_1797_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveBase_spec__0(v_sz_boxed_1795_, v_i_boxed_1796_, v_bs_1789_, v___y_1790_, v___y_1791_, v___y_1792_, v___y_1793_);
    leanh::lean_dec(v___y_1793_);
    leanh::lean_dec_ref(v___y_1792_);
    leanh::lean_dec(v___y_1791_);
    leanh::lean_dec_ref(v___y_1790_);
    return v_res_1797_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(
    mut v_sz_1798_: usize,
    mut v_i_1799_: usize,
    mut v_bs_1800_: *mut leanh::LeanObject,
    mut v___y_1801_: *mut leanh::LeanObject,
    mut v___y_1802_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1804_: u8 = 0;
    let mut v___x_1805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1811_: usize = 0;
    let mut v___x_1812_: usize = 0;
    let mut v___x_1813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1822_: u8 = 0;
    let mut v___x_1824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1826_: u8 = 0;
    let mut v_a_1827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1804_ = lean_usize_dec_lt(v_i_1799_, v_sz_1798_);
                if v___x_1804_ == 0 {
                    v___x_1805_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1805_, 0, v_bs_1800_);
                    return v___x_1805_;
                } else {
                    v_v_1806_ = lean_array_uget(v_bs_1800_, v_i_1799_);
                    v___x_1807_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1808_ = lean_array_uset(v_bs_1800_, v_i_1799_, v___x_1807_);
                    v___x_1815_ = 0;
                    leanh::lean_inc(v_v_1806_);
                    v___x_1816_ = l_Lean_Compiler_LCNF_normalizeFVarIds(
                        v___x_1815_,
                        v_v_1806_,
                        v___y_1801_,
                        v___y_1802_,
                    );
                    if leanh::lean_obj_tag(v___x_1816_) == 0 {
                        v_a_1817_ = leanh::lean_ctor_get(v___x_1816_, 0);
                        leanh::lean_inc(v_a_1817_);
                        leanh::lean_dec_ref_known(v___x_1816_, 1);
                        v___x_1818_ =
                            l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v_a_1817_, v___y_1802_);
                        if leanh::lean_obj_tag(v___x_1818_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1818_, 1);
                            v_a_1810_ = v_v_1806_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_bs_x27_1808_);
                            leanh::lean_dec(v_v_1806_);
                            v_a_1819_ = leanh::lean_ctor_get(v___x_1818_, 0);
                            v_isSharedCheck_1826_ =
                                (!leanh::lean_is_exclusive(v___x_1818_)) as u8;
                            if v_isSharedCheck_1826_ == 0 {
                                v___x_1821_ = v___x_1818_;
                                v_isShared_1822_ = v_isSharedCheck_1826_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1819_);
                                leanh::lean_dec(v___x_1818_);
                                v___x_1821_ = leanh::lean_box(0);
                                v_isShared_1822_ = v_isSharedCheck_1826_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_v_1806_);
                        if leanh::lean_obj_tag(v___x_1816_) == 0 {
                            v_a_1827_ = leanh::lean_ctor_get(v___x_1816_, 0);
                            leanh::lean_inc(v_a_1827_);
                            leanh::lean_dec_ref_known(v___x_1816_, 1);
                            v_a_1810_ = v_a_1827_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_bs_x27_1808_);
                            v_a_1828_ = leanh::lean_ctor_get(v___x_1816_, 0);
                            v_isSharedCheck_1835_ =
                                (!leanh::lean_is_exclusive(v___x_1816_)) as u8;
                            if v_isSharedCheck_1835_ == 0 {
                                v___x_1830_ = v___x_1816_;
                                v_isShared_1831_ = v_isSharedCheck_1835_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1828_);
                                leanh::lean_dec(v___x_1816_);
                                v___x_1830_ = leanh::lean_box(0);
                                v_isShared_1831_ = v_isSharedCheck_1835_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1811_ = 1usize;
                v___x_1812_ = lean_usize_add(v_i_1799_, v___x_1811_);
                v___x_1813_ = lean_array_uset(v_bs_x27_1808_, v_i_1799_, v_a_1810_);
                v_i_1799_ = v___x_1812_;
                v_bs_1800_ = v___x_1813_;
                state = 0;
                continue;
            }
            2 => {
                if v_isShared_1822_ == 0 {
                    v___x_1824_ = v___x_1821_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1825_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
                    v___x_1824_ = v_reuseFailAlloc_1825_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1824_;
            }
            4 => {
                if v_isShared_1831_ == 0 {
                    v___x_1833_ = v___x_1830_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
                    v___x_1833_ = v_reuseFailAlloc_1834_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1833_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg___boxed(
    mut v_sz_1836_: *mut leanh::LeanObject,
    mut v_i_1837_: *mut leanh::LeanObject,
    mut v_bs_1838_: *mut leanh::LeanObject,
    mut v___y_1839_: *mut leanh::LeanObject,
    mut v___y_1840_: *mut leanh::LeanObject,
    mut v___y_1841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1842_: usize = 0;
    let mut v_i_boxed_1843_: usize = 0;
    let mut v_res_1844_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1842_ = leanh::lean_unbox_usize(v_sz_1836_);
    leanh::lean_dec(v_sz_1836_);
    v_i_boxed_1843_ = leanh::lean_unbox_usize(v_i_1837_);
    leanh::lean_dec(v_i_1837_);
    v_res_1844_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_boxed_1842_, v_i_boxed_1843_, v_bs_1838_, v___y_1839_, v___y_1840_);
    leanh::lean_dec(v___y_1840_);
    leanh::lean_dec_ref(v___y_1839_);
    return v_res_1844_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_saveMono___lam__0(
    mut v_decls_1845_: *mut leanh::LeanObject,
    mut v___y_1846_: *mut leanh::LeanObject,
    mut v___y_1847_: *mut leanh::LeanObject,
    mut v___y_1848_: *mut leanh::LeanObject,
    mut v___y_1849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1851_: usize = 0;
    let mut v___x_1852_: usize = 0;
    let mut v___x_1853_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1851_ = lean_array_size(v_decls_1845_);
    v___x_1852_ = 0usize;
    v___x_1853_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_1851_, v___x_1852_, v_decls_1845_, v___y_1848_, v___y_1849_);
    return v___x_1853_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_saveMono___lam__0___boxed(
    mut v_decls_1854_: *mut leanh::LeanObject,
    mut v___y_1855_: *mut leanh::LeanObject,
    mut v___y_1856_: *mut leanh::LeanObject,
    mut v___y_1857_: *mut leanh::LeanObject,
    mut v___y_1858_: *mut leanh::LeanObject,
    mut v___y_1859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1860_ = l_Lean_Compiler_LCNF_Pass_saveMono___lam__0(
        v_decls_1854_,
        v___y_1855_,
        v___y_1856_,
        v___y_1857_,
        v___y_1858_,
    );
    leanh::lean_dec(v___y_1858_);
    leanh::lean_dec_ref(v___y_1857_);
    leanh::lean_dec(v___y_1856_);
    leanh::lean_dec_ref(v___y_1855_);
    return v_res_1860_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0(
    mut v_sz_1872_: usize,
    mut v_i_1873_: usize,
    mut v_bs_1874_: *mut leanh::LeanObject,
    mut v___y_1875_: *mut leanh::LeanObject,
    mut v___y_1876_: *mut leanh::LeanObject,
    mut v___y_1877_: *mut leanh::LeanObject,
    mut v___y_1878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1880_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1880_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___redArg(v_sz_1872_, v_i_1873_, v_bs_1874_, v___y_1877_, v___y_1878_);
    return v___x_1880_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0___boxed(
    mut v_sz_1881_: *mut leanh::LeanObject,
    mut v_i_1882_: *mut leanh::LeanObject,
    mut v_bs_1883_: *mut leanh::LeanObject,
    mut v___y_1884_: *mut leanh::LeanObject,
    mut v___y_1885_: *mut leanh::LeanObject,
    mut v___y_1886_: *mut leanh::LeanObject,
    mut v___y_1887_: *mut leanh::LeanObject,
    mut v___y_1888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1889_: usize = 0;
    let mut v_i_boxed_1890_: usize = 0;
    let mut v_res_1891_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1889_ = leanh::lean_unbox_usize(v_sz_1881_);
    leanh::lean_dec(v_sz_1881_);
    v_i_boxed_1890_ = leanh::lean_unbox_usize(v_i_1882_);
    leanh::lean_dec(v_i_1882_);
    v_res_1891_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveMono_spec__0(v_sz_boxed_1889_, v_i_boxed_1890_, v_bs_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_);
    leanh::lean_dec(v___y_1887_);
    leanh::lean_dec_ref(v___y_1886_);
    leanh::lean_dec(v___y_1885_);
    leanh::lean_dec_ref(v___y_1884_);
    return v_res_1891_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_1892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1892_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_1892_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_1893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1893_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__0);
    v___x_1894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_1894_, 0, v___x_1893_);
    return v___x_1894_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_1895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1896_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_1895_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__1);
    v___x_1896_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_1896_, 0, v___x_1895_);
    leanh::lean_ctor_set(v___x_1896_, 1, v___x_1895_);
    return v___x_1896_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(
    mut v_sz_1897_: usize,
    mut v_i_1898_: usize,
    mut v_bs_1899_: *mut leanh::LeanObject,
    mut v___y_1900_: *mut leanh::LeanObject,
    mut v___y_1901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_1903_: u8 = 0;
    let mut v___x_1904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_1905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_1907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: usize = 0;
    let mut v___x_1911_: usize = 0;
    let mut v___x_1912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: u8 = 0;
    let mut v___x_1915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_1920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_1921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_1922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_1923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_1924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_1925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_1926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_1927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1930_: u8 = 0;
    let mut v_name_1931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1938_: u8 = 0;
    let mut v_unused_1939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1943_: u8 = 0;
    let mut v___x_1945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1947_: u8 = 0;
    let mut v_a_1948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1952_: u8 = 0;
    let mut v___x_1954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1956_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1903_ = lean_usize_dec_lt(v_i_1898_, v_sz_1897_);
                if v___x_1903_ == 0 {
                    v___x_1904_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_1904_, 0, v_bs_1899_);
                    return v___x_1904_;
                } else {
                    v_v_1905_ = lean_array_uget(v_bs_1899_, v_i_1898_);
                    v___x_1906_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_1907_ = lean_array_uset(v_bs_1899_, v_i_1898_, v___x_1906_);
                    v___x_1914_ = 1;
                    v___x_1915_ = l_Lean_Compiler_LCNF_normalizeFVarIds(
                        v___x_1914_,
                        v_v_1905_,
                        v___y_1900_,
                        v___y_1901_,
                    );
                    if leanh::lean_obj_tag(v___x_1915_) == 0 {
                        v_a_1916_ = leanh::lean_ctor_get(v___x_1915_, 0);
                        leanh::lean_inc_n(v_a_1916_, 2);
                        leanh::lean_dec_ref_known(v___x_1915_, 1);
                        v___x_1917_ =
                            l_Lean_Compiler_LCNF_Decl_saveImpure___redArg(v_a_1916_, v___y_1901_);
                        if leanh::lean_obj_tag(v___x_1917_) == 0 {
                            leanh::lean_dec_ref_known(v___x_1917_, 1);
                            v___x_1918_ = lean_st_ref_take(v___y_1901_);
                            v_toSignature_1919_ = leanh::lean_ctor_get(v_a_1916_, 0);
                            v_env_1920_ = leanh::lean_ctor_get(v___x_1918_, 0);
                            v_nextMacroScope_1921_ = leanh::lean_ctor_get(v___x_1918_, 1);
                            v_ngen_1922_ = leanh::lean_ctor_get(v___x_1918_, 2);
                            v_auxDeclNGen_1923_ = leanh::lean_ctor_get(v___x_1918_, 3);
                            v_traceState_1924_ = leanh::lean_ctor_get(v___x_1918_, 4);
                            v_messages_1925_ = leanh::lean_ctor_get(v___x_1918_, 6);
                            v_infoState_1926_ = leanh::lean_ctor_get(v___x_1918_, 7);
                            v_snapshotTasks_1927_ = leanh::lean_ctor_get(v___x_1918_, 8);
                            v_isSharedCheck_1938_ =
                                (!leanh::lean_is_exclusive(v___x_1918_)) as u8;
                            if v_isSharedCheck_1938_ == 0 {
                                v_unused_1939_ = leanh::lean_ctor_get(v___x_1918_, 5);
                                leanh::lean_dec(v_unused_1939_);
                                v___x_1929_ = v___x_1918_;
                                v_isShared_1930_ = v_isSharedCheck_1938_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_snapshotTasks_1927_);
                                leanh::lean_inc(v_infoState_1926_);
                                leanh::lean_inc(v_messages_1925_);
                                leanh::lean_inc(v_traceState_1924_);
                                leanh::lean_inc(v_auxDeclNGen_1923_);
                                leanh::lean_inc(v_ngen_1922_);
                                leanh::lean_inc(v_nextMacroScope_1921_);
                                leanh::lean_inc(v_env_1920_);
                                leanh::lean_dec(v___x_1918_);
                                v___x_1929_ = leanh::lean_box(0);
                                v_isShared_1930_ = v_isSharedCheck_1938_;
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_1916_);
                            leanh::lean_dec_ref(v_bs_x27_1907_);
                            v_a_1940_ = leanh::lean_ctor_get(v___x_1917_, 0);
                            v_isSharedCheck_1947_ =
                                (!leanh::lean_is_exclusive(v___x_1917_)) as u8;
                            if v_isSharedCheck_1947_ == 0 {
                                v___x_1942_ = v___x_1917_;
                                v_isShared_1943_ = v_isSharedCheck_1947_;
                                state = 4;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1940_);
                                leanh::lean_dec(v___x_1917_);
                                v___x_1942_ = leanh::lean_box(0);
                                v_isShared_1943_ = v_isSharedCheck_1947_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        if leanh::lean_obj_tag(v___x_1915_) == 0 {
                            v_a_1948_ = leanh::lean_ctor_get(v___x_1915_, 0);
                            leanh::lean_inc(v_a_1948_);
                            leanh::lean_dec_ref_known(v___x_1915_, 1);
                            v_a_1909_ = v_a_1948_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v_bs_x27_1907_);
                            v_a_1949_ = leanh::lean_ctor_get(v___x_1915_, 0);
                            v_isSharedCheck_1956_ =
                                (!leanh::lean_is_exclusive(v___x_1915_)) as u8;
                            if v_isSharedCheck_1956_ == 0 {
                                v___x_1951_ = v___x_1915_;
                                v_isShared_1952_ = v_isSharedCheck_1956_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_1949_);
                                leanh::lean_dec(v___x_1915_);
                                v___x_1951_ = leanh::lean_box(0);
                                v_isShared_1952_ = v_isSharedCheck_1956_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_1910_ = 1usize;
                v___x_1911_ = lean_usize_add(v_i_1898_, v___x_1910_);
                v___x_1912_ = lean_array_uset(v_bs_x27_1907_, v_i_1898_, v_a_1909_);
                v_i_1898_ = v___x_1911_;
                v_bs_1899_ = v___x_1912_;
                state = 0;
                continue;
            }
            2 => {
                v_name_1931_ = leanh::lean_ctor_get(v_toSignature_1919_, 0);
                leanh::lean_inc(v_name_1931_);
                v___x_1932_ = l_Lean_Compiler_LCNF_recordFinalImpureDecl(v_env_1920_, v_name_1931_);
                v___x_1933_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2);
                if v_isShared_1930_ == 0 {
                    leanh::lean_ctor_set(v___x_1929_, 5, v___x_1933_);
                    leanh::lean_ctor_set(v___x_1929_, 0, v___x_1932_);
                    v___x_1935_ = v___x_1929_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1937_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 0, v___x_1932_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_nextMacroScope_1921_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_ngen_1922_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_auxDeclNGen_1923_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_traceState_1924_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 5, v___x_1933_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 6, v_messages_1925_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 7, v_infoState_1926_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1937_, 8, v_snapshotTasks_1927_);
                    v___x_1935_ = v_reuseFailAlloc_1937_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1936_ = lean_st_ref_set(v___y_1901_, v___x_1935_);
                v_a_1909_ = v_a_1916_;
                state = 1;
                continue;
            }
            4 => {
                if v_isShared_1943_ == 0 {
                    v___x_1945_ = v___x_1942_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1946_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1946_, 0, v_a_1940_);
                    v___x_1945_ = v_reuseFailAlloc_1946_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1945_;
            }
            6 => {
                if v_isShared_1952_ == 0 {
                    v___x_1954_ = v___x_1951_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1955_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_1955_, 0, v_a_1949_);
                    v___x_1954_ = v_reuseFailAlloc_1955_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1954_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___boxed(
    mut v_sz_1957_: *mut leanh::LeanObject,
    mut v_i_1958_: *mut leanh::LeanObject,
    mut v_bs_1959_: *mut leanh::LeanObject,
    mut v___y_1960_: *mut leanh::LeanObject,
    mut v___y_1961_: *mut leanh::LeanObject,
    mut v___y_1962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_1963_: usize = 0;
    let mut v_i_boxed_1964_: usize = 0;
    let mut v_res_1965_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1963_ = leanh::lean_unbox_usize(v_sz_1957_);
    leanh::lean_dec(v_sz_1957_);
    v_i_boxed_1964_ = leanh::lean_unbox_usize(v_i_1958_);
    leanh::lean_dec(v_i_1958_);
    v_res_1965_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_boxed_1963_, v_i_boxed_1964_, v_bs_1959_, v___y_1960_, v___y_1961_);
    leanh::lean_dec(v___y_1961_);
    leanh::lean_dec_ref(v___y_1960_);
    return v_res_1965_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0(
    mut v_decls_1966_: *mut leanh::LeanObject,
    mut v___y_1967_: *mut leanh::LeanObject,
    mut v___y_1968_: *mut leanh::LeanObject,
    mut v___y_1969_: *mut leanh::LeanObject,
    mut v___y_1970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_1972_: usize = 0;
    let mut v___x_1973_: usize = 0;
    let mut v___x_1974_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_1972_ = lean_array_size(v_decls_1966_);
    v___x_1973_ = 0usize;
    v___x_1974_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_1972_, v___x_1973_, v_decls_1966_, v___y_1969_, v___y_1970_);
    return v___x_1974_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0___boxed(
    mut v_decls_1975_: *mut leanh::LeanObject,
    mut v___y_1976_: *mut leanh::LeanObject,
    mut v___y_1977_: *mut leanh::LeanObject,
    mut v___y_1978_: *mut leanh::LeanObject,
    mut v___y_1979_: *mut leanh::LeanObject,
    mut v___y_1980_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_1981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_1981_ = l_Lean_Compiler_LCNF_Pass_saveImpure___lam__0(
        v_decls_1975_,
        v___y_1976_,
        v___y_1977_,
        v___y_1978_,
        v___y_1979_,
    );
    leanh::lean_dec(v___y_1979_);
    leanh::lean_dec_ref(v___y_1978_);
    leanh::lean_dec(v___y_1977_);
    leanh::lean_dec_ref(v___y_1976_);
    return v_res_1981_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0(
    mut v_sz_1993_: usize,
    mut v_i_1994_: usize,
    mut v_bs_1995_: *mut leanh::LeanObject,
    mut v___y_1996_: *mut leanh::LeanObject,
    mut v___y_1997_: *mut leanh::LeanObject,
    mut v___y_1998_: *mut leanh::LeanObject,
    mut v___y_1999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2001_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg(v_sz_1993_, v_i_1994_, v_bs_1995_, v___y_1998_, v___y_1999_);
    return v___x_2001_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___boxed(
    mut v_sz_2002_: *mut leanh::LeanObject,
    mut v_i_2003_: *mut leanh::LeanObject,
    mut v_bs_2004_: *mut leanh::LeanObject,
    mut v___y_2005_: *mut leanh::LeanObject,
    mut v___y_2006_: *mut leanh::LeanObject,
    mut v___y_2007_: *mut leanh::LeanObject,
    mut v___y_2008_: *mut leanh::LeanObject,
    mut v___y_2009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2010_: usize = 0;
    let mut v_i_boxed_2011_: usize = 0;
    let mut v_res_2012_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2010_ = leanh::lean_unbox_usize(v_sz_2002_);
    leanh::lean_dec(v_sz_2002_);
    v_i_boxed_2011_ = leanh::lean_unbox_usize(v_i_2003_);
    leanh::lean_dec(v_i_2003_);
    v_res_2012_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0(v_sz_boxed_2010_, v_i_boxed_2011_, v_bs_2004_, v___y_2005_, v___y_2006_, v___y_2007_, v___y_2008_);
    leanh::lean_dec(v___y_2008_);
    leanh::lean_dec_ref(v___y_2007_);
    leanh::lean_dec(v___y_2006_);
    leanh::lean_dec_ref(v___y_2005_);
    return v_res_2012_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: u8 = 0;
    let mut v___x_2015_: u8 = 0;
    let mut v___x_2016_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2013_ = leanh::lean_unsigned_to_nat(0);
    v___x_2014_ = 0;
    v___x_2015_ = 0;
    v___x_2016_ = l_Lean_Compiler_LCNF_cse(v___x_2015_, v___x_2014_, v___x_2013_);
    return v___x_2016_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2020_: u8 = 0;
    let mut v___x_2021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2020_ = 0;
    v___x_2021_ = leanh::lean_unsigned_to_nat(0);
    v___x_2022_ = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
    v___x_2023_ = l_Lean_Compiler_LCNF_simp(v___x_2022_, v___x_2021_, v___x_2020_);
    return v___x_2023_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2025_: u8 = 0;
    let mut v___x_2026_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2024_ = leanh::lean_unsigned_to_nat(0);
    v___x_2025_ = 0;
    v___x_2026_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_2025_, v___x_2024_);
    return v___x_2026_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2028_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2027_ = leanh::lean_unsigned_to_nat(0);
    v___x_2028_ = l_Lean_Compiler_LCNF_findJoinPoints(v___x_2027_);
    return v___x_2028_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2029_: u8 = 0;
    let mut v___x_2030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2029_ = 0;
    v___x_2030_ = l_Lean_Compiler_LCNF_reduceJpArity(v___x_2029_);
    return v___x_2030_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2033_: u8 = 0;
    let mut v___x_2034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2036_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2033_ = 0;
    v___x_2034_ = leanh::lean_unsigned_to_nat(1);
    v___x_2035_ = l_Lean_Compiler_LCNF_builtinPassManager___closed__6;
    v___x_2036_ = l_Lean_Compiler_LCNF_simp(v___x_2035_, v___x_2034_, v___x_2033_);
    return v___x_2036_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_2037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2038_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2037_ = leanh::lean_unsigned_to_nat(1);
    v___x_2038_ = l_Lean_Compiler_LCNF_findJoinPoints(v___x_2037_);
    return v___x_2038_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2039_: u8 = 0;
    let mut v___x_2040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2042_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2039_ = 0;
    v___x_2040_ = leanh::lean_unsigned_to_nat(2);
    v___x_2041_ = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
    v___x_2042_ = l_Lean_Compiler_LCNF_simp(v___x_2041_, v___x_2040_, v___x_2039_);
    return v___x_2042_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_2043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2044_: u8 = 0;
    let mut v___x_2045_: u8 = 0;
    let mut v___x_2046_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2043_ = leanh::lean_unsigned_to_nat(1);
    v___x_2044_ = 0;
    v___x_2045_ = 0;
    v___x_2046_ = l_Lean_Compiler_LCNF_cse(v___x_2045_, v___x_2044_, v___x_2043_);
    return v___x_2046_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2047_: u8 = 0;
    let mut v___x_2048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2047_ = 0;
    v___x_2048_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_2047_);
    return v___x_2048_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_2049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2086_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2049_ = l_Lean_Compiler_LCNF_toMono;
    v___x_2050_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__11),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__11_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__11,
    );
    v___x_2051_ = l_Lean_Compiler_LCNF_Pass_saveBase;
    v___x_2052_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__10),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__10_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__10,
    );
    v___x_2053_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__9),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__9_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__9,
    );
    v___x_2054_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__8),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__8_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__8,
    );
    v___x_2055_ = l_Lean_Compiler_LCNF_specialize;
    v___x_2056_ = l_Lean_Compiler_LCNF_checkTemplateVisibility;
    v___x_2057_ = l_Lean_Compiler_LCNF_eagerLambdaLifting;
    v___x_2058_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__7),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__7_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__7,
    );
    v___x_2059_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__5_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__5,
    );
    v___x_2060_ = l_Lean_Compiler_LCNF_pullFunDecls;
    v___x_2061_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__4_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__4,
    );
    v___x_2062_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__3_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__3,
    );
    v___x_2063_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__2_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__2,
    );
    v___x_2064_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__0_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__0,
    );
    v___x_2065_ = l_Lean_Compiler_LCNF_pullInstances;
    v___x_2066_ = l_Lean_Compiler_LCNF_Pass_init;
    v___x_2067_ = leanh::lean_unsigned_to_nat(18);
    v___x_2068_ = lean_mk_empty_array_with_capacity(v___x_2067_);
    v___x_2069_ = lean_array_push(v___x_2068_, v___x_2066_);
    v___x_2070_ = lean_array_push(v___x_2069_, v___x_2065_);
    v___x_2071_ = lean_array_push(v___x_2070_, v___x_2064_);
    v___x_2072_ = lean_array_push(v___x_2071_, v___x_2063_);
    v___x_2073_ = lean_array_push(v___x_2072_, v___x_2062_);
    v___x_2074_ = lean_array_push(v___x_2073_, v___x_2061_);
    v___x_2075_ = lean_array_push(v___x_2074_, v___x_2060_);
    v___x_2076_ = lean_array_push(v___x_2075_, v___x_2059_);
    v___x_2077_ = lean_array_push(v___x_2076_, v___x_2058_);
    v___x_2078_ = lean_array_push(v___x_2077_, v___x_2057_);
    v___x_2079_ = lean_array_push(v___x_2078_, v___x_2056_);
    v___x_2080_ = lean_array_push(v___x_2079_, v___x_2055_);
    v___x_2081_ = lean_array_push(v___x_2080_, v___x_2054_);
    v___x_2082_ = lean_array_push(v___x_2081_, v___x_2053_);
    v___x_2083_ = lean_array_push(v___x_2082_, v___x_2052_);
    v___x_2084_ = lean_array_push(v___x_2083_, v___x_2051_);
    v___x_2085_ = lean_array_push(v___x_2084_, v___x_2050_);
    v___x_2086_ = lean_array_push(v___x_2085_, v___x_2049_);
    return v___x_2086_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2087_: u8 = 0;
    let mut v___x_2088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2087_ = 1;
    v___x_2088_ = leanh::lean_unsigned_to_nat(3);
    v___x_2089_ = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
    v___x_2090_ = l_Lean_Compiler_LCNF_simp(v___x_2089_, v___x_2088_, v___x_2087_);
    return v___x_2090_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_2091_: u8 = 0;
    let mut v___x_2092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2091_ = 1;
    v___x_2092_ = l_Lean_Compiler_LCNF_reduceJpArity(v___x_2091_);
    return v___x_2092_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_2093_: u8 = 0;
    let mut v___x_2094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2095_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2093_ = 1;
    v___x_2094_ = leanh::lean_unsigned_to_nat(0);
    v___x_2095_ = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(v___x_2094_, v___x_2093_);
    return v___x_2095_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16()
-> *mut leanh::LeanObject {
    let mut v___x_2096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2097_: u8 = 0;
    let mut v___x_2098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2096_ = leanh::lean_unsigned_to_nat(1);
    v___x_2097_ = 1;
    v___x_2098_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_2097_, v___x_2096_);
    return v___x_2098_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_2099_: u8 = 0;
    let mut v___x_2100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2102_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2099_ = 1;
    v___x_2100_ = leanh::lean_unsigned_to_nat(4);
    v___x_2101_ = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
    v___x_2102_ = l_Lean_Compiler_LCNF_simp(v___x_2101_, v___x_2100_, v___x_2099_);
    return v___x_2102_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18()
-> *mut leanh::LeanObject {
    let mut v___x_2103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2104_: u8 = 0;
    let mut v___x_2105_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2103_ = leanh::lean_unsigned_to_nat(2);
    v___x_2104_ = 1;
    v___x_2105_ = l_Lean_Compiler_LCNF_floatLetIn(v___x_2104_, v___x_2103_);
    return v___x_2105_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_2106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2106_ = l_Lean_Compiler_LCNF_lambdaLifting;
    v___x_2107_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__18),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__18_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__18,
    );
    v___x_2108_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__17),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__17_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__17,
    );
    v___x_2109_ = l_Lean_Compiler_LCNF_commonJoinPointArgs;
    v___x_2110_ = l_Lean_Compiler_LCNF_reduceArity;
    v___x_2111_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__16),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__16_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__16,
    );
    v___x_2112_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__15),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__15_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__15,
    );
    v___x_2113_ = l_Lean_Compiler_LCNF_structProjCases;
    v___x_2114_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__14),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__14_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__14,
    );
    v___x_2115_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__13),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__13_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__13,
    );
    v___x_2116_ = leanh::lean_unsigned_to_nat(10);
    v___x_2117_ = lean_mk_empty_array_with_capacity(v___x_2116_);
    v___x_2118_ = lean_array_push(v___x_2117_, v___x_2115_);
    v___x_2119_ = lean_array_push(v___x_2118_, v___x_2114_);
    v___x_2120_ = lean_array_push(v___x_2119_, v___x_2113_);
    v___x_2121_ = lean_array_push(v___x_2120_, v___x_2112_);
    v___x_2122_ = lean_array_push(v___x_2121_, v___x_2111_);
    v___x_2123_ = lean_array_push(v___x_2122_, v___x_2110_);
    v___x_2124_ = lean_array_push(v___x_2123_, v___x_2109_);
    v___x_2125_ = lean_array_push(v___x_2124_, v___x_2108_);
    v___x_2126_ = lean_array_push(v___x_2125_, v___x_2107_);
    v___x_2127_ = lean_array_push(v___x_2126_, v___x_2106_);
    return v___x_2127_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20()
-> *mut leanh::LeanObject {
    let mut v___x_2128_: u8 = 0;
    let mut v___x_2129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2130_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2128_ = 1;
    v___x_2129_ = leanh::lean_unsigned_to_nat(1);
    v___x_2130_ = l_Lean_Compiler_LCNF_extendJoinPointContext___redArg(v___x_2129_, v___x_2128_);
    return v___x_2130_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_2131_: u8 = 0;
    let mut v___x_2132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2131_ = 1;
    v___x_2132_ = leanh::lean_unsigned_to_nat(5);
    v___x_2133_ = l_Lean_Compiler_LCNF_builtinPassManager___closed__1;
    v___x_2134_ = l_Lean_Compiler_LCNF_simp(v___x_2133_, v___x_2132_, v___x_2131_);
    return v___x_2134_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22()
-> *mut leanh::LeanObject {
    let mut v___x_2135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: u8 = 0;
    let mut v___x_2137_: u8 = 0;
    let mut v___x_2138_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2135_ = leanh::lean_unsigned_to_nat(2);
    v___x_2136_ = 0;
    v___x_2137_ = 1;
    v___x_2138_ = l_Lean_Compiler_LCNF_cse(v___x_2137_, v___x_2136_, v___x_2135_);
    return v___x_2138_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_2139_: u8 = 0;
    let mut v___x_2140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2139_ = 1;
    v___x_2140_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_2139_);
    return v___x_2140_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_2141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2141_ = l_Lean_Compiler_LCNF_toImpure;
    v___x_2142_ = l_Lean_Compiler_LCNF_extractClosed;
    v___x_2143_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__23),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__23_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__23,
    );
    v___x_2144_ = l_Lean_Compiler_LCNF_Pass_saveMono;
    v___x_2145_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__22),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__22_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__22,
    );
    v___x_2146_ = l_Lean_Compiler_LCNF_elimDeadBranches;
    v___x_2147_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__21),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__21_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__21,
    );
    v___x_2148_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__20),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__20_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__20,
    );
    v___x_2149_ = leanh::lean_unsigned_to_nat(8);
    v___x_2150_ = lean_mk_empty_array_with_capacity(v___x_2149_);
    v___x_2151_ = lean_array_push(v___x_2150_, v___x_2148_);
    v___x_2152_ = lean_array_push(v___x_2151_, v___x_2147_);
    v___x_2153_ = lean_array_push(v___x_2152_, v___x_2146_);
    v___x_2154_ = lean_array_push(v___x_2153_, v___x_2145_);
    v___x_2155_ = lean_array_push(v___x_2154_, v___x_2144_);
    v___x_2156_ = lean_array_push(v___x_2155_, v___x_2143_);
    v___x_2157_ = lean_array_push(v___x_2156_, v___x_2142_);
    v___x_2158_ = lean_array_push(v___x_2157_, v___x_2141_);
    return v___x_2158_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25()
-> *mut leanh::LeanObject {
    let mut v___x_2159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2160_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2159_ = leanh::lean_unsigned_to_nat(0);
    v___x_2160_ = l_Lean_Compiler_LCNF_pushProj(v___x_2159_);
    return v___x_2160_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_2161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2162_: u8 = 0;
    let mut v___x_2163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2161_ = leanh::lean_unsigned_to_nat(0);
    v___x_2162_ = 2;
    v___x_2163_ = l_Lean_Compiler_LCNF_elimDeadVars(v___x_2162_, v___x_2161_);
    return v___x_2163_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27()
-> *mut leanh::LeanObject {
    let mut v___x_2164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2164_ = leanh::lean_unsigned_to_nat(1);
    v___x_2165_ = l_Lean_Compiler_LCNF_pushProj(v___x_2164_);
    return v___x_2165_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_2166_: u8 = 0;
    let mut v___x_2167_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2166_ = 2;
    v___x_2167_ = l_Lean_Compiler_LCNF_inferVisibility(v___x_2166_);
    return v___x_2167_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29()
-> *mut leanh::LeanObject {
    let mut v___x_2168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2168_ = l_Lean_Compiler_LCNF_Pass_saveImpure;
    v___x_2169_ = l_Lean_Compiler_LCNF_toposortPass;
    v___x_2170_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__28),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__28_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__28,
    );
    v___x_2171_ = l_Lean_Compiler_LCNF_detectSimpleGround;
    v___x_2172_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__27),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__27_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__27,
    );
    v___x_2173_ = l_Lean_Compiler_LCNF_coalesceRC;
    v___x_2174_ = l_Lean_Compiler_LCNF_expandResetReuse;
    v___x_2175_ = l_Lean_Compiler_LCNF_explicitRc;
    v___x_2176_ = l_Lean_Compiler_LCNF_explicitBoxing;
    v___x_2177_ = l_Lean_Compiler_LCNF_inferBorrow;
    v___x_2178_ = l_Lean_Compiler_LCNF_simpCase;
    v___x_2179_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__26),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__26_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__26,
    );
    v___x_2180_ = l_Lean_Compiler_LCNF_insertResetReuse;
    v___x_2181_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__25),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__25_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__25,
    );
    v___x_2182_ = leanh::lean_unsigned_to_nat(14);
    v___x_2183_ = lean_mk_empty_array_with_capacity(v___x_2182_);
    v___x_2184_ = lean_array_push(v___x_2183_, v___x_2181_);
    v___x_2185_ = lean_array_push(v___x_2184_, v___x_2180_);
    v___x_2186_ = lean_array_push(v___x_2185_, v___x_2179_);
    v___x_2187_ = lean_array_push(v___x_2186_, v___x_2178_);
    v___x_2188_ = lean_array_push(v___x_2187_, v___x_2177_);
    v___x_2189_ = lean_array_push(v___x_2188_, v___x_2176_);
    v___x_2190_ = lean_array_push(v___x_2189_, v___x_2175_);
    v___x_2191_ = lean_array_push(v___x_2190_, v___x_2174_);
    v___x_2192_ = lean_array_push(v___x_2191_, v___x_2173_);
    v___x_2193_ = lean_array_push(v___x_2192_, v___x_2172_);
    v___x_2194_ = lean_array_push(v___x_2193_, v___x_2171_);
    v___x_2195_ = lean_array_push(v___x_2194_, v___x_2170_);
    v___x_2196_ = lean_array_push(v___x_2195_, v___x_2169_);
    v___x_2197_ = lean_array_push(v___x_2196_, v___x_2168_);
    return v___x_2197_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_2198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2198_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__29),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__29_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__29,
    );
    v___x_2199_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__24),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__24_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__24,
    );
    v___x_2200_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__19),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__19_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__19,
    );
    v___x_2201_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__12),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__12_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__12,
    );
    v___x_2202_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2202_, 0, v___x_2201_);
    leanh::lean_ctor_set(v___x_2202_, 1, v___x_2200_);
    leanh::lean_ctor_set(v___x_2202_, 2, v___x_2199_);
    leanh::lean_ctor_set(v___x_2202_, 3, v___x_2198_);
    return v___x_2202_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_builtinPassManager() -> *mut leanh::LeanObject {
    let mut v___x_2203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2203_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__30),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_builtinPassManager___closed__30_once),
        _init_l_Lean_Compiler_LCNF_builtinPassManager___closed__30,
    );
    return v___x_2203_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(
    mut v_as_2204_: *mut leanh::LeanObject,
    mut v_sz_2205_: usize,
    mut v_i_2206_: usize,
    mut v_b_2207_: *mut leanh::LeanObject,
    mut v___y_2208_: *mut leanh::LeanObject,
    mut v___y_2209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2211_: u8 = 0;
    let mut v___x_2212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2211_ = lean_usize_dec_lt(v_i_2206_, v_sz_2205_);
                if v___x_2211_ == 0 {
                    v___x_2212_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2212_, 0, v_b_2207_);
                    return v___x_2212_;
                } else {
                    v_a_2213_ = lean_array_uget_borrowed(v_as_2204_, v_i_2206_);
                    leanh::lean_inc(v_a_2213_);
                    v___x_2214_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(
                        v_b_2207_,
                        v_a_2213_,
                        v___y_2208_,
                        v___y_2209_,
                    );
                    if leanh::lean_obj_tag(v___x_2214_) == 0 {
                        v_a_2215_ = leanh::lean_ctor_get(v___x_2214_, 0);
                        leanh::lean_inc(v_a_2215_);
                        leanh::lean_dec_ref_known(v___x_2214_, 1);
                        v___x_2216_ = 1usize;
                        v___x_2217_ = lean_usize_add(v_i_2206_, v___x_2216_);
                        v_i_2206_ = v___x_2217_;
                        v_b_2207_ = v_a_2215_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2214_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0___boxed(
    mut v_as_2219_: *mut leanh::LeanObject,
    mut v_sz_2220_: *mut leanh::LeanObject,
    mut v_i_2221_: *mut leanh::LeanObject,
    mut v_b_2222_: *mut leanh::LeanObject,
    mut v___y_2223_: *mut leanh::LeanObject,
    mut v___y_2224_: *mut leanh::LeanObject,
    mut v___y_2225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2226_: usize = 0;
    let mut v_i_boxed_2227_: usize = 0;
    let mut v_res_2228_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2226_ = leanh::lean_unbox_usize(v_sz_2220_);
    leanh::lean_dec(v_sz_2220_);
    v_i_boxed_2227_ = leanh::lean_unbox_usize(v_i_2221_);
    leanh::lean_dec(v_i_2221_);
    v_res_2228_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(v_as_2219_, v_sz_boxed_2226_, v_i_boxed_2227_, v_b_2222_, v___y_2223_, v___y_2224_);
    leanh::lean_dec(v___y_2224_);
    leanh::lean_dec_ref(v___y_2223_);
    leanh::lean_dec_ref(v_as_2219_);
    return v_res_2228_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(
    mut v_as_2229_: *mut leanh::LeanObject,
    mut v_sz_2230_: usize,
    mut v_i_2231_: usize,
    mut v_b_2232_: *mut leanh::LeanObject,
    mut v___y_2233_: *mut leanh::LeanObject,
    mut v___y_2234_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2236_: u8 = 0;
    let mut v___x_2237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2239_: usize = 0;
    let mut v___x_2240_: usize = 0;
    let mut v___x_2241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: usize = 0;
    let mut v___x_2244_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2236_ = lean_usize_dec_lt(v_i_2231_, v_sz_2230_);
                if v___x_2236_ == 0 {
                    v___x_2237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2237_, 0, v_b_2232_);
                    return v___x_2237_;
                } else {
                    v_a_2238_ = lean_array_uget_borrowed(v_as_2229_, v_i_2231_);
                    v_sz_2239_ = lean_array_size(v_a_2238_);
                    v___x_2240_ = 0usize;
                    v___x_2241_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__0(v_a_2238_, v_sz_2239_, v___x_2240_, v_b_2232_, v___y_2233_, v___y_2234_);
                    if leanh::lean_obj_tag(v___x_2241_) == 0 {
                        v_a_2242_ = leanh::lean_ctor_get(v___x_2241_, 0);
                        leanh::lean_inc(v_a_2242_);
                        leanh::lean_dec_ref_known(v___x_2241_, 1);
                        v___x_2243_ = 1usize;
                        v___x_2244_ = lean_usize_add(v_i_2231_, v___x_2243_);
                        v_i_2231_ = v___x_2244_;
                        v_b_2232_ = v_a_2242_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2241_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1___boxed(
    mut v_as_2246_: *mut leanh::LeanObject,
    mut v_sz_2247_: *mut leanh::LeanObject,
    mut v_i_2248_: *mut leanh::LeanObject,
    mut v_b_2249_: *mut leanh::LeanObject,
    mut v___y_2250_: *mut leanh::LeanObject,
    mut v___y_2251_: *mut leanh::LeanObject,
    mut v___y_2252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_2253_: usize = 0;
    let mut v_i_boxed_2254_: usize = 0;
    let mut v_res_2255_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2253_ = leanh::lean_unbox_usize(v_sz_2247_);
    leanh::lean_dec(v_sz_2247_);
    v_i_boxed_2254_ = leanh::lean_unbox_usize(v_i_2248_);
    leanh::lean_dec(v_i_2248_);
    v_res_2255_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(v_as_2246_, v_sz_boxed_2253_, v_i_boxed_2254_, v_b_2249_, v___y_2250_, v___y_2251_);
    leanh::lean_dec(v___y_2251_);
    leanh::lean_dec_ref(v___y_2250_);
    leanh::lean_dec_ref(v_as_2246_);
    return v_res_2255_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runImportedDecls(
    mut v_importedDeclNames_2256_: *mut leanh::LeanObject,
    mut v_a_2257_: *mut leanh::LeanObject,
    mut v_a_2258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_m_2260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2261_: usize = 0;
    let mut v___x_2262_: usize = 0;
    let mut v___x_2263_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_m_2260_ = l_Lean_Compiler_LCNF_builtinPassManager;
    v_sz_2261_ = lean_array_size(v_importedDeclNames_2256_);
    v___x_2262_ = 0usize;
    v___x_2263_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_runImportedDecls_spec__1(v_importedDeclNames_2256_, v_sz_2261_, v___x_2262_, v_m_2260_, v_a_2257_, v_a_2258_);
    return v___x_2263_;
}
pub unsafe fn l_Lean_Compiler_LCNF_runImportedDecls___boxed(
    mut v_importedDeclNames_2264_: *mut leanh::LeanObject,
    mut v_a_2265_: *mut leanh::LeanObject,
    mut v_a_2266_: *mut leanh::LeanObject,
    mut v_a_2267_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2268_ =
        l_Lean_Compiler_LCNF_runImportedDecls(v_importedDeclNames_2264_, v_a_2265_, v_a_2266_);
    leanh::lean_dec(v_a_2266_);
    leanh::lean_dec_ref(v_a_2265_);
    leanh::lean_dec_ref(v_importedDeclNames_2264_);
    return v_res_2268_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(
    mut v_s_2269_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2272_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2270_ = leanh::lean_ctor_get(v_s_2269_, 0);
    leanh::lean_inc(v_fst_2270_);
    leanh::lean_dec_ref(v_s_2269_);
    v___x_2271_ = l_List_reverse___redArg(v_fst_2270_);
    v___x_2272_ = lean_array_mk(v___x_2271_);
    return v___x_2272_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(
    mut v_x_2273_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2274_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2274_ = leanh::lean_box(0);
    return v___x_2274_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(
    mut v_x_2275_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2276_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v_x_2275_);
    leanh::lean_dec_ref(v_x_2275_);
    return v_res_2276_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(
    mut v_x_2277_: *mut leanh::LeanObject,
    mut v_s_2278_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fst_2279_ = leanh::lean_ctor_get(v_s_2278_, 0);
    leanh::lean_inc(v_fst_2279_);
    leanh::lean_dec_ref(v_s_2278_);
    v___x_2280_ = l_List_reverse___redArg(v_fst_2279_);
    v___x_2281_ = lean_array_mk(v___x_2280_);
    leanh::lean_inc_ref_n(v___x_2281_, 2);
    v___x_2282_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2282_, 0, v___x_2281_);
    leanh::lean_ctor_set(v___x_2282_, 1, v___x_2281_);
    leanh::lean_ctor_set(v___x_2282_, 2, v___x_2281_);
    return v___x_2282_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(
    mut v_x_2283_: *mut leanh::LeanObject,
    mut v_s_2284_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2285_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2285_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v_x_2283_, v_s_2284_);
    leanh::lean_dec_ref(v_x_2283_);
    return v_res_2285_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(
    mut v_x_2286_: *mut leanh::LeanObject,
    mut v_x_2287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_2288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v_fst_2292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2296_: u8 = 0;
    let mut v___x_2298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_isSharedCheck_2304_: u8 = 0;
    let mut v_unused_2305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_2288_ = leanh::lean_ctor_get(v_x_2286_, 0);
                v_isSharedCheck_2304_ = (!leanh::lean_is_exclusive(v_x_2286_)) as u8;
                if v_isSharedCheck_2304_ == 0 {
                    v_unused_2305_ = leanh::lean_ctor_get(v_x_2286_, 1);
                    leanh::lean_dec(v_unused_2305_);
                    v___x_2290_ = v_x_2286_;
                    v_isShared_2291_ = v_isSharedCheck_2304_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_2288_);
                    leanh::lean_dec(v_x_2286_);
                    v___x_2290_ = leanh::lean_box(0);
                    v_isShared_2291_ = v_isSharedCheck_2304_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_2292_ = leanh::lean_ctor_get(v_x_2287_, 0);
                v_snd_2293_ = leanh::lean_ctor_get(v_x_2287_, 1);
                v_isSharedCheck_2303_ = (!leanh::lean_is_exclusive(v_x_2287_)) as u8;
                if v_isSharedCheck_2303_ == 0 {
                    v___x_2295_ = v_x_2287_;
                    v_isShared_2296_ = v_isSharedCheck_2303_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_2293_);
                    leanh::lean_inc(v_fst_2292_);
                    leanh::lean_dec(v_x_2287_);
                    v___x_2295_ = leanh::lean_box(0);
                    v_isShared_2296_ = v_isSharedCheck_2303_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_2291_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2290_, 1);
                    leanh::lean_ctor_set(v___x_2290_, 1, v_fst_2288_);
                    leanh::lean_ctor_set(v___x_2290_, 0, v_fst_2292_);
                    v___x_2298_ = v___x_2290_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_fst_2292_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 1, v_fst_2288_);
                    v___x_2298_ = v_reuseFailAlloc_2302_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2296_ == 0 {
                    leanh::lean_ctor_set(v___x_2295_, 0, v___x_2298_);
                    v___x_2300_ = v___x_2295_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2301_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 0, v___x_2298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_snd_2293_);
                    v___x_2300_ = v_reuseFailAlloc_2301_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2300_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(
    mut v___x_2306_: *mut leanh::LeanObject,
    mut v_ns_2307_: *mut leanh::LeanObject,
    mut v___y_2308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2315_: u8 = 0;
    let mut v___x_2316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2320_: u8 = 0;
    let mut v_a_2321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2324_: u8 = 0;
    let mut v___x_2326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2328_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2310_ = leanh::lean_alloc_closure(
                    l_Lean_Compiler_LCNF_runImportedDecls___boxed as *mut core::ffi::c_void,
                    4,
                    1,
                );
                leanh::lean_closure_set(v___x_2310_, 0, v_ns_2307_);
                v___x_2311_ = l_Lean_ImportM_runCoreM___redArg(v___x_2310_, v___y_2308_);
                if leanh::lean_obj_tag(v___x_2311_) == 0 {
                    v_a_2312_ = leanh::lean_ctor_get(v___x_2311_, 0);
                    v_isSharedCheck_2320_ = (!leanh::lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2320_ == 0 {
                        v___x_2314_ = v___x_2311_;
                        v_isShared_2315_ = v_isSharedCheck_2320_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2312_);
                        leanh::lean_dec(v___x_2311_);
                        v___x_2314_ = leanh::lean_box(0);
                        v_isShared_2315_ = v_isSharedCheck_2320_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_2306_);
                    v_a_2321_ = leanh::lean_ctor_get(v___x_2311_, 0);
                    v_isSharedCheck_2328_ = (!leanh::lean_is_exclusive(v___x_2311_)) as u8;
                    if v_isSharedCheck_2328_ == 0 {
                        v___x_2323_ = v___x_2311_;
                        v_isShared_2324_ = v_isSharedCheck_2328_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2321_);
                        leanh::lean_dec(v___x_2311_);
                        v___x_2323_ = leanh::lean_box(0);
                        v_isShared_2324_ = v_isSharedCheck_2328_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2316_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2316_, 0, v___x_2306_);
                leanh::lean_ctor_set(v___x_2316_, 1, v_a_2312_);
                if v_isShared_2315_ == 0 {
                    leanh::lean_ctor_set(v___x_2314_, 0, v___x_2316_);
                    v___x_2318_ = v___x_2314_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2319_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2319_, 0, v___x_2316_);
                    v___x_2318_ = v_reuseFailAlloc_2319_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2318_;
            }
            3 => {
                if v_isShared_2324_ == 0 {
                    v___x_2326_ = v___x_2323_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2327_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2327_, 0, v_a_2321_);
                    v___x_2326_ = v_reuseFailAlloc_2327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2326_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(
    mut v___x_2329_: *mut leanh::LeanObject,
    mut v_ns_2330_: *mut leanh::LeanObject,
    mut v___y_2331_: *mut leanh::LeanObject,
    mut v___y_2332_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2333_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v___x_2329_, v_ns_2330_, v___y_2331_);
    leanh::lean_dec_ref(v___y_2331_);
    return v_res_2333_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(
    mut v___x_2334_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2336_, 0, v___x_2334_);
    return v___x_2336_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(
    mut v___x_2337_: *mut leanh::LeanObject,
    mut v___y_2338_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2339_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_(v___x_2337_);
    return v_res_2339_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2355_ = l_Lean_Compiler_LCNF_builtinPassManager;
    v___x_2356_ = leanh::lean_box(0);
    v___x_2357_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2357_, 0, v___x_2356_);
    leanh::lean_ctor_set(v___x_2357_, 1, v___x_2355_);
    return v___x_2357_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2359_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
    v___f_2359_ = leanh::lean_alloc_closure(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_2359_, 0, v___x_2358_);
    return v___f_2359_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_2366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2360_ = leanh::lean_box(0);
    v___x_2361_ = leanh::lean_box(2);
    v___f_2362_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
    v___f_2363_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
    v___f_2364_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
    v___f_2365_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
    v___f_2366_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
    v___x_2367_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
    v___x_2368_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_2368_, 0, v___x_2367_);
    leanh::lean_ctor_set(v___x_2368_, 1, v___f_2366_);
    leanh::lean_ctor_set(v___x_2368_, 2, v___f_2365_);
    leanh::lean_ctor_set(v___x_2368_, 3, v___f_2364_);
    leanh::lean_ctor_set(v___x_2368_, 4, v___f_2363_);
    leanh::lean_ctor_set(v___x_2368_, 5, v___f_2362_);
    leanh::lean_ctor_set(v___x_2368_, 6, v___x_2361_);
    leanh::lean_ctor_set(v___x_2368_, 7, v___x_2360_);
    return v___x_2368_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_2369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_2369_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
    v___x_2370_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
    v___x_2371_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2371_, 0, v___x_2370_);
    leanh::lean_ctor_set(v___x_2371_, 1, v___f_2369_);
    return v___x_2371_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2373_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_);
    v___x_2374_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_2373_);
    return v___x_2374_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2____boxed(
    mut v_a_2375_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2376_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2376_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
    return v_res_2376_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2377_ = l_Lean_Compiler_LCNF_instInhabitedPassManager_default;
    v___x_2378_ = leanh::lean_box(0);
    v___x_2379_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2379_, 0, v___x_2378_);
    leanh::lean_ctor_set(v___x_2379_, 1, v___x_2377_);
    return v___x_2379_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPassManager___redArg(
    mut v_a_2380_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2382_ = lean_st_ref_get(v_a_2380_);
    v_env_2383_ = leanh::lean_ctor_get(v___x_2382_, 0);
    leanh::lean_inc_ref(v_env_2383_);
    leanh::lean_dec(v___x_2382_);
    v___x_2384_ = l_Lean_Compiler_LCNF_passManagerExt;
    v_toEnvExtension_2385_ = leanh::lean_ctor_get(v___x_2384_, 0);
    v_asyncMode_2386_ = leanh::lean_ctor_get(v_toEnvExtension_2385_, 2);
    v___x_2387_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0_once),
        _init_l_Lean_Compiler_LCNF_getPassManager___redArg___closed__0,
    );
    v___x_2388_ = leanh::lean_box(0);
    v___x_2389_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_2387_,
        v___x_2384_,
        v_env_2383_,
        v_asyncMode_2386_,
        v___x_2388_,
    );
    v_snd_2390_ = leanh::lean_ctor_get(v___x_2389_, 1);
    leanh::lean_inc(v_snd_2390_);
    leanh::lean_dec(v___x_2389_);
    v___x_2391_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2391_, 0, v_snd_2390_);
    return v___x_2391_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPassManager___redArg___boxed(
    mut v_a_2392_: *mut leanh::LeanObject,
    mut v_a_2393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2394_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_2392_);
    leanh::lean_dec(v_a_2392_);
    return v_res_2394_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPassManager(
    mut v_a_2395_: *mut leanh::LeanObject,
    mut v_a_2396_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2398_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2398_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_2396_);
    return v___x_2398_;
}
pub unsafe fn l_Lean_Compiler_LCNF_getPassManager___boxed(
    mut v_a_2399_: *mut leanh::LeanObject,
    mut v_a_2400_: *mut leanh::LeanObject,
    mut v_a_2401_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2402_ = l_Lean_Compiler_LCNF_getPassManager(v_a_2399_, v_a_2400_);
    leanh::lean_dec(v_a_2400_);
    leanh::lean_dec_ref(v_a_2399_);
    return v_res_2402_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_2403_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2403_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_2403_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2404_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__0);
    v___x_2405_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2405_, 0, v___x_2404_);
    return v___x_2405_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_2406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2406_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1);
    v___x_2407_ = leanh::lean_unsigned_to_nat(0);
    v___x_2408_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_2408_, 0, v___x_2407_);
    leanh::lean_ctor_set(v___x_2408_, 1, v___x_2407_);
    leanh::lean_ctor_set(v___x_2408_, 2, v___x_2407_);
    leanh::lean_ctor_set(v___x_2408_, 3, v___x_2407_);
    leanh::lean_ctor_set(v___x_2408_, 4, v___x_2406_);
    leanh::lean_ctor_set(v___x_2408_, 5, v___x_2406_);
    leanh::lean_ctor_set(v___x_2408_, 6, v___x_2406_);
    leanh::lean_ctor_set(v___x_2408_, 7, v___x_2406_);
    leanh::lean_ctor_set(v___x_2408_, 8, v___x_2406_);
    leanh::lean_ctor_set(v___x_2408_, 9, v___x_2406_);
    return v___x_2408_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2411_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2409_ = leanh::lean_unsigned_to_nat(32);
    v___x_2410_ = lean_mk_empty_array_with_capacity(v___x_2409_);
    v___x_2411_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2411_, 0, v___x_2410_);
    return v___x_2411_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_2412_: usize = 0;
    let mut v___x_2413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2417_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2412_ = 5usize;
    v___x_2413_ = leanh::lean_unsigned_to_nat(0);
    v___x_2414_ = leanh::lean_unsigned_to_nat(32);
    v___x_2415_ = lean_mk_empty_array_with_capacity(v___x_2414_);
    v___x_2416_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__3);
    v___x_2417_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_2417_, 0, v___x_2416_);
    leanh::lean_ctor_set(v___x_2417_, 1, v___x_2415_);
    leanh::lean_ctor_set(v___x_2417_, 2, v___x_2413_);
    leanh::lean_ctor_set(v___x_2417_, 3, v___x_2413_);
    leanh::lean_ctor_set_usize(v___x_2417_, 4, v___x_2412_);
    return v___x_2417_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2418_ = leanh::lean_box(1);
    v___x_2419_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__4);
    v___x_2420_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__1);
    v___x_2421_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_2421_, 0, v___x_2420_);
    leanh::lean_ctor_set(v___x_2421_, 1, v___x_2419_);
    leanh::lean_ctor_set(v___x_2421_, 2, v___x_2418_);
    return v___x_2421_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(
    mut v_msgData_2422_: *mut leanh::LeanObject,
    mut v___y_2423_: *mut leanh::LeanObject,
    mut v___y_2424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2426_ = lean_st_ref_get(v___y_2424_);
    v_env_2427_ = leanh::lean_ctor_get(v___x_2426_, 0);
    leanh::lean_inc_ref(v_env_2427_);
    leanh::lean_dec(v___x_2426_);
    v_options_2428_ = leanh::lean_ctor_get(v___y_2423_, 2);
    v___x_2429_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2);
    v___x_2430_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5);
    leanh::lean_inc_ref(v_options_2428_);
    v___x_2431_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_2431_, 0, v_env_2427_);
    leanh::lean_ctor_set(v___x_2431_, 1, v___x_2429_);
    leanh::lean_ctor_set(v___x_2431_, 2, v___x_2430_);
    leanh::lean_ctor_set(v___x_2431_, 3, v_options_2428_);
    v___x_2432_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2432_, 0, v___x_2431_);
    leanh::lean_ctor_set(v___x_2432_, 1, v_msgData_2422_);
    v___x_2433_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_2433_, 0, v___x_2432_);
    return v___x_2433_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___boxed(
    mut v_msgData_2434_: *mut leanh::LeanObject,
    mut v___y_2435_: *mut leanh::LeanObject,
    mut v___y_2436_: *mut leanh::LeanObject,
    mut v___y_2437_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2438_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2438_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(v_msgData_2434_, v___y_2435_, v___y_2436_);
    leanh::lean_dec(v___y_2436_);
    leanh::lean_dec_ref(v___y_2435_);
    return v_res_2438_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(
    mut v_msg_2439_: *mut leanh::LeanObject,
    mut v___y_2440_: *mut leanh::LeanObject,
    mut v___y_2441_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2448_: u8 = 0;
    let mut v___x_2449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2453_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2443_ = leanh::lean_ctor_get(v___y_2440_, 5);
                v___x_2444_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4(v_msg_2439_, v___y_2440_, v___y_2441_);
                v_a_2445_ = leanh::lean_ctor_get(v___x_2444_, 0);
                v_isSharedCheck_2453_ = (!leanh::lean_is_exclusive(v___x_2444_)) as u8;
                if v_isSharedCheck_2453_ == 0 {
                    v___x_2447_ = v___x_2444_;
                    v_isShared_2448_ = v_isSharedCheck_2453_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2445_);
                    leanh::lean_dec(v___x_2444_);
                    v___x_2447_ = leanh::lean_box(0);
                    v_isShared_2448_ = v_isSharedCheck_2453_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_2443_);
                v___x_2449_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2449_, 0, v_ref_2443_);
                leanh::lean_ctor_set(v___x_2449_, 1, v_a_2445_);
                if v_isShared_2448_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2447_, 1);
                    leanh::lean_ctor_set(v___x_2447_, 0, v___x_2449_);
                    v___x_2451_ = v___x_2447_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2452_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2452_, 0, v___x_2449_);
                    v___x_2451_ = v_reuseFailAlloc_2452_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2451_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg___boxed(
    mut v_msg_2454_: *mut leanh::LeanObject,
    mut v___y_2455_: *mut leanh::LeanObject,
    mut v___y_2456_: *mut leanh::LeanObject,
    mut v___y_2457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2458_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_2454_, v___y_2455_, v___y_2456_);
    leanh::lean_dec(v___y_2456_);
    leanh::lean_dec_ref(v___y_2455_);
    return v_res_2458_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2460_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__0;
    v___x_2461_ = l_Lean_stringToMessageData(v___x_2460_);
    return v___x_2461_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2463_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__2;
    v___x_2464_ = l_Lean_stringToMessageData(v___x_2463_);
    return v___x_2464_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2466_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__4;
    v___x_2467_ = l_Lean_stringToMessageData(v___x_2466_);
    return v___x_2467_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2469_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__6;
    v___x_2470_ = l_Lean_stringToMessageData(v___x_2469_);
    return v___x_2470_;
}
pub unsafe fn _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2472_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__8;
    v___x_2473_ = l_Lean_stringToMessageData(v___x_2472_);
    return v___x_2473_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(
    mut v_attrName_2474_: *mut leanh::LeanObject,
    mut v_declName_2475_: *mut leanh::LeanObject,
    mut v_givenType_2476_: *mut leanh::LeanObject,
    mut v_expectedType_2477_: *mut leanh::LeanObject,
    mut v___y_2478_: *mut leanh::LeanObject,
    mut v___y_2479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2486_: u8 = 0;
    let mut v___x_2487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2481_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__1);
    v___x_2482_ = l_Lean_MessageData_ofName(v_attrName_2474_);
    leanh::lean_inc_ref(v___x_2482_);
    v___x_2483_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2483_, 0, v___x_2481_);
    leanh::lean_ctor_set(v___x_2483_, 1, v___x_2482_);
    v___x_2484_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__3);
    v___x_2485_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2485_, 0, v___x_2483_);
    leanh::lean_ctor_set(v___x_2485_, 1, v___x_2484_);
    v___x_2486_ = 0;
    v___x_2487_ = l_Lean_MessageData_ofConstName(v_declName_2475_, v___x_2486_);
    v___x_2488_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2488_, 0, v___x_2485_);
    leanh::lean_ctor_set(v___x_2488_, 1, v___x_2487_);
    v___x_2489_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__5);
    v___x_2490_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2490_, 0, v___x_2488_);
    leanh::lean_ctor_set(v___x_2490_, 1, v___x_2489_);
    v___x_2491_ = l_Lean_indentExpr(v_givenType_2476_);
    v___x_2492_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2492_, 0, v___x_2490_);
    leanh::lean_ctor_set(v___x_2492_, 1, v___x_2491_);
    v___x_2493_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__7);
    v___x_2494_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2494_, 0, v___x_2492_);
    leanh::lean_ctor_set(v___x_2494_, 1, v___x_2493_);
    v___x_2495_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2495_, 0, v___x_2494_);
    leanh::lean_ctor_set(v___x_2495_, 1, v___x_2482_);
    v___x_2496_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9_once), _init_l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___closed__9);
    v___x_2497_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2497_, 0, v___x_2495_);
    leanh::lean_ctor_set(v___x_2497_, 1, v___x_2496_);
    v___x_2498_ = l_Lean_indentExpr(v_expectedType_2477_);
    v___x_2499_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2499_, 0, v___x_2497_);
    leanh::lean_ctor_set(v___x_2499_, 1, v___x_2498_);
    v___x_2500_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_2499_, v___y_2478_, v___y_2479_);
    return v___x_2500_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg___boxed(
    mut v_attrName_2501_: *mut leanh::LeanObject,
    mut v_declName_2502_: *mut leanh::LeanObject,
    mut v_givenType_2503_: *mut leanh::LeanObject,
    mut v_expectedType_2504_: *mut leanh::LeanObject,
    mut v___y_2505_: *mut leanh::LeanObject,
    mut v___y_2506_: *mut leanh::LeanObject,
    mut v___y_2507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2508_ =
        l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(
            v_attrName_2501_,
            v_declName_2502_,
            v_givenType_2503_,
            v_expectedType_2504_,
            v___y_2505_,
            v___y_2506_,
        );
    leanh::lean_dec(v___y_2506_);
    leanh::lean_dec_ref(v___y_2505_);
    return v_res_2508_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(
    mut v_ref_2509_: *mut leanh::LeanObject,
    mut v_msg_2510_: *mut leanh::LeanObject,
    mut v___y_2511_: *mut leanh::LeanObject,
    mut v___y_2512_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_2514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_2515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_2517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_2518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_2520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_2521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_2522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_2523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_2524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_2525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_2526_: u8 = 0;
    let mut v_cancelTk_x3f_2527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_2528_: u8 = 0;
    let mut v_inheritedTraceOptions_2529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_2530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fileName_2514_ = leanh::lean_ctor_get(v___y_2511_, 0);
    v_fileMap_2515_ = leanh::lean_ctor_get(v___y_2511_, 1);
    v_options_2516_ = leanh::lean_ctor_get(v___y_2511_, 2);
    v_currRecDepth_2517_ = leanh::lean_ctor_get(v___y_2511_, 3);
    v_maxRecDepth_2518_ = leanh::lean_ctor_get(v___y_2511_, 4);
    v_ref_2519_ = leanh::lean_ctor_get(v___y_2511_, 5);
    v_currNamespace_2520_ = leanh::lean_ctor_get(v___y_2511_, 6);
    v_openDecls_2521_ = leanh::lean_ctor_get(v___y_2511_, 7);
    v_initHeartbeats_2522_ = leanh::lean_ctor_get(v___y_2511_, 8);
    v_maxHeartbeats_2523_ = leanh::lean_ctor_get(v___y_2511_, 9);
    v_quotContext_2524_ = leanh::lean_ctor_get(v___y_2511_, 10);
    v_currMacroScope_2525_ = leanh::lean_ctor_get(v___y_2511_, 11);
    v_diag_2526_ = leanh::lean_ctor_get_uint8(
        v___y_2511_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
    );
    v_cancelTk_x3f_2527_ = leanh::lean_ctor_get(v___y_2511_, 12);
    v_suppressElabErrors_2528_ = leanh::lean_ctor_get_uint8(
        v___y_2511_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
    );
    v_inheritedTraceOptions_2529_ = leanh::lean_ctor_get(v___y_2511_, 13);
    v_ref_2530_ = l_Lean_replaceRef(v_ref_2509_, v_ref_2519_);
    leanh::lean_inc_ref(v_inheritedTraceOptions_2529_);
    leanh::lean_inc(v_cancelTk_x3f_2527_);
    leanh::lean_inc(v_currMacroScope_2525_);
    leanh::lean_inc(v_quotContext_2524_);
    leanh::lean_inc(v_maxHeartbeats_2523_);
    leanh::lean_inc(v_initHeartbeats_2522_);
    leanh::lean_inc(v_openDecls_2521_);
    leanh::lean_inc(v_currNamespace_2520_);
    leanh::lean_inc(v_maxRecDepth_2518_);
    leanh::lean_inc(v_currRecDepth_2517_);
    leanh::lean_inc_ref(v_options_2516_);
    leanh::lean_inc_ref(v_fileMap_2515_);
    leanh::lean_inc_ref(v_fileName_2514_);
    v___x_2531_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
    leanh::lean_ctor_set(v___x_2531_, 0, v_fileName_2514_);
    leanh::lean_ctor_set(v___x_2531_, 1, v_fileMap_2515_);
    leanh::lean_ctor_set(v___x_2531_, 2, v_options_2516_);
    leanh::lean_ctor_set(v___x_2531_, 3, v_currRecDepth_2517_);
    leanh::lean_ctor_set(v___x_2531_, 4, v_maxRecDepth_2518_);
    leanh::lean_ctor_set(v___x_2531_, 5, v_ref_2530_);
    leanh::lean_ctor_set(v___x_2531_, 6, v_currNamespace_2520_);
    leanh::lean_ctor_set(v___x_2531_, 7, v_openDecls_2521_);
    leanh::lean_ctor_set(v___x_2531_, 8, v_initHeartbeats_2522_);
    leanh::lean_ctor_set(v___x_2531_, 9, v_maxHeartbeats_2523_);
    leanh::lean_ctor_set(v___x_2531_, 10, v_quotContext_2524_);
    leanh::lean_ctor_set(v___x_2531_, 11, v_currMacroScope_2525_);
    leanh::lean_ctor_set(v___x_2531_, 12, v_cancelTk_x3f_2527_);
    leanh::lean_ctor_set(v___x_2531_, 13, v_inheritedTraceOptions_2529_);
    leanh::lean_ctor_set_uint8(
        v___x_2531_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
        v_diag_2526_,
    );
    leanh::lean_ctor_set_uint8(
        v___x_2531_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
        v_suppressElabErrors_2528_,
    );
    v___x_2532_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_2510_, v___x_2531_, v___y_2512_);
    leanh::lean_dec_ref_known(v___x_2531_, 14);
    return v___x_2532_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg___boxed(
    mut v_ref_2533_: *mut leanh::LeanObject,
    mut v_msg_2534_: *mut leanh::LeanObject,
    mut v___y_2535_: *mut leanh::LeanObject,
    mut v___y_2536_: *mut leanh::LeanObject,
    mut v___y_2537_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2538_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2538_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_2533_, v_msg_2534_, v___y_2535_, v___y_2536_);
    leanh::lean_dec(v___y_2536_);
    leanh::lean_dec_ref(v___y_2535_);
    leanh::lean_dec(v_ref_2533_);
    return v_res_2538_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2540_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__0;
    v___x_2541_ = l_Lean_stringToMessageData(v___x_2540_);
    return v___x_2541_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2543_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__2;
    v___x_2544_ = l_Lean_stringToMessageData(v___x_2543_);
    return v___x_2544_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_2546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2546_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__4;
    v___x_2547_ = l_Lean_stringToMessageData(v___x_2546_);
    return v___x_2547_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_2549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2549_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__6;
    v___x_2550_ = l_Lean_stringToMessageData(v___x_2549_);
    return v___x_2550_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_2552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__8;
    v___x_2553_ = l_Lean_stringToMessageData(v___x_2552_);
    return v___x_2553_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_2555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2555_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__10;
    v___x_2556_ = l_Lean_stringToMessageData(v___x_2555_);
    return v___x_2556_;
}
pub unsafe fn _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_2558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2558_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__12;
    v___x_2559_ = l_Lean_stringToMessageData(v___x_2558_);
    return v___x_2559_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(
    mut v_msg_2560_: *mut leanh::LeanObject,
    mut v_declHint_2561_: *mut leanh::LeanObject,
    mut v___y_2562_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u8 = 0;
    let mut v_isExporting_2567_: u8 = 0;
    let mut v___x_2568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: u8 = 0;
    let mut v___x_2571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_2577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2589_: u8 = 0;
    let mut v___x_2590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mod_2593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u8 = 0;
    let mut v___x_2595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2621_: u8 = 0;
    let mut v___x_2622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2564_ = lean_st_ref_get(v___y_2562_);
                v_env_2565_ = leanh::lean_ctor_get(v___x_2564_, 0);
                leanh::lean_inc_ref(v_env_2565_);
                leanh::lean_dec(v___x_2564_);
                v___x_2566_ = l_Lean_Name_isAnonymous(v_declHint_2561_);
                if v___x_2566_ == 0 {
                    v_isExporting_2567_ = leanh::lean_ctor_get_uint8(
                        v_env_2565_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 8) as u32,
                    );
                    if v_isExporting_2567_ == 0 {
                        leanh::lean_dec_ref(v_env_2565_);
                        leanh::lean_dec(v_declHint_2561_);
                        v___x_2568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_2568_, 0, v_msg_2560_);
                        return v___x_2568_;
                    } else {
                        leanh::lean_inc_ref(v_env_2565_);
                        v___x_2569_ = l_Lean_Environment_setExporting(v_env_2565_, v___x_2566_);
                        leanh::lean_inc(v_declHint_2561_);
                        leanh::lean_inc_ref(v___x_2569_);
                        v___x_2570_ = l_Lean_Environment_contains(
                            v___x_2569_,
                            v_declHint_2561_,
                            v_isExporting_2567_,
                        );
                        if v___x_2570_ == 0 {
                            leanh::lean_dec_ref(v___x_2569_);
                            leanh::lean_dec_ref(v_env_2565_);
                            leanh::lean_dec(v_declHint_2561_);
                            v___x_2571_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v___x_2571_, 0, v_msg_2560_);
                            return v___x_2571_;
                        } else {
                            v___x_2572_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__2);
                            v___x_2573_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2_spec__4___closed__5);
                            v___x_2574_ = l_Lean_Options_empty;
                            v___x_2575_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
                            leanh::lean_ctor_set(v___x_2575_, 0, v___x_2569_);
                            leanh::lean_ctor_set(v___x_2575_, 1, v___x_2572_);
                            leanh::lean_ctor_set(v___x_2575_, 2, v___x_2573_);
                            leanh::lean_ctor_set(v___x_2575_, 3, v___x_2574_);
                            leanh::lean_inc(v_declHint_2561_);
                            v___x_2576_ =
                                l_Lean_MessageData_ofConstName(v_declHint_2561_, v___x_2566_);
                            v_c_2577_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
                            leanh::lean_ctor_set(v_c_2577_, 0, v___x_2575_);
                            leanh::lean_ctor_set(v_c_2577_, 1, v___x_2576_);
                            v___x_2578_ = l_Lean_Environment_getModuleIdxFor_x3f(
                                v_env_2565_,
                                v_declHint_2561_,
                            );
                            if leanh::lean_obj_tag(v___x_2578_) == 0 {
                                leanh::lean_dec_ref(v_env_2565_);
                                leanh::lean_dec(v_declHint_2561_);
                                v___x_2579_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1);
                                v___x_2580_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2580_, 0, v___x_2579_);
                                leanh::lean_ctor_set(v___x_2580_, 1, v_c_2577_);
                                v___x_2581_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__3);
                                v___x_2582_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2582_, 0, v___x_2580_);
                                leanh::lean_ctor_set(v___x_2582_, 1, v___x_2581_);
                                v___x_2583_ = l_Lean_MessageData_note(v___x_2582_);
                                v___x_2584_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                leanh::lean_ctor_set(v___x_2584_, 0, v_msg_2560_);
                                leanh::lean_ctor_set(v___x_2584_, 1, v___x_2583_);
                                v___x_2585_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_2585_, 0, v___x_2584_);
                                return v___x_2585_;
                            } else {
                                v_val_2586_ = leanh::lean_ctor_get(v___x_2578_, 0);
                                v_isSharedCheck_2621_ =
                                    (!leanh::lean_is_exclusive(v___x_2578_)) as u8;
                                if v_isSharedCheck_2621_ == 0 {
                                    v___x_2588_ = v___x_2578_;
                                    v_isShared_2589_ = v_isSharedCheck_2621_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_val_2586_);
                                    leanh::lean_dec(v___x_2578_);
                                    v___x_2588_ = leanh::lean_box(0);
                                    v_isShared_2589_ = v_isSharedCheck_2621_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_env_2565_);
                    leanh::lean_dec(v_declHint_2561_);
                    v___x_2622_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_2622_, 0, v_msg_2560_);
                    return v___x_2622_;
                }
            }
            1 => {
                v___x_2590_ = leanh::lean_box(0);
                v___x_2591_ = l_Lean_Environment_header(v_env_2565_);
                leanh::lean_dec_ref(v_env_2565_);
                v___x_2592_ = l_Lean_EnvironmentHeader_moduleNames(v___x_2591_);
                v_mod_2593_ = lean_array_get(v___x_2590_, v___x_2592_, v_val_2586_);
                leanh::lean_dec(v_val_2586_);
                leanh::lean_dec_ref(v___x_2592_);
                v___x_2594_ = l_Lean_isPrivateName(v_declHint_2561_);
                leanh::lean_dec(v_declHint_2561_);
                if v___x_2594_ == 0 {
                    v___x_2595_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__5);
                    v___x_2596_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2596_, 0, v___x_2595_);
                    leanh::lean_ctor_set(v___x_2596_, 1, v_c_2577_);
                    v___x_2597_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__7);
                    v___x_2598_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2598_, 0, v___x_2596_);
                    leanh::lean_ctor_set(v___x_2598_, 1, v___x_2597_);
                    v___x_2599_ = l_Lean_MessageData_ofName(v_mod_2593_);
                    v___x_2600_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2600_, 0, v___x_2598_);
                    leanh::lean_ctor_set(v___x_2600_, 1, v___x_2599_);
                    v___x_2601_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__9);
                    v___x_2602_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2602_, 0, v___x_2600_);
                    leanh::lean_ctor_set(v___x_2602_, 1, v___x_2601_);
                    v___x_2603_ = l_Lean_MessageData_note(v___x_2602_);
                    v___x_2604_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2604_, 0, v_msg_2560_);
                    leanh::lean_ctor_set(v___x_2604_, 1, v___x_2603_);
                    if v_isShared_2589_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2588_, 0);
                        leanh::lean_ctor_set(v___x_2588_, 0, v___x_2604_);
                        v___x_2606_ = v___x_2588_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2607_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2607_, 0, v___x_2604_);
                        v___x_2606_ = v_reuseFailAlloc_2607_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_2608_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__1);
                    v___x_2609_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2609_, 0, v___x_2608_);
                    leanh::lean_ctor_set(v___x_2609_, 1, v_c_2577_);
                    v___x_2610_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__11);
                    v___x_2611_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2611_, 0, v___x_2609_);
                    leanh::lean_ctor_set(v___x_2611_, 1, v___x_2610_);
                    v___x_2612_ = l_Lean_MessageData_ofName(v_mod_2593_);
                    v___x_2613_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2613_, 0, v___x_2611_);
                    leanh::lean_ctor_set(v___x_2613_, 1, v___x_2612_);
                    v___x_2614_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13), core::ptr::addr_of_mut!(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13_once), _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___closed__13);
                    v___x_2615_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2615_, 0, v___x_2613_);
                    leanh::lean_ctor_set(v___x_2615_, 1, v___x_2614_);
                    v___x_2616_ = l_Lean_MessageData_note(v___x_2615_);
                    v___x_2617_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_2617_, 0, v_msg_2560_);
                    leanh::lean_ctor_set(v___x_2617_, 1, v___x_2616_);
                    if v_isShared_2589_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_2588_, 0);
                        leanh::lean_ctor_set(v___x_2588_, 0, v___x_2617_);
                        v___x_2619_ = v___x_2588_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2620_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2617_);
                        v___x_2619_ = v_reuseFailAlloc_2620_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2606_;
            }
            3 => {
                return v___x_2619_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg___boxed(
    mut v_msg_2623_: *mut leanh::LeanObject,
    mut v_declHint_2624_: *mut leanh::LeanObject,
    mut v___y_2625_: *mut leanh::LeanObject,
    mut v___y_2626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2627_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2627_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_2623_, v_declHint_2624_, v___y_2625_);
    leanh::lean_dec(v___y_2625_);
    return v_res_2627_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(
    mut v_msg_2628_: *mut leanh::LeanObject,
    mut v_declHint_2629_: *mut leanh::LeanObject,
    mut v___y_2630_: *mut leanh::LeanObject,
    mut v___y_2631_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2637_: u8 = 0;
    let mut v___x_2638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2643_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2633_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_2628_, v_declHint_2629_, v___y_2631_);
                v_a_2634_ = leanh::lean_ctor_get(v___x_2633_, 0);
                v_isSharedCheck_2643_ = (!leanh::lean_is_exclusive(v___x_2633_)) as u8;
                if v_isSharedCheck_2643_ == 0 {
                    v___x_2636_ = v___x_2633_;
                    v_isShared_2637_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_2634_);
                    leanh::lean_dec(v___x_2633_);
                    v___x_2636_ = leanh::lean_box(0);
                    v_isShared_2637_ = v_isSharedCheck_2643_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2638_ = l_Lean_unknownIdentifierMessageTag;
                v___x_2639_ = leanh::lean_alloc_ctor(8, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2639_, 0, v___x_2638_);
                leanh::lean_ctor_set(v___x_2639_, 1, v_a_2634_);
                if v_isShared_2637_ == 0 {
                    leanh::lean_ctor_set(v___x_2636_, 0, v___x_2639_);
                    v___x_2641_ = v___x_2636_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2642_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2642_, 0, v___x_2639_);
                    v___x_2641_ = v_reuseFailAlloc_2642_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2641_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6___boxed(
    mut v_msg_2644_: *mut leanh::LeanObject,
    mut v_declHint_2645_: *mut leanh::LeanObject,
    mut v___y_2646_: *mut leanh::LeanObject,
    mut v___y_2647_: *mut leanh::LeanObject,
    mut v___y_2648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2649_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2649_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_2644_, v_declHint_2645_, v___y_2646_, v___y_2647_);
    leanh::lean_dec(v___y_2647_);
    leanh::lean_dec_ref(v___y_2646_);
    return v_res_2649_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_ref_2650_: *mut leanh::LeanObject,
    mut v_msg_2651_: *mut leanh::LeanObject,
    mut v_declHint_2652_: *mut leanh::LeanObject,
    mut v___y_2653_: *mut leanh::LeanObject,
    mut v___y_2654_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2658_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2656_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6(v_msg_2651_, v_declHint_2652_, v___y_2653_, v___y_2654_);
    v_a_2657_ = leanh::lean_ctor_get(v___x_2656_, 0);
    leanh::lean_inc(v_a_2657_);
    leanh::lean_dec_ref(v___x_2656_);
    v___x_2658_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_2650_, v_a_2657_, v___y_2653_, v___y_2654_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_ref_2659_: *mut leanh::LeanObject,
    mut v_msg_2660_: *mut leanh::LeanObject,
    mut v_declHint_2661_: *mut leanh::LeanObject,
    mut v___y_2662_: *mut leanh::LeanObject,
    mut v___y_2663_: *mut leanh::LeanObject,
    mut v___y_2664_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2665_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2659_, v_msg_2660_, v_declHint_2661_, v___y_2662_, v___y_2663_);
    leanh::lean_dec(v___y_2663_);
    leanh::lean_dec_ref(v___y_2662_);
    leanh::lean_dec(v_ref_2659_);
    return v_res_2665_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2667_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__0;
    v___x_2668_ = l_Lean_stringToMessageData(v___x_2667_);
    return v___x_2668_;
}
pub unsafe fn _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2670_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2670_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__2;
    v___x_2671_ = l_Lean_stringToMessageData(v___x_2670_);
    return v___x_2671_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(
    mut v_ref_2672_: *mut leanh::LeanObject,
    mut v_constName_2673_: *mut leanh::LeanObject,
    mut v___y_2674_: *mut leanh::LeanObject,
    mut v___y_2675_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2678_: u8 = 0;
    let mut v___x_2679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2677_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__1);
    v___x_2678_ = 0;
    leanh::lean_inc(v_constName_2673_);
    v___x_2679_ = l_Lean_MessageData_ofConstName(v_constName_2673_, v___x_2678_);
    v___x_2680_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2680_, 0, v___x_2677_);
    leanh::lean_ctor_set(v___x_2680_, 1, v___x_2679_);
    v___x_2681_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3);
    v___x_2682_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_2682_, 0, v___x_2680_);
    leanh::lean_ctor_set(v___x_2682_, 1, v___x_2681_);
    v___x_2683_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2672_, v___x_2682_, v_constName_2673_, v___y_2674_, v___y_2675_);
    return v___x_2683_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_ref_2684_: *mut leanh::LeanObject,
    mut v_constName_2685_: *mut leanh::LeanObject,
    mut v___y_2686_: *mut leanh::LeanObject,
    mut v___y_2687_: *mut leanh::LeanObject,
    mut v___y_2688_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2689_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_2684_, v_constName_2685_, v___y_2686_, v___y_2687_);
    leanh::lean_dec(v___y_2687_);
    leanh::lean_dec_ref(v___y_2686_);
    leanh::lean_dec(v_ref_2684_);
    return v_res_2689_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(
    mut v_constName_2690_: *mut leanh::LeanObject,
    mut v___y_2691_: *mut leanh::LeanObject,
    mut v___y_2692_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_2694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ref_2694_ = leanh::lean_ctor_get(v___y_2691_, 5);
    v___x_2695_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_2694_, v_constName_2690_, v___y_2691_, v___y_2692_);
    return v___x_2695_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg___boxed(
    mut v_constName_2696_: *mut leanh::LeanObject,
    mut v___y_2697_: *mut leanh::LeanObject,
    mut v___y_2698_: *mut leanh::LeanObject,
    mut v___y_2699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2700_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2700_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_2696_, v___y_2697_, v___y_2698_);
    leanh::lean_dec(v___y_2698_);
    leanh::lean_dec_ref(v___y_2697_);
    return v_res_2700_;
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(
    mut v_constName_2701_: *mut leanh::LeanObject,
    mut v___y_2702_: *mut leanh::LeanObject,
    mut v___y_2703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2707_: u8 = 0;
    let mut v___x_2708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2713_: u8 = 0;
    let mut v___x_2715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2705_ = lean_st_ref_get(v___y_2703_);
                v_env_2706_ = leanh::lean_ctor_get(v___x_2705_, 0);
                leanh::lean_inc_ref(v_env_2706_);
                leanh::lean_dec(v___x_2705_);
                v___x_2707_ = 0;
                leanh::lean_inc(v_constName_2701_);
                v___x_2708_ =
                    l_Lean_Environment_find_x3f(v_env_2706_, v_constName_2701_, v___x_2707_);
                if leanh::lean_obj_tag(v___x_2708_) == 0 {
                    v___x_2709_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_2701_, v___y_2702_, v___y_2703_);
                    return v___x_2709_;
                } else {
                    leanh::lean_dec(v_constName_2701_);
                    v_val_2710_ = leanh::lean_ctor_get(v___x_2708_, 0);
                    v_isSharedCheck_2717_ = (!leanh::lean_is_exclusive(v___x_2708_)) as u8;
                    if v_isSharedCheck_2717_ == 0 {
                        v___x_2712_ = v___x_2708_;
                        v_isShared_2713_ = v_isSharedCheck_2717_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_2710_);
                        leanh::lean_dec(v___x_2708_);
                        v___x_2712_ = leanh::lean_box(0);
                        v_isShared_2713_ = v_isSharedCheck_2717_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2713_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_2712_, 0);
                    v___x_2715_ = v___x_2712_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_val_2710_);
                    v___x_2715_ = v_reuseFailAlloc_2716_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0___boxed(
    mut v_constName_2718_: *mut leanh::LeanObject,
    mut v___y_2719_: *mut leanh::LeanObject,
    mut v___y_2720_: *mut leanh::LeanObject,
    mut v___y_2721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2722_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(
        v_constName_2718_,
        v___y_2719_,
        v___y_2720_,
    );
    leanh::lean_dec(v___y_2720_);
    leanh::lean_dec_ref(v___y_2719_);
    return v_res_2722_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_addPass___closed__4() -> *mut leanh::LeanObject {
    let mut v___x_2732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2734_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2732_ = leanh::lean_box(0);
    v___x_2733_ = l_Lean_Compiler_LCNF_addPass___closed__3;
    v___x_2734_ = l_Lean_mkConst(v___x_2733_, v___x_2732_);
    return v___x_2734_;
}
pub unsafe fn l_Lean_Compiler_LCNF_addPass(
    mut v_declName_2735_: *mut leanh::LeanObject,
    mut v_a_2736_: *mut leanh::LeanObject,
    mut v_a_2737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_2753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_2757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: u8 = 0;
    let mut v___x_2760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: u8 = 0;
    let mut v___x_2764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2772_: u8 = 0;
    let mut v___x_2773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_2775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_2776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_2777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_2778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_2779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_2780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_2781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2784_: u8 = 0;
    let mut v___x_2785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_2786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_2787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2799_: u8 = 0;
    let mut v_unused_2800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2801_: u8 = 0;
    let mut v_a_2802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2805_: u8 = 0;
    let mut v___x_2807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2809_: u8 = 0;
    let mut v_a_2810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2817_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc(v_declName_2735_);
                v___x_2739_ = l_Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0(
                    v_declName_2735_,
                    v_a_2736_,
                    v_a_2737_,
                );
                if leanh::lean_obj_tag(v___x_2739_) == 0 {
                    v_a_2740_ = leanh::lean_ctor_get(v___x_2739_, 0);
                    leanh::lean_inc(v_a_2740_);
                    leanh::lean_dec_ref_known(v___x_2739_, 1);
                    v___x_2748_ = l_Lean_ConstantInfo_type(v_a_2740_);
                    if leanh::lean_obj_tag(v___x_2748_) == 4 {
                        v_declName_2749_ = leanh::lean_ctor_get(v___x_2748_, 0);
                        leanh::lean_inc(v_declName_2749_);
                        leanh::lean_dec_ref_known(v___x_2748_, 2);
                        if leanh::lean_obj_tag(v_declName_2749_) == 1 {
                            v_pre_2750_ = leanh::lean_ctor_get(v_declName_2749_, 0);
                            leanh::lean_inc(v_pre_2750_);
                            if leanh::lean_obj_tag(v_pre_2750_) == 1 {
                                v_pre_2751_ = leanh::lean_ctor_get(v_pre_2750_, 0);
                                leanh::lean_inc(v_pre_2751_);
                                if leanh::lean_obj_tag(v_pre_2751_) == 1 {
                                    v_pre_2752_ = leanh::lean_ctor_get(v_pre_2751_, 0);
                                    leanh::lean_inc(v_pre_2752_);
                                    if leanh::lean_obj_tag(v_pre_2752_) == 1 {
                                        v_pre_2753_ = leanh::lean_ctor_get(v_pre_2752_, 0);
                                        leanh::lean_inc(v_pre_2753_);
                                        if leanh::lean_obj_tag(v_pre_2753_) == 0 {
                                            v_str_2754_ =
                                                leanh::lean_ctor_get(v_declName_2749_, 1);
                                            leanh::lean_inc_ref(v_str_2754_);
                                            leanh::lean_dec_ref_known(v_declName_2749_, 2);
                                            v_str_2755_ =
                                                leanh::lean_ctor_get(v_pre_2750_, 1);
                                            leanh::lean_inc_ref(v_str_2755_);
                                            leanh::lean_dec_ref_known(v_pre_2750_, 2);
                                            v_str_2756_ =
                                                leanh::lean_ctor_get(v_pre_2751_, 1);
                                            leanh::lean_inc_ref(v_str_2756_);
                                            leanh::lean_dec_ref_known(v_pre_2751_, 2);
                                            v_str_2757_ =
                                                leanh::lean_ctor_get(v_pre_2752_, 1);
                                            leanh::lean_inc_ref(v_str_2757_);
                                            leanh::lean_dec_ref_known(v_pre_2752_, 2);
                                            v___x_2758_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
                                            v___x_2759_ =
                                                lean_string_dec_eq(v_str_2757_, v___x_2758_);
                                            leanh::lean_dec_ref(v_str_2757_);
                                            if v___x_2759_ == 0 {
                                                leanh::lean_dec_ref(v_str_2756_);
                                                leanh::lean_dec_ref(v_str_2755_);
                                                leanh::lean_dec_ref(v_str_2754_);
                                                v___y_2742_ = v_a_2736_;
                                                v___y_2743_ = v_a_2737_;
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_2760_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
                                                v___x_2761_ =
                                                    lean_string_dec_eq(v_str_2756_, v___x_2760_);
                                                leanh::lean_dec_ref(v_str_2756_);
                                                if v___x_2761_ == 0 {
                                                    leanh::lean_dec_ref(v_str_2755_);
                                                    leanh::lean_dec_ref(v_str_2754_);
                                                    v___y_2742_ = v_a_2736_;
                                                    v___y_2743_ = v_a_2737_;
                                                    state = 1;
                                                    continue;
                                                } else {
                                                    v___x_2762_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_;
                                                    v___x_2763_ = lean_string_dec_eq(
                                                        v_str_2755_,
                                                        v___x_2762_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_2755_);
                                                    if v___x_2763_ == 0 {
                                                        leanh::lean_dec_ref(v_str_2754_);
                                                        v___y_2742_ = v_a_2736_;
                                                        v___y_2743_ = v_a_2737_;
                                                        state = 1;
                                                        continue;
                                                    } else {
                                                        v___x_2764_ = l_Lean_Compiler_LCNF_addPass___closed__2;
                                                        v___x_2765_ = lean_string_dec_eq(
                                                            v_str_2754_,
                                                            v___x_2764_,
                                                        );
                                                        leanh::lean_dec_ref(v_str_2754_);
                                                        if v___x_2765_ == 0 {
                                                            v___y_2742_ = v_a_2736_;
                                                            v___y_2743_ = v_a_2737_;
                                                            state = 1;
                                                            continue;
                                                        } else {
                                                            leanh::lean_dec(v_a_2740_);
                                                            v___x_2766_ = l_Lean_Compiler_LCNF_getPassManager___redArg(v_a_2737_);
                                                            v_a_2767_ = leanh::lean_ctor_get(
                                                                v___x_2766_,
                                                                0,
                                                            );
                                                            leanh::lean_inc(v_a_2767_);
                                                            leanh::lean_dec_ref(v___x_2766_);
                                                            leanh::lean_inc(
                                                                v_declName_2735_,
                                                            );
                                                            v___x_2768_ = l_Lean_Compiler_LCNF_PassInstaller_runFromDecl(v_a_2767_, v_declName_2735_, v_a_2736_, v_a_2737_);
                                                            if leanh::lean_obj_tag(
                                                                v___x_2768_,
                                                            ) == 0
                                                            {
                                                                v_a_2769_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2768_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2801_ = (!leanh::lean_is_exclusive(v___x_2768_)) as u8;
                                                                if v_isSharedCheck_2801_ == 0 {
                                                                    v___x_2771_ = v___x_2768_;
                                                                    v_isShared_2772_ =
                                                                        v_isSharedCheck_2801_;
                                                                    state = 2;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_2769_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_2768_,
                                                                    );
                                                                    v___x_2771_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_2772_ =
                                                                        v_isSharedCheck_2801_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                leanh::lean_dec(
                                                                    v_declName_2735_,
                                                                );
                                                                v_a_2802_ =
                                                                    leanh::lean_ctor_get(
                                                                        v___x_2768_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2809_ = (!leanh::lean_is_exclusive(v___x_2768_)) as u8;
                                                                if v_isSharedCheck_2809_ == 0 {
                                                                    v___x_2804_ = v___x_2768_;
                                                                    v_isShared_2805_ =
                                                                        v_isSharedCheck_2809_;
                                                                    state = 6;
                                                                    continue;
                                                                } else {
                                                                    leanh::lean_inc(
                                                                        v_a_2802_,
                                                                    );
                                                                    leanh::lean_dec(
                                                                        v___x_2768_,
                                                                    );
                                                                    v___x_2804_ =
                                                                        leanh::lean_box(0);
                                                                    v_isShared_2805_ =
                                                                        v_isSharedCheck_2809_;
                                                                    state = 6;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec(v_pre_2753_);
                                            leanh::lean_dec_ref_known(v_pre_2752_, 2);
                                            leanh::lean_dec_ref_known(v_pre_2751_, 2);
                                            leanh::lean_dec_ref_known(v_pre_2750_, 2);
                                            leanh::lean_dec_ref_known(v_declName_2749_, 2);
                                            v___y_2742_ = v_a_2736_;
                                            v___y_2743_ = v_a_2737_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_pre_2752_);
                                        leanh::lean_dec_ref_known(v_pre_2751_, 2);
                                        leanh::lean_dec_ref_known(v_pre_2750_, 2);
                                        leanh::lean_dec_ref_known(v_declName_2749_, 2);
                                        v___y_2742_ = v_a_2736_;
                                        v___y_2743_ = v_a_2737_;
                                        state = 1;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v_pre_2750_, 2);
                                    leanh::lean_dec(v_pre_2751_);
                                    leanh::lean_dec_ref_known(v_declName_2749_, 2);
                                    v___y_2742_ = v_a_2736_;
                                    v___y_2743_ = v_a_2737_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_pre_2750_);
                                leanh::lean_dec_ref_known(v_declName_2749_, 2);
                                v___y_2742_ = v_a_2736_;
                                v___y_2743_ = v_a_2737_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_declName_2749_);
                            v___y_2742_ = v_a_2736_;
                            v___y_2743_ = v_a_2737_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_2748_);
                        v___y_2742_ = v_a_2736_;
                        v___y_2743_ = v_a_2737_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_2735_);
                    v_a_2810_ = leanh::lean_ctor_get(v___x_2739_, 0);
                    v_isSharedCheck_2817_ = (!leanh::lean_is_exclusive(v___x_2739_)) as u8;
                    if v_isSharedCheck_2817_ == 0 {
                        v___x_2812_ = v___x_2739_;
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_2810_);
                        leanh::lean_dec(v___x_2739_);
                        v___x_2812_ = leanh::lean_box(0);
                        v_isShared_2813_ = v_isSharedCheck_2817_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2744_ = l_Lean_Compiler_LCNF_addPass___closed__1;
                v___x_2745_ = l_Lean_ConstantInfo_type(v_a_2740_);
                leanh::lean_dec(v_a_2740_);
                v___x_2746_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_addPass___closed__4),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_addPass___closed__4_once),
                    _init_l_Lean_Compiler_LCNF_addPass___closed__4,
                );
                v___x_2747_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(v___x_2744_, v_declName_2735_, v___x_2745_, v___x_2746_, v___y_2742_, v___y_2743_);
                return v___x_2747_;
            }
            2 => {
                v___x_2773_ = lean_st_ref_take(v_a_2737_);
                v_env_2774_ = leanh::lean_ctor_get(v___x_2773_, 0);
                v_nextMacroScope_2775_ = leanh::lean_ctor_get(v___x_2773_, 1);
                v_ngen_2776_ = leanh::lean_ctor_get(v___x_2773_, 2);
                v_auxDeclNGen_2777_ = leanh::lean_ctor_get(v___x_2773_, 3);
                v_traceState_2778_ = leanh::lean_ctor_get(v___x_2773_, 4);
                v_messages_2779_ = leanh::lean_ctor_get(v___x_2773_, 6);
                v_infoState_2780_ = leanh::lean_ctor_get(v___x_2773_, 7);
                v_snapshotTasks_2781_ = leanh::lean_ctor_get(v___x_2773_, 8);
                v_isSharedCheck_2799_ = (!leanh::lean_is_exclusive(v___x_2773_)) as u8;
                if v_isSharedCheck_2799_ == 0 {
                    v_unused_2800_ = leanh::lean_ctor_get(v___x_2773_, 5);
                    leanh::lean_dec(v_unused_2800_);
                    v___x_2783_ = v___x_2773_;
                    v_isShared_2784_ = v_isSharedCheck_2799_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_2781_);
                    leanh::lean_inc(v_infoState_2780_);
                    leanh::lean_inc(v_messages_2779_);
                    leanh::lean_inc(v_traceState_2778_);
                    leanh::lean_inc(v_auxDeclNGen_2777_);
                    leanh::lean_inc(v_ngen_2776_);
                    leanh::lean_inc(v_nextMacroScope_2775_);
                    leanh::lean_inc(v_env_2774_);
                    leanh::lean_dec(v___x_2773_);
                    v___x_2783_ = leanh::lean_box(0);
                    v_isShared_2784_ = v_isSharedCheck_2799_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2785_ = l_Lean_Compiler_LCNF_passManagerExt;
                v_toEnvExtension_2786_ = leanh::lean_ctor_get(v___x_2785_, 0);
                v_asyncMode_2787_ = leanh::lean_ctor_get(v_toEnvExtension_2786_, 2);
                v___x_2788_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2788_, 0, v_declName_2735_);
                leanh::lean_ctor_set(v___x_2788_, 1, v_a_2769_);
                v___x_2789_ = l_Lean_PersistentEnvExtension_addEntry___redArg(
                    v___x_2785_,
                    v_env_2774_,
                    v___x_2788_,
                    v_asyncMode_2787_,
                    v_pre_2753_,
                );
                v___x_2790_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Pass_saveImpure_spec__0___redArg___closed__2);
                if v_isShared_2784_ == 0 {
                    leanh::lean_ctor_set(v___x_2783_, 5, v___x_2790_);
                    leanh::lean_ctor_set(v___x_2783_, 0, v___x_2789_);
                    v___x_2792_ = v___x_2783_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2798_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2789_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_nextMacroScope_2775_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_ngen_2776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 3, v_auxDeclNGen_2777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 4, v_traceState_2778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 5, v___x_2790_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 6, v_messages_2779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 7, v_infoState_2780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2798_, 8, v_snapshotTasks_2781_);
                    v___x_2792_ = v_reuseFailAlloc_2798_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_2793_ = lean_st_ref_set(v_a_2737_, v___x_2792_);
                v___x_2794_ = leanh::lean_box(0);
                if v_isShared_2772_ == 0 {
                    leanh::lean_ctor_set(v___x_2771_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2771_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2796_;
            }
            6 => {
                if v_isShared_2805_ == 0 {
                    v___x_2807_ = v___x_2804_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v_a_2802_);
                    v___x_2807_ = v_reuseFailAlloc_2808_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2807_;
            }
            8 => {
                if v_isShared_2813_ == 0 {
                    v___x_2815_ = v___x_2812_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2816_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2816_, 0, v_a_2810_);
                    v___x_2815_ = v_reuseFailAlloc_2816_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2815_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_addPass___boxed(
    mut v_declName_2818_: *mut leanh::LeanObject,
    mut v_a_2819_: *mut leanh::LeanObject,
    mut v_a_2820_: *mut leanh::LeanObject,
    mut v_a_2821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2822_ = l_Lean_Compiler_LCNF_addPass(v_declName_2818_, v_a_2819_, v_a_2820_);
    leanh::lean_dec(v_a_2820_);
    leanh::lean_dec_ref(v_a_2819_);
    return v_res_2822_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1(
    mut v_00_u03b1_2823_: *mut leanh::LeanObject,
    mut v_attrName_2824_: *mut leanh::LeanObject,
    mut v_declName_2825_: *mut leanh::LeanObject,
    mut v_givenType_2826_: *mut leanh::LeanObject,
    mut v_expectedType_2827_: *mut leanh::LeanObject,
    mut v___y_2828_: *mut leanh::LeanObject,
    mut v___y_2829_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2831_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2831_ =
        l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___redArg(
            v_attrName_2824_,
            v_declName_2825_,
            v_givenType_2826_,
            v_expectedType_2827_,
            v___y_2828_,
            v___y_2829_,
        );
    return v___x_2831_;
}
pub unsafe fn l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1___boxed(
    mut v_00_u03b1_2832_: *mut leanh::LeanObject,
    mut v_attrName_2833_: *mut leanh::LeanObject,
    mut v_declName_2834_: *mut leanh::LeanObject,
    mut v_givenType_2835_: *mut leanh::LeanObject,
    mut v_expectedType_2836_: *mut leanh::LeanObject,
    mut v___y_2837_: *mut leanh::LeanObject,
    mut v___y_2838_: *mut leanh::LeanObject,
    mut v___y_2839_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2840_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2840_ = l_Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1(
        v_00_u03b1_2832_,
        v_attrName_2833_,
        v_declName_2834_,
        v_givenType_2835_,
        v_expectedType_2836_,
        v___y_2837_,
        v___y_2838_,
    );
    leanh::lean_dec(v___y_2838_);
    leanh::lean_dec_ref(v___y_2837_);
    return v_res_2840_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0(
    mut v_00_u03b1_2841_: *mut leanh::LeanObject,
    mut v_constName_2842_: *mut leanh::LeanObject,
    mut v___y_2843_: *mut leanh::LeanObject,
    mut v___y_2844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2846_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2846_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___redArg(v_constName_2842_, v___y_2843_, v___y_2844_);
    return v___x_2846_;
}
pub unsafe fn l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0___boxed(
    mut v_00_u03b1_2847_: *mut leanh::LeanObject,
    mut v_constName_2848_: *mut leanh::LeanObject,
    mut v___y_2849_: *mut leanh::LeanObject,
    mut v___y_2850_: *mut leanh::LeanObject,
    mut v___y_2851_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2852_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2852_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0(v_00_u03b1_2847_, v_constName_2848_, v___y_2849_, v___y_2850_);
    leanh::lean_dec(v___y_2850_);
    leanh::lean_dec_ref(v___y_2849_);
    return v_res_2852_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2(
    mut v_00_u03b1_2853_: *mut leanh::LeanObject,
    mut v_msg_2854_: *mut leanh::LeanObject,
    mut v___y_2855_: *mut leanh::LeanObject,
    mut v___y_2856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2858_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v_msg_2854_, v___y_2855_, v___y_2856_);
    return v___x_2858_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___boxed(
    mut v_00_u03b1_2859_: *mut leanh::LeanObject,
    mut v_msg_2860_: *mut leanh::LeanObject,
    mut v___y_2861_: *mut leanh::LeanObject,
    mut v___y_2862_: *mut leanh::LeanObject,
    mut v___y_2863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2864_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2(v_00_u03b1_2859_, v_msg_2860_, v___y_2861_, v___y_2862_);
    leanh::lean_dec(v___y_2862_);
    leanh::lean_dec_ref(v___y_2861_);
    return v_res_2864_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1(
    mut v_00_u03b1_2865_: *mut leanh::LeanObject,
    mut v_ref_2866_: *mut leanh::LeanObject,
    mut v_constName_2867_: *mut leanh::LeanObject,
    mut v___y_2868_: *mut leanh::LeanObject,
    mut v___y_2869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2871_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2871_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg(v_ref_2866_, v_constName_2867_, v___y_2868_, v___y_2869_);
    return v___x_2871_;
}
pub unsafe fn l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b1_2872_: *mut leanh::LeanObject,
    mut v_ref_2873_: *mut leanh::LeanObject,
    mut v_constName_2874_: *mut leanh::LeanObject,
    mut v___y_2875_: *mut leanh::LeanObject,
    mut v___y_2876_: *mut leanh::LeanObject,
    mut v___y_2877_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2878_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1(v_00_u03b1_2872_, v_ref_2873_, v_constName_2874_, v___y_2875_, v___y_2876_);
    leanh::lean_dec(v___y_2876_);
    leanh::lean_dec_ref(v___y_2875_);
    leanh::lean_dec(v_ref_2873_);
    return v_res_2878_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_2879_: *mut leanh::LeanObject,
    mut v_ref_2880_: *mut leanh::LeanObject,
    mut v_msg_2881_: *mut leanh::LeanObject,
    mut v_declHint_2882_: *mut leanh::LeanObject,
    mut v___y_2883_: *mut leanh::LeanObject,
    mut v___y_2884_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2886_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2886_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___redArg(v_ref_2880_, v_msg_2881_, v_declHint_2882_, v___y_2883_, v___y_2884_);
    return v___x_2886_;
}
pub unsafe fn l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_2887_: *mut leanh::LeanObject,
    mut v_ref_2888_: *mut leanh::LeanObject,
    mut v_msg_2889_: *mut leanh::LeanObject,
    mut v_declHint_2890_: *mut leanh::LeanObject,
    mut v___y_2891_: *mut leanh::LeanObject,
    mut v___y_2892_: *mut leanh::LeanObject,
    mut v___y_2893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2894_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3(v_00_u03b1_2887_, v_ref_2888_, v_msg_2889_, v_declHint_2890_, v___y_2891_, v___y_2892_);
    leanh::lean_dec(v___y_2892_);
    leanh::lean_dec_ref(v___y_2891_);
    leanh::lean_dec(v_ref_2888_);
    return v_res_2894_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7(
    mut v_msg_2895_: *mut leanh::LeanObject,
    mut v_declHint_2896_: *mut leanh::LeanObject,
    mut v___y_2897_: *mut leanh::LeanObject,
    mut v___y_2898_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2900_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2900_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___redArg(v_msg_2895_, v_declHint_2896_, v___y_2898_);
    return v___x_2900_;
}
pub unsafe fn l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7___boxed(
    mut v_msg_2901_: *mut leanh::LeanObject,
    mut v_declHint_2902_: *mut leanh::LeanObject,
    mut v___y_2903_: *mut leanh::LeanObject,
    mut v___y_2904_: *mut leanh::LeanObject,
    mut v___y_2905_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2906_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__6_spec__7(v_msg_2901_, v_declHint_2902_, v___y_2903_, v___y_2904_);
    leanh::lean_dec(v___y_2904_);
    leanh::lean_dec_ref(v___y_2903_);
    return v_res_2906_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7(
    mut v_00_u03b1_2907_: *mut leanh::LeanObject,
    mut v_ref_2908_: *mut leanh::LeanObject,
    mut v_msg_2909_: *mut leanh::LeanObject,
    mut v___y_2910_: *mut leanh::LeanObject,
    mut v___y_2911_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2913_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2913_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___redArg(v_ref_2908_, v_msg_2909_, v___y_2910_, v___y_2911_);
    return v___x_2913_;
}
pub unsafe fn l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7___boxed(
    mut v_00_u03b1_2914_: *mut leanh::LeanObject,
    mut v_ref_2915_: *mut leanh::LeanObject,
    mut v_msg_2916_: *mut leanh::LeanObject,
    mut v___y_2917_: *mut leanh::LeanObject,
    mut v___y_2918_: *mut leanh::LeanObject,
    mut v___y_2919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_2920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_2920_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1_spec__3_spec__7(v_00_u03b1_2914_, v_ref_2915_, v_msg_2916_, v___y_2917_, v___y_2918_);
    leanh::lean_dec(v___y_2918_);
    leanh::lean_dec_ref(v___y_2917_);
    leanh::lean_dec(v_ref_2915_);
    return v_res_2920_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_2922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2922_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__0;
    v___x_2923_ = l_Lean_stringToMessageData(v___x_2922_);
    return v___x_2923_;
}
pub unsafe fn _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_2925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2926_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2925_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__2;
    v___x_2926_ = l_Lean_stringToMessageData(v___x_2925_);
    return v___x_2926_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(
    mut v_name_2930_: *mut leanh::LeanObject,
    mut v_kind_2931_: u8,
    mut v___y_2932_: *mut leanh::LeanObject,
    mut v___y_2933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_2935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2935_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__1);
                v___x_2936_ = l_Lean_MessageData_ofName(v_name_2930_);
                v___x_2937_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2937_, 0, v___x_2935_);
                leanh::lean_ctor_set(v___x_2937_, 1, v___x_2936_);
                v___x_2938_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3_once), _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__3);
                v___x_2939_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2939_, 0, v___x_2937_);
                leanh::lean_ctor_set(v___x_2939_, 1, v___x_2938_);
                match v_kind_2931_ {
                    0 => {
                        v___x_2948_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__4;
                        v___y_2941_ = v___x_2948_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_2949_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__5;
                        v___y_2941_ = v___x_2949_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_2950_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___closed__6;
                        v___y_2941_ = v___x_2950_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                leanh::lean_inc_ref(v___y_2941_);
                v___x_2942_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_2942_, 0, v___y_2941_);
                v___x_2943_ = l_Lean_MessageData_ofFormat(v___x_2942_);
                v___x_2944_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2944_, 0, v___x_2939_);
                leanh::lean_ctor_set(v___x_2944_, 1, v___x_2943_);
                v___x_2945_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3_once), _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Compiler_LCNF_addPass_spec__0_spec__0_spec__1___redArg___closed__3);
                v___x_2946_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_2946_, 0, v___x_2944_);
                leanh::lean_ctor_set(v___x_2946_, 1, v___x_2945_);
                v___x_2947_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_2946_, v___y_2932_, v___y_2933_);
                return v___x_2947_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_name_2951_: *mut leanh::LeanObject,
    mut v_kind_2952_: *mut leanh::LeanObject,
    mut v___y_2953_: *mut leanh::LeanObject,
    mut v___y_2954_: *mut leanh::LeanObject,
    mut v___y_2955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_2956_: u8 = 0;
    let mut v_res_2957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2956_ = (leanh::lean_unbox(v_kind_2952_) as u8);
    v_res_2957_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v_name_2951_, v_kind_boxed_2956_, v___y_2953_, v___y_2954_);
    leanh::lean_dec(v___y_2954_);
    leanh::lean_dec_ref(v___y_2953_);
    return v_res_2957_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(
    mut v___x_2958_: *mut leanh::LeanObject,
    mut v_declName_2959_: *mut leanh::LeanObject,
    mut v_stx_2960_: *mut leanh::LeanObject,
    mut v_kind_2961_: u8,
    mut v___y_2962_: *mut leanh::LeanObject,
    mut v___y_2963_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_2966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2972_: u8 = 0;
    let mut v___x_2973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2977_: u8 = 0;
    let mut v_unused_2978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: u8 = 0;
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2979_ =
                    l_Lean_Attribute_Builtin_ensureNoArgs(v_stx_2960_, v___y_2962_, v___y_2963_);
                if leanh::lean_obj_tag(v___x_2979_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2979_, 1);
                    v___x_2980_ = 0;
                    v___x_2981_ = l_Lean_instBEqAttributeKind_beq(v_kind_2961_, v___x_2980_);
                    if v___x_2981_ == 0 {
                        leanh::lean_dec(v_declName_2959_);
                        v___x_2982_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v___x_2958_, v_kind_2961_, v___y_2962_, v___y_2963_);
                        return v___x_2982_;
                    } else {
                        v___y_2966_ = v___y_2962_;
                        v___y_2967_ = v___y_2963_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_declName_2959_);
                    leanh::lean_dec(v___x_2958_);
                    return v___x_2979_;
                }
            }
            1 => {
                leanh::lean_inc(v_declName_2959_);
                v___x_2968_ = l_Lean_ensureAttrDeclIsMeta(
                    v___x_2958_,
                    v_declName_2959_,
                    v_kind_2961_,
                    v___y_2966_,
                    v___y_2967_,
                );
                if leanh::lean_obj_tag(v___x_2968_) == 0 {
                    leanh::lean_dec_ref_known(v___x_2968_, 1);
                    v___x_2969_ =
                        l_Lean_Compiler_LCNF_addPass(v_declName_2959_, v___y_2966_, v___y_2967_);
                    if leanh::lean_obj_tag(v___x_2969_) == 0 {
                        v_isSharedCheck_2977_ =
                            (!leanh::lean_is_exclusive(v___x_2969_)) as u8;
                        if v_isSharedCheck_2977_ == 0 {
                            v_unused_2978_ = leanh::lean_ctor_get(v___x_2969_, 0);
                            leanh::lean_dec(v_unused_2978_);
                            v___x_2971_ = v___x_2969_;
                            v_isShared_2972_ = v_isSharedCheck_2977_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_2969_);
                            v___x_2971_ = leanh::lean_box(0);
                            v_isShared_2972_ = v_isSharedCheck_2977_;
                            state = 2;
                            continue;
                        }
                    } else {
                        return v___x_2969_;
                    }
                } else {
                    leanh::lean_dec(v_declName_2959_);
                    return v___x_2968_;
                }
            }
            2 => {
                v___x_2973_ = leanh::lean_box(0);
                if v_isShared_2972_ == 0 {
                    leanh::lean_ctor_set(v___x_2971_, 0, v___x_2973_);
                    v___x_2975_ = v___x_2971_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2976_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_2976_, 0, v___x_2973_);
                    v___x_2975_ = v_reuseFailAlloc_2976_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(
    mut v___x_2983_: *mut leanh::LeanObject,
    mut v_declName_2984_: *mut leanh::LeanObject,
    mut v_stx_2985_: *mut leanh::LeanObject,
    mut v_kind_2986_: *mut leanh::LeanObject,
    mut v___y_2987_: *mut leanh::LeanObject,
    mut v___y_2988_: *mut leanh::LeanObject,
    mut v___y_2989_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_2990_: u8 = 0;
    let mut v_res_2991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_2990_ = (leanh::lean_unbox(v_kind_2986_) as u8);
    v_res_2991_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(v___x_2983_, v_declName_2984_, v_stx_2985_, v_kind_boxed_2990_, v___y_2987_, v___y_2988_);
    leanh::lean_dec(v___y_2988_);
    leanh::lean_dec_ref(v___y_2987_);
    return v_res_2991_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2993_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__0_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___x_2994_ = l_Lean_stringToMessageData(v___x_2993_);
    return v___x_2994_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_2996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_2996_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__2_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___x_2997_ = l_Lean_stringToMessageData(v___x_2996_);
    return v___x_2997_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(
    mut v___x_2998_: *mut leanh::LeanObject,
    mut v_decl_2999_: *mut leanh::LeanObject,
    mut v___y_3000_: *mut leanh::LeanObject,
    mut v___y_3001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3003_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3004_ = l_Lean_MessageData_ofName(v___x_2998_);
    v___x_3005_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3005_, 0, v___x_3003_);
    leanh::lean_ctor_set(v___x_3005_, 1, v___x_3004_);
    v___x_3006_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1___closed__3_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3007_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_3007_, 0, v___x_3005_);
    leanh::lean_ctor_set(v___x_3007_, 1, v___x_3006_);
    v___x_3008_ = l_Lean_throwError___at___00Lean_throwAttrDeclNotOfExpectedType___at___00Lean_Compiler_LCNF_addPass_spec__1_spec__2___redArg(v___x_3007_, v___y_3000_, v___y_3001_);
    return v___x_3008_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(
    mut v___x_3009_: *mut leanh::LeanObject,
    mut v_decl_3010_: *mut leanh::LeanObject,
    mut v___y_3011_: *mut leanh::LeanObject,
    mut v___y_3012_: *mut leanh::LeanObject,
    mut v___y_3013_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3014_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___lam__1_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_(v___x_3009_, v_decl_3010_, v___y_3011_, v___y_3012_);
    leanh::lean_dec(v___y_3012_);
    leanh::lean_dec_ref(v___y_3011_);
    leanh::lean_dec(v_decl_3010_);
    return v_res_3014_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3064_ = leanh::lean_unsigned_to_nat(3159741348);
    v___x_3065_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___x_3066_ = l_Lean_Name_num___override(v___x_3065_, v___x_3064_);
    return v___x_3066_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3068_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___x_3069_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3070_ = l_Lean_Name_str___override(v___x_3069_, v___x_3068_);
    return v___x_3070_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3072_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___x_3073_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3074_ = l_Lean_Name_str___override(v___x_3073_, v___x_3072_);
    return v___x_3074_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3075_ = leanh::lean_unsigned_to_nat(2);
    v___x_3076_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3077_ = l_Lean_Name_num___override(v___x_3076_, v___x_3075_);
    return v___x_3077_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3083_: u8 = 0;
    let mut v___x_3084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3087_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3083_ = 1;
    v___x_3084_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___x_3085_ = l_Lean_Compiler_LCNF_addPass___closed__1;
    v___x_3086_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3087_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_3087_, 0, v___x_3086_);
    leanh::lean_ctor_set(v___x_3087_, 1, v___x_3085_);
    leanh::lean_ctor_set(v___x_3087_, 2, v___x_3084_);
    leanh::lean_ctor_set_uint8(
        v___x_3087_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_3083_,
    );
    return v___x_3087_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_3088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_3088_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___f_3089_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_;
    v___x_3090_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3091_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_3091_, 0, v___x_3090_);
    leanh::lean_ctor_set(v___x_3091_, 1, v___f_3089_);
    leanh::lean_ctor_set(v___x_3091_, 2, v___f_3088_);
    return v___x_3091_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3093_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_);
    v___x_3094_ = l_Lean_registerBuiltinAttribute(v___x_3093_);
    return v___x_3094_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2____boxed(
    mut v_a_3095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3096_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_();
    return v_res_3096_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0(
    mut v_00_u03b1_3097_: *mut leanh::LeanObject,
    mut v_name_3098_: *mut leanh::LeanObject,
    mut v_kind_3099_: u8,
    mut v___y_3100_: *mut leanh::LeanObject,
    mut v___y_3101_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3103_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3103_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___redArg(v_name_3098_, v_kind_3099_, v___y_3100_, v___y_3101_);
    return v___x_3103_;
}
pub unsafe fn l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03b1_3104_: *mut leanh::LeanObject,
    mut v_name_3105_: *mut leanh::LeanObject,
    mut v_kind_3106_: *mut leanh::LeanObject,
    mut v___y_3107_: *mut leanh::LeanObject,
    mut v___y_3108_: *mut leanh::LeanObject,
    mut v___y_3109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_3110_: u8 = 0;
    let mut v_res_3111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_3110_ = (leanh::lean_unbox(v_kind_3106_) as u8);
    v_res_3111_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2__spec__0(v_00_u03b1_3104_, v_name_3105_, v_kind_boxed_3110_, v___y_3107_, v___y_3108_);
    leanh::lean_dec(v___y_3108_);
    leanh::lean_dec_ref(v___y_3107_);
    return v_res_3111_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_3137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: u8 = 0;
    let mut v___x_3139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3137_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_;
    v___x_3138_ = 1;
    v___x_3139_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_;
    v___x_3140_ = l_Lean_registerTraceClass(v___x_3137_, v___x_3138_, v___x_3139_);
    if leanh::lean_obj_tag(v___x_3140_) == 0 {
        let mut v___x_3141_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3142_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_3140_, 1);
        v___x_3141_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_;
        v___x_3142_ = l_Lean_registerTraceClass(v___x_3141_, v___x_3138_, v___x_3139_);
        if leanh::lean_obj_tag(v___x_3142_) == 0 {
            let mut v___x_3143_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_3144_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_3142_, 1);
            v___x_3143_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_;
            v___x_3144_ = l_Lean_registerTraceClass(v___x_3143_, v___x_3138_, v___x_3139_);
            if leanh::lean_obj_tag(v___x_3144_) == 0 {
                let mut v___x_3145_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_3146_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_3144_, 1);
                v___x_3145_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_;
                v___x_3146_ = l_Lean_registerTraceClass(v___x_3145_, v___x_3138_, v___x_3139_);
                return v___x_3146_;
            } else {
                return v___x_3144_;
            }
        } else {
            return v___x_3142_;
        }
    } else {
        return v___x_3140_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2____boxed(
    mut v_a_3147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3148_ = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_();
    return v_res_3148_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Passes(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CSE(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_JoinPoints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Specialize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToMono(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Visibility(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToImpure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_PushProj(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SimpCase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_InferBorrow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Toposort(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Compiler_LCNF_builtinPassManager = _init_l_Lean_Compiler_LCNF_builtinPassManager();
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_builtinPassManager);
    res = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3698839830____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Compiler_LCNF_passManagerExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Compiler_LCNF_passManagerExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_3159741348____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Passes_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Passes_1750802602____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Passes(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Passes(builtin: u8) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_PullLetDecls(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CSE(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_JoinPoints(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Specialize(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToMono(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_LambdaLifting(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_FloatLetIn(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ElimDeadBranches(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_StructProjCases(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Visibility(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToImpure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_PushProj(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ResetReuse(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_SimpCase(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_InferBorrow(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ExplicitBoxing(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ExplicitRC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_CoalesceRC(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Toposort(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ExpandResetReuse(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_SimpleGroundExpr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Passes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Passes(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Passes(builtin);
}