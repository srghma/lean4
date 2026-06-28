// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp
// Imports: Lean.Compiler.LCNF.ReduceJpArity Lean.Compiler.LCNF.Simp.Basic Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.JpCases Lean.Compiler.LCNF.Simp.Config Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.SimpM Lean.Compiler.LCNF.Simp.Main Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.Used
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_mkStr3,
    l_Lean_Name_mkStr4, l_Lean_Name_num___override, l_Lean_Name_str___override,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l_Lean_Compiler_LCNF_Code_size, l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::l_Lean_Compiler_LCNF_getPurity___redArg;
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PassManager::{
    l_Lean_Compiler_LCNF_Pass_mkPerDeclaration,
    l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg, l_Lean_Compiler_LCNF_instInhabitedPass,
};
use crate::r#gen::Lean::Compiler::LCNF::PrettyPrinter::{
    l_Lean_Compiler_LCNF_ppCode, l_Lean_Compiler_LCNF_ppDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::ReduceJpArity::{
    initialize_Lean_Compiler_LCNF_ReduceJpArity, l_Lean_Compiler_LCNF_Decl_reduceJpArity,
    runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity,
};
use crate::r#gen::Lean::Compiler::LCNF::Renaming::l_Lean_Compiler_LCNF_Code_applyRenaming;
use crate::r#gen::Lean::Compiler::LCNF::Simp::Basic::{
    initialize_Lean_Compiler_LCNF_Simp_Basic, runtime_initialize_Lean_Compiler_LCNF_Simp_Basic,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::Config::{
    initialize_Lean_Compiler_LCNF_Simp_Config, runtime_initialize_Lean_Compiler_LCNF_Simp_Config,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::DefaultAlt::{
    initialize_Lean_Compiler_LCNF_Simp_DefaultAlt,
    runtime_initialize_Lean_Compiler_LCNF_Simp_DefaultAlt,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::FunDeclInfo::{
    initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo,
    l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format,
    runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::InlineCandidate::{
    initialize_Lean_Compiler_LCNF_Simp_InlineCandidate,
    runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::InlineProj::{
    initialize_Lean_Compiler_LCNF_Simp_InlineProj,
    runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::JpCases::{
    initialize_Lean_Compiler_LCNF_Simp_JpCases, l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f,
    runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::Main::{
    initialize_Lean_Compiler_LCNF_Simp_Main, l_Lean_Compiler_LCNF_Simp_simp,
    runtime_initialize_Lean_Compiler_LCNF_Simp_Main,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpM::{
    initialize_Lean_Compiler_LCNF_Simp_SimpM, l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg,
    runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::SimpValue::{
    initialize_Lean_Compiler_LCNF_Simp_SimpValue,
    runtime_initialize_Lean_Compiler_LCNF_Simp_SimpValue,
};
use crate::r#gen::Lean::Compiler::LCNF::Simp::Used::{
    initialize_Lean_Compiler_LCNF_Simp_Used, runtime_initialize_Lean_Compiler_LCNF_Simp_Used,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::l_Lean_instEmptyCollectionFVarIdHashSet;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::lean_mk_array;
use crate::lean_imports_rs::Init::Data::Int::Basic::lean_nat_to_int;
use crate::lean_imports_rs::Init::Prelude::lean_mk_empty_array_with_capacity;
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3: f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 105, 109, 112, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2_value: crate::leanh::LeanStringObject<5> =
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
        m_data: [115, 116, 97, 116, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_0: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value)
                as *mut crate::leanh::LeanObject,
            2042452093243897853 as *mut crate::leanh::LeanObject,
        ],
    };
static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_1: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_0)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            11260351269579028997 as *mut crate::leanh::LeanObject,
        ],
    };
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__2_value)
                as *mut crate::leanh::LeanObject,
            1633346503863011865 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value: crate::leanh::LeanStringObject<6> =
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
        m_data: [116, 114, 97, 99, 101, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__4_value)
                as *mut crate::leanh::LeanObject,
            14231257465488249300 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7_value: crate::leanh::LeanStringObject<9> =
    crate::leanh::LeanStringObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 9,
        m_capacity: 9,
        m_length: 8,
        m_data: [44, 32, 115, 105, 122, 101, 58, 32, 0],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9_value: crate::leanh::LeanStringObject<
    14,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [44, 32, 35, 32, 118, 105, 115, 105, 116, 101, 100, 58, 32, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11_value: crate::leanh::LeanStringObject<
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
    m_data: [44, 32, 35, 32, 105, 110, 108, 105, 110, 101, 58, 32, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13_value: crate::leanh::LeanStringObject<
    19,
> = crate::leanh::LeanStringObject {
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
        44, 32, 35, 32, 105, 110, 108, 105, 110, 101, 32, 108, 111, 99, 97, 108, 58, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value: crate::leanh::LeanStringObject<
    4,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [110, 101, 119, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [32, 58, 61, 10, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [115, 116, 101, 112, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2042452093243897853 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11260351269579028997 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value_aux_1)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value)
                as *mut crate::leanh::LeanObject,
            1899580914216730241 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_value: crate::leanh::LeanStringObject<
    7,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_value: crate::leanh::LeanStringObject<
    5,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [105, 110, 102, 111, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_0: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value)
            as *mut crate::leanh::LeanObject,
        2042452093243897853 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_1: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value)
            as *mut crate::leanh::LeanObject,
        11260351269579028997 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_2: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__21_value)
            as *mut crate::leanh::LeanObject,
        7114391375504651962 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value_aux_2)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__22_value)
                as *mut crate::leanh::LeanObject,
            6986475323094637670 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25_value: crate::leanh::LeanStringObject<
    2,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [58, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_simp___lam__1___closed__0_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value)
                as *mut crate::leanh::LeanObject,
            13994041031692860867 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_simp___lam__1___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_simp___lam__1___closed__0_value)
        as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value) as *mut crate::leanh::LeanObject,11260351269579028997 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,12083366481402619969 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,14629059294864442468 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8517981871186407109 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value) as *mut crate::leanh::LeanObject,5011576643341190019 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,9182225960428293262 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4807581633879355939 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7681412766860519702 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8091713760975198655 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value) as *mut crate::leanh::LeanObject,12227809817628263761 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8283643305148160596 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,7009559383324688616 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 1672504145 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,5106008647149914696 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,1410591350330125423 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10812710185534408279 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,2710134935888211714 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0_value) as *mut crate::leanh::LeanObject,2042452093243897853 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1_value) as *mut crate::leanh::LeanObject,11260351269579028997 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18_value) as *mut crate::leanh::LeanObject,1899580914216730241 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15_value) as *mut crate::leanh::LeanObject,10573577049475885148 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_672_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_672_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_673_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__0);
    v___x_674_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_674_, 0, v___x_673_);
    return v___x_674_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_675_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__1);
    v___x_676_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_677_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_677_, 0, v___x_676_);
    crate::leanh::lean_ctor_set(v___x_677_, 1, v___x_676_);
    crate::leanh::lean_ctor_set(v___x_677_, 2, v___x_676_);
    crate::leanh::lean_ctor_set(v___x_677_, 3, v___x_676_);
    crate::leanh::lean_ctor_set(v___x_677_, 4, v___x_675_);
    crate::leanh::lean_ctor_set(v___x_677_, 5, v___x_675_);
    crate::leanh::lean_ctor_set(v___x_677_, 6, v___x_675_);
    crate::leanh::lean_ctor_set(v___x_677_, 7, v___x_675_);
    crate::leanh::lean_ctor_set(v___x_677_, 8, v___x_675_);
    crate::leanh::lean_ctor_set(v___x_677_, 9, v___x_675_);
    return v___x_677_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3()
-> f64 {
    let mut v___x_678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_679_: f64 = 0.0;
    v___x_678_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_679_ = lean_float_of_nat(v___x_678_);
    return v___x_679_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(
    mut v_cls_683_: *mut crate::leanh::LeanObject,
    mut v_msg_684_: *mut crate::leanh::LeanObject,
    mut v___y_685_: *mut crate::leanh::LeanObject,
    mut v___y_686_: *mut crate::leanh::LeanObject,
    mut v___y_687_: *mut crate::leanh::LeanObject,
    mut v___y_688_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_698_: u8 = 0;
    let mut v_env_699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_703_: u8 = 0;
    let mut v___x_704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_717_: u8 = 0;
    let mut v_tid_718_: u64 = 0;
    let mut v_traces_719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_722_: u8 = 0;
    let mut v___x_723_: u8 = 0;
    let mut v___x_724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_729_: f64 = 0.0;
    let mut v___x_730_: u8 = 0;
    let mut v___x_731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_749_: u8 = 0;
    let mut v_isSharedCheck_750_: u8 = 0;
    let mut v_isSharedCheck_751_: u8 = 0;
    let mut v_unused_752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_753_: u8 = 0;
    let mut v_a_754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_757_: u8 = 0;
    let mut v___x_759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_761_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_690_ = crate::leanh::lean_ctor_get(v___y_687_, 2);
                v_ref_691_ = crate::leanh::lean_ctor_get(v___y_687_, 5);
                v___x_692_ = lean_st_ref_get(v___y_688_);
                v___x_693_ = lean_st_ref_get(v___y_686_);
                v___x_694_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_685_);
                if crate::leanh::lean_obj_tag(v___x_694_) == 0 {
                    v_a_695_ = crate::leanh::lean_ctor_get(v___x_694_, 0);
                    v_isSharedCheck_753_ = (!crate::leanh::lean_is_exclusive(v___x_694_)) as u8;
                    if v_isSharedCheck_753_ == 0 {
                        v___x_697_ = v___x_694_;
                        v_isShared_698_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_695_);
                        crate::leanh::lean_dec(v___x_694_);
                        v___x_697_ = crate::leanh::lean_box(0);
                        v_isShared_698_ = v_isSharedCheck_753_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_693_);
                    crate::leanh::lean_dec(v___x_692_);
                    crate::leanh::lean_dec_ref(v_msg_684_);
                    crate::leanh::lean_dec(v_cls_683_);
                    v_a_754_ = crate::leanh::lean_ctor_get(v___x_694_, 0);
                    v_isSharedCheck_761_ = (!crate::leanh::lean_is_exclusive(v___x_694_)) as u8;
                    if v_isSharedCheck_761_ == 0 {
                        v___x_756_ = v___x_694_;
                        v_isShared_757_ = v_isSharedCheck_761_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_754_);
                        crate::leanh::lean_dec(v___x_694_);
                        v___x_756_ = crate::leanh::lean_box(0);
                        v_isShared_757_ = v_isSharedCheck_761_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_699_ = crate::leanh::lean_ctor_get(v___x_692_, 0);
                crate::leanh::lean_inc_ref(v_env_699_);
                crate::leanh::lean_dec(v___x_692_);
                v_lctx_700_ = crate::leanh::lean_ctor_get(v___x_693_, 0);
                v_isSharedCheck_751_ = (!crate::leanh::lean_is_exclusive(v___x_693_)) as u8;
                if v_isSharedCheck_751_ == 0 {
                    v_unused_752_ = crate::leanh::lean_ctor_get(v___x_693_, 1);
                    crate::leanh::lean_dec(v_unused_752_);
                    v___x_702_ = v___x_693_;
                    v_isShared_703_ = v_isSharedCheck_751_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_700_);
                    crate::leanh::lean_dec(v___x_693_);
                    v___x_702_ = crate::leanh::lean_box(0);
                    v_isShared_703_ = v_isSharedCheck_751_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_704_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__2);
                v___x_705_ = lean_st_ref_take(v___y_688_);
                v_traceState_706_ = crate::leanh::lean_ctor_get(v___x_705_, 4);
                v_env_707_ = crate::leanh::lean_ctor_get(v___x_705_, 0);
                v_nextMacroScope_708_ = crate::leanh::lean_ctor_get(v___x_705_, 1);
                v_ngen_709_ = crate::leanh::lean_ctor_get(v___x_705_, 2);
                v_auxDeclNGen_710_ = crate::leanh::lean_ctor_get(v___x_705_, 3);
                v_cache_711_ = crate::leanh::lean_ctor_get(v___x_705_, 5);
                v_messages_712_ = crate::leanh::lean_ctor_get(v___x_705_, 6);
                v_infoState_713_ = crate::leanh::lean_ctor_get(v___x_705_, 7);
                v_snapshotTasks_714_ = crate::leanh::lean_ctor_get(v___x_705_, 8);
                v_isSharedCheck_750_ = (!crate::leanh::lean_is_exclusive(v___x_705_)) as u8;
                if v_isSharedCheck_750_ == 0 {
                    v___x_716_ = v___x_705_;
                    v_isShared_717_ = v_isSharedCheck_750_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_714_);
                    crate::leanh::lean_inc(v_infoState_713_);
                    crate::leanh::lean_inc(v_messages_712_);
                    crate::leanh::lean_inc(v_cache_711_);
                    crate::leanh::lean_inc(v_traceState_706_);
                    crate::leanh::lean_inc(v_auxDeclNGen_710_);
                    crate::leanh::lean_inc(v_ngen_709_);
                    crate::leanh::lean_inc(v_nextMacroScope_708_);
                    crate::leanh::lean_inc(v_env_707_);
                    crate::leanh::lean_dec(v___x_705_);
                    v___x_716_ = crate::leanh::lean_box(0);
                    v_isShared_717_ = v_isSharedCheck_750_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_718_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_706_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_719_ = crate::leanh::lean_ctor_get(v_traceState_706_, 0);
                v_isSharedCheck_749_ = (!crate::leanh::lean_is_exclusive(v_traceState_706_)) as u8;
                if v_isSharedCheck_749_ == 0 {
                    v___x_721_ = v_traceState_706_;
                    v_isShared_722_ = v_isSharedCheck_749_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_719_);
                    crate::leanh::lean_dec(v_traceState_706_);
                    v___x_721_ = crate::leanh::lean_box(0);
                    v_isShared_722_ = v_isSharedCheck_749_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_723_ = (crate::leanh::lean_unbox(v_a_695_) as u8);
                crate::leanh::lean_dec(v_a_695_);
                v___x_724_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_700_, v___x_723_);
                crate::leanh::lean_dec_ref(v_lctx_700_);
                crate::leanh::lean_inc_ref(v_options_690_);
                v___x_725_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_725_, 0, v_env_699_);
                crate::leanh::lean_ctor_set(v___x_725_, 1, v___x_704_);
                crate::leanh::lean_ctor_set(v___x_725_, 2, v___x_724_);
                crate::leanh::lean_ctor_set(v___x_725_, 3, v_options_690_);
                if v_isShared_703_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_702_, 3);
                    crate::leanh::lean_ctor_set(v___x_702_, 1, v_msg_684_);
                    crate::leanh::lean_ctor_set(v___x_702_, 0, v___x_725_);
                    v___x_727_ = v___x_702_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_748_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_748_, 0, v___x_725_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_748_, 1, v_msg_684_);
                    v___x_727_ = v_reuseFailAlloc_748_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_728_ = crate::leanh::lean_box(0);
                v___x_729_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__3);
                v___x_730_ = 0;
                v___x_731_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__4;
                v___x_732_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_732_, 0, v_cls_683_);
                crate::leanh::lean_ctor_set(v___x_732_, 1, v___x_728_);
                crate::leanh::lean_ctor_set(v___x_732_, 2, v___x_731_);
                crate::leanh::lean_ctor_set_float(
                    v___x_732_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_729_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_732_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_729_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_732_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_730_,
                );
                v___x_733_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___closed__5;
                v___x_734_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_734_, 0, v___x_732_);
                crate::leanh::lean_ctor_set(v___x_734_, 1, v___x_727_);
                crate::leanh::lean_ctor_set(v___x_734_, 2, v___x_733_);
                crate::leanh::lean_inc(v_ref_691_);
                v___x_735_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_735_, 0, v_ref_691_);
                crate::leanh::lean_ctor_set(v___x_735_, 1, v___x_734_);
                v___x_736_ = l_Lean_PersistentArray_push___redArg(v_traces_719_, v___x_735_);
                if v_isShared_722_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_721_, 0, v___x_736_);
                    v___x_738_ = v___x_721_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_747_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_747_, 0, v___x_736_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_747_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_718_,
                    );
                    v___x_738_ = v_reuseFailAlloc_747_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_717_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_716_, 4, v___x_738_);
                    v___x_740_ = v___x_716_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_746_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 0, v_env_707_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 1, v_nextMacroScope_708_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 2, v_ngen_709_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 3, v_auxDeclNGen_710_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 4, v___x_738_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 5, v_cache_711_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 6, v_messages_712_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 7, v_infoState_713_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_746_, 8, v_snapshotTasks_714_);
                    v___x_740_ = v_reuseFailAlloc_746_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_741_ = lean_st_ref_set(v___y_688_, v___x_740_);
                v___x_742_ = crate::leanh::lean_box(0);
                if v_isShared_698_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_697_, 0, v___x_742_);
                    v___x_744_ = v___x_697_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_745_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_745_, 0, v___x_742_);
                    v___x_744_ = v_reuseFailAlloc_745_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_744_;
            }
            9 => {
                if v_isShared_757_ == 0 {
                    v___x_759_ = v___x_756_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_760_, 0, v_a_754_);
                    v___x_759_ = v_reuseFailAlloc_760_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_759_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg___boxed(
    mut v_cls_762_: *mut crate::leanh::LeanObject,
    mut v_msg_763_: *mut crate::leanh::LeanObject,
    mut v___y_764_: *mut crate::leanh::LeanObject,
    mut v___y_765_: *mut crate::leanh::LeanObject,
    mut v___y_766_: *mut crate::leanh::LeanObject,
    mut v___y_767_: *mut crate::leanh::LeanObject,
    mut v___y_768_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_769_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(
        v_cls_762_, v_msg_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_,
    );
    crate::leanh::lean_dec(v___y_767_);
    crate::leanh::lean_dec_ref(v___y_766_);
    crate::leanh::lean_dec(v___y_765_);
    crate::leanh::lean_dec_ref(v___y_764_);
    return v_res_769_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(
    mut v_cls_770_: *mut crate::leanh::LeanObject,
    mut v_msg_771_: *mut crate::leanh::LeanObject,
    mut v___y_772_: *mut crate::leanh::LeanObject,
    mut v___y_773_: *mut crate::leanh::LeanObject,
    mut v___y_774_: *mut crate::leanh::LeanObject,
    mut v___y_775_: *mut crate::leanh::LeanObject,
    mut v___y_776_: *mut crate::leanh::LeanObject,
    mut v___y_777_: *mut crate::leanh::LeanObject,
    mut v___y_778_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_780_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(
        v_cls_770_, v_msg_771_, v___y_775_, v___y_776_, v___y_777_, v___y_778_,
    );
    return v___x_780_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___boxed(
    mut v_cls_781_: *mut crate::leanh::LeanObject,
    mut v_msg_782_: *mut crate::leanh::LeanObject,
    mut v___y_783_: *mut crate::leanh::LeanObject,
    mut v___y_784_: *mut crate::leanh::LeanObject,
    mut v___y_785_: *mut crate::leanh::LeanObject,
    mut v___y_786_: *mut crate::leanh::LeanObject,
    mut v___y_787_: *mut crate::leanh::LeanObject,
    mut v___y_788_: *mut crate::leanh::LeanObject,
    mut v___y_789_: *mut crate::leanh::LeanObject,
    mut v___y_790_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_791_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0(
        v_cls_781_, v_msg_782_, v___y_783_, v___y_784_, v___y_785_, v___y_786_, v___y_787_,
        v___y_788_, v___y_789_,
    );
    crate::leanh::lean_dec(v___y_789_);
    crate::leanh::lean_dec_ref(v___y_788_);
    crate::leanh::lean_dec(v___y_787_);
    crate::leanh::lean_dec_ref(v___y_786_);
    crate::leanh::lean_dec_ref(v___y_785_);
    crate::leanh::lean_dec(v___y_784_);
    crate::leanh::lean_dec_ref(v___y_783_);
    return v_res_791_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6() -> *mut crate::leanh::LeanObject
{
    let mut v___x_802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_802_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
    v___x_803_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
    v___x_804_ = l_Lean_Name_append(v___x_803_, v___x_802_);
    return v___x_804_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8() -> *mut crate::leanh::LeanObject
{
    let mut v___x_806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_806_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__7;
    v___x_807_ = l_Lean_stringToMessageData(v___x_806_);
    return v___x_807_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10()
-> *mut crate::leanh::LeanObject {
    let mut v___x_809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_809_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__9;
    v___x_810_ = l_Lean_stringToMessageData(v___x_809_);
    return v___x_810_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12()
-> *mut crate::leanh::LeanObject {
    let mut v___x_812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_812_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__11;
    v___x_813_ = l_Lean_stringToMessageData(v___x_812_);
    return v___x_813_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14()
-> *mut crate::leanh::LeanObject {
    let mut v___x_815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_815_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__13;
    v___x_816_ = l_Lean_stringToMessageData(v___x_815_);
    return v___x_816_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17()
-> *mut crate::leanh::LeanObject {
    let mut v___x_819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_819_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__16;
    v___x_820_ = l_Lean_stringToMessageData(v___x_819_);
    return v___x_820_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20()
-> *mut crate::leanh::LeanObject {
    let mut v___x_826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_826_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
    v___x_827_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
    v___x_828_ = l_Lean_Name_append(v___x_827_, v___x_826_);
    return v___x_828_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24()
-> *mut crate::leanh::LeanObject {
    let mut v___x_836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_836_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
    v___x_837_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
    v___x_838_ = l_Lean_Name_append(v___x_837_, v___x_836_);
    return v___x_838_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26()
-> *mut crate::leanh::LeanObject {
    let mut v___x_840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_840_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__25;
    v___x_841_ = l_Lean_stringToMessageData(v___x_840_);
    return v___x_841_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27()
-> *mut crate::leanh::LeanObject {
    let mut v___x_842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_842_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_843_ = lean_nat_to_int(v___x_842_);
    return v___x_843_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_simp_x3f(
    mut v_decl_844_: *mut crate::leanh::LeanObject,
    mut v_a_845_: *mut crate::leanh::LeanObject,
    mut v_a_846_: *mut crate::leanh::LeanObject,
    mut v_a_847_: *mut crate::leanh::LeanObject,
    mut v_a_848_: *mut crate::leanh::LeanObject,
    mut v_a_849_: *mut crate::leanh::LeanObject,
    mut v_a_850_: *mut crate::leanh::LeanObject,
    mut v_a_851_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_855_: u8 = 0;
    let mut v_inlineAttr_x3f_856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_868_: u8 = 0;
    let mut v_val_869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_872_: u8 = 0;
    let mut v___x_873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_879_: u8 = 0;
    let mut v___x_881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_886_: u8 = 0;
    let mut v_a_887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_890_: u8 = 0;
    let mut v___x_892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_894_: u8 = 0;
    let mut v_isSharedCheck_895_: u8 = 0;
    let mut v___x_896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_simplified_897_: u8 = 0;
    let mut v___x_898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_908_: u8 = 0;
    let mut v_a_909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_912_: u8 = 0;
    let mut v___x_914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_916_: u8 = 0;
    let mut v_code_917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_920_: u8 = 0;
    let mut v___x_921_: u8 = 0;
    let mut v___x_922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_925_: u8 = 0;
    let mut v___x_926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_931_: u8 = 0;
    let mut v___y_932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_936_: u8 = 0;
    let mut v_name_937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_969_: u8 = 0;
    let mut v___x_971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_973_: u8 = 0;
    let mut v_reuseFailAlloc_974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_976_: u8 = 0;
    let mut v___y_977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_binderRenaming_981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_visited_982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inline_983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_inlineLocal_984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_992_: u8 = 0;
    let mut v___x_993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1005_: u8 = 0;
    let mut v___x_1007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1009_: u8 = 0;
    let mut v_a_1010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1013_: u8 = 0;
    let mut v___x_1015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1017_: u8 = 0;
    let mut v_a_1018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1021_: u8 = 0;
    let mut v___x_1023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1025_: u8 = 0;
    let mut v_a_1026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1029_: u8 = 0;
    let mut v___x_1031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1033_: u8 = 0;
    let mut v___x_1035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1036_: u8 = 0;
    let mut v___x_1037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1039_: u8 = 0;
    let mut v___x_1040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1047_: u8 = 0;
    let mut v___x_1049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1051_: u8 = 0;
    let mut v_a_1052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1055_: u8 = 0;
    let mut v___x_1057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1059_: u8 = 0;
    let mut v___x_1060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1062_: u8 = 0;
    let mut v___x_1063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_funDeclInfoMap_1064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1079_: u8 = 0;
    let mut v___x_1081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1083_: u8 = 0;
    let mut v_a_1084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1087_: u8 = 0;
    let mut v___x_1089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1091_: u8 = 0;
    let mut v_a_1092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1095_: u8 = 0;
    let mut v___x_1097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1099_: u8 = 0;
    let mut v_isSharedCheck_1100_: u8 = 0;
    let mut v___x_1101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_853_ = crate::leanh::lean_ctor_get(v_decl_844_, 0);
                crate::leanh::lean_inc_ref(v_toSignature_853_);
                v_value_854_ = crate::leanh::lean_ctor_get(v_decl_844_, 1);
                crate::leanh::lean_inc_ref(v_value_854_);
                v_recursive_855_ = crate::leanh::lean_ctor_get_uint8(
                    v_decl_844_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_856_ = crate::leanh::lean_ctor_get(v_decl_844_, 2);
                crate::leanh::lean_inc(v_inlineAttr_x3f_856_);
                if crate::leanh::lean_obj_tag(v_value_854_) == 0 {
                    v_code_917_ = crate::leanh::lean_ctor_get(v_value_854_, 0);
                    v_isSharedCheck_1100_ = (!crate::leanh::lean_is_exclusive(v_value_854_)) as u8;
                    if v_isSharedCheck_1100_ == 0 {
                        v___x_919_ = v_value_854_;
                        v_isShared_920_ = v_isSharedCheck_1100_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_917_);
                        crate::leanh::lean_dec(v_value_854_);
                        v___x_919_ = crate::leanh::lean_box(0);
                        v_isShared_920_ = v_isSharedCheck_1100_;
                        state = 13;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                    crate::leanh::lean_dec_ref(v_value_854_);
                    crate::leanh::lean_dec_ref(v_toSignature_853_);
                    crate::leanh::lean_dec_ref(v_decl_844_);
                    v___x_1101_ = crate::leanh::lean_box(0);
                    v___x_1102_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1102_, 0, v___x_1101_);
                    return v___x_1102_;
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v___y_858_);
                v___x_864_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(
                    v___y_858_, v___y_860_, v___y_861_, v___y_862_, v___y_863_,
                );
                if crate::leanh::lean_obj_tag(v___x_864_) == 0 {
                    v_a_865_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_908_ = (!crate::leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_908_ == 0 {
                        v___x_867_ = v___x_864_;
                        v_isShared_868_ = v_isSharedCheck_908_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_865_);
                        crate::leanh::lean_dec(v___x_864_);
                        v___x_867_ = crate::leanh::lean_box(0);
                        v_isShared_868_ = v_isSharedCheck_908_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_858_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                    crate::leanh::lean_dec_ref(v_toSignature_853_);
                    v_a_909_ = crate::leanh::lean_ctor_get(v___x_864_, 0);
                    v_isSharedCheck_916_ = (!crate::leanh::lean_is_exclusive(v___x_864_)) as u8;
                    if v_isSharedCheck_916_ == 0 {
                        v___x_911_ = v___x_864_;
                        v_isShared_912_ = v_isSharedCheck_916_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_909_);
                        crate::leanh::lean_dec(v___x_864_);
                        v___x_911_ = crate::leanh::lean_box(0);
                        v_isShared_912_ = v_isSharedCheck_916_;
                        state = 11;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_865_) == 1 {
                    crate::leanh::lean_del_object(v___x_867_);
                    crate::leanh::lean_dec_ref(v___y_858_);
                    v_val_869_ = crate::leanh::lean_ctor_get(v_a_865_, 0);
                    v_isSharedCheck_895_ = (!crate::leanh::lean_is_exclusive(v_a_865_)) as u8;
                    if v_isSharedCheck_895_ == 0 {
                        v___x_871_ = v_a_865_;
                        v_isShared_872_ = v_isSharedCheck_895_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_869_);
                        crate::leanh::lean_dec(v_a_865_);
                        v___x_871_ = crate::leanh::lean_box(0);
                        v_isShared_872_ = v_isSharedCheck_895_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_865_);
                    v___x_896_ = lean_st_ref_get(v___y_859_);
                    v_simplified_897_ = crate::leanh::lean_ctor_get_uint8(
                        v___x_896_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    );
                    crate::leanh::lean_dec(v___x_896_);
                    if v_simplified_897_ == 0 {
                        crate::leanh::lean_dec_ref(v___y_858_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                        crate::leanh::lean_dec_ref(v_toSignature_853_);
                        v___x_898_ = crate::leanh::lean_box(0);
                        if v_isShared_868_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_867_, 0, v___x_898_);
                            v___x_900_ = v___x_867_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_901_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_901_, 0, v___x_898_);
                            v___x_900_ = v_reuseFailAlloc_901_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___x_902_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_902_, 0, v___y_858_);
                        v___x_903_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                        crate::leanh::lean_ctor_set(v___x_903_, 0, v_toSignature_853_);
                        crate::leanh::lean_ctor_set(v___x_903_, 1, v___x_902_);
                        crate::leanh::lean_ctor_set(v___x_903_, 2, v_inlineAttr_x3f_856_);
                        crate::leanh::lean_ctor_set_uint8(
                            v___x_903_,
                            (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                            v_recursive_855_,
                        );
                        v___x_904_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_904_, 0, v___x_903_);
                        if v_isShared_868_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_867_, 0, v___x_904_);
                            v___x_906_ = v___x_867_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_907_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_907_, 0, v___x_904_);
                            v___x_906_ = v_reuseFailAlloc_907_;
                            state = 10;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v___x_873_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_873_, 0, v_val_869_);
                v___x_874_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_874_, 0, v_toSignature_853_);
                crate::leanh::lean_ctor_set(v___x_874_, 1, v___x_873_);
                crate::leanh::lean_ctor_set(v___x_874_, 2, v_inlineAttr_x3f_856_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_874_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_recursive_855_,
                );
                v___x_875_ = l_Lean_Compiler_LCNF_Decl_reduceJpArity(
                    v___x_874_, v___y_860_, v___y_861_, v___y_862_, v___y_863_,
                );
                if crate::leanh::lean_obj_tag(v___x_875_) == 0 {
                    v_a_876_ = crate::leanh::lean_ctor_get(v___x_875_, 0);
                    v_isSharedCheck_886_ = (!crate::leanh::lean_is_exclusive(v___x_875_)) as u8;
                    if v_isSharedCheck_886_ == 0 {
                        v___x_878_ = v___x_875_;
                        v_isShared_879_ = v_isSharedCheck_886_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_876_);
                        crate::leanh::lean_dec(v___x_875_);
                        v___x_878_ = crate::leanh::lean_box(0);
                        v_isShared_879_ = v_isSharedCheck_886_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_871_);
                    v_a_887_ = crate::leanh::lean_ctor_get(v___x_875_, 0);
                    v_isSharedCheck_894_ = (!crate::leanh::lean_is_exclusive(v___x_875_)) as u8;
                    if v_isSharedCheck_894_ == 0 {
                        v___x_889_ = v___x_875_;
                        v_isShared_890_ = v_isSharedCheck_894_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_887_);
                        crate::leanh::lean_dec(v___x_875_);
                        v___x_889_ = crate::leanh::lean_box(0);
                        v_isShared_890_ = v_isSharedCheck_894_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                if v_isShared_872_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_871_, 0, v_a_876_);
                    v___x_881_ = v___x_871_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_885_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_885_, 0, v_a_876_);
                    v___x_881_ = v_reuseFailAlloc_885_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_879_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_878_, 0, v___x_881_);
                    v___x_883_ = v___x_878_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_884_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
                    v___x_883_ = v_reuseFailAlloc_884_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_883_;
            }
            7 => {
                if v_isShared_890_ == 0 {
                    v___x_892_ = v___x_889_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_893_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_893_, 0, v_a_887_);
                    v___x_892_ = v_reuseFailAlloc_893_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_892_;
            }
            9 => {
                return v___x_900_;
            }
            10 => {
                return v___x_906_;
            }
            11 => {
                if v_isShared_912_ == 0 {
                    v___x_914_ = v___x_911_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_915_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_915_, 0, v_a_909_);
                    v___x_914_ = v_reuseFailAlloc_915_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_914_;
            }
            13 => {
                v___x_921_ = 0;
                crate::leanh::lean_inc_ref(v_code_917_);
                v___x_922_ = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(
                    v_code_917_,
                    v___x_921_,
                    v_a_846_,
                    v_a_848_,
                    v_a_849_,
                    v_a_850_,
                    v_a_851_,
                );
                if crate::leanh::lean_obj_tag(v___x_922_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_922_, 1);
                    v_options_923_ = crate::leanh::lean_ctor_get(v_a_850_, 2);
                    v_inheritedTraceOptions_924_ = crate::leanh::lean_ctor_get(v_a_850_, 13);
                    v_hasTrace_925_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_923_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_926_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__0;
                    v___x_927_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__1;
                    if v_hasTrace_925_ == 0 {
                        state = 27;
                        continue;
                    } else {
                        v___x_1060_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__23;
                        v___x_1061_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__24,
                        );
                        v___x_1062_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_924_,
                            v_options_923_,
                            v___x_1061_,
                        );
                        if v___x_1062_ == 0 {
                            state = 27;
                            continue;
                        } else {
                            v___x_1063_ = lean_st_ref_get(v_a_846_);
                            v_funDeclInfoMap_1064_ = crate::leanh::lean_ctor_get(v___x_1063_, 3);
                            crate::leanh::lean_inc_ref(v_funDeclInfoMap_1064_);
                            crate::leanh::lean_dec(v___x_1063_);
                            v___x_1065_ = l_Lean_Compiler_LCNF_Simp_FunDeclInfoMap_format(
                                v_funDeclInfoMap_1064_,
                                v_a_848_,
                                v_a_849_,
                                v_a_850_,
                                v_a_851_,
                            );
                            crate::leanh::lean_dec_ref(v_funDeclInfoMap_1064_);
                            if crate::leanh::lean_obj_tag(v___x_1065_) == 0 {
                                v_a_1066_ = crate::leanh::lean_ctor_get(v___x_1065_, 0);
                                crate::leanh::lean_inc(v_a_1066_);
                                crate::leanh::lean_dec_ref_known(v___x_1065_, 1);
                                v_name_1067_ = crate::leanh::lean_ctor_get(v_toSignature_853_, 0);
                                crate::leanh::lean_inc(v_name_1067_);
                                v___x_1068_ = l_Lean_MessageData_ofName(v_name_1067_);
                                v___x_1069_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__26,
                                );
                                v___x_1070_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1070_, 0, v___x_1068_);
                                crate::leanh::lean_ctor_set(v___x_1070_, 1, v___x_1069_);
                                v___x_1071_ = crate::leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27_once
                                    ),
                                    _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__27,
                                );
                                v___x_1072_ = crate::leanh::lean_alloc_ctor(4, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1072_, 0, v___x_1071_);
                                crate::leanh::lean_ctor_set(v___x_1072_, 1, v_a_1066_);
                                v___x_1073_ = l_Lean_MessageData_ofFormat(v___x_1072_);
                                v___x_1074_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1074_, 0, v___x_1070_);
                                crate::leanh::lean_ctor_set(v___x_1074_, 1, v___x_1073_);
                                v___x_1075_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_1060_, v___x_1074_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
                                if crate::leanh::lean_obj_tag(v___x_1075_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_1075_, 1);
                                    state = 27;
                                    continue;
                                } else {
                                    crate::leanh::lean_del_object(v___x_919_);
                                    crate::leanh::lean_dec_ref(v_code_917_);
                                    crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                                    crate::leanh::lean_dec_ref(v_toSignature_853_);
                                    crate::leanh::lean_dec_ref(v_decl_844_);
                                    v_a_1076_ = crate::leanh::lean_ctor_get(v___x_1075_, 0);
                                    v_isSharedCheck_1083_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1075_)) as u8;
                                    if v_isSharedCheck_1083_ == 0 {
                                        v___x_1078_ = v___x_1075_;
                                        v_isShared_1079_ = v_isSharedCheck_1083_;
                                        state = 32;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1076_);
                                        crate::leanh::lean_dec(v___x_1075_);
                                        v___x_1078_ = crate::leanh::lean_box(0);
                                        v_isShared_1079_ = v_isSharedCheck_1083_;
                                        state = 32;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_del_object(v___x_919_);
                                crate::leanh::lean_dec_ref(v_code_917_);
                                crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                                crate::leanh::lean_dec_ref(v_toSignature_853_);
                                crate::leanh::lean_dec_ref(v_decl_844_);
                                v_a_1084_ = crate::leanh::lean_ctor_get(v___x_1065_, 0);
                                v_isSharedCheck_1091_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1065_)) as u8;
                                if v_isSharedCheck_1091_ == 0 {
                                    v___x_1086_ = v___x_1065_;
                                    v_isShared_1087_ = v_isSharedCheck_1091_;
                                    state = 34;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1084_);
                                    crate::leanh::lean_dec(v___x_1065_);
                                    v___x_1086_ = crate::leanh::lean_box(0);
                                    v_isShared_1087_ = v_isSharedCheck_1091_;
                                    state = 34;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_919_);
                    crate::leanh::lean_dec_ref(v_code_917_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                    crate::leanh::lean_dec_ref(v_toSignature_853_);
                    crate::leanh::lean_dec_ref(v_decl_844_);
                    v_a_1092_ = crate::leanh::lean_ctor_get(v___x_922_, 0);
                    v_isSharedCheck_1099_ = (!crate::leanh::lean_is_exclusive(v___x_922_)) as u8;
                    if v_isSharedCheck_1099_ == 0 {
                        v___x_1094_ = v___x_922_;
                        v_isShared_1095_ = v_isSharedCheck_1099_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1092_);
                        crate::leanh::lean_dec(v___x_922_);
                        v___x_1094_ = crate::leanh::lean_box(0);
                        v_isShared_1095_ = v_isSharedCheck_1099_;
                        state = 36;
                        continue;
                    }
                }
            }
            14 => {
                if v_hasTrace_925_ == 0 {
                    crate::leanh::lean_dec(v___y_933_);
                    crate::leanh::lean_dec(v___y_930_);
                    crate::leanh::lean_dec(v___y_929_);
                    crate::leanh::lean_del_object(v___x_919_);
                    v___y_858_ = v___y_932_;
                    v___y_859_ = v_a_846_;
                    v___y_860_ = v_a_848_;
                    v___y_861_ = v_a_849_;
                    v___y_862_ = v_a_850_;
                    v___y_863_ = v_a_851_;
                    state = 1;
                    continue;
                } else {
                    v___x_934_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
                    v___x_935_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__6,
                    );
                    v___x_936_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_924_,
                        v_options_923_,
                        v___x_935_,
                    );
                    if v___x_936_ == 0 {
                        crate::leanh::lean_dec(v___y_933_);
                        crate::leanh::lean_dec(v___y_930_);
                        crate::leanh::lean_dec(v___y_929_);
                        crate::leanh::lean_del_object(v___x_919_);
                        v___y_858_ = v___y_932_;
                        v___y_859_ = v_a_846_;
                        v___y_860_ = v_a_848_;
                        v___y_861_ = v_a_849_;
                        v___y_862_ = v_a_850_;
                        v___y_863_ = v_a_851_;
                        state = 1;
                        continue;
                    } else {
                        v_name_937_ = crate::leanh::lean_ctor_get(v_toSignature_853_, 0);
                        crate::leanh::lean_inc(v_name_937_);
                        v___x_938_ = l_Lean_MessageData_ofName(v_name_937_);
                        v___x_939_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__8,
                        );
                        v___x_940_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_940_, 0, v___x_938_);
                        crate::leanh::lean_ctor_set(v___x_940_, 1, v___x_939_);
                        v___x_941_ = l_Lean_Compiler_LCNF_Code_size(v___y_931_, v___y_932_);
                        v___x_942_ = l_Nat_reprFast(v___x_941_);
                        if v_isShared_920_ == 0 {
                            crate::leanh::lean_ctor_set_tag(v___x_919_, 3);
                            crate::leanh::lean_ctor_set(v___x_919_, 0, v___x_942_);
                            v___x_944_ = v___x_919_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_974_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_974_, 0, v___x_942_);
                            v___x_944_ = v_reuseFailAlloc_974_;
                            state = 15;
                            continue;
                        }
                    }
                }
            }
            15 => {
                v___x_945_ = l_Lean_MessageData_ofFormat(v___x_944_);
                v___x_946_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_946_, 0, v___x_940_);
                crate::leanh::lean_ctor_set(v___x_946_, 1, v___x_945_);
                v___x_947_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10_once),
                    _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__10,
                );
                v___x_948_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_948_, 0, v___x_946_);
                crate::leanh::lean_ctor_set(v___x_948_, 1, v___x_947_);
                v___x_949_ = l_Nat_reprFast(v___y_929_);
                v___x_950_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_950_, 0, v___x_949_);
                v___x_951_ = l_Lean_MessageData_ofFormat(v___x_950_);
                v___x_952_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_952_, 0, v___x_948_);
                crate::leanh::lean_ctor_set(v___x_952_, 1, v___x_951_);
                v___x_953_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12_once),
                    _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__12,
                );
                v___x_954_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_954_, 0, v___x_952_);
                crate::leanh::lean_ctor_set(v___x_954_, 1, v___x_953_);
                v___x_955_ = l_Nat_reprFast(v___y_930_);
                v___x_956_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_956_, 0, v___x_955_);
                v___x_957_ = l_Lean_MessageData_ofFormat(v___x_956_);
                v___x_958_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_958_, 0, v___x_954_);
                crate::leanh::lean_ctor_set(v___x_958_, 1, v___x_957_);
                v___x_959_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14),
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14_once),
                    _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__14,
                );
                v___x_960_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_960_, 0, v___x_958_);
                crate::leanh::lean_ctor_set(v___x_960_, 1, v___x_959_);
                v___x_961_ = l_Nat_reprFast(v___y_933_);
                v___x_962_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_962_, 0, v___x_961_);
                v___x_963_ = l_Lean_MessageData_ofFormat(v___x_962_);
                v___x_964_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_964_, 0, v___x_960_);
                crate::leanh::lean_ctor_set(v___x_964_, 1, v___x_963_);
                v___x_965_ =
                    l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(
                        v___x_934_, v___x_964_, v_a_848_, v_a_849_, v_a_850_, v_a_851_,
                    );
                if crate::leanh::lean_obj_tag(v___x_965_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_965_, 1);
                    v___y_858_ = v___y_932_;
                    v___y_859_ = v_a_846_;
                    v___y_860_ = v_a_848_;
                    v___y_861_ = v_a_849_;
                    v___y_862_ = v_a_850_;
                    v___y_863_ = v_a_851_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v___y_932_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                    crate::leanh::lean_dec_ref(v_toSignature_853_);
                    v_a_966_ = crate::leanh::lean_ctor_get(v___x_965_, 0);
                    v_isSharedCheck_973_ = (!crate::leanh::lean_is_exclusive(v___x_965_)) as u8;
                    if v_isSharedCheck_973_ == 0 {
                        v___x_968_ = v___x_965_;
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 16;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_966_);
                        crate::leanh::lean_dec(v___x_965_);
                        v___x_968_ = crate::leanh::lean_box(0);
                        v_isShared_969_ = v_isSharedCheck_973_;
                        state = 16;
                        continue;
                    }
                }
            }
            16 => {
                if v_isShared_969_ == 0 {
                    v___x_971_ = v___x_968_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_972_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_972_, 0, v_a_966_);
                    v___x_971_ = v_reuseFailAlloc_972_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_971_;
            }
            18 => {
                crate::leanh::lean_inc_ref(v_a_850_);
                v___x_978_ = l_Lean_Compiler_LCNF_Simp_simp(
                    v_code_917_,
                    v_a_845_,
                    v_a_846_,
                    v_a_847_,
                    v_a_848_,
                    v_a_849_,
                    v_a_850_,
                    v_a_851_,
                );
                if crate::leanh::lean_obj_tag(v___x_978_) == 0 {
                    v_a_979_ = crate::leanh::lean_ctor_get(v___x_978_, 0);
                    crate::leanh::lean_inc(v_a_979_);
                    crate::leanh::lean_dec_ref_known(v___x_978_, 1);
                    v___x_980_ = lean_st_ref_get(v_a_846_);
                    v_binderRenaming_981_ = crate::leanh::lean_ctor_get(v___x_980_, 2);
                    crate::leanh::lean_inc(v_binderRenaming_981_);
                    v_visited_982_ = crate::leanh::lean_ctor_get(v___x_980_, 4);
                    crate::leanh::lean_inc(v_visited_982_);
                    v_inline_983_ = crate::leanh::lean_ctor_get(v___x_980_, 5);
                    crate::leanh::lean_inc(v_inline_983_);
                    v_inlineLocal_984_ = crate::leanh::lean_ctor_get(v___x_980_, 6);
                    crate::leanh::lean_inc(v_inlineLocal_984_);
                    crate::leanh::lean_dec(v___x_980_);
                    v___x_985_ = l_Lean_Compiler_LCNF_Code_applyRenaming(
                        v___y_976_,
                        v_a_979_,
                        v_binderRenaming_981_,
                        v_a_848_,
                        v_a_849_,
                        v_a_850_,
                        v_a_851_,
                    );
                    crate::leanh::lean_dec(v_binderRenaming_981_);
                    if crate::leanh::lean_obj_tag(v___x_985_) == 0 {
                        if v_hasTrace_925_ == 0 {
                            v_a_986_ = crate::leanh::lean_ctor_get(v___x_985_, 0);
                            crate::leanh::lean_inc(v_a_986_);
                            crate::leanh::lean_dec_ref_known(v___x_985_, 1);
                            v___y_929_ = v_visited_982_;
                            v___y_930_ = v_inline_983_;
                            v___y_931_ = v___y_976_;
                            v___y_932_ = v_a_986_;
                            v___y_933_ = v_inlineLocal_984_;
                            state = 14;
                            continue;
                        } else {
                            v_a_987_ = crate::leanh::lean_ctor_get(v___x_985_, 0);
                            crate::leanh::lean_inc(v_a_987_);
                            crate::leanh::lean_dec_ref_known(v___x_985_, 1);
                            v___x_988_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__15;
                            crate::leanh::lean_inc_ref(v___y_977_);
                            v___x_989_ =
                                l_Lean_Name_mkStr4(v___x_926_, v___x_927_, v___y_977_, v___x_988_);
                            v___x_990_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__5;
                            crate::leanh::lean_inc(v___x_989_);
                            v___x_991_ = l_Lean_Name_append(v___x_990_, v___x_989_);
                            v___x_992_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                                v_inheritedTraceOptions_924_,
                                v_options_923_,
                                v___x_991_,
                            );
                            crate::leanh::lean_dec(v___x_991_);
                            if v___x_992_ == 0 {
                                crate::leanh::lean_dec(v___x_989_);
                                v___y_929_ = v_visited_982_;
                                v___y_930_ = v_inline_983_;
                                v___y_931_ = v___y_976_;
                                v___y_932_ = v_a_987_;
                                v___y_933_ = v_inlineLocal_984_;
                                state = 14;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_987_);
                                v___x_993_ = l_Lean_Compiler_LCNF_ppCode(
                                    v___y_976_, v_a_987_, v_a_848_, v_a_849_, v_a_850_, v_a_851_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_993_) == 0 {
                                    v_a_994_ = crate::leanh::lean_ctor_get(v___x_993_, 0);
                                    crate::leanh::lean_inc(v_a_994_);
                                    crate::leanh::lean_dec_ref_known(v___x_993_, 1);
                                    v_name_995_ =
                                        crate::leanh::lean_ctor_get(v_toSignature_853_, 0);
                                    crate::leanh::lean_inc(v_name_995_);
                                    v___x_996_ = l_Lean_MessageData_ofName(v_name_995_);
                                    v___x_997_ = crate::leanh::lean_obj_once(
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17
                                        ),
                                        core::ptr::addr_of_mut!(
                                            l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17_once
                                        ),
                                        _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__17,
                                    );
                                    v___x_998_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_998_, 0, v___x_996_);
                                    crate::leanh::lean_ctor_set(v___x_998_, 1, v___x_997_);
                                    v___x_999_ = l_Lean_MessageData_ofFormat(v_a_994_);
                                    v___x_1000_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_1000_, 0, v___x_998_);
                                    crate::leanh::lean_ctor_set(v___x_1000_, 1, v___x_999_);
                                    v___x_1001_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_989_, v___x_1000_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
                                    if crate::leanh::lean_obj_tag(v___x_1001_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_1001_, 1);
                                        v___y_929_ = v_visited_982_;
                                        v___y_930_ = v_inline_983_;
                                        v___y_931_ = v___y_976_;
                                        v___y_932_ = v_a_987_;
                                        v___y_933_ = v_inlineLocal_984_;
                                        state = 14;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_987_);
                                        crate::leanh::lean_dec(v_inlineLocal_984_);
                                        crate::leanh::lean_dec(v_inline_983_);
                                        crate::leanh::lean_dec(v_visited_982_);
                                        crate::leanh::lean_del_object(v___x_919_);
                                        crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                                        crate::leanh::lean_dec_ref(v_toSignature_853_);
                                        v_a_1002_ = crate::leanh::lean_ctor_get(v___x_1001_, 0);
                                        v_isSharedCheck_1009_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_1001_)) as u8;
                                        if v_isSharedCheck_1009_ == 0 {
                                            v___x_1004_ = v___x_1001_;
                                            v_isShared_1005_ = v_isSharedCheck_1009_;
                                            state = 19;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_1002_);
                                            crate::leanh::lean_dec(v___x_1001_);
                                            v___x_1004_ = crate::leanh::lean_box(0);
                                            v_isShared_1005_ = v_isSharedCheck_1009_;
                                            state = 19;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec(v___x_989_);
                                    crate::leanh::lean_dec(v_a_987_);
                                    crate::leanh::lean_dec(v_inlineLocal_984_);
                                    crate::leanh::lean_dec(v_inline_983_);
                                    crate::leanh::lean_dec(v_visited_982_);
                                    crate::leanh::lean_del_object(v___x_919_);
                                    crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                                    crate::leanh::lean_dec_ref(v_toSignature_853_);
                                    v_a_1010_ = crate::leanh::lean_ctor_get(v___x_993_, 0);
                                    v_isSharedCheck_1017_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_993_)) as u8;
                                    if v_isSharedCheck_1017_ == 0 {
                                        v___x_1012_ = v___x_993_;
                                        v_isShared_1013_ = v_isSharedCheck_1017_;
                                        state = 21;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1010_);
                                        crate::leanh::lean_dec(v___x_993_);
                                        v___x_1012_ = crate::leanh::lean_box(0);
                                        v_isShared_1013_ = v_isSharedCheck_1017_;
                                        state = 21;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_inlineLocal_984_);
                        crate::leanh::lean_dec(v_inline_983_);
                        crate::leanh::lean_dec(v_visited_982_);
                        crate::leanh::lean_del_object(v___x_919_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                        crate::leanh::lean_dec_ref(v_toSignature_853_);
                        v_a_1018_ = crate::leanh::lean_ctor_get(v___x_985_, 0);
                        v_isSharedCheck_1025_ =
                            (!crate::leanh::lean_is_exclusive(v___x_985_)) as u8;
                        if v_isSharedCheck_1025_ == 0 {
                            v___x_1020_ = v___x_985_;
                            v_isShared_1021_ = v_isSharedCheck_1025_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1018_);
                            crate::leanh::lean_dec(v___x_985_);
                            v___x_1020_ = crate::leanh::lean_box(0);
                            v_isShared_1021_ = v_isSharedCheck_1025_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_919_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                    crate::leanh::lean_dec_ref(v_toSignature_853_);
                    v_a_1026_ = crate::leanh::lean_ctor_get(v___x_978_, 0);
                    v_isSharedCheck_1033_ = (!crate::leanh::lean_is_exclusive(v___x_978_)) as u8;
                    if v_isSharedCheck_1033_ == 0 {
                        v___x_1028_ = v___x_978_;
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1026_);
                        crate::leanh::lean_dec(v___x_978_);
                        v___x_1028_ = crate::leanh::lean_box(0);
                        v_isShared_1029_ = v_isSharedCheck_1033_;
                        state = 25;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_1005_ == 0 {
                    v___x_1007_ = v___x_1004_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_1008_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1008_, 0, v_a_1002_);
                    v___x_1007_ = v_reuseFailAlloc_1008_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_1007_;
            }
            21 => {
                if v_isShared_1013_ == 0 {
                    v___x_1015_ = v___x_1012_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_1016_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1016_, 0, v_a_1010_);
                    v___x_1015_ = v_reuseFailAlloc_1016_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_1015_;
            }
            23 => {
                if v_isShared_1021_ == 0 {
                    v___x_1023_ = v___x_1020_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_1024_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1024_, 0, v_a_1018_);
                    v___x_1023_ = v_reuseFailAlloc_1024_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_1023_;
            }
            25 => {
                if v_isShared_1029_ == 0 {
                    v___x_1031_ = v___x_1028_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_1032_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1032_, 0, v_a_1026_);
                    v___x_1031_ = v_reuseFailAlloc_1032_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_1031_;
            }
            27 => {
                v___x_1035_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__18;
                v___x_1036_ = 0;
                if v_hasTrace_925_ == 0 {
                    crate::leanh::lean_dec_ref(v_decl_844_);
                    v___y_976_ = v___x_1036_;
                    v___y_977_ = v___x_1035_;
                    state = 18;
                    continue;
                } else {
                    v___x_1037_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
                    v___x_1038_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__20,
                    );
                    v___x_1039_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_924_,
                        v_options_923_,
                        v___x_1038_,
                    );
                    if v___x_1039_ == 0 {
                        crate::leanh::lean_dec_ref(v_decl_844_);
                        v___y_976_ = v___x_1036_;
                        v___y_977_ = v___x_1035_;
                        state = 18;
                        continue;
                    } else {
                        v___x_1040_ = l_Lean_Compiler_LCNF_ppDecl(
                            v___x_1036_,
                            v_decl_844_,
                            v_a_848_,
                            v_a_849_,
                            v_a_850_,
                            v_a_851_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_1040_) == 0 {
                            v_a_1041_ = crate::leanh::lean_ctor_get(v___x_1040_, 0);
                            crate::leanh::lean_inc(v_a_1041_);
                            crate::leanh::lean_dec_ref_known(v___x_1040_, 1);
                            v___x_1042_ = l_Lean_MessageData_ofFormat(v_a_1041_);
                            v___x_1043_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_simp_x3f_spec__0___redArg(v___x_1037_, v___x_1042_, v_a_848_, v_a_849_, v_a_850_, v_a_851_);
                            if crate::leanh::lean_obj_tag(v___x_1043_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_1043_, 1);
                                v___y_976_ = v___x_1036_;
                                v___y_977_ = v___x_1035_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_del_object(v___x_919_);
                                crate::leanh::lean_dec_ref(v_code_917_);
                                crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                                crate::leanh::lean_dec_ref(v_toSignature_853_);
                                v_a_1044_ = crate::leanh::lean_ctor_get(v___x_1043_, 0);
                                v_isSharedCheck_1051_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_1043_)) as u8;
                                if v_isSharedCheck_1051_ == 0 {
                                    v___x_1046_ = v___x_1043_;
                                    v_isShared_1047_ = v_isSharedCheck_1051_;
                                    state = 28;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_1044_);
                                    crate::leanh::lean_dec(v___x_1043_);
                                    v___x_1046_ = crate::leanh::lean_box(0);
                                    v_isShared_1047_ = v_isSharedCheck_1051_;
                                    state = 28;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_919_);
                            crate::leanh::lean_dec_ref(v_code_917_);
                            crate::leanh::lean_dec(v_inlineAttr_x3f_856_);
                            crate::leanh::lean_dec_ref(v_toSignature_853_);
                            v_a_1052_ = crate::leanh::lean_ctor_get(v___x_1040_, 0);
                            v_isSharedCheck_1059_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1040_)) as u8;
                            if v_isSharedCheck_1059_ == 0 {
                                v___x_1054_ = v___x_1040_;
                                v_isShared_1055_ = v_isSharedCheck_1059_;
                                state = 30;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1052_);
                                crate::leanh::lean_dec(v___x_1040_);
                                v___x_1054_ = crate::leanh::lean_box(0);
                                v_isShared_1055_ = v_isSharedCheck_1059_;
                                state = 30;
                                continue;
                            }
                        }
                    }
                }
            }
            28 => {
                if v_isShared_1047_ == 0 {
                    v___x_1049_ = v___x_1046_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_1050_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1050_, 0, v_a_1044_);
                    v___x_1049_ = v_reuseFailAlloc_1050_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_1049_;
            }
            30 => {
                if v_isShared_1055_ == 0 {
                    v___x_1057_ = v___x_1054_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_1058_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
                    v___x_1057_ = v_reuseFailAlloc_1058_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_1057_;
            }
            32 => {
                if v_isShared_1079_ == 0 {
                    v___x_1081_ = v___x_1078_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_1082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1082_, 0, v_a_1076_);
                    v___x_1081_ = v_reuseFailAlloc_1082_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_1081_;
            }
            34 => {
                if v_isShared_1087_ == 0 {
                    v___x_1089_ = v___x_1086_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_1090_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1090_, 0, v_a_1084_);
                    v___x_1089_ = v_reuseFailAlloc_1090_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_1089_;
            }
            36 => {
                if v_isShared_1095_ == 0 {
                    v___x_1097_ = v___x_1094_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_1098_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1098_, 0, v_a_1092_);
                    v___x_1097_ = v_reuseFailAlloc_1098_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_1097_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_simp_x3f___boxed(
    mut v_decl_1103_: *mut crate::leanh::LeanObject,
    mut v_a_1104_: *mut crate::leanh::LeanObject,
    mut v_a_1105_: *mut crate::leanh::LeanObject,
    mut v_a_1106_: *mut crate::leanh::LeanObject,
    mut v_a_1107_: *mut crate::leanh::LeanObject,
    mut v_a_1108_: *mut crate::leanh::LeanObject,
    mut v_a_1109_: *mut crate::leanh::LeanObject,
    mut v_a_1110_: *mut crate::leanh::LeanObject,
    mut v_a_1111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1112_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(
        v_decl_1103_,
        v_a_1104_,
        v_a_1105_,
        v_a_1106_,
        v_a_1107_,
        v_a_1108_,
        v_a_1109_,
        v_a_1110_,
    );
    crate::leanh::lean_dec(v_a_1110_);
    crate::leanh::lean_dec_ref(v_a_1109_);
    crate::leanh::lean_dec(v_a_1108_);
    crate::leanh::lean_dec_ref(v_a_1107_);
    crate::leanh::lean_dec_ref(v_a_1106_);
    crate::leanh::lean_dec(v_a_1105_);
    crate::leanh::lean_dec_ref(v_a_1104_);
    return v_res_1112_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1113_ = crate::leanh::lean_box(0);
    v___x_1114_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_1115_ = lean_mk_array(v___x_1114_, v___x_1113_);
    return v___x_1115_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1116_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0_once
        ),
        _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__0,
    );
    v___x_1117_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1118_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1118_, 0, v___x_1117_);
    crate::leanh::lean_ctor_set(v___x_1118_, 1, v___x_1116_);
    return v___x_1118_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1120_: u8 = 0;
    let mut v___x_1121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1119_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_1120_ = 0;
    v___x_1121_ = crate::leanh::lean_box(1);
    v___x_1122_ = l_Lean_instEmptyCollectionFVarIdHashSet;
    v___x_1123_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1_once
        ),
        _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__1,
    );
    v___x_1124_ = crate::leanh::lean_alloc_ctor(0, 7, (1) as u32);
    crate::leanh::lean_ctor_set(v___x_1124_, 0, v___x_1123_);
    crate::leanh::lean_ctor_set(v___x_1124_, 1, v___x_1122_);
    crate::leanh::lean_ctor_set(v___x_1124_, 2, v___x_1121_);
    crate::leanh::lean_ctor_set(v___x_1124_, 3, v___x_1123_);
    crate::leanh::lean_ctor_set(v___x_1124_, 4, v___x_1119_);
    crate::leanh::lean_ctor_set(v___x_1124_, 5, v___x_1119_);
    crate::leanh::lean_ctor_set(v___x_1124_, 6, v___x_1119_);
    crate::leanh::lean_ctor_set_uint8(
        v___x_1124_,
        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
        v___x_1120_,
    );
    return v___x_1124_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1125_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_1125_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1126_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3_once
        ),
        _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__3,
    );
    v___x_1127_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1127_, 0, v___x_1126_);
    return v___x_1127_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1128_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4
        ),
        core::ptr::addr_of_mut!(
            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once
        ),
        _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4,
    );
    v___x_1129_ = crate::leanh::lean_box(1);
    v___x_1130_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_1130_, 0, v___x_1129_);
    crate::leanh::lean_ctor_set(v___x_1130_, 1, v___x_1128_);
    return v___x_1130_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(
    mut v_decl_1131_: *mut crate::leanh::LeanObject,
    mut v_config_1132_: *mut crate::leanh::LeanObject,
    mut v_a_1133_: *mut crate::leanh::LeanObject,
    mut v_a_1134_: *mut crate::leanh::LeanObject,
    mut v_a_1135_: *mut crate::leanh::LeanObject,
    mut v_a_1136_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_1140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_1141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1150_: u8 = 0;
    let mut v___x_1151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1157_: u8 = 0;
    let mut v_a_1158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1161_: u8 = 0;
    let mut v___x_1163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1165_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1138_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2_once), _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__2);
                v___x_1139_ = lean_st_mk_ref(v___x_1138_);
                v_toSignature_1140_ = crate::leanh::lean_ctor_get(v_decl_1131_, 0);
                v_name_1141_ = crate::leanh::lean_ctor_get(v_toSignature_1140_, 0);
                v___x_1142_ = crate::leanh::lean_box(0);
                v___x_1143_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4_once), _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__4);
                crate::leanh::lean_inc_ref(v_config_1132_);
                crate::leanh::lean_inc(v_name_1141_);
                v___x_1144_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1144_, 0, v_name_1141_);
                crate::leanh::lean_ctor_set(v___x_1144_, 1, v_config_1132_);
                crate::leanh::lean_ctor_set(v___x_1144_, 2, v___x_1142_);
                crate::leanh::lean_ctor_set(v___x_1144_, 3, v___x_1143_);
                v___x_1145_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5_once), _init_l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___closed__5);
                crate::leanh::lean_inc_ref(v_decl_1131_);
                v___x_1146_ = l_Lean_Compiler_LCNF_Decl_simp_x3f(
                    v_decl_1131_,
                    v___x_1144_,
                    v___x_1139_,
                    v___x_1145_,
                    v_a_1133_,
                    v_a_1134_,
                    v_a_1135_,
                    v_a_1136_,
                );
                crate::leanh::lean_dec_ref_known(v___x_1144_, 4);
                if crate::leanh::lean_obj_tag(v___x_1146_) == 0 {
                    v_a_1147_ = crate::leanh::lean_ctor_get(v___x_1146_, 0);
                    v_isSharedCheck_1157_ = (!crate::leanh::lean_is_exclusive(v___x_1146_)) as u8;
                    if v_isSharedCheck_1157_ == 0 {
                        v___x_1149_ = v___x_1146_;
                        v_isShared_1150_ = v_isSharedCheck_1157_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1147_);
                        crate::leanh::lean_dec(v___x_1146_);
                        v___x_1149_ = crate::leanh::lean_box(0);
                        v_isShared_1150_ = v_isSharedCheck_1157_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1139_);
                    crate::leanh::lean_dec_ref(v_config_1132_);
                    crate::leanh::lean_dec_ref(v_decl_1131_);
                    v_a_1158_ = crate::leanh::lean_ctor_get(v___x_1146_, 0);
                    v_isSharedCheck_1165_ = (!crate::leanh::lean_is_exclusive(v___x_1146_)) as u8;
                    if v_isSharedCheck_1165_ == 0 {
                        v___x_1160_ = v___x_1146_;
                        v_isShared_1161_ = v_isSharedCheck_1165_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1158_);
                        crate::leanh::lean_dec(v___x_1146_);
                        v___x_1160_ = crate::leanh::lean_box(0);
                        v_isShared_1161_ = v_isSharedCheck_1165_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1151_ = lean_st_ref_get(v___x_1139_);
                crate::leanh::lean_dec(v___x_1139_);
                crate::leanh::lean_dec(v___x_1151_);
                if crate::leanh::lean_obj_tag(v_a_1147_) == 1 {
                    crate::leanh::lean_del_object(v___x_1149_);
                    crate::leanh::lean_dec_ref(v_decl_1131_);
                    v_val_1152_ = crate::leanh::lean_ctor_get(v_a_1147_, 0);
                    crate::leanh::lean_inc(v_val_1152_);
                    crate::leanh::lean_dec_ref_known(v_a_1147_, 1);
                    v_decl_1131_ = v_val_1152_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_1147_);
                    crate::leanh::lean_dec_ref(v_config_1132_);
                    if v_isShared_1150_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1149_, 0, v_decl_1131_);
                        v___x_1155_ = v___x_1149_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1156_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_decl_1131_);
                        v___x_1155_ = v_reuseFailAlloc_1156_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_1155_;
            }
            3 => {
                if v_isShared_1161_ == 0 {
                    v___x_1163_ = v___x_1160_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1164_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1164_, 0, v_a_1158_);
                    v___x_1163_ = v_reuseFailAlloc_1164_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1163_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go___boxed(
    mut v_decl_1166_: *mut crate::leanh::LeanObject,
    mut v_config_1167_: *mut crate::leanh::LeanObject,
    mut v_a_1168_: *mut crate::leanh::LeanObject,
    mut v_a_1169_: *mut crate::leanh::LeanObject,
    mut v_a_1170_: *mut crate::leanh::LeanObject,
    mut v_a_1171_: *mut crate::leanh::LeanObject,
    mut v_a_1172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1173_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(
        v_decl_1166_,
        v_config_1167_,
        v_a_1168_,
        v_a_1169_,
        v_a_1170_,
        v_a_1171_,
    );
    crate::leanh::lean_dec(v_a_1171_);
    crate::leanh::lean_dec_ref(v_a_1170_);
    crate::leanh::lean_dec(v_a_1169_);
    crate::leanh::lean_dec_ref(v_a_1168_);
    return v_res_1173_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_simp(
    mut v_decl_1174_: *mut crate::leanh::LeanObject,
    mut v_config_1175_: *mut crate::leanh::LeanObject,
    mut v_a_1176_: *mut crate::leanh::LeanObject,
    mut v_a_1177_: *mut crate::leanh::LeanObject,
    mut v_a_1178_: *mut crate::leanh::LeanObject,
    mut v_a_1179_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1183_: u8 = 0;
    let mut v___x_1184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_implementedBy_1185_: u8 = 0;
    let mut v_inlineDefs_1186_: u8 = 0;
    let mut v___x_1188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1189_: u8 = 0;
    let mut v___x_1190_: u8 = 0;
    let mut v___x_1192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1195_: u8 = 0;
    let mut v_a_1196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1199_: u8 = 0;
    let mut v___x_1201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                crate::leanh::lean_inc_ref(v_decl_1174_);
                v___x_1181_ = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(
                    v_decl_1174_,
                    v_a_1178_,
                    v_a_1179_,
                );
                if crate::leanh::lean_obj_tag(v___x_1181_) == 0 {
                    v_a_1182_ = crate::leanh::lean_ctor_get(v___x_1181_, 0);
                    crate::leanh::lean_inc(v_a_1182_);
                    crate::leanh::lean_dec_ref_known(v___x_1181_, 1);
                    v___x_1183_ = (crate::leanh::lean_unbox(v_a_1182_) as u8);
                    crate::leanh::lean_dec(v_a_1182_);
                    if v___x_1183_ == 0 {
                        v___x_1184_ =
                            l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(
                                v_decl_1174_,
                                v_config_1175_,
                                v_a_1176_,
                                v_a_1177_,
                                v_a_1178_,
                                v_a_1179_,
                            );
                        return v___x_1184_;
                    } else {
                        v_implementedBy_1185_ =
                            crate::leanh::lean_ctor_get_uint8(v_config_1175_, 2 as u32);
                        v_inlineDefs_1186_ =
                            crate::leanh::lean_ctor_get_uint8(v_config_1175_, 3 as u32);
                        v_isSharedCheck_1195_ =
                            (!crate::leanh::lean_is_exclusive(v_config_1175_)) as u8;
                        if v_isSharedCheck_1195_ == 0 {
                            v___x_1188_ = v_config_1175_;
                            v_isShared_1189_ = v_isSharedCheck_1195_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_config_1175_);
                            v___x_1188_ = crate::leanh::lean_box(0);
                            v_isShared_1189_ = v_isSharedCheck_1195_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_config_1175_);
                    crate::leanh::lean_dec_ref(v_decl_1174_);
                    v_a_1196_ = crate::leanh::lean_ctor_get(v___x_1181_, 0);
                    v_isSharedCheck_1203_ = (!crate::leanh::lean_is_exclusive(v___x_1181_)) as u8;
                    if v_isSharedCheck_1203_ == 0 {
                        v___x_1198_ = v___x_1181_;
                        v_isShared_1199_ = v_isSharedCheck_1203_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1196_);
                        crate::leanh::lean_dec(v___x_1181_);
                        v___x_1198_ = crate::leanh::lean_box(0);
                        v_isShared_1199_ = v_isSharedCheck_1203_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1190_ = 0;
                if v_isShared_1189_ == 0 {
                    v___x_1192_ = v___x_1188_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1194_ = crate::leanh::lean_alloc_ctor(0, 0, (4) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1194_,
                        2 as u32,
                        v_implementedBy_1185_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1194_,
                        3 as u32,
                        v_inlineDefs_1186_,
                    );
                    v___x_1192_ = v_reuseFailAlloc_1194_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v___x_1192_, 0 as u32, v___x_1190_);
                crate::leanh::lean_ctor_set_uint8(v___x_1192_, 1 as u32, v___x_1190_);
                v___x_1193_ =
                    l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_Decl_simp_go(
                        v_decl_1174_,
                        v___x_1192_,
                        v_a_1176_,
                        v_a_1177_,
                        v_a_1178_,
                        v_a_1179_,
                    );
                return v___x_1193_;
            }
            3 => {
                if v_isShared_1199_ == 0 {
                    v___x_1201_ = v___x_1198_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1202_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
                    v___x_1201_ = v_reuseFailAlloc_1202_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_simp___boxed(
    mut v_decl_1204_: *mut crate::leanh::LeanObject,
    mut v_config_1205_: *mut crate::leanh::LeanObject,
    mut v_a_1206_: *mut crate::leanh::LeanObject,
    mut v_a_1207_: *mut crate::leanh::LeanObject,
    mut v_a_1208_: *mut crate::leanh::LeanObject,
    mut v_a_1209_: *mut crate::leanh::LeanObject,
    mut v_a_1210_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1211_ = l_Lean_Compiler_LCNF_Decl_simp(
        v_decl_1204_,
        v_config_1205_,
        v_a_1206_,
        v_a_1207_,
        v_a_1208_,
        v_a_1209_,
    );
    crate::leanh::lean_dec(v_a_1209_);
    crate::leanh::lean_dec_ref(v_a_1208_);
    crate::leanh::lean_dec(v_a_1207_);
    crate::leanh::lean_dec_ref(v_a_1206_);
    return v_res_1211_;
}
pub unsafe fn l_Lean_Compiler_LCNF_simp___lam__0(
    mut v_config_1212_: *mut crate::leanh::LeanObject,
    mut v_x_1213_: *mut crate::leanh::LeanObject,
    mut v___y_1214_: *mut crate::leanh::LeanObject,
    mut v___y_1215_: *mut crate::leanh::LeanObject,
    mut v___y_1216_: *mut crate::leanh::LeanObject,
    mut v___y_1217_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1219_ = l_Lean_Compiler_LCNF_Decl_simp(
        v_x_1213_,
        v_config_1212_,
        v___y_1214_,
        v___y_1215_,
        v___y_1216_,
        v___y_1217_,
    );
    return v___x_1219_;
}
pub unsafe fn l_Lean_Compiler_LCNF_simp___lam__0___boxed(
    mut v_config_1220_: *mut crate::leanh::LeanObject,
    mut v_x_1221_: *mut crate::leanh::LeanObject,
    mut v___y_1222_: *mut crate::leanh::LeanObject,
    mut v___y_1223_: *mut crate::leanh::LeanObject,
    mut v___y_1224_: *mut crate::leanh::LeanObject,
    mut v___y_1225_: *mut crate::leanh::LeanObject,
    mut v___y_1226_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1227_ = l_Lean_Compiler_LCNF_simp___lam__0(
        v_config_1220_,
        v_x_1221_,
        v___y_1222_,
        v___y_1223_,
        v___y_1224_,
        v___y_1225_,
    );
    crate::leanh::lean_dec(v___y_1225_);
    crate::leanh::lean_dec_ref(v___y_1224_);
    crate::leanh::lean_dec(v___y_1223_);
    crate::leanh::lean_dec_ref(v___y_1222_);
    return v_res_1227_;
}
pub unsafe fn l_Lean_Compiler_LCNF_simp___lam__1(
    mut v_phase_1230_: u8,
    mut v___f_1231_: *mut crate::leanh::LeanObject,
    mut v_occurrence_1232_: *mut crate::leanh::LeanObject,
    mut v_h_1233_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1234_ = l_Lean_Compiler_LCNF_simp___lam__1___closed__0;
    v___x_1235_ = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(
        v___x_1234_,
        v_phase_1230_,
        v___f_1231_,
        v_occurrence_1232_,
    );
    return v___x_1235_;
}
pub unsafe fn l_Lean_Compiler_LCNF_simp___lam__1___boxed(
    mut v_phase_1236_: *mut crate::leanh::LeanObject,
    mut v___f_1237_: *mut crate::leanh::LeanObject,
    mut v_occurrence_1238_: *mut crate::leanh::LeanObject,
    mut v_h_1239_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_1240_: u8 = 0;
    let mut v_res_1241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1240_ = (crate::leanh::lean_unbox(v_phase_1236_) as u8);
    v_res_1241_ = l_Lean_Compiler_LCNF_simp___lam__1(
        v_phase_boxed_1240_,
        v___f_1237_,
        v_occurrence_1238_,
        v_h_1239_,
    );
    return v_res_1241_;
}
pub unsafe fn l_Lean_Compiler_LCNF_simp(
    mut v_config_1242_: *mut crate::leanh::LeanObject,
    mut v_occurrence_1243_: *mut crate::leanh::LeanObject,
    mut v_phase_1244_: u8,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_1245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_1247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1249_: u8 = 0;
    let mut v___x_1250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___f_1245_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_simp___lam__0___boxed as *mut core::ffi::c_void,
        7,
        1,
    );
    crate::leanh::lean_closure_set(v___f_1245_, 0, v_config_1242_);
    v___x_1246_ = crate::leanh::lean_box((v_phase_1244_) as usize);
    v___f_1247_ = crate::leanh::lean_alloc_closure(
        l_Lean_Compiler_LCNF_simp___lam__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___f_1247_, 0, v___x_1246_);
    crate::leanh::lean_closure_set(v___f_1247_, 1, v___f_1245_);
    crate::leanh::lean_closure_set(v___f_1247_, 2, v_occurrence_1243_);
    v___x_1248_ = l_Lean_Compiler_LCNF_instInhabitedPass;
    v___x_1249_ = 0;
    v___x_1250_ = l_Lean_Compiler_LCNF_Phase_withPurityCheck___redArg(
        v___x_1248_,
        v_phase_1244_,
        v___x_1249_,
        v___f_1247_,
    );
    return v___x_1250_;
}
pub unsafe fn l_Lean_Compiler_LCNF_simp___boxed(
    mut v_config_1251_: *mut crate::leanh::LeanObject,
    mut v_occurrence_1252_: *mut crate::leanh::LeanObject,
    mut v_phase_1253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_phase_boxed_1254_: u8 = 0;
    let mut v_res_1255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_1254_ = (crate::leanh::lean_unbox(v_phase_1253_) as u8);
    v_res_1255_ =
        l_Lean_Compiler_LCNF_simp(v_config_1251_, v_occurrence_1252_, v_phase_boxed_1254_);
    return v_res_1255_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1331_: u8 = 0;
    let mut v___x_1332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1330_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
    v___x_1331_ = 1;
    v___x_1332_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
    v___x_1333_ = l_Lean_registerTraceClass(v___x_1330_, v___x_1331_, v___x_1332_);
    if crate::leanh::lean_obj_tag(v___x_1333_) == 0 {
        let mut v___x_1334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1335_: u8 = 0;
        let mut v___x_1336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_1333_, 1);
        v___x_1334_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__3;
        v___x_1335_ = 0;
        v___x_1336_ = l_Lean_registerTraceClass(v___x_1334_, v___x_1335_, v___x_1332_);
        if crate::leanh::lean_obj_tag(v___x_1336_) == 0 {
            let mut v___x_1337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_1336_, 1);
            v___x_1337_ = l_Lean_Compiler_LCNF_Decl_simp_x3f___closed__19;
            v___x_1338_ = l_Lean_registerTraceClass(v___x_1337_, v___x_1335_, v___x_1332_);
            if crate::leanh::lean_obj_tag(v___x_1338_) == 0 {
                let mut v___x_1339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_1338_, 1);
                v___x_1339_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_;
                v___x_1340_ = l_Lean_registerTraceClass(v___x_1339_, v___x_1335_, v___x_1332_);
                return v___x_1340_;
            } else {
                return v___x_1338_;
            }
        } else {
            return v___x_1336_;
        }
    } else {
        return v___x_1333_;
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2____boxed(
    mut v_a_1341_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1342_ = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
    return v_res_1342_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
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
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_Simp_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_1672504145____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp(builtin: u8) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_ReduceJpArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Basic(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Config(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_SimpM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_Main(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin);
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
    res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp(builtin);
}
