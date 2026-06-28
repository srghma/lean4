// Lean compiler output
// Module: Lean.Compiler.LCNF.ExtractClosed
// Imports: Lean.Compiler.ClosedTermCache Lean.Compiler.NeverExtractAttr Lean.Compiler.LCNF.Internalize Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.DependsOn Init.Data.FloatArray.Basic
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_reverse___redArg};
use crate::r#gen::Init::Data::FloatArray::Basic::{
    initialize_Init_Data_FloatArray_Basic, meta_initialize_Init_Data_FloatArray_Basic,
};
use crate::r#gen::Init::Meta::Defs::lean_name_append_index_after;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::ClosedTermCache::{
    initialize_Lean_Compiler_ClosedTermCache, l_Lean_cacheClosedTermName,
    l_Lean_getClosedTermName_x3f, runtime_initialize_Lean_Compiler_ClosedTermCache,
};
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg, l_Lean_Compiler_LCNF_Decl_getArity___redArg,
    l_Lean_Compiler_LCNF_attachCodeDecls, l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
    l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg, l_Lean_Compiler_LCNF_eraseCode___redArg,
    l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg, l_Lean_Compiler_LCNF_findLetValue_x3f___redArg,
    l_Lean_Compiler_LCNF_getConfig___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::DependsOn::{
    initialize_Lean_Compiler_LCNF_DependsOn, l_Lean_Compiler_LCNF_Code_dependsOn,
    runtime_initialize_Lean_Compiler_LCNF_DependsOn,
};
use crate::r#gen::Lean::Compiler::LCNF::ElimDead::{
    initialize_Lean_Compiler_LCNF_ElimDead, l_Lean_Compiler_LCNF_Decl_elimDeadVars,
    runtime_initialize_Lean_Compiler_LCNF_ElimDead,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize,
    l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl,
    runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::{
    l_Lean_Compiler_LCNF_Decl_saveMono___redArg, l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::ToExpr::{
    initialize_Lean_Compiler_LCNF_ToExpr, l_Lean_Compiler_LCNF_Code_toExpr,
    runtime_initialize_Lean_Compiler_LCNF_ToExpr,
};
use crate::r#gen::Lean::Compiler::NeverExtractAttr::{
    initialize_Lean_Compiler_NeverExtractAttr, l_Lean_hasNeverExtractAttribute,
    runtime_initialize_Lean_Compiler_NeverExtractAttr,
};
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Environment::l_Lean_Environment_find_x3f;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_isForall, l_Lean_FVarIdSet_insert, l_Lean_instBEqFVarId_beq,
    l_Lean_instHashableFVarId_hash,
};
use crate::r#gen::Lean::Util::Trace::l_Lean_registerTraceClass;
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat, lean_usize_sub,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_string_dec_eq, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_apply_8, lean_box, lean_cstr_to_nat,
    lean_ctor_get, lean_ctor_get_uint8, lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8,
    lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_n,
    lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [112, 117, 115, 104, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [66, 121, 116, 101, 65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [70, 108, 111, 97, 116, 65, 114, 114, 97, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [109, 107, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0_value:
    LeanStringObject<8> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [109, 107, 69, 109, 112, 116, 121, 0],
};
static mut l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1_value:
    LeanStringObject<18> = LeanStringObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 18,
    m_capacity: 18,
    m_length: 17,
    m_data: [
        101, 109, 112, 116, 121, 87, 105, 116, 104, 67, 97, 112, 97, 99, 105, 116, 121, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1_value)
        as *mut LeanObject;
static mut l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 99, 108, 111, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__5_value) as *mut LeanObject,15208063451797683741 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7_value) as *mut LeanObject;
static mut l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0:
    *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2_value: LeanStringObject<34> =
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
static mut l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1_value: LeanStringObject<68> =
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
static mut l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0_value: LeanStringObject<25> =
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
static mut l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0_value: LeanClosureObject<0> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed as *const core::ffi::c_void,
        m_arity: 8,
        m_num_fixed: 0,
        m_objs: [],
    };
static mut l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0_value: LeanArrayObject<0> =
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
static mut l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once: LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_extractClosed___closed__0_value: LeanClosureObject<1> =
    LeanClosureObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut LeanObject>() * 1) as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut LeanObject],
    };
static mut l_Lean_Compiler_LCNF_extractClosed___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__0_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_extractClosed___closed__1_value: LeanStringObject<14> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 14,
        m_capacity: 14,
        m_length: 13,
        m_data: [
            101, 120, 116, 114, 97, 99, 116, 67, 108, 111, 115, 101, 100, 0,
        ],
    };
static mut l_Lean_Compiler_LCNF_extractClosed___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__1_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_extractClosed___closed__2_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__1_value)
                as *mut LeanObject,
            2720316290169443600 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_extractClosed___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__2_value) as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_extractClosed___closed__3_value: LeanCtorObject<4> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__2_value)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__0_value)
                as *mut LeanObject,
            257 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_extractClosed___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__3_value) as *mut LeanObject;
pub static mut l_Lean_Compiler_LCNF_extractClosed: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [67, 111, 109, 112, 105, 108, 101, 114, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,2042452093243897853 as *mut LeanObject] };
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_extractClosed___closed__1_value) as *mut LeanObject,3067862634373844558 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<14> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [69, 120, 116, 114, 97, 99, 116, 67, 108, 111, 115, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,658117732910141706 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,15537811569428196235 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,17844854786806673654 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,78082080516119764 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,12412313858240640277 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,2785285543277984572 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,4282159267101488693 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,14824770250903986336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,651304018329614394 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,15508236182584595611 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,17808822902525732088 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,((( 998081055 as usize) << 1) | 1) as *mut LeanObject,9623710272586375282 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,16781247485244476413 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,167924126984734045 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,16245560068144511536 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(
    mut v_as_2335_: *mut LeanObject,
    mut v_i_2336_: usize,
    mut v_stop_2337_: usize,
    mut v_b_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2345_: u8 = 0;
    let mut v___x_2346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2349_: usize = 0;
    let mut v___x_2350_: usize = 0;
    let mut v___x_2352_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2345_ = lean_usize_dec_eq(v_i_2336_, v_stop_2337_);
                if v___x_2345_ == 0 {
                    v___x_2346_ = lean_array_uget_borrowed(v_as_2335_, v_i_2336_);
                    v___x_2347_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(
                        v___x_2346_,
                        v___y_2339_,
                        v___y_2340_,
                        v___y_2341_,
                        v___y_2342_,
                        v___y_2343_,
                    );
                    if lean_obj_tag(v___x_2347_) == 0 {
                        v_a_2348_ = lean_ctor_get(v___x_2347_, 0);
                        lean_inc(v_a_2348_);
                        lean_dec_ref_known(v___x_2347_, 1);
                        v___x_2349_ = 1usize;
                        v___x_2350_ = lean_usize_add(v_i_2336_, v___x_2349_);
                        v_i_2336_ = v___x_2350_;
                        v_b_2338_ = v_a_2348_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2347_;
                    }
                } else {
                    v___x_2352_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2352_, 0, v_b_2338_);
                    return v___x_2352_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(
    mut v_v_2353_: *mut LeanObject,
    mut v_a_2354_: *mut LeanObject,
    mut v_a_2355_: *mut LeanObject,
    mut v_a_2356_: *mut LeanObject,
    mut v_a_2357_: *mut LeanObject,
    mut v_a_2358_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2362_: u8 = 0;
    let mut v___x_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2367_: u8 = 0;
    let mut v_unused_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2375_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: u8 = 0;
    let mut v___x_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: u8 = 0;
    let mut v___x_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: usize = 0;
    let mut v___x_2382_: usize = 0;
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: usize = 0;
    let mut v___x_2385_: usize = 0;
    let mut v___x_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2392_: u8 = 0;
    let mut v___x_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2396_: u8 = 0;
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2404_: usize = 0;
    let mut v___x_2405_: usize = 0;
    let mut v___x_2406_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: usize = 0;
    let mut v___x_2408_: usize = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2410_: u8 = 0;
    let mut v_unused_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_v_2353_) {
                0 => {
                    v_isSharedCheck_2367_ = (!lean_is_exclusive(v_v_2353_)) as u8;
                    if v_isSharedCheck_2367_ == 0 {
                        v_unused_2368_ = lean_ctor_get(v_v_2353_, 0);
                        lean_dec(v_unused_2368_);
                        v___x_2361_ = v_v_2353_;
                        v_isShared_2362_ = v_isSharedCheck_2367_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_v_2353_);
                        v___x_2361_ = lean_box(0);
                        v_isShared_2362_ = v_isSharedCheck_2367_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2369_ = lean_box(0);
                    v___x_2370_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2370_, 0, v___x_2369_);
                    return v___x_2370_;
                }
                2 => {
                    v_struct_2371_ = lean_ctor_get(v_v_2353_, 2);
                    lean_inc(v_struct_2371_);
                    lean_dec_ref_known(v_v_2353_, 3);
                    v___x_2372_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(
                        v_struct_2371_,
                        v_a_2354_,
                        v_a_2355_,
                        v_a_2356_,
                        v_a_2357_,
                        v_a_2358_,
                    );
                    lean_dec(v_struct_2371_);
                    return v___x_2372_;
                }
                3 => {
                    v_args_2373_ = lean_ctor_get(v_v_2353_, 2);
                    lean_inc_ref(v_args_2373_);
                    lean_dec_ref_known(v_v_2353_, 3);
                    v___x_2374_ = lean_unsigned_to_nat(0);
                    v___x_2375_ = lean_array_get_size(v_args_2373_);
                    v___x_2376_ = lean_box(0);
                    v___x_2377_ = lean_nat_dec_lt(v___x_2374_, v___x_2375_);
                    if v___x_2377_ == 0 {
                        lean_dec_ref(v_args_2373_);
                        v___x_2378_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2378_, 0, v___x_2376_);
                        return v___x_2378_;
                    } else {
                        v___x_2379_ = lean_nat_dec_le(v___x_2375_, v___x_2375_);
                        if v___x_2379_ == 0 {
                            if v___x_2377_ == 0 {
                                lean_dec_ref(v_args_2373_);
                                v___x_2380_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v___x_2380_, 0, v___x_2376_);
                                return v___x_2380_;
                            } else {
                                v___x_2381_ = 0usize;
                                v___x_2382_ = lean_usize_of_nat(v___x_2375_);
                                v___x_2383_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_2373_, v___x_2381_, v___x_2382_, v___x_2376_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
                                lean_dec_ref(v_args_2373_);
                                return v___x_2383_;
                            }
                        } else {
                            v___x_2384_ = 0usize;
                            v___x_2385_ = lean_usize_of_nat(v___x_2375_);
                            v___x_2386_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_2373_, v___x_2384_, v___x_2385_, v___x_2376_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
                            lean_dec_ref(v_args_2373_);
                            return v___x_2386_;
                        }
                    }
                }
                _ => {
                    v_fvarId_2387_ = lean_ctor_get(v_v_2353_, 0);
                    lean_inc(v_fvarId_2387_);
                    v_args_2388_ = lean_ctor_get(v_v_2353_, 1);
                    lean_inc_ref(v_args_2388_);
                    lean_dec_ref_known(v_v_2353_, 2);
                    v___x_2389_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(
                        v_fvarId_2387_,
                        v_a_2354_,
                        v_a_2355_,
                        v_a_2356_,
                        v_a_2357_,
                        v_a_2358_,
                    );
                    lean_dec(v_fvarId_2387_);
                    if lean_obj_tag(v___x_2389_) == 0 {
                        v_isSharedCheck_2410_ = (!lean_is_exclusive(v___x_2389_)) as u8;
                        if v_isSharedCheck_2410_ == 0 {
                            v_unused_2411_ = lean_ctor_get(v___x_2389_, 0);
                            lean_dec(v_unused_2411_);
                            v___x_2391_ = v___x_2389_;
                            v_isShared_2392_ = v_isSharedCheck_2410_;
                            state = 3;
                            continue;
                        } else {
                            lean_dec(v___x_2389_);
                            v___x_2391_ = lean_box(0);
                            v_isShared_2392_ = v_isSharedCheck_2410_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_args_2388_);
                        return v___x_2389_;
                    }
                }
            },
            1 => {
                v___x_2363_ = lean_box(0);
                if v_isShared_2362_ == 0 {
                    lean_ctor_set(v___x_2361_, 0, v___x_2363_);
                    v___x_2365_ = v___x_2361_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2366_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2366_, 0, v___x_2363_);
                    v___x_2365_ = v_reuseFailAlloc_2366_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2365_;
            }
            3 => {
                v___x_2393_ = lean_unsigned_to_nat(0);
                v___x_2394_ = lean_array_get_size(v_args_2388_);
                v___x_2395_ = lean_box(0);
                v___x_2396_ = lean_nat_dec_lt(v___x_2393_, v___x_2394_);
                if v___x_2396_ == 0 {
                    lean_dec_ref(v_args_2388_);
                    if v_isShared_2392_ == 0 {
                        lean_ctor_set(v___x_2391_, 0, v___x_2395_);
                        v___x_2398_ = v___x_2391_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2399_, 0, v___x_2395_);
                        v___x_2398_ = v_reuseFailAlloc_2399_;
                        state = 4;
                        continue;
                    }
                } else {
                    v___x_2400_ = lean_nat_dec_le(v___x_2394_, v___x_2394_);
                    if v___x_2400_ == 0 {
                        if v___x_2396_ == 0 {
                            lean_dec_ref(v_args_2388_);
                            if v_isShared_2392_ == 0 {
                                lean_ctor_set(v___x_2391_, 0, v___x_2395_);
                                v___x_2402_ = v___x_2391_;
                                state = 5;
                                continue;
                            } else {
                                v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2403_, 0, v___x_2395_);
                                v___x_2402_ = v_reuseFailAlloc_2403_;
                                state = 5;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2391_);
                            v___x_2404_ = 0usize;
                            v___x_2405_ = lean_usize_of_nat(v___x_2394_);
                            v___x_2406_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_2388_, v___x_2404_, v___x_2405_, v___x_2395_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
                            lean_dec_ref(v_args_2388_);
                            return v___x_2406_;
                        }
                    } else {
                        lean_del_object(v___x_2391_);
                        v___x_2407_ = 0usize;
                        v___x_2408_ = lean_usize_of_nat(v___x_2394_);
                        v___x_2409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_args_2388_, v___x_2407_, v___x_2408_, v___x_2395_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
                        lean_dec_ref(v_args_2388_);
                        return v___x_2409_;
                    }
                }
            }
            4 => {
                return v___x_2398_;
            }
            5 => {
                return v___x_2402_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(
    mut v_fvarId_2412_: *mut LeanObject,
    mut v_a_2413_: *mut LeanObject,
    mut v_a_2414_: *mut LeanObject,
    mut v_a_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2419_: u8 = 0;
    let mut v___x_2420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2424_: u8 = 0;
    let mut v_val_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2428_: u8 = 0;
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2437_: u8 = 0;
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2442_: u8 = 0;
    let mut v_a_2443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2446_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2450_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2419_ = 0;
                v___x_2420_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                    v___x_2419_,
                    v_fvarId_2412_,
                    v_a_2415_,
                );
                if lean_obj_tag(v___x_2420_) == 0 {
                    v_a_2421_ = lean_ctor_get(v___x_2420_, 0);
                    v_isSharedCheck_2442_ = (!lean_is_exclusive(v___x_2420_)) as u8;
                    if v_isSharedCheck_2442_ == 0 {
                        v___x_2423_ = v___x_2420_;
                        v_isShared_2424_ = v_isSharedCheck_2442_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2421_);
                        lean_dec(v___x_2420_);
                        v___x_2423_ = lean_box(0);
                        v_isShared_2424_ = v_isSharedCheck_2442_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2443_ = lean_ctor_get(v___x_2420_, 0);
                    v_isSharedCheck_2450_ = (!lean_is_exclusive(v___x_2420_)) as u8;
                    if v_isSharedCheck_2450_ == 0 {
                        v___x_2445_ = v___x_2420_;
                        v_isShared_2446_ = v_isSharedCheck_2450_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2443_);
                        lean_dec(v___x_2420_);
                        v___x_2445_ = lean_box(0);
                        v_isShared_2446_ = v_isSharedCheck_2450_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2421_) == 1 {
                    lean_del_object(v___x_2423_);
                    v_val_2425_ = lean_ctor_get(v_a_2421_, 0);
                    v_isSharedCheck_2437_ = (!lean_is_exclusive(v_a_2421_)) as u8;
                    if v_isSharedCheck_2437_ == 0 {
                        v___x_2427_ = v_a_2421_;
                        v_isShared_2428_ = v_isSharedCheck_2437_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_2425_);
                        lean_dec(v_a_2421_);
                        v___x_2427_ = lean_box(0);
                        v_isShared_2428_ = v_isSharedCheck_2437_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2421_);
                    v___x_2438_ = lean_box(0);
                    if v_isShared_2424_ == 0 {
                        lean_ctor_set(v___x_2423_, 0, v___x_2438_);
                        v___x_2440_ = v___x_2423_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2441_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2441_, 0, v___x_2438_);
                        v___x_2440_ = v_reuseFailAlloc_2441_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2429_ = lean_st_ref_take(v_a_2413_);
                lean_inc(v_val_2425_);
                if v_isShared_2428_ == 0 {
                    lean_ctor_set_tag(v___x_2427_, 0);
                    v___x_2431_ = v___x_2427_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2436_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_val_2425_);
                    v___x_2431_ = v_reuseFailAlloc_2436_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2432_ = lean_array_push(v___x_2429_, v___x_2431_);
                v___x_2433_ = lean_st_ref_set(v_a_2413_, v___x_2432_);
                v_value_2434_ = lean_ctor_get(v_val_2425_, 3);
                lean_inc(v_value_2434_);
                lean_dec(v_val_2425_);
                v___x_2435_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(
                    v_value_2434_,
                    v_a_2413_,
                    v_a_2414_,
                    v_a_2415_,
                    v_a_2416_,
                    v_a_2417_,
                );
                return v___x_2435_;
            }
            4 => {
                return v___x_2440_;
            }
            5 => {
                if v_isShared_2446_ == 0 {
                    v___x_2448_ = v___x_2445_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2449_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2449_, 0, v_a_2443_);
                    v___x_2448_ = v_reuseFailAlloc_2449_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2448_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_extractArg(
    mut v_arg_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
    mut v_a_2453_: *mut LeanObject,
    mut v_a_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_arg_2451_) == 1 {
        let mut v_fvarId_2458_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2459_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_2458_ = lean_ctor_get(v_arg_2451_, 0);
        v___x_2459_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(
            v_fvarId_2458_,
            v_a_2452_,
            v_a_2453_,
            v_a_2454_,
            v_a_2455_,
            v_a_2456_,
        );
        return v___x_2459_;
    } else {
        let mut v___x_2460_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
        v___x_2460_ = lean_box(0);
        v___x_2461_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2461_, 0, v___x_2460_);
        return v___x_2461_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_extractArg___boxed(
    mut v_arg_2462_: *mut LeanObject,
    mut v_a_2463_: *mut LeanObject,
    mut v_a_2464_: *mut LeanObject,
    mut v_a_2465_: *mut LeanObject,
    mut v_a_2466_: *mut LeanObject,
    mut v_a_2467_: *mut LeanObject,
    mut v_a_2468_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2469_: *mut LeanObject = core::ptr::null_mut();
    v_res_2469_ = l_Lean_Compiler_LCNF_ExtractClosed_extractArg(
        v_arg_2462_,
        v_a_2463_,
        v_a_2464_,
        v_a_2465_,
        v_a_2466_,
        v_a_2467_,
    );
    lean_dec(v_a_2467_);
    lean_dec_ref(v_a_2466_);
    lean_dec(v_a_2465_);
    lean_dec_ref(v_a_2464_);
    lean_dec(v_a_2463_);
    lean_dec(v_arg_2462_);
    return v_res_2469_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0___boxed(
    mut v_as_2470_: *mut LeanObject,
    mut v_i_2471_: *mut LeanObject,
    mut v_stop_2472_: *mut LeanObject,
    mut v_b_2473_: *mut LeanObject,
    mut v___y_2474_: *mut LeanObject,
    mut v___y_2475_: *mut LeanObject,
    mut v___y_2476_: *mut LeanObject,
    mut v___y_2477_: *mut LeanObject,
    mut v___y_2478_: *mut LeanObject,
    mut v___y_2479_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2480_: usize = 0;
    let mut v_stop_boxed_2481_: usize = 0;
    let mut v_res_2482_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2480_ = lean_unbox_usize(v_i_2471_);
    lean_dec(v_i_2471_);
    v_stop_boxed_2481_ = lean_unbox_usize(v_stop_2472_);
    lean_dec(v_stop_2472_);
    v_res_2482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_ExtractClosed_extractLetValue_spec__0(v_as_2470_, v_i_boxed_2480_, v_stop_boxed_2481_, v_b_2473_, v___y_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
    lean_dec(v___y_2478_);
    lean_dec_ref(v___y_2477_);
    lean_dec(v___y_2476_);
    lean_dec_ref(v___y_2475_);
    lean_dec(v___y_2474_);
    lean_dec_ref(v_as_2470_);
    return v_res_2482_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_extractFVar___boxed(
    mut v_fvarId_2483_: *mut LeanObject,
    mut v_a_2484_: *mut LeanObject,
    mut v_a_2485_: *mut LeanObject,
    mut v_a_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2490_: *mut LeanObject = core::ptr::null_mut();
    v_res_2490_ = l_Lean_Compiler_LCNF_ExtractClosed_extractFVar(
        v_fvarId_2483_,
        v_a_2484_,
        v_a_2485_,
        v_a_2486_,
        v_a_2487_,
        v_a_2488_,
    );
    lean_dec(v_a_2488_);
    lean_dec_ref(v_a_2487_);
    lean_dec(v_a_2486_);
    lean_dec_ref(v_a_2485_);
    lean_dec(v_a_2484_);
    lean_dec(v_fvarId_2483_);
    return v_res_2490_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue___boxed(
    mut v_v_2491_: *mut LeanObject,
    mut v_a_2492_: *mut LeanObject,
    mut v_a_2493_: *mut LeanObject,
    mut v_a_2494_: *mut LeanObject,
    mut v_a_2495_: *mut LeanObject,
    mut v_a_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2498_: *mut LeanObject = core::ptr::null_mut();
    v_res_2498_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(
        v_v_2491_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_,
    );
    lean_dec(v_a_2496_);
    lean_dec_ref(v_a_2495_);
    lean_dec(v_a_2494_);
    lean_dec_ref(v_a_2493_);
    lean_dec(v_a_2492_);
    return v_res_2498_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(
    mut v_arg_2499_: *mut LeanObject,
) -> u8 {
    if lean_obj_tag(v_arg_2499_) == 1 {
        let mut v___x_2500_: u8 = 0;
        v___x_2500_ = 0;
        return v___x_2500_;
    } else {
        let mut v___x_2501_: u8 = 0;
        v___x_2501_ = 1;
        return v___x_2501_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg___boxed(
    mut v_arg_2502_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2503_: u8 = 0;
    let mut v_r_2504_: *mut LeanObject = core::ptr::null_mut();
    v_res_2503_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v_arg_2502_);
    lean_dec(v_arg_2502_);
    v_r_2504_ = lean_box((v_res_2503_) as usize);
    return v_r_2504_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(
    mut v_____do__lift_2505_: u8,
    mut v___y_2506_: *mut LeanObject,
    mut v___y_2507_: *mut LeanObject,
    mut v___y_2508_: *mut LeanObject,
    mut v___y_2509_: *mut LeanObject,
    mut v___y_2510_: *mut LeanObject,
    mut v___y_2511_: *mut LeanObject,
) -> *mut LeanObject {
    if v_____do__lift_2505_ == 0 {
        let mut v___x_2513_: u8 = 0;
        let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
        v___x_2513_ = 1;
        v___x_2514_ = lean_box((v___x_2513_) as usize);
        v___x_2515_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2515_, 0, v___x_2514_);
        return v___x_2515_;
    } else {
        let mut v___x_2516_: u8 = 0;
        let mut v___x_2517_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
        v___x_2516_ = 0;
        v___x_2517_ = lean_box((v___x_2516_) as usize);
        v___x_2518_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_2518_, 0, v___x_2517_);
        return v___x_2518_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0___boxed(
    mut v_____do__lift_2519_: *mut LeanObject,
    mut v___y_2520_: *mut LeanObject,
    mut v___y_2521_: *mut LeanObject,
    mut v___y_2522_: *mut LeanObject,
    mut v___y_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____do__lift_18059__boxed_2527_: u8 = 0;
    let mut v_res_2528_: *mut LeanObject = core::ptr::null_mut();
    v_____do__lift_18059__boxed_2527_ = (lean_unbox(v_____do__lift_2519_) as u8);
    v_res_2528_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(
        v_____do__lift_18059__boxed_2527_,
        v___y_2520_,
        v___y_2521_,
        v___y_2522_,
        v___y_2523_,
        v___y_2524_,
        v___y_2525_,
    );
    lean_dec(v___y_2525_);
    lean_dec_ref(v___y_2524_);
    lean_dec(v___y_2523_);
    lean_dec_ref(v___y_2522_);
    lean_dec(v___y_2521_);
    lean_dec_ref(v___y_2520_);
    return v_res_2528_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(
    mut v_a_2529_: *mut LeanObject,
    mut v_x_2530_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2535_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2530_) == 0 {
                    v___x_2531_ = lean_box(0);
                    return v___x_2531_;
                } else {
                    v_key_2532_ = lean_ctor_get(v_x_2530_, 0);
                    v_value_2533_ = lean_ctor_get(v_x_2530_, 1);
                    v_tail_2534_ = lean_ctor_get(v_x_2530_, 2);
                    v___x_2535_ = l_Lean_instBEqFVarId_beq(v_key_2532_, v_a_2529_);
                    if v___x_2535_ == 0 {
                        v_x_2530_ = v_tail_2534_;
                        state = 0;
                        continue;
                    } else {
                        lean_inc(v_value_2533_);
                        v___x_2537_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2537_, 0, v_value_2533_);
                        return v___x_2537_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg___boxed(
    mut v_a_2538_: *mut LeanObject,
    mut v_x_2539_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2540_: *mut LeanObject = core::ptr::null_mut();
    v_res_2540_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_2538_, v_x_2539_);
    lean_dec(v_x_2539_);
    lean_dec(v_a_2538_);
    return v_res_2540_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(
    mut v_m_2541_: *mut LeanObject,
    mut v_a_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2545_: u64 = 0;
    let mut v___x_2546_: u64 = 0;
    let mut v___x_2547_: u64 = 0;
    let mut v_fold_2548_: u64 = 0;
    let mut v___x_2549_: u64 = 0;
    let mut v___x_2550_: u64 = 0;
    let mut v___x_2551_: u64 = 0;
    let mut v___x_2552_: usize = 0;
    let mut v___x_2553_: usize = 0;
    let mut v___x_2554_: usize = 0;
    let mut v___x_2555_: usize = 0;
    let mut v___x_2556_: usize = 0;
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_2543_ = lean_ctor_get(v_m_2541_, 1);
    v___x_2544_ = lean_array_get_size(v_buckets_2543_);
    v___x_2545_ = l_Lean_instHashableFVarId_hash(v_a_2542_);
    v___x_2546_ = 32u64;
    v___x_2547_ = lean_uint64_shift_right(v___x_2545_, v___x_2546_);
    v_fold_2548_ = lean_uint64_xor(v___x_2545_, v___x_2547_);
    v___x_2549_ = 16u64;
    v___x_2550_ = lean_uint64_shift_right(v_fold_2548_, v___x_2549_);
    v___x_2551_ = lean_uint64_xor(v_fold_2548_, v___x_2550_);
    v___x_2552_ = lean_uint64_to_usize(v___x_2551_);
    v___x_2553_ = lean_usize_of_nat(v___x_2544_);
    v___x_2554_ = 1usize;
    v___x_2555_ = lean_usize_sub(v___x_2553_, v___x_2554_);
    v___x_2556_ = lean_usize_land(v___x_2552_, v___x_2555_);
    v___x_2557_ = lean_array_uget_borrowed(v_buckets_2543_, v___x_2556_);
    v___x_2558_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_2542_, v___x_2557_);
    return v___x_2558_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg___boxed(
    mut v_m_2559_: *mut LeanObject,
    mut v_a_2560_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2561_: *mut LeanObject = core::ptr::null_mut();
    v_res_2561_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_2559_, v_a_2560_);
    lean_dec(v_a_2560_);
    lean_dec_ref(v_m_2559_);
    return v_res_2561_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(
    mut v_x_2562_: *mut LeanObject,
    mut v_x_2563_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2569_: u8 = 0;
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: u64 = 0;
    let mut v___x_2572_: u64 = 0;
    let mut v___x_2573_: u64 = 0;
    let mut v_fold_2574_: u64 = 0;
    let mut v___x_2575_: u64 = 0;
    let mut v___x_2576_: u64 = 0;
    let mut v___x_2577_: u64 = 0;
    let mut v___x_2578_: usize = 0;
    let mut v___x_2579_: usize = 0;
    let mut v___x_2580_: usize = 0;
    let mut v___x_2581_: usize = 0;
    let mut v___x_2582_: usize = 0;
    let mut v___x_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2588_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2563_) == 0 {
                    return v_x_2562_;
                } else {
                    v_key_2564_ = lean_ctor_get(v_x_2563_, 0);
                    v_value_2565_ = lean_ctor_get(v_x_2563_, 1);
                    v_tail_2566_ = lean_ctor_get(v_x_2563_, 2);
                    v_isSharedCheck_2589_ = (!lean_is_exclusive(v_x_2563_)) as u8;
                    if v_isSharedCheck_2589_ == 0 {
                        v___x_2568_ = v_x_2563_;
                        v_isShared_2569_ = v_isSharedCheck_2589_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2566_);
                        lean_inc(v_value_2565_);
                        lean_inc(v_key_2564_);
                        lean_dec(v_x_2563_);
                        v___x_2568_ = lean_box(0);
                        v_isShared_2569_ = v_isSharedCheck_2589_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2570_ = lean_array_get_size(v_x_2562_);
                v___x_2571_ = l_Lean_instHashableFVarId_hash(v_key_2564_);
                v___x_2572_ = 32u64;
                v___x_2573_ = lean_uint64_shift_right(v___x_2571_, v___x_2572_);
                v_fold_2574_ = lean_uint64_xor(v___x_2571_, v___x_2573_);
                v___x_2575_ = 16u64;
                v___x_2576_ = lean_uint64_shift_right(v_fold_2574_, v___x_2575_);
                v___x_2577_ = lean_uint64_xor(v_fold_2574_, v___x_2576_);
                v___x_2578_ = lean_uint64_to_usize(v___x_2577_);
                v___x_2579_ = lean_usize_of_nat(v___x_2570_);
                v___x_2580_ = 1usize;
                v___x_2581_ = lean_usize_sub(v___x_2579_, v___x_2580_);
                v___x_2582_ = lean_usize_land(v___x_2578_, v___x_2581_);
                v___x_2583_ = lean_array_uget_borrowed(v_x_2562_, v___x_2582_);
                lean_inc(v___x_2583_);
                if v_isShared_2569_ == 0 {
                    lean_ctor_set(v___x_2568_, 2, v___x_2583_);
                    v___x_2585_ = v___x_2568_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2588_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_key_2564_);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_value_2565_);
                    lean_ctor_set(v_reuseFailAlloc_2588_, 2, v___x_2583_);
                    v___x_2585_ = v_reuseFailAlloc_2588_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2586_ = lean_array_uset(v_x_2562_, v___x_2582_, v___x_2585_);
                v_x_2562_ = v___x_2586_;
                v_x_2563_ = v_tail_2566_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(
    mut v_i_2590_: *mut LeanObject,
    mut v_source_2591_: *mut LeanObject,
    mut v_target_2592_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: u8 = 0;
    let mut v_es_2595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2593_ = lean_array_get_size(v_source_2591_);
                v___x_2594_ = lean_nat_dec_lt(v_i_2590_, v___x_2593_);
                if v___x_2594_ == 0 {
                    lean_dec_ref(v_source_2591_);
                    lean_dec(v_i_2590_);
                    return v_target_2592_;
                } else {
                    v_es_2595_ = lean_array_fget(v_source_2591_, v_i_2590_);
                    v___x_2596_ = lean_box(0);
                    v_source_2597_ = lean_array_fset(v_source_2591_, v_i_2590_, v___x_2596_);
                    v_target_2598_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_target_2592_, v_es_2595_);
                    v___x_2599_ = lean_unsigned_to_nat(1);
                    v___x_2600_ = lean_nat_add(v_i_2590_, v___x_2599_);
                    lean_dec(v_i_2590_);
                    v_i_2590_ = v___x_2600_;
                    v_source_2591_ = v_source_2597_;
                    v_target_2592_ = v_target_2598_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(
    mut v_data_2602_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    v___x_2603_ = lean_array_get_size(v_data_2602_);
    v___x_2604_ = lean_unsigned_to_nat(2);
    v_nbuckets_2605_ = lean_nat_mul(v___x_2603_, v___x_2604_);
    v___x_2606_ = lean_unsigned_to_nat(0);
    v___x_2607_ = lean_box(0);
    v___x_2608_ = lean_mk_array(v_nbuckets_2605_, v___x_2607_);
    v___x_2609_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v___x_2606_, v_data_2602_, v___x_2608_);
    return v___x_2609_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(
    mut v_a_2610_: *mut LeanObject,
    mut v_b_2611_: *mut LeanObject,
    mut v_x_2612_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2618_: u8 = 0;
    let mut v___x_2619_: u8 = 0;
    let mut v___x_2620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2627_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2612_) == 0 {
                    lean_dec(v_b_2611_);
                    lean_dec(v_a_2610_);
                    return v_x_2612_;
                } else {
                    v_key_2613_ = lean_ctor_get(v_x_2612_, 0);
                    v_value_2614_ = lean_ctor_get(v_x_2612_, 1);
                    v_tail_2615_ = lean_ctor_get(v_x_2612_, 2);
                    v_isSharedCheck_2627_ = (!lean_is_exclusive(v_x_2612_)) as u8;
                    if v_isSharedCheck_2627_ == 0 {
                        v___x_2617_ = v_x_2612_;
                        v_isShared_2618_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_2615_);
                        lean_inc(v_value_2614_);
                        lean_inc(v_key_2613_);
                        lean_dec(v_x_2612_);
                        v___x_2617_ = lean_box(0);
                        v_isShared_2618_ = v_isSharedCheck_2627_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2619_ = l_Lean_instBEqFVarId_beq(v_key_2613_, v_a_2610_);
                if v___x_2619_ == 0 {
                    v___x_2620_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_2610_, v_b_2611_, v_tail_2615_);
                    if v_isShared_2618_ == 0 {
                        lean_ctor_set(v___x_2617_, 2, v___x_2620_);
                        v___x_2622_ = v___x_2617_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2623_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2623_, 0, v_key_2613_);
                        lean_ctor_set(v_reuseFailAlloc_2623_, 1, v_value_2614_);
                        lean_ctor_set(v_reuseFailAlloc_2623_, 2, v___x_2620_);
                        v___x_2622_ = v_reuseFailAlloc_2623_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_2614_);
                    lean_dec(v_key_2613_);
                    if v_isShared_2618_ == 0 {
                        lean_ctor_set(v___x_2617_, 1, v_b_2611_);
                        lean_ctor_set(v___x_2617_, 0, v_a_2610_);
                        v___x_2625_ = v___x_2617_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2626_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2626_, 0, v_a_2610_);
                        lean_ctor_set(v_reuseFailAlloc_2626_, 1, v_b_2611_);
                        lean_ctor_set(v_reuseFailAlloc_2626_, 2, v_tail_2615_);
                        v___x_2625_ = v_reuseFailAlloc_2626_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2622_;
            }
            3 => {
                return v___x_2625_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(
    mut v_a_2628_: *mut LeanObject,
    mut v_x_2629_: *mut LeanObject,
) -> u8 {
    let mut v___x_2630_: u8 = 0;
    let mut v_key_2631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2629_) == 0 {
                    v___x_2630_ = 0;
                    return v___x_2630_;
                } else {
                    v_key_2631_ = lean_ctor_get(v_x_2629_, 0);
                    v_tail_2632_ = lean_ctor_get(v_x_2629_, 2);
                    v___x_2633_ = l_Lean_instBEqFVarId_beq(v_key_2631_, v_a_2628_);
                    if v___x_2633_ == 0 {
                        v_x_2629_ = v_tail_2632_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2633_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg___boxed(
    mut v_a_2635_: *mut LeanObject,
    mut v_x_2636_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2637_: u8 = 0;
    let mut v_r_2638_: *mut LeanObject = core::ptr::null_mut();
    v_res_2637_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_2635_, v_x_2636_);
    lean_dec(v_x_2636_);
    lean_dec(v_a_2635_);
    v_r_2638_ = lean_box((v_res_2637_) as usize);
    return v_r_2638_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(
    mut v_m_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_b_2641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2646_: u8 = 0;
    let mut v___x_2647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2648_: u64 = 0;
    let mut v___x_2649_: u64 = 0;
    let mut v___x_2650_: u64 = 0;
    let mut v_fold_2651_: u64 = 0;
    let mut v___x_2652_: u64 = 0;
    let mut v___x_2653_: u64 = 0;
    let mut v___x_2654_: u64 = 0;
    let mut v___x_2655_: usize = 0;
    let mut v___x_2656_: usize = 0;
    let mut v___x_2657_: usize = 0;
    let mut v___x_2658_: usize = 0;
    let mut v___x_2659_: usize = 0;
    let mut v_bkt_2660_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2661_: u8 = 0;
    let mut v___x_2662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2671_: u8 = 0;
    let mut v_val_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2675_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2686_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2642_ = lean_ctor_get(v_m_2639_, 0);
                v_buckets_2643_ = lean_ctor_get(v_m_2639_, 1);
                v_isSharedCheck_2686_ = (!lean_is_exclusive(v_m_2639_)) as u8;
                if v_isSharedCheck_2686_ == 0 {
                    v___x_2645_ = v_m_2639_;
                    v_isShared_2646_ = v_isSharedCheck_2686_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_2643_);
                    lean_inc(v_size_2642_);
                    lean_dec(v_m_2639_);
                    v___x_2645_ = lean_box(0);
                    v_isShared_2646_ = v_isSharedCheck_2686_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2647_ = lean_array_get_size(v_buckets_2643_);
                v___x_2648_ = l_Lean_instHashableFVarId_hash(v_a_2640_);
                v___x_2649_ = 32u64;
                v___x_2650_ = lean_uint64_shift_right(v___x_2648_, v___x_2649_);
                v_fold_2651_ = lean_uint64_xor(v___x_2648_, v___x_2650_);
                v___x_2652_ = 16u64;
                v___x_2653_ = lean_uint64_shift_right(v_fold_2651_, v___x_2652_);
                v___x_2654_ = lean_uint64_xor(v_fold_2651_, v___x_2653_);
                v___x_2655_ = lean_uint64_to_usize(v___x_2654_);
                v___x_2656_ = lean_usize_of_nat(v___x_2647_);
                v___x_2657_ = 1usize;
                v___x_2658_ = lean_usize_sub(v___x_2656_, v___x_2657_);
                v___x_2659_ = lean_usize_land(v___x_2655_, v___x_2658_);
                v_bkt_2660_ = lean_array_uget_borrowed(v_buckets_2643_, v___x_2659_);
                v___x_2661_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_2640_, v_bkt_2660_);
                if v___x_2661_ == 0 {
                    v___x_2662_ = lean_unsigned_to_nat(1);
                    v_size_x27_2663_ = lean_nat_add(v_size_2642_, v___x_2662_);
                    lean_dec(v_size_2642_);
                    lean_inc(v_bkt_2660_);
                    v___x_2664_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_2664_, 0, v_a_2640_);
                    lean_ctor_set(v___x_2664_, 1, v_b_2641_);
                    lean_ctor_set(v___x_2664_, 2, v_bkt_2660_);
                    v_buckets_x27_2665_ =
                        lean_array_uset(v_buckets_2643_, v___x_2659_, v___x_2664_);
                    v___x_2666_ = lean_unsigned_to_nat(4);
                    v___x_2667_ = lean_nat_mul(v_size_x27_2663_, v___x_2666_);
                    v___x_2668_ = lean_unsigned_to_nat(3);
                    v___x_2669_ = lean_nat_div(v___x_2667_, v___x_2668_);
                    lean_dec(v___x_2667_);
                    v___x_2670_ = lean_array_get_size(v_buckets_x27_2665_);
                    v___x_2671_ = lean_nat_dec_le(v___x_2669_, v___x_2670_);
                    lean_dec(v___x_2669_);
                    if v___x_2671_ == 0 {
                        v_val_2672_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_buckets_x27_2665_);
                        if v_isShared_2646_ == 0 {
                            lean_ctor_set(v___x_2645_, 1, v_val_2672_);
                            lean_ctor_set(v___x_2645_, 0, v_size_x27_2663_);
                            v___x_2674_ = v___x_2645_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2675_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2675_, 0, v_size_x27_2663_);
                            lean_ctor_set(v_reuseFailAlloc_2675_, 1, v_val_2672_);
                            v___x_2674_ = v_reuseFailAlloc_2675_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_2646_ == 0 {
                            lean_ctor_set(v___x_2645_, 1, v_buckets_x27_2665_);
                            lean_ctor_set(v___x_2645_, 0, v_size_x27_2663_);
                            v___x_2677_ = v___x_2645_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_size_x27_2663_);
                            lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_buckets_x27_2665_);
                            v___x_2677_ = v_reuseFailAlloc_2678_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_2660_);
                    v___x_2679_ = lean_box(0);
                    v_buckets_x27_2680_ =
                        lean_array_uset(v_buckets_2643_, v___x_2659_, v___x_2679_);
                    v___x_2681_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_2640_, v_b_2641_, v_bkt_2660_);
                    v___x_2682_ = lean_array_uset(v_buckets_x27_2680_, v___x_2659_, v___x_2681_);
                    if v_isShared_2646_ == 0 {
                        lean_ctor_set(v___x_2645_, 1, v___x_2682_);
                        v___x_2684_ = v___x_2645_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2685_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2685_, 0, v_size_2642_);
                        lean_ctor_set(v_reuseFailAlloc_2685_, 1, v___x_2682_);
                        v___x_2684_ = v_reuseFailAlloc_2685_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2674_;
            }
            3 => {
                return v___x_2677_;
            }
            4 => {
                return v___x_2684_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(
    mut v_declName_2687_: *mut LeanObject,
    mut v_as_2688_: *mut LeanObject,
    mut v_i_2689_: usize,
    mut v_stop_2690_: usize,
) -> u8 {
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: u8 = 0;
    let mut v___x_2696_: usize = 0;
    let mut v___x_2697_: usize = 0;
    let mut v___x_2699_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2691_ = lean_usize_dec_eq(v_i_2689_, v_stop_2690_);
                if v___x_2691_ == 0 {
                    v___x_2692_ = lean_array_uget_borrowed(v_as_2688_, v_i_2689_);
                    v_toSignature_2693_ = lean_ctor_get(v___x_2692_, 0);
                    v_name_2694_ = lean_ctor_get(v_toSignature_2693_, 0);
                    v___x_2695_ = lean_name_eq(v_name_2694_, v_declName_2687_);
                    if v___x_2695_ == 0 {
                        v___x_2696_ = 1usize;
                        v___x_2697_ = lean_usize_add(v_i_2689_, v___x_2696_);
                        v_i_2689_ = v___x_2697_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2695_;
                    }
                } else {
                    v___x_2699_ = 0;
                    return v___x_2699_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3___boxed(
    mut v_declName_2700_: *mut LeanObject,
    mut v_as_2701_: *mut LeanObject,
    mut v_i_2702_: *mut LeanObject,
    mut v_stop_2703_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2704_: usize = 0;
    let mut v_stop_boxed_2705_: usize = 0;
    let mut v_res_2706_: u8 = 0;
    let mut v_r_2707_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2704_ = lean_unbox_usize(v_i_2702_);
    lean_dec(v_i_2702_);
    v_stop_boxed_2705_ = lean_unbox_usize(v_stop_2703_);
    lean_dec(v_stop_2703_);
    v_res_2706_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_2700_, v_as_2701_, v_i_boxed_2704_, v_stop_boxed_2705_);
    lean_dec_ref(v_as_2701_);
    lean_dec(v_declName_2700_);
    v_r_2707_ = lean_box((v_res_2706_) as usize);
    return v_r_2707_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(
    mut v_isRoot_2708_: u8,
    mut v___x_2709_: u8,
    mut v_as_2710_: *mut LeanObject,
    mut v_i_2711_: usize,
    mut v_stop_2712_: usize,
) -> u8 {
    let mut v___x_2713_: u8 = 0;
    let mut v___x_2714_: u8 = 0;
    let mut v___y_2716_: u8 = 0;
    let mut v___x_2717_: usize = 0;
    let mut v___x_2718_: usize = 0;
    let mut v___x_2720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2721_: u8 = 0;
    let mut v___x_2722_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2713_ = lean_usize_dec_eq(v_i_2711_, v_stop_2712_);
                if v___x_2713_ == 0 {
                    v___x_2714_ = 1;
                    v___x_2720_ = lean_array_uget_borrowed(v_as_2710_, v_i_2711_);
                    v___x_2721_ = l_Lean_Compiler_LCNF_ExtractClosed_isIrrelevantArg(v___x_2720_);
                    if v___x_2721_ == 0 {
                        v___y_2716_ = v_isRoot_2708_;
                        state = 1;
                        continue;
                    } else {
                        v___y_2716_ = v___x_2709_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_2722_ = 0;
                    return v___x_2722_;
                }
            }
            1 => {
                if v___y_2716_ == 0 {
                    v___x_2717_ = 1usize;
                    v___x_2718_ = lean_usize_add(v_i_2711_, v___x_2717_);
                    v_i_2711_ = v___x_2718_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2714_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2___boxed(
    mut v_isRoot_2723_: *mut LeanObject,
    mut v___x_2724_: *mut LeanObject,
    mut v_as_2725_: *mut LeanObject,
    mut v_i_2726_: *mut LeanObject,
    mut v_stop_2727_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isRoot_boxed_2728_: u8 = 0;
    let mut v___x_18364__boxed_2729_: u8 = 0;
    let mut v_i_boxed_2730_: usize = 0;
    let mut v_stop_boxed_2731_: usize = 0;
    let mut v_res_2732_: u8 = 0;
    let mut v_r_2733_: *mut LeanObject = core::ptr::null_mut();
    v_isRoot_boxed_2728_ = (lean_unbox(v_isRoot_2723_) as u8);
    v___x_18364__boxed_2729_ = (lean_unbox(v___x_2724_) as u8);
    v_i_boxed_2730_ = lean_unbox_usize(v_i_2726_);
    lean_dec(v_i_2726_);
    v_stop_boxed_2731_ = lean_unbox_usize(v_stop_2727_);
    lean_dec(v_stop_2727_);
    v_res_2732_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_boxed_2728_, v___x_18364__boxed_2729_, v_as_2725_, v_i_boxed_2730_, v_stop_boxed_2731_);
    lean_dec_ref(v_as_2725_);
    v_r_2733_ = lean_box((v_res_2732_) as usize);
    return v_r_2733_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0()
-> *mut LeanObject {
    let mut v___x_2734_: *mut LeanObject = core::ptr::null_mut();
    v___x_2734_ = lean_cstr_to_nat(b"9223372036854775808\0".as_ptr().cast());
    return v___x_2734_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(
    mut v___x_2735_: u8,
    mut v_as_2736_: *mut LeanObject,
    mut v_i_2737_: usize,
    mut v_stop_2738_: usize,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: u8 = 0;
    let mut v_a_2749_: u8 = 0;
    let mut v___x_2750_: usize = 0;
    let mut v___x_2751_: usize = 0;
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2760_: u8 = 0;
    let mut v___x_2761_: u8 = 0;
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2766_: u8 = 0;
    let mut v_a_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: u8 = 0;
    let mut v___x_2769_: u8 = 0;
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = lean_usize_dec_eq(v_i_2737_, v_stop_2738_);
                if v___x_2746_ == 0 {
                    v___x_2747_ = 1;
                    v___x_2755_ = lean_array_uget_borrowed(v_as_2736_, v_i_2737_);
                    lean_inc(v___x_2755_);
                    v___x_2756_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(
                        v___x_2755_,
                        v___y_2739_,
                        v___y_2740_,
                        v___y_2741_,
                        v___y_2742_,
                        v___y_2743_,
                        v___y_2744_,
                    );
                    if lean_obj_tag(v___x_2756_) == 0 {
                        v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
                        v_isSharedCheck_2766_ = (!lean_is_exclusive(v___x_2756_)) as u8;
                        if v_isSharedCheck_2766_ == 0 {
                            v___x_2759_ = v___x_2756_;
                            v_isShared_2760_ = v_isSharedCheck_2766_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2757_);
                            lean_dec(v___x_2756_);
                            v___x_2759_ = lean_box(0);
                            v_isShared_2760_ = v_isSharedCheck_2766_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_2756_) == 0 {
                            v_a_2767_ = lean_ctor_get(v___x_2756_, 0);
                            lean_inc(v_a_2767_);
                            lean_dec_ref_known(v___x_2756_, 1);
                            v___x_2768_ = (lean_unbox(v_a_2767_) as u8);
                            lean_dec(v_a_2767_);
                            v_a_2749_ = v___x_2768_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_2756_;
                        }
                    }
                } else {
                    v___x_2769_ = 0;
                    v___x_2770_ = lean_box((v___x_2769_) as usize);
                    v___x_2771_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2771_, 0, v___x_2770_);
                    return v___x_2771_;
                }
            }
            1 => {
                if v_a_2749_ == 0 {
                    v___x_2750_ = 1usize;
                    v___x_2751_ = lean_usize_add(v_i_2737_, v___x_2750_);
                    v_i_2737_ = v___x_2751_;
                    state = 0;
                    continue;
                } else {
                    v___x_2753_ = lean_box((v___x_2747_) as usize);
                    v___x_2754_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2754_, 0, v___x_2753_);
                    return v___x_2754_;
                }
            }
            2 => {
                v___x_2761_ = (lean_unbox(v_a_2757_) as u8);
                lean_dec(v_a_2757_);
                if v___x_2761_ == 0 {
                    v___x_2762_ = lean_box((v___x_2747_) as usize);
                    if v_isShared_2760_ == 0 {
                        lean_ctor_set(v___x_2759_, 0, v___x_2762_);
                        v___x_2764_ = v___x_2759_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2765_, 0, v___x_2762_);
                        v___x_2764_ = v_reuseFailAlloc_2765_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2759_);
                    v_a_2749_ = v___x_2735_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_2764_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(
    mut v_as_2772_: *mut LeanObject,
    mut v_i_2773_: usize,
    mut v_stop_2774_: usize,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
    mut v___y_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2782_: u8 = 0;
    let mut v___x_2783_: u8 = 0;
    let mut v_a_2785_: u8 = 0;
    let mut v___x_2786_: usize = 0;
    let mut v___x_2787_: usize = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2796_: u8 = 0;
    let mut v___x_2797_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2802_: u8 = 0;
    let mut v_a_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: u8 = 0;
    let mut v___x_2805_: u8 = 0;
    let mut v___x_2806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2782_ = lean_usize_dec_eq(v_i_2773_, v_stop_2774_);
                if v___x_2782_ == 0 {
                    v___x_2783_ = 1;
                    v___x_2791_ = lean_array_uget_borrowed(v_as_2772_, v_i_2773_);
                    lean_inc(v___x_2791_);
                    v___x_2792_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(
                        v___x_2791_,
                        v___y_2775_,
                        v___y_2776_,
                        v___y_2777_,
                        v___y_2778_,
                        v___y_2779_,
                        v___y_2780_,
                    );
                    if lean_obj_tag(v___x_2792_) == 0 {
                        v_a_2793_ = lean_ctor_get(v___x_2792_, 0);
                        v_isSharedCheck_2802_ = (!lean_is_exclusive(v___x_2792_)) as u8;
                        if v_isSharedCheck_2802_ == 0 {
                            v___x_2795_ = v___x_2792_;
                            v_isShared_2796_ = v_isSharedCheck_2802_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2793_);
                            lean_dec(v___x_2792_);
                            v___x_2795_ = lean_box(0);
                            v_isShared_2796_ = v_isSharedCheck_2802_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if lean_obj_tag(v___x_2792_) == 0 {
                            v_a_2803_ = lean_ctor_get(v___x_2792_, 0);
                            lean_inc(v_a_2803_);
                            lean_dec_ref_known(v___x_2792_, 1);
                            v___x_2804_ = (lean_unbox(v_a_2803_) as u8);
                            lean_dec(v_a_2803_);
                            v_a_2785_ = v___x_2804_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_2792_;
                        }
                    }
                } else {
                    v___x_2805_ = 0;
                    v___x_2806_ = lean_box((v___x_2805_) as usize);
                    v___x_2807_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2807_, 0, v___x_2806_);
                    return v___x_2807_;
                }
            }
            1 => {
                if v_a_2785_ == 0 {
                    v___x_2786_ = 1usize;
                    v___x_2787_ = lean_usize_add(v_i_2773_, v___x_2786_);
                    v_i_2773_ = v___x_2787_;
                    state = 0;
                    continue;
                } else {
                    v___x_2789_ = lean_box((v___x_2783_) as usize);
                    v___x_2790_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2790_, 0, v___x_2789_);
                    return v___x_2790_;
                }
            }
            2 => {
                v___x_2797_ = (lean_unbox(v_a_2793_) as u8);
                lean_dec(v_a_2793_);
                if v___x_2797_ == 0 {
                    v___x_2798_ = lean_box((v___x_2783_) as usize);
                    if v_isShared_2796_ == 0 {
                        lean_ctor_set(v___x_2795_, 0, v___x_2798_);
                        v___x_2800_ = v___x_2795_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2798_);
                        v___x_2800_ = v_reuseFailAlloc_2801_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2795_);
                    v_a_2785_ = v___x_2782_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                return v___x_2800_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(
    mut v_isRoot_2808_: u8,
    mut v_v_2809_: *mut LeanObject,
    mut v_a_2810_: *mut LeanObject,
    mut v_a_2811_: *mut LeanObject,
    mut v_a_2812_: *mut LeanObject,
    mut v_a_2813_: *mut LeanObject,
    mut v_a_2814_: *mut LeanObject,
    mut v_a_2815_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2818_: u8 = 0;
    let mut v_____do__lift_2819_: u8 = 0;
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2822_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2828_: u8 = 0;
    let mut v___x_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2831_: u8 = 0;
    let mut v___x_2832_: u8 = 0;
    let mut v___x_2833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2837_: u8 = 0;
    let mut v_unused_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2841_: u8 = 0;
    let mut v___x_2842_: u8 = 0;
    let mut v___x_2843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2847_: u8 = 0;
    let mut v_unused_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2852_: u8 = 0;
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    let mut v___x_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2859_: u8 = 0;
    let mut v___x_2860_: u8 = 0;
    let mut v___x_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: u8 = 0;
    let mut v___x_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2870_: u8 = 0;
    let mut v___x_2871_: u8 = 0;
    let mut v___x_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: u8 = 0;
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2876_: *mut LeanObject = core::ptr::null_mut();
    let mut v_struct_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_2879_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sccDecls_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2884_: u8 = 0;
    let mut v___y_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: u8 = 0;
    let mut v___x_2893_: usize = 0;
    let mut v___x_2894_: usize = 0;
    let mut v___x_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: u8 = 0;
    let mut v___y_2899_: u8 = 0;
    let mut v___y_2900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2910_: u8 = 0;
    let mut v_val_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2913_: u8 = 0;
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2918_: u8 = 0;
    let mut v_a_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2922_: u8 = 0;
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2926_: u8 = 0;
    let mut v___y_2928_: u8 = 0;
    let mut v___x_2929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2932_: u8 = 0;
    let mut v___y_2933_: u8 = 0;
    let mut v___x_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2937_: u8 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: u8 = 0;
    let mut v___x_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: u8 = 0;
    let mut v___x_2951_: usize = 0;
    let mut v___x_2952_: usize = 0;
    let mut v___x_2953_: u8 = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2958_: usize = 0;
    let mut v___x_2959_: usize = 0;
    let mut v___x_2960_: u8 = 0;
    let mut v___x_2961_: u8 = 0;
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2964_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2970_: u8 = 0;
    let mut v___x_2972_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2973_: u8 = 0;
    let mut v___x_2975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2977_: u8 = 0;
    let mut v_unused_2978_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2980_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2981_: u8 = 0;
    let mut v___x_2982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2984_: usize = 0;
    let mut v___x_2985_: usize = 0;
    let mut v___x_2986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2987_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2988_: u8 = 0;
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                match lean_obj_tag(v_v_2809_) {
                    0 => {
                        v_value_2825_ = lean_ctor_get(v_v_2809_, 0);
                        v_isSharedCheck_2870_ = (!lean_is_exclusive(v_v_2809_)) as u8;
                        if v_isSharedCheck_2870_ == 0 {
                            v___x_2827_ = v_v_2809_;
                            v_isShared_2828_ = v_isSharedCheck_2870_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_value_2825_);
                            lean_dec(v_v_2809_);
                            v___x_2827_ = lean_box(0);
                            v_isShared_2828_ = v_isSharedCheck_2870_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        if v_isRoot_2808_ == 0 {
                            v___x_2871_ = 1;
                            v___x_2872_ = lean_box((v___x_2871_) as usize);
                            v___x_2873_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2873_, 0, v___x_2872_);
                            return v___x_2873_;
                        } else {
                            v___x_2874_ = 0;
                            v___x_2875_ = lean_box((v___x_2874_) as usize);
                            v___x_2876_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v___x_2876_, 0, v___x_2875_);
                            return v___x_2876_;
                        }
                    }
                    2 => {
                        v_struct_2877_ = lean_ctor_get(v_v_2809_, 2);
                        lean_inc(v_struct_2877_);
                        lean_dec_ref_known(v_v_2809_, 3);
                        v___x_2878_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(
                            v_struct_2877_,
                            v_a_2810_,
                            v_a_2811_,
                            v_a_2812_,
                            v_a_2813_,
                            v_a_2814_,
                            v_a_2815_,
                        );
                        return v___x_2878_;
                    }
                    3 => {
                        v_declName_2879_ = lean_ctor_get(v_v_2809_, 0);
                        lean_inc(v_declName_2879_);
                        v_args_2880_ = lean_ctor_get(v_v_2809_, 2);
                        lean_inc_ref(v_args_2880_);
                        lean_dec_ref_known(v_v_2809_, 3);
                        v_sccDecls_2881_ = lean_ctor_get(v_a_2810_, 1);
                        v___x_2882_ = lean_unsigned_to_nat(0);
                        v___x_2956_ = lean_array_get_size(v_sccDecls_2881_);
                        v___x_2957_ = lean_nat_dec_lt(v___x_2882_, v___x_2956_);
                        if v___x_2957_ == 0 {
                            v___y_2937_ = v___x_2957_;
                            state = 19;
                            continue;
                        } else {
                            if v___x_2957_ == 0 {
                                v___y_2937_ = v___x_2957_;
                                state = 19;
                                continue;
                            } else {
                                v___x_2958_ = 0usize;
                                v___x_2959_ = lean_usize_of_nat(v___x_2956_);
                                v___x_2960_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__3(v_declName_2879_, v_sccDecls_2881_, v___x_2958_, v___x_2959_);
                                if v___x_2960_ == 0 {
                                    v___y_2937_ = v___x_2960_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_dec_ref(v_args_2880_);
                                    lean_dec(v_declName_2879_);
                                    v___x_2961_ = 0;
                                    v___x_2962_ = lean_box((v___x_2961_) as usize);
                                    v___x_2963_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_2963_, 0, v___x_2962_);
                                    return v___x_2963_;
                                }
                            }
                        }
                    }
                    _ => {
                        v_fvarId_2964_ = lean_ctor_get(v_v_2809_, 0);
                        lean_inc(v_fvarId_2964_);
                        v_args_2965_ = lean_ctor_get(v_v_2809_, 1);
                        lean_inc_ref(v_args_2965_);
                        lean_dec_ref_known(v_v_2809_, 2);
                        v___x_2966_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(
                            v_fvarId_2964_,
                            v_a_2810_,
                            v_a_2811_,
                            v_a_2812_,
                            v_a_2813_,
                            v_a_2814_,
                            v_a_2815_,
                        );
                        if lean_obj_tag(v___x_2966_) == 0 {
                            v_a_2967_ = lean_ctor_get(v___x_2966_, 0);
                            lean_inc(v_a_2967_);
                            lean_dec_ref_known(v___x_2966_, 1);
                            v___x_2979_ = lean_unsigned_to_nat(0);
                            v___x_2980_ = lean_array_get_size(v_args_2965_);
                            v___x_2981_ = lean_nat_dec_lt(v___x_2979_, v___x_2980_);
                            if v___x_2981_ == 0 {
                                lean_dec_ref(v_args_2965_);
                                v___x_2982_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_2981_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
                                v___y_2969_ = v___x_2982_;
                                state = 20;
                                continue;
                            } else {
                                if v___x_2981_ == 0 {
                                    lean_dec_ref(v_args_2965_);
                                    v___x_2983_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_2981_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
                                    v___y_2969_ = v___x_2983_;
                                    state = 20;
                                    continue;
                                } else {
                                    v___x_2984_ = 0usize;
                                    v___x_2985_ = lean_usize_of_nat(v___x_2980_);
                                    v___x_2986_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_args_2965_, v___x_2984_, v___x_2985_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
                                    lean_dec_ref(v_args_2965_);
                                    if lean_obj_tag(v___x_2986_) == 0 {
                                        v_a_2987_ = lean_ctor_get(v___x_2986_, 0);
                                        lean_inc(v_a_2987_);
                                        lean_dec_ref_known(v___x_2986_, 1);
                                        v___x_2988_ = (lean_unbox(v_a_2987_) as u8);
                                        lean_dec(v_a_2987_);
                                        v___x_2989_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___lam__0(v___x_2988_, v_a_2810_, v_a_2811_, v_a_2812_, v_a_2813_, v_a_2814_, v_a_2815_);
                                        v___y_2969_ = v___x_2989_;
                                        state = 20;
                                        continue;
                                    } else {
                                        v___y_2969_ = v___x_2986_;
                                        state = 20;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v_args_2965_);
                            return v___x_2966_;
                        }
                    }
                }
            }
            1 => {
                if v_____do__lift_2819_ == 0 {
                    v___x_2820_ = 1;
                    v___x_2821_ = lean_box((v___x_2820_) as usize);
                    v___x_2822_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2822_, 0, v___x_2821_);
                    return v___x_2822_;
                } else {
                    v___x_2823_ = lean_box((v___y_2818_) as usize);
                    v___x_2824_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2824_, 0, v___x_2823_);
                    return v___x_2824_;
                }
            }
            2 => match lean_obj_tag(v_value_2825_) {
                1 => {
                    lean_del_object(v___x_2827_);
                    v_isSharedCheck_2837_ = (!lean_is_exclusive(v_value_2825_)) as u8;
                    if v_isSharedCheck_2837_ == 0 {
                        v_unused_2838_ = lean_ctor_get(v_value_2825_, 0);
                        lean_dec(v_unused_2838_);
                        v___x_2830_ = v_value_2825_;
                        v_isShared_2831_ = v_isSharedCheck_2837_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_value_2825_);
                        v___x_2830_ = lean_box(0);
                        v_isShared_2831_ = v_isSharedCheck_2837_;
                        state = 3;
                        continue;
                    }
                }
                0 => {
                    lean_del_object(v___x_2827_);
                    if v_isRoot_2808_ == 0 {
                        v_isSharedCheck_2847_ = (!lean_is_exclusive(v_value_2825_)) as u8;
                        if v_isSharedCheck_2847_ == 0 {
                            v_unused_2848_ = lean_ctor_get(v_value_2825_, 0);
                            lean_dec(v_unused_2848_);
                            v___x_2840_ = v_value_2825_;
                            v_isShared_2841_ = v_isSharedCheck_2847_;
                            state = 5;
                            continue;
                        } else {
                            lean_dec(v_value_2825_);
                            v___x_2840_ = lean_box(0);
                            v_isShared_2841_ = v_isSharedCheck_2847_;
                            state = 5;
                            continue;
                        }
                    } else {
                        v_val_2849_ = lean_ctor_get(v_value_2825_, 0);
                        v_isSharedCheck_2859_ = (!lean_is_exclusive(v_value_2825_)) as u8;
                        if v_isSharedCheck_2859_ == 0 {
                            v___x_2851_ = v_value_2825_;
                            v_isShared_2852_ = v_isSharedCheck_2859_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_val_2849_);
                            lean_dec(v_value_2825_);
                            v___x_2851_ = lean_box(0);
                            v_isShared_2852_ = v_isSharedCheck_2859_;
                            state = 7;
                            continue;
                        }
                    }
                }
                _ => {
                    lean_dec_ref(v_value_2825_);
                    if v_isRoot_2808_ == 0 {
                        v___x_2860_ = 1;
                        v___x_2861_ = lean_box((v___x_2860_) as usize);
                        if v_isShared_2828_ == 0 {
                            lean_ctor_set(v___x_2827_, 0, v___x_2861_);
                            v___x_2863_ = v___x_2827_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_2864_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2864_, 0, v___x_2861_);
                            v___x_2863_ = v_reuseFailAlloc_2864_;
                            state = 9;
                            continue;
                        }
                    } else {
                        v___x_2865_ = 0;
                        v___x_2866_ = lean_box((v___x_2865_) as usize);
                        if v_isShared_2828_ == 0 {
                            lean_ctor_set(v___x_2827_, 0, v___x_2866_);
                            v___x_2868_ = v___x_2827_;
                            state = 10;
                            continue;
                        } else {
                            v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
                            v___x_2868_ = v_reuseFailAlloc_2869_;
                            state = 10;
                            continue;
                        }
                    }
                }
            },
            3 => {
                v___x_2832_ = 1;
                v___x_2833_ = lean_box((v___x_2832_) as usize);
                if v_isShared_2831_ == 0 {
                    lean_ctor_set_tag(v___x_2830_, 0);
                    lean_ctor_set(v___x_2830_, 0, v___x_2833_);
                    v___x_2835_ = v___x_2830_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2836_, 0, v___x_2833_);
                    v___x_2835_ = v_reuseFailAlloc_2836_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2835_;
            }
            5 => {
                v___x_2842_ = 1;
                v___x_2843_ = lean_box((v___x_2842_) as usize);
                if v_isShared_2841_ == 0 {
                    lean_ctor_set(v___x_2840_, 0, v___x_2843_);
                    v___x_2845_ = v___x_2840_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2846_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2846_, 0, v___x_2843_);
                    v___x_2845_ = v_reuseFailAlloc_2846_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2845_;
            }
            7 => {
                v___x_2853_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0_once
                    ),
                    _init_l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___closed__0,
                );
                v___x_2854_ = lean_nat_dec_le(v___x_2853_, v_val_2849_);
                lean_dec(v_val_2849_);
                v___x_2855_ = lean_box((v___x_2854_) as usize);
                if v_isShared_2852_ == 0 {
                    lean_ctor_set(v___x_2851_, 0, v___x_2855_);
                    v___x_2857_ = v___x_2851_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
                    v___x_2857_ = v_reuseFailAlloc_2858_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2857_;
            }
            9 => {
                return v___x_2863_;
            }
            10 => {
                return v___x_2868_;
            }
            11 => {
                v___x_2891_ = lean_array_get_size(v_args_2880_);
                v___x_2892_ = lean_nat_dec_lt(v___x_2882_, v___x_2891_);
                if v___x_2892_ == 0 {
                    lean_dec_ref(v_args_2880_);
                    v___y_2818_ = v___y_2884_;
                    v_____do__lift_2819_ = v___y_2884_;
                    state = 1;
                    continue;
                } else {
                    if v___x_2892_ == 0 {
                        lean_dec_ref(v_args_2880_);
                        v___y_2818_ = v___y_2884_;
                        v_____do__lift_2819_ = v___y_2884_;
                        state = 1;
                        continue;
                    } else {
                        v___x_2893_ = 0usize;
                        v___x_2894_ = lean_usize_of_nat(v___x_2891_);
                        v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___y_2884_, v_args_2880_, v___x_2893_, v___x_2894_, v___y_2885_, v___y_2886_, v___y_2887_, v___y_2888_, v___y_2889_, v___y_2890_);
                        lean_dec_ref(v_args_2880_);
                        if lean_obj_tag(v___x_2895_) == 0 {
                            v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
                            lean_inc(v_a_2896_);
                            lean_dec_ref_known(v___x_2895_, 1);
                            v___x_2897_ = (lean_unbox(v_a_2896_) as u8);
                            lean_dec(v_a_2896_);
                            v___y_2818_ = v___y_2884_;
                            v_____do__lift_2819_ = v___x_2897_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_2895_;
                        }
                    }
                }
            }
            12 => {
                v___x_2906_ =
                    l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(v_declName_2879_, v___y_2905_);
                if lean_obj_tag(v___x_2906_) == 0 {
                    v_a_2907_ = lean_ctor_get(v___x_2906_, 0);
                    v_isSharedCheck_2918_ = (!lean_is_exclusive(v___x_2906_)) as u8;
                    if v_isSharedCheck_2918_ == 0 {
                        v___x_2909_ = v___x_2906_;
                        v_isShared_2910_ = v_isSharedCheck_2918_;
                        state = 13;
                        continue;
                    } else {
                        lean_inc(v_a_2907_);
                        lean_dec(v___x_2906_);
                        v___x_2909_ = lean_box(0);
                        v_isShared_2910_ = v_isSharedCheck_2918_;
                        state = 13;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_args_2880_);
                    v_a_2919_ = lean_ctor_get(v___x_2906_, 0);
                    v_isSharedCheck_2926_ = (!lean_is_exclusive(v___x_2906_)) as u8;
                    if v_isSharedCheck_2926_ == 0 {
                        v___x_2921_ = v___x_2906_;
                        v_isShared_2922_ = v_isSharedCheck_2926_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_2919_);
                        lean_dec(v___x_2906_);
                        v___x_2921_ = lean_box(0);
                        v_isShared_2922_ = v_isSharedCheck_2926_;
                        state = 15;
                        continue;
                    }
                }
            }
            13 => {
                if lean_obj_tag(v_a_2907_) == 1 {
                    v_val_2911_ = lean_ctor_get(v_a_2907_, 0);
                    lean_inc(v_val_2911_);
                    lean_dec_ref_known(v_a_2907_, 1);
                    v___x_2912_ = l_Lean_Compiler_LCNF_Decl_getArity___redArg(v_val_2911_);
                    lean_dec(v_val_2911_);
                    v___x_2913_ = lean_nat_dec_eq(v___x_2912_, v___x_2882_);
                    lean_dec(v___x_2912_);
                    if v___x_2913_ == 0 {
                        lean_del_object(v___x_2909_);
                        v___y_2884_ = v___y_2899_;
                        v___y_2885_ = v___y_2900_;
                        v___y_2886_ = v___y_2901_;
                        v___y_2887_ = v___y_2902_;
                        v___y_2888_ = v___y_2903_;
                        v___y_2889_ = v___y_2904_;
                        v___y_2890_ = v___y_2905_;
                        state = 11;
                        continue;
                    } else {
                        lean_dec_ref(v_args_2880_);
                        v___x_2914_ = lean_box((v___y_2899_) as usize);
                        if v_isShared_2910_ == 0 {
                            lean_ctor_set(v___x_2909_, 0, v___x_2914_);
                            v___x_2916_ = v___x_2909_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2917_, 0, v___x_2914_);
                            v___x_2916_ = v_reuseFailAlloc_2917_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_2909_);
                    lean_dec(v_a_2907_);
                    v___y_2884_ = v___y_2899_;
                    v___y_2885_ = v___y_2900_;
                    v___y_2886_ = v___y_2901_;
                    v___y_2887_ = v___y_2902_;
                    v___y_2888_ = v___y_2903_;
                    v___y_2889_ = v___y_2904_;
                    v___y_2890_ = v___y_2905_;
                    state = 11;
                    continue;
                }
            }
            14 => {
                return v___x_2916_;
            }
            15 => {
                if v_isShared_2922_ == 0 {
                    v___x_2924_ = v___x_2921_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_2925_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2925_, 0, v_a_2919_);
                    v___x_2924_ = v_reuseFailAlloc_2925_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_2924_;
            }
            17 => {
                if v___y_2928_ == 0 {
                    v___y_2899_ = v___y_2928_;
                    v___y_2900_ = v_a_2810_;
                    v___y_2901_ = v_a_2811_;
                    v___y_2902_ = v_a_2812_;
                    v___y_2903_ = v_a_2813_;
                    v___y_2904_ = v_a_2814_;
                    v___y_2905_ = v_a_2815_;
                    state = 12;
                    continue;
                } else {
                    lean_dec_ref(v_args_2880_);
                    lean_dec(v_declName_2879_);
                    v___x_2929_ = lean_box((v___y_2928_) as usize);
                    v___x_2930_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2930_, 0, v___x_2929_);
                    return v___x_2930_;
                }
            }
            18 => {
                if v___y_2933_ == 0 {
                    lean_dec_ref(v_args_2880_);
                    lean_dec(v_declName_2879_);
                    v___x_2934_ = lean_box((v___y_2932_) as usize);
                    v___x_2935_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2935_, 0, v___x_2934_);
                    return v___x_2935_;
                } else {
                    v___y_2928_ = v___y_2932_;
                    state = 17;
                    continue;
                }
            }
            19 => {
                v___x_2938_ = lean_st_ref_get(v_a_2815_);
                v_env_2939_ = lean_ctor_get(v___x_2938_, 0);
                lean_inc_ref(v_env_2939_);
                lean_dec(v___x_2938_);
                lean_inc(v_declName_2879_);
                v___x_2940_ = l_Lean_hasNeverExtractAttribute(v_env_2939_, v_declName_2879_);
                if v___x_2940_ == 0 {
                    if v_isRoot_2808_ == 0 {
                        lean_dec(v_declName_2879_);
                        v___y_2884_ = v___x_2940_;
                        v___y_2885_ = v_a_2810_;
                        v___y_2886_ = v_a_2811_;
                        v___y_2887_ = v_a_2812_;
                        v___y_2888_ = v_a_2813_;
                        v___y_2889_ = v_a_2814_;
                        v___y_2890_ = v_a_2815_;
                        state = 11;
                        continue;
                    } else {
                        v___x_2941_ = lean_st_ref_get(v_a_2815_);
                        v_env_2942_ = lean_ctor_get(v___x_2941_, 0);
                        lean_inc_ref(v_env_2942_);
                        lean_dec(v___x_2941_);
                        lean_inc(v_declName_2879_);
                        v___x_2943_ =
                            l_Lean_Environment_find_x3f(v_env_2942_, v_declName_2879_, v___x_2940_);
                        if lean_obj_tag(v___x_2943_) == 1 {
                            v_val_2944_ = lean_ctor_get(v___x_2943_, 0);
                            lean_inc(v_val_2944_);
                            lean_dec_ref_known(v___x_2943_, 1);
                            match lean_obj_tag(v_val_2944_) {
                                1 => {
                                    v_val_2945_ = lean_ctor_get(v_val_2944_, 0);
                                    lean_inc_ref(v_val_2945_);
                                    lean_dec_ref_known(v_val_2944_, 1);
                                    v_toConstantVal_2946_ = lean_ctor_get(v_val_2945_, 0);
                                    lean_inc_ref(v_toConstantVal_2946_);
                                    lean_dec_ref(v_val_2945_);
                                    v_type_2947_ = lean_ctor_get(v_toConstantVal_2946_, 2);
                                    lean_inc_ref(v_type_2947_);
                                    lean_dec_ref(v_toConstantVal_2946_);
                                    v___x_2948_ = l_Lean_Expr_isForall(v_type_2947_);
                                    lean_dec_ref(v_type_2947_);
                                    v___y_2932_ = v___x_2940_;
                                    v___y_2933_ = v___x_2948_;
                                    state = 18;
                                    continue;
                                }
                                6 => {
                                    lean_dec_ref_known(v_val_2944_, 1);
                                    v___x_2949_ = lean_array_get_size(v_args_2880_);
                                    v___x_2950_ = lean_nat_dec_lt(v___x_2882_, v___x_2949_);
                                    if v___x_2950_ == 0 {
                                        v___y_2932_ = v___x_2940_;
                                        v___y_2933_ = v___x_2940_;
                                        state = 18;
                                        continue;
                                    } else {
                                        if v___x_2950_ == 0 {
                                            v___y_2932_ = v___x_2940_;
                                            v___y_2933_ = v___x_2940_;
                                            state = 18;
                                            continue;
                                        } else {
                                            v___x_2951_ = 0usize;
                                            v___x_2952_ = lean_usize_of_nat(v___x_2949_);
                                            v___x_2953_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__2(v_isRoot_2808_, v___x_2940_, v_args_2880_, v___x_2951_, v___x_2952_);
                                            if v___x_2953_ == 0 {
                                                v___y_2932_ = v___x_2940_;
                                                v___y_2933_ = v___x_2940_;
                                                state = 18;
                                                continue;
                                            } else {
                                                v___y_2932_ = v___x_2940_;
                                                v___y_2933_ = v___x_2953_;
                                                state = 18;
                                                continue;
                                            }
                                        }
                                    }
                                }
                                _ => {
                                    lean_dec(v_val_2944_);
                                    v___y_2928_ = v___x_2940_;
                                    state = 17;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v___x_2943_);
                            v___y_2899_ = v___x_2940_;
                            v___y_2900_ = v_a_2810_;
                            v___y_2901_ = v_a_2811_;
                            v___y_2902_ = v_a_2812_;
                            v___y_2903_ = v_a_2813_;
                            v___y_2904_ = v_a_2814_;
                            v___y_2905_ = v_a_2815_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_args_2880_);
                    lean_dec(v_declName_2879_);
                    v___x_2954_ = lean_box((v___y_2937_) as usize);
                    v___x_2955_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2955_, 0, v___x_2954_);
                    return v___x_2955_;
                }
            }
            20 => {
                if lean_obj_tag(v___y_2969_) == 0 {
                    v___x_2970_ = (lean_unbox(v_a_2967_) as u8);
                    if v___x_2970_ == 0 {
                        v_isSharedCheck_2977_ = (!lean_is_exclusive(v___y_2969_)) as u8;
                        if v_isSharedCheck_2977_ == 0 {
                            v_unused_2978_ = lean_ctor_get(v___y_2969_, 0);
                            lean_dec(v_unused_2978_);
                            v___x_2972_ = v___y_2969_;
                            v_isShared_2973_ = v_isSharedCheck_2977_;
                            state = 21;
                            continue;
                        } else {
                            lean_dec(v___y_2969_);
                            v___x_2972_ = lean_box(0);
                            v_isShared_2973_ = v_isSharedCheck_2977_;
                            state = 21;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2967_);
                        return v___y_2969_;
                    }
                } else {
                    lean_dec(v_a_2967_);
                    return v___y_2969_;
                }
            }
            21 => {
                if v_isShared_2973_ == 0 {
                    lean_ctor_set(v___x_2972_, 0, v_a_2967_);
                    v___x_2975_ = v___x_2972_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_2976_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2967_);
                    v___x_2975_ = v_reuseFailAlloc_2976_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_2975_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(
    mut v_fvarId_2990_: *mut LeanObject,
    mut v_a_2991_: *mut LeanObject,
    mut v_a_2992_: *mut LeanObject,
    mut v_a_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_a_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2998_: u8 = 0;
    let mut v___x_2999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3003_: u8 = 0;
    let mut v_val_3004_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3005_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3006_: u8 = 0;
    let mut v___x_3007_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: u8 = 0;
    let mut v___x_3009_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3013_: u8 = 0;
    let mut v_a_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3016_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3017_: u8 = 0;
    let mut v___x_3019_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3021_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2998_ = 0;
                v___x_2999_ = l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                    v___x_2998_,
                    v_fvarId_2990_,
                    v_a_2994_,
                );
                if lean_obj_tag(v___x_2999_) == 0 {
                    v_a_3000_ = lean_ctor_get(v___x_2999_, 0);
                    v_isSharedCheck_3013_ = (!lean_is_exclusive(v___x_2999_)) as u8;
                    if v_isSharedCheck_3013_ == 0 {
                        v___x_3002_ = v___x_2999_;
                        v_isShared_3003_ = v_isSharedCheck_3013_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3000_);
                        lean_dec(v___x_2999_);
                        v___x_3002_ = lean_box(0);
                        v_isShared_3003_ = v_isSharedCheck_3013_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3014_ = lean_ctor_get(v___x_2999_, 0);
                    v_isSharedCheck_3021_ = (!lean_is_exclusive(v___x_2999_)) as u8;
                    if v_isSharedCheck_3021_ == 0 {
                        v___x_3016_ = v___x_2999_;
                        v_isShared_3017_ = v_isSharedCheck_3021_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3014_);
                        lean_dec(v___x_2999_);
                        v___x_3016_ = lean_box(0);
                        v_isShared_3017_ = v_isSharedCheck_3021_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3000_) == 1 {
                    lean_del_object(v___x_3002_);
                    v_val_3004_ = lean_ctor_get(v_a_3000_, 0);
                    lean_inc(v_val_3004_);
                    lean_dec_ref_known(v_a_3000_, 1);
                    v_value_3005_ = lean_ctor_get(v_val_3004_, 3);
                    lean_inc(v_value_3005_);
                    lean_dec(v_val_3004_);
                    v___x_3006_ = 0;
                    v___x_3007_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(
                        v___x_3006_,
                        v_value_3005_,
                        v_a_2991_,
                        v_a_2992_,
                        v_a_2993_,
                        v_a_2994_,
                        v_a_2995_,
                        v_a_2996_,
                    );
                    return v___x_3007_;
                } else {
                    lean_dec(v_a_3000_);
                    v___x_3008_ = 0;
                    v___x_3009_ = lean_box((v___x_3008_) as usize);
                    if v_isShared_3003_ == 0 {
                        lean_ctor_set(v___x_3002_, 0, v___x_3009_);
                        v___x_3011_ = v___x_3002_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3012_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3012_, 0, v___x_3009_);
                        v___x_3011_ = v_reuseFailAlloc_3012_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3011_;
            }
            3 => {
                if v_isShared_3017_ == 0 {
                    v___x_3019_ = v___x_3016_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3020_, 0, v_a_3014_);
                    v___x_3019_ = v_reuseFailAlloc_3020_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3019_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(
    mut v_fvarId_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
    mut v_a_3026_: *mut LeanObject,
    mut v_a_3027_: *mut LeanObject,
    mut v_a_3028_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarDecisionCache_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3036_: u8 = 0;
    let mut v___x_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3040_: u8 = 0;
    let mut v___x_3041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3042_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3045_: u8 = 0;
    let mut v___x_3046_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3047_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarDecisionCache_3048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3051_: u8 = 0;
    let mut v___x_3052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3060_: u8 = 0;
    let mut v_isSharedCheck_3061_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3030_ = lean_st_ref_get(v_a_3024_);
                v_fvarDecisionCache_3031_ = lean_ctor_get(v___x_3030_, 1);
                lean_inc_ref(v_fvarDecisionCache_3031_);
                lean_dec(v___x_3030_);
                v___x_3032_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_fvarDecisionCache_3031_, v_fvarId_3022_);
                lean_dec_ref(v_fvarDecisionCache_3031_);
                if lean_obj_tag(v___x_3032_) == 1 {
                    lean_dec(v_fvarId_3022_);
                    v_val_3033_ = lean_ctor_get(v___x_3032_, 0);
                    v_isSharedCheck_3040_ = (!lean_is_exclusive(v___x_3032_)) as u8;
                    if v_isSharedCheck_3040_ == 0 {
                        v___x_3035_ = v___x_3032_;
                        v_isShared_3036_ = v_isSharedCheck_3040_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3033_);
                        lean_dec(v___x_3032_);
                        v___x_3035_ = lean_box(0);
                        v_isShared_3036_ = v_isSharedCheck_3040_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3032_);
                    v___x_3041_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_3022_, v_a_3023_, v_a_3024_, v_a_3025_, v_a_3026_, v_a_3027_, v_a_3028_);
                    if lean_obj_tag(v___x_3041_) == 0 {
                        v_a_3042_ = lean_ctor_get(v___x_3041_, 0);
                        v_isSharedCheck_3061_ = (!lean_is_exclusive(v___x_3041_)) as u8;
                        if v_isSharedCheck_3061_ == 0 {
                            v___x_3044_ = v___x_3041_;
                            v_isShared_3045_ = v_isSharedCheck_3061_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3042_);
                            lean_dec(v___x_3041_);
                            v___x_3044_ = lean_box(0);
                            v_isShared_3045_ = v_isSharedCheck_3061_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_fvarId_3022_);
                        return v___x_3041_;
                    }
                }
            }
            1 => {
                if v_isShared_3036_ == 0 {
                    lean_ctor_set_tag(v___x_3035_, 0);
                    v___x_3038_ = v___x_3035_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3039_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3039_, 0, v_val_3033_);
                    v___x_3038_ = v_reuseFailAlloc_3039_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3038_;
            }
            3 => {
                v___x_3046_ = lean_st_ref_take(v_a_3024_);
                v_decls_3047_ = lean_ctor_get(v___x_3046_, 0);
                v_fvarDecisionCache_3048_ = lean_ctor_get(v___x_3046_, 1);
                v_isSharedCheck_3060_ = (!lean_is_exclusive(v___x_3046_)) as u8;
                if v_isSharedCheck_3060_ == 0 {
                    v___x_3050_ = v___x_3046_;
                    v_isShared_3051_ = v_isSharedCheck_3060_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_fvarDecisionCache_3048_);
                    lean_inc(v_decls_3047_);
                    lean_dec(v___x_3046_);
                    v___x_3050_ = lean_box(0);
                    v_isShared_3051_ = v_isSharedCheck_3060_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                lean_inc(v_a_3042_);
                v___x_3052_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_fvarDecisionCache_3048_, v_fvarId_3022_, v_a_3042_);
                if v_isShared_3051_ == 0 {
                    lean_ctor_set(v___x_3050_, 1, v___x_3052_);
                    v___x_3054_ = v___x_3050_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_decls_3047_);
                    lean_ctor_set(v_reuseFailAlloc_3059_, 1, v___x_3052_);
                    v___x_3054_ = v_reuseFailAlloc_3059_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3055_ = lean_st_ref_set(v_a_3024_, v___x_3054_);
                if v_isShared_3045_ == 0 {
                    v___x_3057_ = v___x_3044_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3058_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3058_, 0, v_a_3042_);
                    v___x_3057_ = v_reuseFailAlloc_3058_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3057_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(
    mut v_arg_3062_: *mut LeanObject,
    mut v_a_3063_: *mut LeanObject,
    mut v_a_3064_: *mut LeanObject,
    mut v_a_3065_: *mut LeanObject,
    mut v_a_3066_: *mut LeanObject,
    mut v_a_3067_: *mut LeanObject,
    mut v_a_3068_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_arg_3062_) == 1 {
        let mut v_fvarId_3070_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
        v_fvarId_3070_ = lean_ctor_get(v_arg_3062_, 0);
        lean_inc(v_fvarId_3070_);
        lean_dec_ref_known(v_arg_3062_, 1);
        v___x_3071_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(
            v_fvarId_3070_,
            v_a_3063_,
            v_a_3064_,
            v_a_3065_,
            v_a_3066_,
            v_a_3067_,
            v_a_3068_,
        );
        return v___x_3071_;
    } else {
        let mut v___x_3072_: u8 = 0;
        let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
        lean_dec(v_arg_3062_);
        v___x_3072_ = 1;
        v___x_3073_ = lean_box((v___x_3072_) as usize);
        v___x_3074_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3074_, 0, v___x_3073_);
        return v___x_3074_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg___boxed(
    mut v_arg_3075_: *mut LeanObject,
    mut v_a_3076_: *mut LeanObject,
    mut v_a_3077_: *mut LeanObject,
    mut v_a_3078_: *mut LeanObject,
    mut v_a_3079_: *mut LeanObject,
    mut v_a_3080_: *mut LeanObject,
    mut v_a_3081_: *mut LeanObject,
    mut v_a_3082_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3083_: *mut LeanObject = core::ptr::null_mut();
    v_res_3083_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(
        v_arg_3075_,
        v_a_3076_,
        v_a_3077_,
        v_a_3078_,
        v_a_3079_,
        v_a_3080_,
        v_a_3081_,
    );
    lean_dec(v_a_3081_);
    lean_dec_ref(v_a_3080_);
    lean_dec(v_a_3079_);
    lean_dec_ref(v_a_3078_);
    lean_dec(v_a_3077_);
    lean_dec_ref(v_a_3076_);
    return v_res_3083_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go___boxed(
    mut v_fvarId_3084_: *mut LeanObject,
    mut v_a_3085_: *mut LeanObject,
    mut v_a_3086_: *mut LeanObject,
    mut v_a_3087_: *mut LeanObject,
    mut v_a_3088_: *mut LeanObject,
    mut v_a_3089_: *mut LeanObject,
    mut v_a_3090_: *mut LeanObject,
    mut v_a_3091_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3092_: *mut LeanObject = core::ptr::null_mut();
    v_res_3092_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_go(v_fvarId_3084_, v_a_3085_, v_a_3086_, v_a_3087_, v_a_3088_, v_a_3089_, v_a_3090_);
    lean_dec(v_a_3090_);
    lean_dec_ref(v_a_3089_);
    lean_dec(v_a_3088_);
    lean_dec_ref(v_a_3087_);
    lean_dec(v_a_3086_);
    lean_dec_ref(v_a_3085_);
    lean_dec(v_fvarId_3084_);
    return v_res_3092_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar___boxed(
    mut v_fvarId_3093_: *mut LeanObject,
    mut v_a_3094_: *mut LeanObject,
    mut v_a_3095_: *mut LeanObject,
    mut v_a_3096_: *mut LeanObject,
    mut v_a_3097_: *mut LeanObject,
    mut v_a_3098_: *mut LeanObject,
    mut v_a_3099_: *mut LeanObject,
    mut v_a_3100_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3101_: *mut LeanObject = core::ptr::null_mut();
    v_res_3101_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar(
        v_fvarId_3093_,
        v_a_3094_,
        v_a_3095_,
        v_a_3096_,
        v_a_3097_,
        v_a_3098_,
        v_a_3099_,
    );
    lean_dec(v_a_3099_);
    lean_dec_ref(v_a_3098_);
    lean_dec(v_a_3097_);
    lean_dec_ref(v_a_3096_);
    lean_dec(v_a_3095_);
    lean_dec_ref(v_a_3094_);
    return v_res_3101_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1___boxed(
    mut v___x_3102_: *mut LeanObject,
    mut v_as_3103_: *mut LeanObject,
    mut v_i_3104_: *mut LeanObject,
    mut v_stop_3105_: *mut LeanObject,
    mut v___y_3106_: *mut LeanObject,
    mut v___y_3107_: *mut LeanObject,
    mut v___y_3108_: *mut LeanObject,
    mut v___y_3109_: *mut LeanObject,
    mut v___y_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_18417__boxed_3113_: u8 = 0;
    let mut v_i_boxed_3114_: usize = 0;
    let mut v_stop_boxed_3115_: usize = 0;
    let mut v_res_3116_: *mut LeanObject = core::ptr::null_mut();
    v___x_18417__boxed_3113_ = (lean_unbox(v___x_3102_) as u8);
    v_i_boxed_3114_ = lean_unbox_usize(v_i_3104_);
    lean_dec(v_i_3104_);
    v_stop_boxed_3115_ = lean_unbox_usize(v_stop_3105_);
    lean_dec(v_stop_3105_);
    v_res_3116_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__1(v___x_18417__boxed_3113_, v_as_3103_, v_i_boxed_3114_, v_stop_boxed_3115_, v___y_3106_, v___y_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
    lean_dec(v___y_3111_);
    lean_dec_ref(v___y_3110_);
    lean_dec(v___y_3109_);
    lean_dec_ref(v___y_3108_);
    lean_dec(v___y_3107_);
    lean_dec_ref(v___y_3106_);
    lean_dec_ref(v_as_3103_);
    return v_res_3116_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4___boxed(
    mut v_as_3117_: *mut LeanObject,
    mut v_i_3118_: *mut LeanObject,
    mut v_stop_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
    mut v___y_3122_: *mut LeanObject,
    mut v___y_3123_: *mut LeanObject,
    mut v___y_3124_: *mut LeanObject,
    mut v___y_3125_: *mut LeanObject,
    mut v___y_3126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_3127_: usize = 0;
    let mut v_stop_boxed_3128_: usize = 0;
    let mut v_res_3129_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_3127_ = lean_unbox_usize(v_i_3118_);
    lean_dec(v_i_3118_);
    v_stop_boxed_3128_ = lean_unbox_usize(v_stop_3119_);
    lean_dec(v_stop_3119_);
    v_res_3129_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue_spec__4(v_as_3117_, v_i_boxed_3127_, v_stop_boxed_3128_, v___y_3120_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_, v___y_3125_);
    lean_dec(v___y_3125_);
    lean_dec_ref(v___y_3124_);
    lean_dec(v___y_3123_);
    lean_dec_ref(v___y_3122_);
    lean_dec(v___y_3121_);
    lean_dec_ref(v___y_3120_);
    lean_dec_ref(v_as_3117_);
    return v_res_3129_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue___boxed(
    mut v_isRoot_3130_: *mut LeanObject,
    mut v_v_3131_: *mut LeanObject,
    mut v_a_3132_: *mut LeanObject,
    mut v_a_3133_: *mut LeanObject,
    mut v_a_3134_: *mut LeanObject,
    mut v_a_3135_: *mut LeanObject,
    mut v_a_3136_: *mut LeanObject,
    mut v_a_3137_: *mut LeanObject,
    mut v_a_3138_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isRoot_boxed_3139_: u8 = 0;
    let mut v_res_3140_: *mut LeanObject = core::ptr::null_mut();
    v_isRoot_boxed_3139_ = (lean_unbox(v_isRoot_3130_) as u8);
    v_res_3140_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(
        v_isRoot_boxed_3139_,
        v_v_3131_,
        v_a_3132_,
        v_a_3133_,
        v_a_3134_,
        v_a_3135_,
        v_a_3136_,
        v_a_3137_,
    );
    lean_dec(v_a_3137_);
    lean_dec_ref(v_a_3136_);
    lean_dec(v_a_3135_);
    lean_dec_ref(v_a_3134_);
    lean_dec(v_a_3133_);
    lean_dec_ref(v_a_3132_);
    return v_res_3140_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(
    mut v_00_u03b2_3141_: *mut LeanObject,
    mut v_m_3142_: *mut LeanObject,
    mut v_a_3143_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    v___x_3144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___redArg(v_m_3142_, v_a_3143_);
    return v___x_3144_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6___boxed(
    mut v_00_u03b2_3145_: *mut LeanObject,
    mut v_m_3146_: *mut LeanObject,
    mut v_a_3147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3148_: *mut LeanObject = core::ptr::null_mut();
    v_res_3148_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6(v_00_u03b2_3145_, v_m_3146_, v_a_3147_);
    lean_dec(v_a_3147_);
    lean_dec_ref(v_m_3146_);
    return v_res_3148_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7(
    mut v_00_u03b2_3149_: *mut LeanObject,
    mut v_m_3150_: *mut LeanObject,
    mut v_a_3151_: *mut LeanObject,
    mut v_b_3152_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3153_: *mut LeanObject = core::ptr::null_mut();
    v___x_3153_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7___redArg(v_m_3150_, v_a_3151_, v_b_3152_);
    return v___x_3153_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(
    mut v_00_u03b2_3154_: *mut LeanObject,
    mut v_a_3155_: *mut LeanObject,
    mut v_x_3156_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    v___x_3157_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___redArg(v_a_3155_, v_x_3156_);
    return v___x_3157_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7___boxed(
    mut v_00_u03b2_3158_: *mut LeanObject,
    mut v_a_3159_: *mut LeanObject,
    mut v_x_3160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3161_: *mut LeanObject = core::ptr::null_mut();
    v_res_3161_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__6_spec__7(v_00_u03b2_3158_, v_a_3159_, v_x_3160_);
    lean_dec(v_x_3160_);
    lean_dec(v_a_3159_);
    return v_res_3161_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(
    mut v_00_u03b2_3162_: *mut LeanObject,
    mut v_a_3163_: *mut LeanObject,
    mut v_x_3164_: *mut LeanObject,
) -> u8 {
    let mut v___x_3165_: u8 = 0;
    v___x_3165_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___redArg(v_a_3163_, v_x_3164_);
    return v___x_3165_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9___boxed(
    mut v_00_u03b2_3166_: *mut LeanObject,
    mut v_a_3167_: *mut LeanObject,
    mut v_x_3168_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3169_: u8 = 0;
    let mut v_r_3170_: *mut LeanObject = core::ptr::null_mut();
    v_res_3169_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__9(v_00_u03b2_3166_, v_a_3167_, v_x_3168_);
    lean_dec(v_x_3168_);
    lean_dec(v_a_3167_);
    v_r_3170_ = lean_box((v_res_3169_) as usize);
    return v_r_3170_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10(
    mut v_00_u03b2_3171_: *mut LeanObject,
    mut v_data_3172_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    v___x_3173_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10___redArg(v_data_3172_);
    return v___x_3173_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11(
    mut v_00_u03b2_3174_: *mut LeanObject,
    mut v_a_3175_: *mut LeanObject,
    mut v_b_3176_: *mut LeanObject,
    mut v_x_3177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3178_: *mut LeanObject = core::ptr::null_mut();
    v___x_3178_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__11___redArg(v_a_3175_, v_b_3176_, v_x_3177_);
    return v___x_3178_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11(
    mut v_00_u03b2_3179_: *mut LeanObject,
    mut v_i_3180_: *mut LeanObject,
    mut v_source_3181_: *mut LeanObject,
    mut v_target_3182_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3183_: *mut LeanObject = core::ptr::null_mut();
    v___x_3183_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11___redArg(v_i_3180_, v_source_3181_, v_target_3182_);
    return v___x_3183_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12(
    mut v_00_u03b2_3184_: *mut LeanObject,
    mut v_x_3185_: *mut LeanObject,
    mut v_x_3186_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    v___x_3187_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Compiler_LCNF_ExtractClosed_shouldExtractFVar_spec__7_spec__10_spec__11_spec__12___redArg(v_x_3185_, v_x_3186_);
    return v___x_3187_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(
    mut v_prevArrayId_3193_: *mut LeanObject,
    mut v_decl_3194_: *mut LeanObject,
    mut v_k_3195_: *mut LeanObject,
    mut v_illegalSet_3196_: *mut LeanObject,
    mut v_size_3197_: *mut LeanObject,
    mut v_a_3198_: *mut LeanObject,
    mut v_a_3199_: *mut LeanObject,
    mut v_a_3200_: *mut LeanObject,
    mut v_a_3201_: *mut LeanObject,
    mut v_a_3202_: *mut LeanObject,
    mut v_a_3203_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_illegalSet_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3212_: u8 = 0;
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_3219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3220_: u8 = 0;
    let mut v___x_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3228_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: u8 = 0;
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3234_: u8 = 0;
    let mut v___x_3235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3243_: u8 = 0;
    let mut v___x_3244_: u8 = 0;
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3255_: u8 = 0;
    let mut v___x_3256_: u8 = 0;
    let mut v___x_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: u8 = 0;
    let mut v_decl_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_binderName_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3282_: u8 = 0;
    let mut v_us_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3287_: u8 = 0;
    let mut v_str_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: u8 = 0;
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3297_: u8 = 0;
    let mut v___x_3298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3302_: u8 = 0;
    let mut v___x_3303_: u8 = 0;
    let mut v___x_3304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3308_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: u8 = 0;
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3343_: u8 = 0;
    let mut v_isSharedCheck_3344_: u8 = 0;
    let mut v_unused_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3346_: u8 = 0;
    let mut v_unused_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3348_: u8 = 0;
    let mut v_a_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3352_: u8 = 0;
    let mut v___x_3354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3356_: u8 = 0;
    let mut v_isSharedCheck_3357_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_3219_ = lean_unsigned_to_nat(0);
                v_isZero_3220_ = lean_nat_dec_eq(v_size_3197_, v_zero_3219_);
                if v_isZero_3220_ == 1 {
                    lean_dec(v_size_3197_);
                    lean_dec(v_illegalSet_3196_);
                    lean_dec_ref(v_k_3195_);
                    lean_dec_ref(v_decl_3194_);
                    lean_dec(v_prevArrayId_3193_);
                    v___x_3221_ = lean_box(0);
                    v___x_3222_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3222_, 0, v___x_3221_);
                    return v___x_3222_;
                } else {
                    v_value_3223_ = lean_ctor_get(v_decl_3194_, 3);
                    if lean_obj_tag(v_value_3223_) == 3 {
                        v_declName_3224_ = lean_ctor_get(v_value_3223_, 0);
                        if lean_obj_tag(v_declName_3224_) == 1 {
                            v_pre_3225_ = lean_ctor_get(v_declName_3224_, 0);
                            if lean_obj_tag(v_pre_3225_) == 1 {
                                v_pre_3226_ = lean_ctor_get(v_pre_3225_, 0);
                                if lean_obj_tag(v_pre_3226_) == 0 {
                                    v_fvarId_3227_ = lean_ctor_get(v_decl_3194_, 0);
                                    v_args_3228_ = lean_ctor_get(v_value_3223_, 2);
                                    v_str_3229_ = lean_ctor_get(v_declName_3224_, 1);
                                    v_str_3230_ = lean_ctor_get(v_pre_3225_, 1);
                                    v___x_3231_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0;
                                    v___x_3232_ = lean_string_dec_eq(v_str_3230_, v___x_3231_);
                                    if v___x_3232_ == 0 {
                                        lean_dec(v_size_3197_);
                                        lean_dec(v_illegalSet_3196_);
                                        lean_dec_ref(v_k_3195_);
                                        lean_dec_ref(v_decl_3194_);
                                        lean_dec(v_prevArrayId_3193_);
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3233_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1;
                                        v___x_3234_ = lean_string_dec_eq(v_str_3229_, v___x_3233_);
                                        if v___x_3234_ == 0 {
                                            lean_dec(v_size_3197_);
                                            lean_dec(v_illegalSet_3196_);
                                            lean_dec_ref(v_k_3195_);
                                            lean_dec_ref(v_decl_3194_);
                                            lean_dec(v_prevArrayId_3193_);
                                            state = 1;
                                            continue;
                                        } else {
                                            v___x_3235_ = lean_array_get_size(v_args_3228_);
                                            v___x_3236_ = lean_unsigned_to_nat(3);
                                            v___x_3237_ = lean_nat_dec_eq(v___x_3235_, v___x_3236_);
                                            if v___x_3237_ == 0 {
                                                lean_dec(v_size_3197_);
                                                lean_dec(v_illegalSet_3196_);
                                                lean_dec_ref(v_k_3195_);
                                                lean_dec_ref(v_decl_3194_);
                                                lean_dec(v_prevArrayId_3193_);
                                                state = 1;
                                                continue;
                                            } else {
                                                v___x_3238_ = lean_unsigned_to_nat(1);
                                                v___x_3239_ =
                                                    lean_array_fget(v_args_3228_, v___x_3238_);
                                                if lean_obj_tag(v___x_3239_) == 1 {
                                                    v_fvarId_3240_ = lean_ctor_get(v___x_3239_, 0);
                                                    v_isSharedCheck_3357_ =
                                                        (!lean_is_exclusive(v___x_3239_)) as u8;
                                                    if v_isSharedCheck_3357_ == 0 {
                                                        v___x_3242_ = v___x_3239_;
                                                        v_isShared_3243_ = v_isSharedCheck_3357_;
                                                        state = 3;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_fvarId_3240_);
                                                        lean_dec(v___x_3239_);
                                                        v___x_3242_ = lean_box(0);
                                                        v_isShared_3243_ = v_isSharedCheck_3357_;
                                                        state = 3;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec(v___x_3239_);
                                                    lean_dec(v_size_3197_);
                                                    lean_dec(v_illegalSet_3196_);
                                                    lean_dec_ref(v_k_3195_);
                                                    lean_dec_ref(v_decl_3194_);
                                                    lean_dec(v_prevArrayId_3193_);
                                                    state = 1;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec(v_size_3197_);
                                    lean_dec(v_illegalSet_3196_);
                                    lean_dec_ref(v_k_3195_);
                                    lean_dec_ref(v_decl_3194_);
                                    lean_dec(v_prevArrayId_3193_);
                                    state = 1;
                                    continue;
                                }
                            } else {
                                lean_dec(v_size_3197_);
                                lean_dec(v_illegalSet_3196_);
                                lean_dec_ref(v_k_3195_);
                                lean_dec_ref(v_decl_3194_);
                                lean_dec(v_prevArrayId_3193_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_size_3197_);
                            lean_dec(v_illegalSet_3196_);
                            lean_dec_ref(v_k_3195_);
                            lean_dec_ref(v_decl_3194_);
                            lean_dec(v_prevArrayId_3193_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_3197_);
                        lean_dec(v_illegalSet_3196_);
                        lean_dec_ref(v_k_3195_);
                        lean_dec_ref(v_decl_3194_);
                        lean_dec(v_prevArrayId_3193_);
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3206_ = lean_box(0);
                v___x_3207_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3207_, 0, v___x_3206_);
                return v___x_3207_;
            }
            2 => {
                v___x_3212_ = 0;
                v___x_3213_ =
                    l_Lean_Compiler_LCNF_Code_dependsOn(v___x_3212_, v_k_3210_, v_illegalSet_3211_);
                lean_dec(v_illegalSet_3211_);
                if v___x_3213_ == 0 {
                    v___x_3214_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3214_, 0, v_decl_3209_);
                    lean_ctor_set(v___x_3214_, 1, v_k_3210_);
                    v___x_3215_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3215_, 0, v___x_3214_);
                    v___x_3216_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3216_, 0, v___x_3215_);
                    return v___x_3216_;
                } else {
                    lean_dec_ref(v_k_3210_);
                    lean_dec_ref(v_decl_3209_);
                    v___x_3217_ = lean_box(0);
                    v___x_3218_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3218_, 0, v___x_3217_);
                    return v___x_3218_;
                }
            }
            3 => {
                v___x_3244_ = l_Lean_instBEqFVarId_beq(v_fvarId_3240_, v_prevArrayId_3193_);
                lean_dec(v_prevArrayId_3193_);
                lean_dec(v_fvarId_3240_);
                if v___x_3244_ == 0 {
                    lean_dec(v_size_3197_);
                    lean_dec(v_illegalSet_3196_);
                    lean_dec_ref(v_k_3195_);
                    lean_dec_ref(v_decl_3194_);
                    v___x_3245_ = lean_box(0);
                    if v_isShared_3243_ == 0 {
                        lean_ctor_set_tag(v___x_3242_, 0);
                        lean_ctor_set(v___x_3242_, 0, v___x_3245_);
                        v___x_3247_ = v___x_3242_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3248_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3245_);
                        v___x_3247_ = v_reuseFailAlloc_3248_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3242_);
                    v___x_3249_ = lean_unsigned_to_nat(2);
                    v___x_3250_ = lean_array_fget_borrowed(v_args_3228_, v___x_3249_);
                    lean_inc(v___x_3250_);
                    v___x_3251_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractArg(
                        v___x_3250_,
                        v_a_3198_,
                        v_a_3199_,
                        v_a_3200_,
                        v_a_3201_,
                        v_a_3202_,
                        v_a_3203_,
                    );
                    if lean_obj_tag(v___x_3251_) == 0 {
                        v_a_3252_ = lean_ctor_get(v___x_3251_, 0);
                        v_isSharedCheck_3348_ = (!lean_is_exclusive(v___x_3251_)) as u8;
                        if v_isSharedCheck_3348_ == 0 {
                            v___x_3254_ = v___x_3251_;
                            v_isShared_3255_ = v_isSharedCheck_3348_;
                            state = 5;
                            continue;
                        } else {
                            lean_inc(v_a_3252_);
                            lean_dec(v___x_3251_);
                            v___x_3254_ = lean_box(0);
                            v_isShared_3255_ = v_isSharedCheck_3348_;
                            state = 5;
                            continue;
                        }
                    } else {
                        lean_dec(v_size_3197_);
                        lean_dec(v_illegalSet_3196_);
                        lean_dec_ref(v_k_3195_);
                        lean_dec_ref(v_decl_3194_);
                        v_a_3349_ = lean_ctor_get(v___x_3251_, 0);
                        v_isSharedCheck_3356_ = (!lean_is_exclusive(v___x_3251_)) as u8;
                        if v_isSharedCheck_3356_ == 0 {
                            v___x_3351_ = v___x_3251_;
                            v_isShared_3352_ = v_isSharedCheck_3356_;
                            state = 18;
                            continue;
                        } else {
                            lean_inc(v_a_3349_);
                            lean_dec(v___x_3251_);
                            v___x_3351_ = lean_box(0);
                            v_isShared_3352_ = v_isSharedCheck_3356_;
                            state = 18;
                            continue;
                        }
                    }
                }
            }
            4 => {
                return v___x_3247_;
            }
            5 => {
                v___x_3256_ = (lean_unbox(v_a_3252_) as u8);
                lean_dec(v_a_3252_);
                if v___x_3256_ == 0 {
                    lean_dec(v_size_3197_);
                    lean_dec(v_illegalSet_3196_);
                    lean_dec_ref(v_k_3195_);
                    lean_dec_ref(v_decl_3194_);
                    v___x_3257_ = lean_box(0);
                    if v_isShared_3255_ == 0 {
                        lean_ctor_set(v___x_3254_, 0, v___x_3257_);
                        v___x_3259_ = v___x_3254_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3260_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3260_, 0, v___x_3257_);
                        v___x_3259_ = v_reuseFailAlloc_3260_;
                        state = 6;
                        continue;
                    }
                } else {
                    v_n_3261_ = lean_nat_sub(v_size_3197_, v___x_3238_);
                    lean_dec(v_size_3197_);
                    v___x_3262_ = lean_nat_dec_eq(v_n_3261_, v_zero_3219_);
                    if v___x_3262_ == 0 {
                        lean_inc(v_fvarId_3227_);
                        lean_dec_ref(v_decl_3194_);
                        if lean_obj_tag(v_k_3195_) == 0 {
                            lean_del_object(v___x_3254_);
                            v_decl_3263_ = lean_ctor_get(v_k_3195_, 0);
                            lean_inc_ref(v_decl_3263_);
                            v_k_3264_ = lean_ctor_get(v_k_3195_, 1);
                            lean_inc_ref(v_k_3264_);
                            lean_dec_ref_known(v_k_3195_, 2);
                            lean_inc(v_fvarId_3227_);
                            v___x_3265_ =
                                l_Lean_FVarIdSet_insert(v_illegalSet_3196_, v_fvarId_3227_);
                            v_prevArrayId_3193_ = v_fvarId_3227_;
                            v_decl_3194_ = v_decl_3263_;
                            v_k_3195_ = v_k_3264_;
                            v_illegalSet_3196_ = v___x_3265_;
                            v_size_3197_ = v_n_3261_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_n_3261_);
                            lean_dec(v_fvarId_3227_);
                            lean_dec(v_illegalSet_3196_);
                            lean_dec_ref(v_k_3195_);
                            v___x_3267_ = lean_box(0);
                            if v_isShared_3255_ == 0 {
                                lean_ctor_set(v___x_3254_, 0, v___x_3267_);
                                v___x_3269_ = v___x_3254_;
                                state = 7;
                                continue;
                            } else {
                                v_reuseFailAlloc_3270_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3270_, 0, v___x_3267_);
                                v___x_3269_ = v_reuseFailAlloc_3270_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_n_3261_);
                        lean_del_object(v___x_3254_);
                        if lean_obj_tag(v_k_3195_) == 0 {
                            v_decl_3271_ = lean_ctor_get(v_k_3195_, 0);
                            lean_inc_ref(v_decl_3271_);
                            v_value_3272_ = lean_ctor_get(v_decl_3271_, 3);
                            lean_inc(v_value_3272_);
                            if lean_obj_tag(v_value_3272_) == 3 {
                                v_declName_3273_ = lean_ctor_get(v_value_3272_, 0);
                                lean_inc(v_declName_3273_);
                                if lean_obj_tag(v_declName_3273_) == 1 {
                                    v_pre_3274_ = lean_ctor_get(v_declName_3273_, 0);
                                    lean_inc(v_pre_3274_);
                                    if lean_obj_tag(v_pre_3274_) == 1 {
                                        v_pre_3275_ = lean_ctor_get(v_pre_3274_, 0);
                                        lean_inc(v_pre_3275_);
                                        if lean_obj_tag(v_pre_3275_) == 0 {
                                            v_k_3276_ = lean_ctor_get(v_k_3195_, 1);
                                            v_fvarId_3277_ = lean_ctor_get(v_decl_3271_, 0);
                                            v_binderName_3278_ = lean_ctor_get(v_decl_3271_, 1);
                                            v_type_3279_ = lean_ctor_get(v_decl_3271_, 2);
                                            v_isSharedCheck_3346_ =
                                                (!lean_is_exclusive(v_decl_3271_)) as u8;
                                            if v_isSharedCheck_3346_ == 0 {
                                                v_unused_3347_ = lean_ctor_get(v_decl_3271_, 3);
                                                lean_dec(v_unused_3347_);
                                                v___x_3281_ = v_decl_3271_;
                                                v_isShared_3282_ = v_isSharedCheck_3346_;
                                                state = 8;
                                                continue;
                                            } else {
                                                lean_inc(v_type_3279_);
                                                lean_inc(v_binderName_3278_);
                                                lean_inc(v_fvarId_3277_);
                                                lean_dec(v_decl_3271_);
                                                v___x_3281_ = lean_box(0);
                                                v_isShared_3282_ = v_isSharedCheck_3346_;
                                                state = 8;
                                                continue;
                                            }
                                        } else {
                                            lean_dec_ref_known(v_pre_3274_, 2);
                                            lean_dec(v_pre_3275_);
                                            lean_dec_ref_known(v_declName_3273_, 2);
                                            lean_dec_ref_known(v_value_3272_, 3);
                                            lean_dec_ref(v_decl_3271_);
                                            v_decl_3209_ = v_decl_3194_;
                                            v_k_3210_ = v_k_3195_;
                                            v_illegalSet_3211_ = v_illegalSet_3196_;
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        lean_dec(v_pre_3274_);
                                        lean_dec_ref_known(v_declName_3273_, 2);
                                        lean_dec_ref_known(v_value_3272_, 3);
                                        lean_dec_ref(v_decl_3271_);
                                        v_decl_3209_ = v_decl_3194_;
                                        v_k_3210_ = v_k_3195_;
                                        v_illegalSet_3211_ = v_illegalSet_3196_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_value_3272_, 3);
                                    lean_dec(v_declName_3273_);
                                    lean_dec_ref(v_decl_3271_);
                                    v_decl_3209_ = v_decl_3194_;
                                    v_k_3210_ = v_k_3195_;
                                    v_illegalSet_3211_ = v_illegalSet_3196_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec(v_value_3272_);
                                lean_dec_ref(v_decl_3271_);
                                v_decl_3209_ = v_decl_3194_;
                                v_k_3210_ = v_k_3195_;
                                v_illegalSet_3211_ = v_illegalSet_3196_;
                                state = 2;
                                continue;
                            }
                        } else {
                            v_decl_3209_ = v_decl_3194_;
                            v_k_3210_ = v_k_3195_;
                            v_illegalSet_3211_ = v_illegalSet_3196_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            6 => {
                return v___x_3259_;
            }
            7 => {
                return v___x_3269_;
            }
            8 => {
                v_us_3283_ = lean_ctor_get(v_value_3272_, 1);
                v_args_3284_ = lean_ctor_get(v_value_3272_, 2);
                v_isSharedCheck_3344_ = (!lean_is_exclusive(v_value_3272_)) as u8;
                if v_isSharedCheck_3344_ == 0 {
                    v_unused_3345_ = lean_ctor_get(v_value_3272_, 0);
                    lean_dec(v_unused_3345_);
                    v___x_3286_ = v_value_3272_;
                    v_isShared_3287_ = v_isSharedCheck_3344_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_args_3284_);
                    lean_inc(v_us_3283_);
                    lean_dec(v_value_3272_);
                    v___x_3286_ = lean_box(0);
                    v_isShared_3287_ = v_isSharedCheck_3344_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_str_3288_ = lean_ctor_get(v_declName_3273_, 1);
                lean_inc_ref(v_str_3288_);
                lean_dec_ref_known(v_declName_3273_, 2);
                v_str_3289_ = lean_ctor_get(v_pre_3274_, 1);
                lean_inc_ref(v_str_3289_);
                lean_dec_ref_known(v_pre_3274_, 2);
                v___x_3290_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__2;
                v___x_3291_ = lean_string_dec_eq(v_str_3289_, v___x_3290_);
                if v___x_3291_ == 0 {
                    v___x_3292_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__3;
                    v___x_3293_ = lean_string_dec_eq(v_str_3289_, v___x_3292_);
                    lean_dec_ref(v_str_3289_);
                    if v___x_3293_ == 0 {
                        lean_dec_ref(v_str_3288_);
                        lean_del_object(v___x_3286_);
                        lean_dec_ref(v_args_3284_);
                        lean_dec(v_us_3283_);
                        lean_del_object(v___x_3281_);
                        lean_dec_ref(v_type_3279_);
                        lean_dec(v_binderName_3278_);
                        lean_dec(v_fvarId_3277_);
                        v_decl_3209_ = v_decl_3194_;
                        v_k_3210_ = v_k_3195_;
                        v_illegalSet_3211_ = v_illegalSet_3196_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3294_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4;
                        v___x_3295_ = lean_string_dec_eq(v_str_3288_, v___x_3294_);
                        lean_dec_ref(v_str_3288_);
                        if v___x_3295_ == 0 {
                            lean_del_object(v___x_3286_);
                            lean_dec_ref(v_args_3284_);
                            lean_dec(v_us_3283_);
                            lean_del_object(v___x_3281_);
                            lean_dec_ref(v_type_3279_);
                            lean_dec(v_binderName_3278_);
                            lean_dec(v_fvarId_3277_);
                            v_decl_3209_ = v_decl_3194_;
                            v_k_3210_ = v_k_3195_;
                            v_illegalSet_3211_ = v_illegalSet_3196_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3296_ = lean_array_get_size(v_args_3284_);
                            v___x_3297_ = lean_nat_dec_eq(v___x_3296_, v___x_3238_);
                            if v___x_3297_ == 0 {
                                lean_del_object(v___x_3286_);
                                lean_dec_ref(v_args_3284_);
                                lean_dec(v_us_3283_);
                                lean_del_object(v___x_3281_);
                                lean_dec_ref(v_type_3279_);
                                lean_dec(v_binderName_3278_);
                                lean_dec(v_fvarId_3277_);
                                v_decl_3209_ = v_decl_3194_;
                                v_k_3210_ = v_k_3195_;
                                v_illegalSet_3211_ = v_illegalSet_3196_;
                                state = 2;
                                continue;
                            } else {
                                v___x_3298_ = lean_array_fget(v_args_3284_, v_zero_3219_);
                                lean_dec_ref(v_args_3284_);
                                if lean_obj_tag(v___x_3298_) == 1 {
                                    v_fvarId_3299_ = lean_ctor_get(v___x_3298_, 0);
                                    v_isSharedCheck_3318_ = (!lean_is_exclusive(v___x_3298_)) as u8;
                                    if v_isSharedCheck_3318_ == 0 {
                                        v___x_3301_ = v___x_3298_;
                                        v_isShared_3302_ = v_isSharedCheck_3318_;
                                        state = 10;
                                        continue;
                                    } else {
                                        lean_inc(v_fvarId_3299_);
                                        lean_dec(v___x_3298_);
                                        v___x_3301_ = lean_box(0);
                                        v_isShared_3302_ = v_isSharedCheck_3318_;
                                        state = 10;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v___x_3298_);
                                    lean_del_object(v___x_3286_);
                                    lean_dec(v_us_3283_);
                                    lean_del_object(v___x_3281_);
                                    lean_dec_ref(v_type_3279_);
                                    lean_dec(v_binderName_3278_);
                                    lean_dec(v_fvarId_3277_);
                                    v_decl_3209_ = v_decl_3194_;
                                    v_k_3210_ = v_k_3195_;
                                    v_illegalSet_3211_ = v_illegalSet_3196_;
                                    state = 2;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_str_3289_);
                    v___x_3319_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__4;
                    v___x_3320_ = lean_string_dec_eq(v_str_3288_, v___x_3319_);
                    lean_dec_ref(v_str_3288_);
                    if v___x_3320_ == 0 {
                        lean_del_object(v___x_3286_);
                        lean_dec_ref(v_args_3284_);
                        lean_dec(v_us_3283_);
                        lean_del_object(v___x_3281_);
                        lean_dec_ref(v_type_3279_);
                        lean_dec(v_binderName_3278_);
                        lean_dec(v_fvarId_3277_);
                        v_decl_3209_ = v_decl_3194_;
                        v_k_3210_ = v_k_3195_;
                        v_illegalSet_3211_ = v_illegalSet_3196_;
                        state = 2;
                        continue;
                    } else {
                        v___x_3321_ = lean_array_get_size(v_args_3284_);
                        v___x_3322_ = lean_nat_dec_eq(v___x_3321_, v___x_3238_);
                        if v___x_3322_ == 0 {
                            lean_del_object(v___x_3286_);
                            lean_dec_ref(v_args_3284_);
                            lean_dec(v_us_3283_);
                            lean_del_object(v___x_3281_);
                            lean_dec_ref(v_type_3279_);
                            lean_dec(v_binderName_3278_);
                            lean_dec(v_fvarId_3277_);
                            v_decl_3209_ = v_decl_3194_;
                            v_k_3210_ = v_k_3195_;
                            v_illegalSet_3211_ = v_illegalSet_3196_;
                            state = 2;
                            continue;
                        } else {
                            v___x_3323_ = lean_array_fget(v_args_3284_, v_zero_3219_);
                            lean_dec_ref(v_args_3284_);
                            if lean_obj_tag(v___x_3323_) == 1 {
                                v_fvarId_3324_ = lean_ctor_get(v___x_3323_, 0);
                                v_isSharedCheck_3343_ = (!lean_is_exclusive(v___x_3323_)) as u8;
                                if v_isSharedCheck_3343_ == 0 {
                                    v___x_3326_ = v___x_3323_;
                                    v_isShared_3327_ = v_isSharedCheck_3343_;
                                    state = 14;
                                    continue;
                                } else {
                                    lean_inc(v_fvarId_3324_);
                                    lean_dec(v___x_3323_);
                                    v___x_3326_ = lean_box(0);
                                    v_isShared_3327_ = v_isSharedCheck_3343_;
                                    state = 14;
                                    continue;
                                }
                            } else {
                                lean_dec(v___x_3323_);
                                lean_del_object(v___x_3286_);
                                lean_dec(v_us_3283_);
                                lean_del_object(v___x_3281_);
                                lean_dec_ref(v_type_3279_);
                                lean_dec(v_binderName_3278_);
                                lean_dec(v_fvarId_3277_);
                                v_decl_3209_ = v_decl_3194_;
                                v_k_3210_ = v_k_3195_;
                                v_illegalSet_3211_ = v_illegalSet_3196_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            10 => {
                v___x_3303_ = l_Lean_instBEqFVarId_beq(v_fvarId_3299_, v_fvarId_3227_);
                if v___x_3303_ == 0 {
                    lean_del_object(v___x_3301_);
                    lean_dec(v_fvarId_3299_);
                    lean_del_object(v___x_3286_);
                    lean_dec(v_us_3283_);
                    lean_del_object(v___x_3281_);
                    lean_dec_ref(v_type_3279_);
                    lean_dec(v_binderName_3278_);
                    lean_dec(v_fvarId_3277_);
                    v_decl_3209_ = v_decl_3194_;
                    v_k_3210_ = v_k_3195_;
                    v_illegalSet_3211_ = v_illegalSet_3196_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_k_3276_);
                    lean_inc(v_fvarId_3227_);
                    lean_dec_ref_known(v_k_3195_, 2);
                    lean_dec_ref(v_decl_3194_);
                    v___x_3304_ = l_Lean_Name_str___override(v_pre_3275_, v___x_3292_);
                    v___x_3305_ = l_Lean_Name_str___override(v___x_3304_, v___x_3294_);
                    if v_isShared_3302_ == 0 {
                        v___x_3307_ = v___x_3301_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_3317_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3317_, 0, v_fvarId_3299_);
                        v___x_3307_ = v_reuseFailAlloc_3317_;
                        state = 11;
                        continue;
                    }
                }
            }
            11 => {
                v___x_3308_ = lean_mk_empty_array_with_capacity(v___x_3238_);
                v___x_3309_ = lean_array_push(v___x_3308_, v___x_3307_);
                if v_isShared_3287_ == 0 {
                    lean_ctor_set(v___x_3286_, 2, v___x_3309_);
                    lean_ctor_set(v___x_3286_, 0, v___x_3305_);
                    v___x_3311_ = v___x_3286_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3316_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3316_, 0, v___x_3305_);
                    lean_ctor_set(v_reuseFailAlloc_3316_, 1, v_us_3283_);
                    lean_ctor_set(v_reuseFailAlloc_3316_, 2, v___x_3309_);
                    v___x_3311_ = v_reuseFailAlloc_3316_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3282_ == 0 {
                    lean_ctor_set(v___x_3281_, 3, v___x_3311_);
                    v___x_3313_ = v___x_3281_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3315_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 0, v_fvarId_3277_);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 1, v_binderName_3278_);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 2, v_type_3279_);
                    lean_ctor_set(v_reuseFailAlloc_3315_, 3, v___x_3311_);
                    v___x_3313_ = v_reuseFailAlloc_3315_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_3314_ = l_Lean_FVarIdSet_insert(v_illegalSet_3196_, v_fvarId_3227_);
                v_decl_3209_ = v___x_3313_;
                v_k_3210_ = v_k_3276_;
                v_illegalSet_3211_ = v___x_3314_;
                state = 2;
                continue;
            }
            14 => {
                v___x_3328_ = l_Lean_instBEqFVarId_beq(v_fvarId_3324_, v_fvarId_3227_);
                if v___x_3328_ == 0 {
                    lean_del_object(v___x_3326_);
                    lean_dec(v_fvarId_3324_);
                    lean_del_object(v___x_3286_);
                    lean_dec(v_us_3283_);
                    lean_del_object(v___x_3281_);
                    lean_dec_ref(v_type_3279_);
                    lean_dec(v_binderName_3278_);
                    lean_dec(v_fvarId_3277_);
                    v_decl_3209_ = v_decl_3194_;
                    v_k_3210_ = v_k_3195_;
                    v_illegalSet_3211_ = v_illegalSet_3196_;
                    state = 2;
                    continue;
                } else {
                    lean_inc_ref(v_k_3276_);
                    lean_inc(v_fvarId_3227_);
                    lean_dec_ref_known(v_k_3195_, 2);
                    lean_dec_ref(v_decl_3194_);
                    v___x_3329_ = l_Lean_Name_str___override(v_pre_3275_, v___x_3290_);
                    v___x_3330_ = l_Lean_Name_str___override(v___x_3329_, v___x_3319_);
                    if v_isShared_3327_ == 0 {
                        v___x_3332_ = v___x_3326_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3342_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3342_, 0, v_fvarId_3324_);
                        v___x_3332_ = v_reuseFailAlloc_3342_;
                        state = 15;
                        continue;
                    }
                }
            }
            15 => {
                v___x_3333_ = lean_mk_empty_array_with_capacity(v___x_3238_);
                v___x_3334_ = lean_array_push(v___x_3333_, v___x_3332_);
                if v_isShared_3287_ == 0 {
                    lean_ctor_set(v___x_3286_, 2, v___x_3334_);
                    lean_ctor_set(v___x_3286_, 0, v___x_3330_);
                    v___x_3336_ = v___x_3286_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3341_ = lean_alloc_ctor(3, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 0, v___x_3330_);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 1, v_us_3283_);
                    lean_ctor_set(v_reuseFailAlloc_3341_, 2, v___x_3334_);
                    v___x_3336_ = v_reuseFailAlloc_3341_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                if v_isShared_3282_ == 0 {
                    lean_ctor_set(v___x_3281_, 3, v___x_3336_);
                    v___x_3338_ = v___x_3281_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_fvarId_3277_);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_binderName_3278_);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 2, v_type_3279_);
                    lean_ctor_set(v_reuseFailAlloc_3340_, 3, v___x_3336_);
                    v___x_3338_ = v_reuseFailAlloc_3340_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                v___x_3339_ = l_Lean_FVarIdSet_insert(v_illegalSet_3196_, v_fvarId_3227_);
                v_decl_3209_ = v___x_3338_;
                v_k_3210_ = v_k_3276_;
                v_illegalSet_3211_ = v___x_3339_;
                state = 2;
                continue;
            }
            18 => {
                if v_isShared_3352_ == 0 {
                    v___x_3354_ = v___x_3351_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3355_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3355_, 0, v_a_3349_);
                    v___x_3354_ = v_reuseFailAlloc_3355_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3354_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___boxed(
    mut v_prevArrayId_3358_: *mut LeanObject,
    mut v_decl_3359_: *mut LeanObject,
    mut v_k_3360_: *mut LeanObject,
    mut v_illegalSet_3361_: *mut LeanObject,
    mut v_size_3362_: *mut LeanObject,
    mut v_a_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
    mut v_a_3365_: *mut LeanObject,
    mut v_a_3366_: *mut LeanObject,
    mut v_a_3367_: *mut LeanObject,
    mut v_a_3368_: *mut LeanObject,
    mut v_a_3369_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3370_: *mut LeanObject = core::ptr::null_mut();
    v_res_3370_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_prevArrayId_3358_, v_decl_3359_, v_k_3360_, v_illegalSet_3361_, v_size_3362_, v_a_3363_, v_a_3364_, v_a_3365_, v_a_3366_, v_a_3367_, v_a_3368_);
    lean_dec(v_a_3368_);
    lean_dec_ref(v_a_3367_);
    lean_dec(v_a_3366_);
    lean_dec_ref(v_a_3365_);
    lean_dec(v_a_3364_);
    lean_dec_ref(v_a_3363_);
    return v_res_3370_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(
    mut v_decl_3373_: *mut LeanObject,
    mut v_k_3374_: *mut LeanObject,
    mut v_a_3375_: *mut LeanObject,
    mut v_a_3376_: *mut LeanObject,
    mut v_a_3377_: *mut LeanObject,
    mut v_a_3378_: *mut LeanObject,
    mut v_a_3379_: *mut LeanObject,
    mut v_a_3380_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: u8 = 0;
    let mut v___x_3400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3401_: u8 = 0;
    let mut v___x_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: u8 = 0;
    let mut v___x_3405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3408_: u8 = 0;
    let mut v___x_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3413_: u8 = 0;
    let mut v_val_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_declName_3416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_3418_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_3422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3423_: u8 = 0;
    let mut v___x_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sizeFVar_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3433_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3442_: u8 = 0;
    let mut v___x_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3446_: u8 = 0;
    let mut v___x_3447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: u8 = 0;
    let mut v___x_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3450_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: u8 = 0;
    let mut v___x_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: u8 = 0;
    let mut v___x_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3465_: u8 = 0;
    let mut v_a_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3469_: u8 = 0;
    let mut v___x_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3473_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_3391_ = lean_ctor_get(v_decl_3373_, 3);
                if lean_obj_tag(v_value_3391_) == 3 {
                    v_declName_3392_ = lean_ctor_get(v_value_3391_, 0);
                    if lean_obj_tag(v_declName_3392_) == 1 {
                        v_pre_3393_ = lean_ctor_get(v_declName_3392_, 0);
                        if lean_obj_tag(v_pre_3393_) == 1 {
                            v_pre_3394_ = lean_ctor_get(v_pre_3393_, 0);
                            if lean_obj_tag(v_pre_3394_) == 0 {
                                v_args_3395_ = lean_ctor_get(v_value_3391_, 2);
                                v_str_3396_ = lean_ctor_get(v_declName_3392_, 1);
                                v_str_3397_ = lean_ctor_get(v_pre_3393_, 1);
                                v___x_3398_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0;
                                v___x_3399_ = lean_string_dec_eq(v_str_3397_, v___x_3398_);
                                if v___x_3399_ == 0 {
                                    lean_dec_ref(v_k_3374_);
                                    lean_dec_ref(v_decl_3373_);
                                    state = 3;
                                    continue;
                                } else {
                                    v___x_3400_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__1;
                                    v___x_3401_ = lean_string_dec_eq(v_str_3396_, v___x_3400_);
                                    if v___x_3401_ == 0 {
                                        lean_dec_ref(v_k_3374_);
                                        lean_dec_ref(v_decl_3373_);
                                        state = 3;
                                        continue;
                                    } else {
                                        v___x_3402_ = lean_array_get_size(v_args_3395_);
                                        v___x_3403_ = lean_unsigned_to_nat(3);
                                        v___x_3404_ = lean_nat_dec_eq(v___x_3402_, v___x_3403_);
                                        if v___x_3404_ == 0 {
                                            lean_dec_ref(v_k_3374_);
                                            lean_dec_ref(v_decl_3373_);
                                            state = 3;
                                            continue;
                                        } else {
                                            v___x_3405_ = lean_unsigned_to_nat(1);
                                            v___x_3406_ =
                                                lean_array_fget_borrowed(v_args_3395_, v___x_3405_);
                                            if lean_obj_tag(v___x_3406_) == 1 {
                                                v_fvarId_3407_ = lean_ctor_get(v___x_3406_, 0);
                                                v___x_3408_ = 0;
                                                v___x_3409_ =
                                                    l_Lean_Compiler_LCNF_findLetDecl_x3f___redArg(
                                                        v___x_3408_,
                                                        v_fvarId_3407_,
                                                        v_a_3378_,
                                                    );
                                                if lean_obj_tag(v___x_3409_) == 0 {
                                                    v_a_3410_ = lean_ctor_get(v___x_3409_, 0);
                                                    v_isSharedCheck_3465_ =
                                                        (!lean_is_exclusive(v___x_3409_)) as u8;
                                                    if v_isSharedCheck_3465_ == 0 {
                                                        v___x_3412_ = v___x_3409_;
                                                        v_isShared_3413_ = v_isSharedCheck_3465_;
                                                        state = 4;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3410_);
                                                        lean_dec(v___x_3409_);
                                                        v___x_3412_ = lean_box(0);
                                                        v_isShared_3413_ = v_isSharedCheck_3465_;
                                                        state = 4;
                                                        continue;
                                                    }
                                                } else {
                                                    lean_dec_ref(v_k_3374_);
                                                    lean_dec_ref(v_decl_3373_);
                                                    v_a_3466_ = lean_ctor_get(v___x_3409_, 0);
                                                    v_isSharedCheck_3473_ =
                                                        (!lean_is_exclusive(v___x_3409_)) as u8;
                                                    if v_isSharedCheck_3473_ == 0 {
                                                        v___x_3468_ = v___x_3409_;
                                                        v_isShared_3469_ = v_isSharedCheck_3473_;
                                                        state = 9;
                                                        continue;
                                                    } else {
                                                        lean_inc(v_a_3466_);
                                                        lean_dec(v___x_3409_);
                                                        v___x_3468_ = lean_box(0);
                                                        v_isShared_3469_ = v_isSharedCheck_3473_;
                                                        state = 9;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                lean_dec_ref(v_k_3374_);
                                                lean_dec_ref(v_decl_3373_);
                                                state = 3;
                                                continue;
                                            }
                                        }
                                    }
                                }
                            } else {
                                lean_dec_ref(v_k_3374_);
                                lean_dec_ref(v_decl_3373_);
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_k_3374_);
                            lean_dec_ref(v_decl_3373_);
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_k_3374_);
                        lean_dec_ref(v_decl_3373_);
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_k_3374_);
                    lean_dec_ref(v_decl_3373_);
                    state = 3;
                    continue;
                }
            }
            1 => {
                v___x_3383_ = lean_box(0);
                v___x_3384_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3384_, 0, v___x_3383_);
                return v___x_3384_;
            }
            2 => {
                v___x_3386_ = lean_box(0);
                v___x_3387_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3387_, 0, v___x_3386_);
                return v___x_3387_;
            }
            3 => {
                v___x_3389_ = lean_box(0);
                v___x_3390_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3390_, 0, v___x_3389_);
                return v___x_3390_;
            }
            4 => {
                if lean_obj_tag(v_a_3410_) == 1 {
                    lean_del_object(v___x_3412_);
                    v_val_3414_ = lean_ctor_get(v_a_3410_, 0);
                    lean_inc(v_val_3414_);
                    lean_dec_ref_known(v_a_3410_, 1);
                    v_value_3415_ = lean_ctor_get(v_val_3414_, 3);
                    lean_inc(v_value_3415_);
                    if lean_obj_tag(v_value_3415_) == 3 {
                        v_declName_3416_ = lean_ctor_get(v_value_3415_, 0);
                        lean_inc(v_declName_3416_);
                        if lean_obj_tag(v_declName_3416_) == 1 {
                            v_pre_3417_ = lean_ctor_get(v_declName_3416_, 0);
                            lean_inc(v_pre_3417_);
                            if lean_obj_tag(v_pre_3417_) == 1 {
                                v_pre_3418_ = lean_ctor_get(v_pre_3417_, 0);
                                if lean_obj_tag(v_pre_3418_) == 0 {
                                    v_fvarId_3419_ = lean_ctor_get(v_val_3414_, 0);
                                    lean_inc(v_fvarId_3419_);
                                    lean_dec(v_val_3414_);
                                    v_args_3420_ = lean_ctor_get(v_value_3415_, 2);
                                    lean_inc_ref(v_args_3420_);
                                    lean_dec_ref_known(v_value_3415_, 3);
                                    v_str_3421_ = lean_ctor_get(v_declName_3416_, 1);
                                    lean_inc_ref(v_str_3421_);
                                    lean_dec_ref_known(v_declName_3416_, 2);
                                    v_str_3422_ = lean_ctor_get(v_pre_3417_, 1);
                                    lean_inc_ref(v_str_3422_);
                                    lean_dec_ref_known(v_pre_3417_, 2);
                                    v___x_3423_ = lean_string_dec_eq(v_str_3422_, v___x_3398_);
                                    lean_dec_ref(v_str_3422_);
                                    if v___x_3423_ == 0 {
                                        lean_dec_ref(v_str_3421_);
                                        lean_dec_ref(v_args_3420_);
                                        lean_dec(v_fvarId_3419_);
                                        lean_dec_ref(v_k_3374_);
                                        lean_dec_ref(v_decl_3373_);
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3424_ = lean_box(1);
                                        v___x_3447_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0;
                                        v___x_3448_ = lean_string_dec_eq(v_str_3421_, v___x_3447_);
                                        if v___x_3448_ == 0 {
                                            v___x_3449_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1;
                                            v___x_3450_ =
                                                lean_string_dec_eq(v_str_3421_, v___x_3449_);
                                            lean_dec_ref(v_str_3421_);
                                            if v___x_3450_ == 0 {
                                                lean_dec_ref(v_args_3420_);
                                                lean_dec(v_fvarId_3419_);
                                                lean_dec_ref(v_k_3374_);
                                                lean_dec_ref(v_decl_3373_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_3451_ = lean_array_get_size(v_args_3420_);
                                                v___x_3452_ = lean_unsigned_to_nat(2);
                                                v___x_3453_ =
                                                    lean_nat_dec_eq(v___x_3451_, v___x_3452_);
                                                if v___x_3453_ == 0 {
                                                    lean_dec_ref(v_args_3420_);
                                                    lean_dec(v_fvarId_3419_);
                                                    lean_dec_ref(v_k_3374_);
                                                    lean_dec_ref(v_decl_3373_);
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_3454_ =
                                                        lean_array_fget(v_args_3420_, v___x_3405_);
                                                    lean_dec_ref(v_args_3420_);
                                                    if lean_obj_tag(v___x_3454_) == 1 {
                                                        v_fvarId_3455_ =
                                                            lean_ctor_get(v___x_3454_, 0);
                                                        lean_inc(v_fvarId_3455_);
                                                        lean_dec_ref_known(v___x_3454_, 1);
                                                        v_sizeFVar_3426_ = v_fvarId_3455_;
                                                        v___y_3427_ = v_a_3375_;
                                                        v___y_3428_ = v_a_3376_;
                                                        v___y_3429_ = v_a_3377_;
                                                        v___y_3430_ = v_a_3378_;
                                                        v___y_3431_ = v_a_3379_;
                                                        v___y_3432_ = v_a_3380_;
                                                        state = 5;
                                                        continue;
                                                    } else {
                                                        lean_dec(v___x_3454_);
                                                        lean_dec(v_fvarId_3419_);
                                                        lean_dec_ref(v_k_3374_);
                                                        lean_dec_ref(v_decl_3373_);
                                                        state = 2;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            lean_dec_ref(v_str_3421_);
                                            v___x_3456_ = lean_array_get_size(v_args_3420_);
                                            v___x_3457_ = lean_unsigned_to_nat(2);
                                            v___x_3458_ = lean_nat_dec_eq(v___x_3456_, v___x_3457_);
                                            if v___x_3458_ == 0 {
                                                lean_dec_ref(v_args_3420_);
                                                lean_dec(v_fvarId_3419_);
                                                lean_dec_ref(v_k_3374_);
                                                lean_dec_ref(v_decl_3373_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_3459_ =
                                                    lean_array_fget(v_args_3420_, v___x_3405_);
                                                lean_dec_ref(v_args_3420_);
                                                if lean_obj_tag(v___x_3459_) == 1 {
                                                    v_fvarId_3460_ = lean_ctor_get(v___x_3459_, 0);
                                                    lean_inc(v_fvarId_3460_);
                                                    lean_dec_ref_known(v___x_3459_, 1);
                                                    v_sizeFVar_3426_ = v_fvarId_3460_;
                                                    v___y_3427_ = v_a_3375_;
                                                    v___y_3428_ = v_a_3376_;
                                                    v___y_3429_ = v_a_3377_;
                                                    v___y_3430_ = v_a_3378_;
                                                    v___y_3431_ = v_a_3379_;
                                                    v___y_3432_ = v_a_3380_;
                                                    state = 5;
                                                    continue;
                                                } else {
                                                    lean_dec(v___x_3459_);
                                                    lean_dec(v_fvarId_3419_);
                                                    lean_dec_ref(v_k_3374_);
                                                    lean_dec_ref(v_decl_3373_);
                                                    state = 2;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v_pre_3417_, 2);
                                    lean_dec_ref_known(v_declName_3416_, 2);
                                    lean_dec_ref_known(v_value_3415_, 3);
                                    lean_dec(v_val_3414_);
                                    lean_dec_ref(v_k_3374_);
                                    lean_dec_ref(v_decl_3373_);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                lean_dec_ref_known(v_declName_3416_, 2);
                                lean_dec(v_pre_3417_);
                                lean_dec_ref_known(v_value_3415_, 3);
                                lean_dec(v_val_3414_);
                                lean_dec_ref(v_k_3374_);
                                lean_dec_ref(v_decl_3373_);
                                state = 2;
                                continue;
                            }
                        } else {
                            lean_dec(v_declName_3416_);
                            lean_dec_ref_known(v_value_3415_, 3);
                            lean_dec(v_val_3414_);
                            lean_dec_ref(v_k_3374_);
                            lean_dec_ref(v_decl_3373_);
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_value_3415_);
                        lean_dec(v_val_3414_);
                        lean_dec_ref(v_k_3374_);
                        lean_dec_ref(v_decl_3373_);
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3410_);
                    lean_dec_ref(v_k_3374_);
                    lean_dec_ref(v_decl_3373_);
                    v___x_3461_ = lean_box(0);
                    if v_isShared_3413_ == 0 {
                        lean_ctor_set(v___x_3412_, 0, v___x_3461_);
                        v___x_3463_ = v___x_3412_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
                        v___x_3463_ = v_reuseFailAlloc_3464_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3433_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                    v___x_3408_,
                    v_sizeFVar_3426_,
                    v___y_3430_,
                );
                lean_dec(v_sizeFVar_3426_);
                if lean_obj_tag(v___x_3433_) == 0 {
                    v_a_3434_ = lean_ctor_get(v___x_3433_, 0);
                    lean_inc(v_a_3434_);
                    lean_dec_ref_known(v___x_3433_, 1);
                    if lean_obj_tag(v_a_3434_) == 1 {
                        v_val_3435_ = lean_ctor_get(v_a_3434_, 0);
                        lean_inc(v_val_3435_);
                        lean_dec_ref_known(v_a_3434_, 1);
                        if lean_obj_tag(v_val_3435_) == 0 {
                            v_value_3436_ = lean_ctor_get(v_val_3435_, 0);
                            lean_inc_ref(v_value_3436_);
                            lean_dec_ref_known(v_val_3435_, 1);
                            if lean_obj_tag(v_value_3436_) == 0 {
                                v_val_3437_ = lean_ctor_get(v_value_3436_, 0);
                                lean_inc(v_val_3437_);
                                lean_dec_ref_known(v_value_3436_, 1);
                                v___x_3438_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain(v_fvarId_3419_, v_decl_3373_, v_k_3374_, v___x_3424_, v_val_3437_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_, v___y_3431_, v___y_3432_);
                                return v___x_3438_;
                            } else {
                                lean_dec_ref(v_value_3436_);
                                lean_dec(v_fvarId_3419_);
                                lean_dec_ref(v_k_3374_);
                                lean_dec_ref(v_decl_3373_);
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_3435_);
                            lean_dec(v_fvarId_3419_);
                            lean_dec_ref(v_k_3374_);
                            lean_dec_ref(v_decl_3373_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3434_);
                        lean_dec(v_fvarId_3419_);
                        lean_dec_ref(v_k_3374_);
                        lean_dec_ref(v_decl_3373_);
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_fvarId_3419_);
                    lean_dec_ref(v_k_3374_);
                    lean_dec_ref(v_decl_3373_);
                    v_a_3439_ = lean_ctor_get(v___x_3433_, 0);
                    v_isSharedCheck_3446_ = (!lean_is_exclusive(v___x_3433_)) as u8;
                    if v_isSharedCheck_3446_ == 0 {
                        v___x_3441_ = v___x_3433_;
                        v_isShared_3442_ = v_isSharedCheck_3446_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3439_);
                        lean_dec(v___x_3433_);
                        v___x_3441_ = lean_box(0);
                        v_isShared_3442_ = v_isSharedCheck_3446_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                if v_isShared_3442_ == 0 {
                    v___x_3444_ = v___x_3441_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3445_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3445_, 0, v_a_3439_);
                    v___x_3444_ = v_reuseFailAlloc_3445_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3444_;
            }
            8 => {
                return v___x_3463_;
            }
            9 => {
                if v_isShared_3469_ == 0 {
                    v___x_3471_ = v___x_3468_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3472_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3472_, 0, v_a_3466_);
                    v___x_3471_ = v_reuseFailAlloc_3472_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3471_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___boxed(
    mut v_decl_3474_: *mut LeanObject,
    mut v_k_3475_: *mut LeanObject,
    mut v_a_3476_: *mut LeanObject,
    mut v_a_3477_: *mut LeanObject,
    mut v_a_3478_: *mut LeanObject,
    mut v_a_3479_: *mut LeanObject,
    mut v_a_3480_: *mut LeanObject,
    mut v_a_3481_: *mut LeanObject,
    mut v_a_3482_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3483_: *mut LeanObject = core::ptr::null_mut();
    v_res_3483_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(
        v_decl_3474_,
        v_k_3475_,
        v_a_3476_,
        v_a_3477_,
        v_a_3478_,
        v_a_3479_,
        v_a_3480_,
        v_a_3481_,
    );
    lean_dec(v_a_3481_);
    lean_dec_ref(v_a_3480_);
    lean_dec(v_a_3479_);
    lean_dec_ref(v_a_3478_);
    lean_dec(v_a_3477_);
    lean_dec_ref(v_a_3476_);
    return v_res_3483_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3484_: *mut LeanObject = core::ptr::null_mut();
    v___x_3484_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_3484_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    v___x_3485_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0_once), _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__0);
    v___x_3486_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_3486_, 0, v___x_3485_);
    return v___x_3486_;
}
pub unsafe fn _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    v___x_3487_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1_once), _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__1);
    v___x_3488_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3488_, 0, v___x_3487_);
    lean_ctor_set(v___x_3488_, 1, v___x_3487_);
    return v___x_3488_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(
    mut v_env_3489_: *mut LeanObject,
    mut v___y_3490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3495_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_3497_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_3498_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3502_: u8 = 0;
    let mut v___x_3503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3506_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3510_: u8 = 0;
    let mut v_unused_3511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3492_ = lean_st_ref_take(v___y_3490_);
                v_nextMacroScope_3493_ = lean_ctor_get(v___x_3492_, 1);
                v_ngen_3494_ = lean_ctor_get(v___x_3492_, 2);
                v_auxDeclNGen_3495_ = lean_ctor_get(v___x_3492_, 3);
                v_traceState_3496_ = lean_ctor_get(v___x_3492_, 4);
                v_messages_3497_ = lean_ctor_get(v___x_3492_, 6);
                v_infoState_3498_ = lean_ctor_get(v___x_3492_, 7);
                v_snapshotTasks_3499_ = lean_ctor_get(v___x_3492_, 8);
                v_isSharedCheck_3510_ = (!lean_is_exclusive(v___x_3492_)) as u8;
                if v_isSharedCheck_3510_ == 0 {
                    v_unused_3511_ = lean_ctor_get(v___x_3492_, 5);
                    lean_dec(v_unused_3511_);
                    v_unused_3512_ = lean_ctor_get(v___x_3492_, 0);
                    lean_dec(v_unused_3512_);
                    v___x_3501_ = v___x_3492_;
                    v_isShared_3502_ = v_isSharedCheck_3510_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_3499_);
                    lean_inc(v_infoState_3498_);
                    lean_inc(v_messages_3497_);
                    lean_inc(v_traceState_3496_);
                    lean_inc(v_auxDeclNGen_3495_);
                    lean_inc(v_ngen_3494_);
                    lean_inc(v_nextMacroScope_3493_);
                    lean_dec(v___x_3492_);
                    v___x_3501_ = lean_box(0);
                    v_isShared_3502_ = v_isSharedCheck_3510_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3503_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2_once), _init_l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___closed__2);
                if v_isShared_3502_ == 0 {
                    lean_ctor_set(v___x_3501_, 5, v___x_3503_);
                    lean_ctor_set(v___x_3501_, 0, v_env_3489_);
                    v___x_3505_ = v___x_3501_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3509_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 0, v_env_3489_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 1, v_nextMacroScope_3493_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 2, v_ngen_3494_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 3, v_auxDeclNGen_3495_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 4, v_traceState_3496_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 5, v___x_3503_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 6, v_messages_3497_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 7, v_infoState_3498_);
                    lean_ctor_set(v_reuseFailAlloc_3509_, 8, v_snapshotTasks_3499_);
                    v___x_3505_ = v_reuseFailAlloc_3509_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3506_ = lean_st_ref_set(v___y_3490_, v___x_3505_);
                v___x_3507_ = lean_box(0);
                v___x_3508_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3508_, 0, v___x_3507_);
                return v___x_3508_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg___boxed(
    mut v_env_3513_: *mut LeanObject,
    mut v___y_3514_: *mut LeanObject,
    mut v___y_3515_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3516_: *mut LeanObject = core::ptr::null_mut();
    v_res_3516_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_3513_, v___y_3514_);
    lean_dec(v___y_3514_);
    return v_res_3516_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(
    mut v_env_3517_: *mut LeanObject,
    mut v___y_3518_: *mut LeanObject,
    mut v___y_3519_: *mut LeanObject,
    mut v___y_3520_: *mut LeanObject,
    mut v___y_3521_: *mut LeanObject,
    mut v___y_3522_: *mut LeanObject,
    mut v___y_3523_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3525_: *mut LeanObject = core::ptr::null_mut();
    v___x_3525_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v_env_3517_, v___y_3523_);
    return v___x_3525_;
}
pub unsafe fn l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___boxed(
    mut v_env_3526_: *mut LeanObject,
    mut v___y_3527_: *mut LeanObject,
    mut v___y_3528_: *mut LeanObject,
    mut v___y_3529_: *mut LeanObject,
    mut v___y_3530_: *mut LeanObject,
    mut v___y_3531_: *mut LeanObject,
    mut v___y_3532_: *mut LeanObject,
    mut v___y_3533_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3534_: *mut LeanObject = core::ptr::null_mut();
    v_res_3534_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0(v_env_3526_, v___y_3527_, v___y_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
    lean_dec(v___y_3532_);
    lean_dec_ref(v___y_3531_);
    lean_dec(v___y_3530_);
    lean_dec_ref(v___y_3529_);
    lean_dec(v___y_3528_);
    lean_dec_ref(v___y_3527_);
    return v_res_3534_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(
    mut v_sz_3535_: usize,
    mut v_i_3536_: usize,
    mut v_bs_3537_: *mut LeanObject,
    mut v___y_3538_: u8,
    mut v___y_3539_: *mut LeanObject,
    mut v___y_3540_: *mut LeanObject,
    mut v___y_3541_: *mut LeanObject,
    mut v___y_3542_: *mut LeanObject,
    mut v___y_3543_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3545_: u8 = 0;
    let mut v___x_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3547_: u8 = 0;
    let mut v_v_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: usize = 0;
    let mut v___x_3554_: usize = 0;
    let mut v___x_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3560_: u8 = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3545_ = lean_usize_dec_lt(v_i_3536_, v_sz_3535_);
                if v___x_3545_ == 0 {
                    v___x_3546_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3546_, 0, v_bs_3537_);
                    return v___x_3546_;
                } else {
                    v___x_3547_ = 0;
                    v_v_3548_ = lean_array_uget_borrowed(v_bs_3537_, v_i_3536_);
                    lean_inc(v_v_3548_);
                    v___x_3549_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(
                        v___x_3547_,
                        v_v_3548_,
                        v___y_3538_,
                        v___y_3539_,
                        v___y_3540_,
                        v___y_3541_,
                        v___y_3542_,
                        v___y_3543_,
                    );
                    if lean_obj_tag(v___x_3549_) == 0 {
                        v_a_3550_ = lean_ctor_get(v___x_3549_, 0);
                        lean_inc(v_a_3550_);
                        lean_dec_ref_known(v___x_3549_, 1);
                        v___x_3551_ = lean_unsigned_to_nat(0);
                        v_bs_x27_3552_ = lean_array_uset(v_bs_3537_, v_i_3536_, v___x_3551_);
                        v___x_3553_ = 1usize;
                        v___x_3554_ = lean_usize_add(v_i_3536_, v___x_3553_);
                        v___x_3555_ = lean_array_uset(v_bs_x27_3552_, v_i_3536_, v_a_3550_);
                        v_i_3536_ = v___x_3554_;
                        v_bs_3537_ = v___x_3555_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_3537_);
                        v_a_3557_ = lean_ctor_get(v___x_3549_, 0);
                        v_isSharedCheck_3564_ = (!lean_is_exclusive(v___x_3549_)) as u8;
                        if v_isSharedCheck_3564_ == 0 {
                            v___x_3559_ = v___x_3549_;
                            v_isShared_3560_ = v_isSharedCheck_3564_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3557_);
                            lean_dec(v___x_3549_);
                            v___x_3559_ = lean_box(0);
                            v_isShared_3560_ = v_isSharedCheck_3564_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3560_ == 0 {
                    v___x_3562_ = v___x_3559_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
                    v___x_3562_ = v_reuseFailAlloc_3563_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3562_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1___boxed(
    mut v_sz_3565_: *mut LeanObject,
    mut v_i_3566_: *mut LeanObject,
    mut v_bs_3567_: *mut LeanObject,
    mut v___y_3568_: *mut LeanObject,
    mut v___y_3569_: *mut LeanObject,
    mut v___y_3570_: *mut LeanObject,
    mut v___y_3571_: *mut LeanObject,
    mut v___y_3572_: *mut LeanObject,
    mut v___y_3573_: *mut LeanObject,
    mut v___y_3574_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3575_: usize = 0;
    let mut v_i_boxed_3576_: usize = 0;
    let mut v___y_8210__boxed_3577_: u8 = 0;
    let mut v_res_3578_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3575_ = lean_unbox_usize(v_sz_3565_);
    lean_dec(v_sz_3565_);
    v_i_boxed_3576_ = lean_unbox_usize(v_i_3566_);
    lean_dec(v_i_3566_);
    v___y_8210__boxed_3577_ = (lean_unbox(v___y_3568_) as u8);
    v_res_3578_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_boxed_3575_, v_i_boxed_3576_, v_bs_3567_, v___y_8210__boxed_3577_, v___y_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
    lean_dec(v___y_3573_);
    lean_dec_ref(v___y_3572_);
    lean_dec(v___y_3571_);
    lean_dec_ref(v___y_3570_);
    lean_dec(v___y_3569_);
    return v_res_3578_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1()
-> *mut LeanObject {
    let mut v___x_3581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    v___x_3581_ = lean_box(0);
    v___x_3582_ = lean_unsigned_to_nat(16);
    v___x_3583_ = lean_mk_array(v___x_3582_, v___x_3581_);
    return v___x_3583_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2()
-> *mut LeanObject {
    let mut v___x_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3586_: *mut LeanObject = core::ptr::null_mut();
    v___x_3584_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1_once), _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__1);
    v___x_3585_ = lean_unsigned_to_nat(0);
    v___x_3586_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3586_, 0, v___x_3585_);
    lean_ctor_set(v___x_3586_, 1, v___x_3584_);
    return v___x_3586_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3()
-> *mut LeanObject {
    let mut v___x_3587_: u8 = 0;
    let mut v___x_3588_: *mut LeanObject = core::ptr::null_mut();
    v___x_3587_ = 0;
    v___x_3588_ = l_Lean_Compiler_LCNF_instInhabitedCodeDecl_default(v___x_3587_);
    return v___x_3588_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(
    mut v_decl_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
    mut v_a_3600_: *mut LeanObject,
    mut v_a_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3611_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: u8 = 0;
    let mut v___x_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3618_: u8 = 0;
    let mut v_a_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut v_unused_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3646_: u8 = 0;
    let mut v___x_3648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3650_: u8 = 0;
    let mut v___x_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_baseName_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3662_: u8 = 0;
    let mut v___x_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3664_: u8 = 0;
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3670_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3673_: u8 = 0;
    let mut v___x_3674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarDecisionCache_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3679_: u8 = 0;
    let mut v___x_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3683_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3688_: u8 = 0;
    let mut v_isSharedCheck_3689_: u8 = 0;
    let mut v_unused_3690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3694_: u8 = 0;
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3698_: u8 = 0;
    let mut v_reuseFailAlloc_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut v_unused_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3702_: usize = 0;
    let mut v___x_3703_: usize = 0;
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3705_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3710_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3711_: u8 = 0;
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3715_: u8 = 0;
    let mut v_a_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3719_: u8 = 0;
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3605_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__0;
                v___x_3606_ = lean_st_mk_ref(v___x_3605_);
                v_type_3607_ = lean_ctor_get(v_decl_3597_, 2);
                lean_inc_ref(v_type_3607_);
                v_value_3608_ = lean_ctor_get(v_decl_3597_, 3);
                lean_inc(v_value_3608_);
                v___x_3609_ = l_Lean_Compiler_LCNF_ExtractClosed_extractLetValue(
                    v_value_3608_,
                    v___x_3606_,
                    v_a_3600_,
                    v_a_3601_,
                    v_a_3602_,
                    v_a_3603_,
                );
                if lean_obj_tag(v___x_3609_) == 0 {
                    lean_dec_ref_known(v___x_3609_, 1);
                    v___x_3610_ = lean_st_ref_get(v___x_3606_);
                    lean_dec(v___x_3606_);
                    v___x_3611_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
                    v___x_3612_ = lean_st_mk_ref(v___x_3611_);
                    v___x_3613_ = 0;
                    v___x_3614_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3614_, 0, v_decl_3597_);
                    v___x_3615_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3_once), _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__3);
                    v___x_3616_ = l_Array_reverse___redArg(v___x_3610_);
                    v___x_3617_ = lean_array_push(v___x_3616_, v___x_3614_);
                    v___x_3618_ = 0;
                    v_sz_3702_ = lean_array_size(v___x_3617_);
                    v___x_3703_ = 0usize;
                    v___x_3704_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__1(v_sz_3702_, v___x_3703_, v___x_3617_, v___x_3618_, v___x_3612_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
                    if lean_obj_tag(v___x_3704_) == 0 {
                        v_a_3705_ = lean_ctor_get(v___x_3704_, 0);
                        lean_inc(v_a_3705_);
                        lean_dec_ref_known(v___x_3704_, 1);
                        v___x_3706_ = lean_st_ref_get(v___x_3612_);
                        lean_dec(v___x_3612_);
                        lean_dec(v___x_3706_);
                        v_a_3620_ = v_a_3705_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3612_);
                        if lean_obj_tag(v___x_3704_) == 0 {
                            v_a_3707_ = lean_ctor_get(v___x_3704_, 0);
                            lean_inc(v_a_3707_);
                            lean_dec_ref_known(v___x_3704_, 1);
                            v_a_3620_ = v_a_3707_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_type_3607_);
                            v_a_3708_ = lean_ctor_get(v___x_3704_, 0);
                            v_isSharedCheck_3715_ = (!lean_is_exclusive(v___x_3704_)) as u8;
                            if v_isSharedCheck_3715_ == 0 {
                                v___x_3710_ = v___x_3704_;
                                v_isShared_3711_ = v_isSharedCheck_3715_;
                                state = 14;
                                continue;
                            } else {
                                lean_inc(v_a_3708_);
                                lean_dec(v___x_3704_);
                                v___x_3710_ = lean_box(0);
                                v_isShared_3711_ = v_isSharedCheck_3715_;
                                state = 14;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_type_3607_);
                    lean_dec(v___x_3606_);
                    lean_dec_ref(v_decl_3597_);
                    v_a_3716_ = lean_ctor_get(v___x_3609_, 0);
                    v_isSharedCheck_3723_ = (!lean_is_exclusive(v___x_3609_)) as u8;
                    if v_isSharedCheck_3723_ == 0 {
                        v___x_3718_ = v___x_3609_;
                        v_isShared_3719_ = v_isSharedCheck_3723_;
                        state = 16;
                        continue;
                    } else {
                        lean_inc(v_a_3716_);
                        lean_dec(v___x_3609_);
                        v___x_3718_ = lean_box(0);
                        v_isShared_3719_ = v_isSharedCheck_3723_;
                        state = 16;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3621_ = lean_st_ref_get(v_a_3603_);
                v_env_3622_ = lean_ctor_get(v___x_3621_, 0);
                lean_inc_ref_n(v_env_3622_, 2);
                lean_dec(v___x_3621_);
                v___x_3623_ = lean_array_get_size(v_a_3620_);
                v___x_3624_ = lean_unsigned_to_nat(1);
                v___x_3625_ = lean_nat_sub(v___x_3623_, v___x_3624_);
                v___x_3626_ = lean_array_get_borrowed(v___x_3615_, v_a_3620_, v___x_3625_);
                lean_dec(v___x_3625_);
                v___x_3627_ = l_Lean_Compiler_LCNF_CodeDecl_fvarId___redArg(v___x_3626_);
                v___x_3628_ = lean_alloc_ctor(5, 1, (0) as u32);
                lean_ctor_set(v___x_3628_, 0, v___x_3627_);
                v___x_3629_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3613_, v_a_3620_, v___x_3628_);
                lean_dec_ref(v_a_3620_);
                v___x_3630_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__4;
                lean_inc_ref(v___x_3629_);
                v___x_3631_ =
                    l_Lean_Compiler_LCNF_Code_toExpr(v___x_3613_, v___x_3629_, v___x_3630_);
                v___x_3632_ = l_Lean_getClosedTermName_x3f(v_env_3622_, v___x_3631_);
                if lean_obj_tag(v___x_3632_) == 1 {
                    lean_dec_ref(v___x_3631_);
                    lean_dec_ref(v_env_3622_);
                    lean_dec_ref(v_type_3607_);
                    v_val_3633_ = lean_ctor_get(v___x_3632_, 0);
                    lean_inc(v_val_3633_);
                    lean_dec_ref_known(v___x_3632_, 1);
                    v___x_3634_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                        v___x_3613_,
                        v___x_3629_,
                        v_a_3601_,
                    );
                    lean_dec_ref(v___x_3629_);
                    if lean_obj_tag(v___x_3634_) == 0 {
                        v_isSharedCheck_3641_ = (!lean_is_exclusive(v___x_3634_)) as u8;
                        if v_isSharedCheck_3641_ == 0 {
                            v_unused_3642_ = lean_ctor_get(v___x_3634_, 0);
                            lean_dec(v_unused_3642_);
                            v___x_3636_ = v___x_3634_;
                            v_isShared_3637_ = v_isSharedCheck_3641_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3634_);
                            v___x_3636_ = lean_box(0);
                            v_isShared_3637_ = v_isSharedCheck_3641_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_val_3633_);
                        v_a_3643_ = lean_ctor_get(v___x_3634_, 0);
                        v_isSharedCheck_3650_ = (!lean_is_exclusive(v___x_3634_)) as u8;
                        if v_isSharedCheck_3650_ == 0 {
                            v___x_3645_ = v___x_3634_;
                            v_isShared_3646_ = v_isSharedCheck_3650_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3643_);
                            lean_dec(v___x_3634_);
                            v___x_3645_ = lean_box(0);
                            v_isShared_3646_ = v_isSharedCheck_3650_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_3632_);
                    v___x_3651_ = lean_st_ref_get(v_a_3599_);
                    v_baseName_3652_ = lean_ctor_get(v_a_3598_, 0);
                    v_decls_3653_ = lean_ctor_get(v___x_3651_, 0);
                    lean_inc_ref(v_decls_3653_);
                    lean_dec(v___x_3651_);
                    v___x_3654_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__6;
                    v___x_3655_ = lean_array_get_size(v_decls_3653_);
                    lean_dec_ref(v_decls_3653_);
                    v___x_3656_ = lean_name_append_index_after(v___x_3654_, v___x_3655_);
                    lean_inc(v_baseName_3652_);
                    v___x_3657_ = l_Lean_Name_append(v_baseName_3652_, v___x_3656_);
                    lean_inc(v___x_3657_);
                    v___x_3658_ = l_Lean_cacheClosedTermName(v_env_3622_, v___x_3631_, v___x_3657_);
                    v___x_3659_ = l_Lean_setEnv___at___00__private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction_spec__0___redArg(v___x_3658_, v_a_3603_);
                    v_isSharedCheck_3700_ = (!lean_is_exclusive(v___x_3659_)) as u8;
                    if v_isSharedCheck_3700_ == 0 {
                        v_unused_3701_ = lean_ctor_get(v___x_3659_, 0);
                        lean_dec(v_unused_3701_);
                        v___x_3661_ = v___x_3659_;
                        v_isShared_3662_ = v_isSharedCheck_3700_;
                        state = 6;
                        continue;
                    } else {
                        lean_dec(v___x_3659_);
                        v___x_3661_ = lean_box(0);
                        v_isShared_3662_ = v_isSharedCheck_3700_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3637_ == 0 {
                    lean_ctor_set(v___x_3636_, 0, v_val_3633_);
                    v___x_3639_ = v___x_3636_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3640_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_val_3633_);
                    v___x_3639_ = v_reuseFailAlloc_3640_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3639_;
            }
            4 => {
                if v_isShared_3646_ == 0 {
                    v___x_3648_ = v___x_3645_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3649_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3649_, 0, v_a_3643_);
                    v___x_3648_ = v_reuseFailAlloc_3649_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3648_;
            }
            6 => {
                v___x_3663_ = lean_box(0);
                v___x_3664_ = 1;
                lean_inc(v___x_3657_);
                v___x_3665_ = lean_alloc_ctor(0, 4, (1) as u32);
                lean_ctor_set(v___x_3665_, 0, v___x_3657_);
                lean_ctor_set(v___x_3665_, 1, v___x_3663_);
                lean_ctor_set(v___x_3665_, 2, v_type_3607_);
                lean_ctor_set(v___x_3665_, 3, v___x_3630_);
                lean_ctor_set_uint8(
                    v___x_3665_,
                    (core::mem::size_of::<*mut LeanObject>() * 4) as u32,
                    v___x_3664_,
                );
                if v_isShared_3662_ == 0 {
                    lean_ctor_set(v___x_3661_, 0, v___x_3629_);
                    v___x_3667_ = v___x_3661_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3699_, 0, v___x_3629_);
                    v___x_3667_ = v_reuseFailAlloc_3699_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3668_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__7;
                v___x_3669_ = lean_alloc_ctor(0, 3, (1) as u32);
                lean_ctor_set(v___x_3669_, 0, v___x_3665_);
                lean_ctor_set(v___x_3669_, 1, v___x_3667_);
                lean_ctor_set(v___x_3669_, 2, v___x_3668_);
                lean_ctor_set_uint8(
                    v___x_3669_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_3618_,
                );
                lean_inc_ref(v___x_3669_);
                v___x_3670_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_3669_, v_a_3603_);
                if lean_obj_tag(v___x_3670_) == 0 {
                    v_isSharedCheck_3689_ = (!lean_is_exclusive(v___x_3670_)) as u8;
                    if v_isSharedCheck_3689_ == 0 {
                        v_unused_3690_ = lean_ctor_get(v___x_3670_, 0);
                        lean_dec(v_unused_3690_);
                        v___x_3672_ = v___x_3670_;
                        v_isShared_3673_ = v_isSharedCheck_3689_;
                        state = 8;
                        continue;
                    } else {
                        lean_dec(v___x_3670_);
                        v___x_3672_ = lean_box(0);
                        v_isShared_3673_ = v_isSharedCheck_3689_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v___x_3669_, 3);
                    lean_dec(v___x_3657_);
                    v_a_3691_ = lean_ctor_get(v___x_3670_, 0);
                    v_isSharedCheck_3698_ = (!lean_is_exclusive(v___x_3670_)) as u8;
                    if v_isSharedCheck_3698_ == 0 {
                        v___x_3693_ = v___x_3670_;
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_3691_);
                        lean_dec(v___x_3670_);
                        v___x_3693_ = lean_box(0);
                        v_isShared_3694_ = v_isSharedCheck_3698_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                v___x_3674_ = lean_st_ref_take(v_a_3599_);
                v_decls_3675_ = lean_ctor_get(v___x_3674_, 0);
                v_fvarDecisionCache_3676_ = lean_ctor_get(v___x_3674_, 1);
                v_isSharedCheck_3688_ = (!lean_is_exclusive(v___x_3674_)) as u8;
                if v_isSharedCheck_3688_ == 0 {
                    v___x_3678_ = v___x_3674_;
                    v_isShared_3679_ = v_isSharedCheck_3688_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_fvarDecisionCache_3676_);
                    lean_inc(v_decls_3675_);
                    lean_dec(v___x_3674_);
                    v___x_3678_ = lean_box(0);
                    v_isShared_3679_ = v_isSharedCheck_3688_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_3680_ = lean_array_push(v_decls_3675_, v___x_3669_);
                if v_isShared_3679_ == 0 {
                    lean_ctor_set(v___x_3678_, 0, v___x_3680_);
                    v___x_3682_ = v___x_3678_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3687_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3687_, 0, v___x_3680_);
                    lean_ctor_set(v_reuseFailAlloc_3687_, 1, v_fvarDecisionCache_3676_);
                    v___x_3682_ = v_reuseFailAlloc_3687_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3683_ = lean_st_ref_set(v_a_3599_, v___x_3682_);
                if v_isShared_3673_ == 0 {
                    lean_ctor_set(v___x_3672_, 0, v___x_3657_);
                    v___x_3685_ = v___x_3672_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3686_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3686_, 0, v___x_3657_);
                    v___x_3685_ = v_reuseFailAlloc_3686_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3685_;
            }
            12 => {
                if v_isShared_3694_ == 0 {
                    v___x_3696_ = v___x_3693_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3697_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3697_, 0, v_a_3691_);
                    v___x_3696_ = v_reuseFailAlloc_3697_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3696_;
            }
            14 => {
                if v_isShared_3711_ == 0 {
                    v___x_3713_ = v___x_3710_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 0, v_a_3708_);
                    v___x_3713_ = v_reuseFailAlloc_3714_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3713_;
            }
            16 => {
                if v_isShared_3719_ == 0 {
                    v___x_3721_ = v___x_3718_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_3722_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3722_, 0, v_a_3716_);
                    v___x_3721_ = v_reuseFailAlloc_3722_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_3721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___boxed(
    mut v_decl_3724_: *mut LeanObject,
    mut v_a_3725_: *mut LeanObject,
    mut v_a_3726_: *mut LeanObject,
    mut v_a_3727_: *mut LeanObject,
    mut v_a_3728_: *mut LeanObject,
    mut v_a_3729_: *mut LeanObject,
    mut v_a_3730_: *mut LeanObject,
    mut v_a_3731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3732_: *mut LeanObject = core::ptr::null_mut();
    v_res_3732_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_);
    lean_dec(v_a_3730_);
    lean_dec_ref(v_a_3729_);
    lean_dec(v_a_3728_);
    lean_dec_ref(v_a_3727_);
    lean_dec(v_a_3726_);
    lean_dec_ref(v_a_3725_);
    return v_res_3732_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3733_: u8 = 0;
    let mut v___x_3734_: *mut LeanObject = core::ptr::null_mut();
    v___x_3733_ = 0;
    v___x_3734_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_3733_);
    return v___x_3734_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(
    mut v_msg_3735_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut LeanObject = core::ptr::null_mut();
    v___x_3736_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0___closed__0,
    );
    v___x_3737_ = lean_panic_fn_borrowed(v___x_3736_, v_msg_3735_);
    return v___x_3737_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3() -> *mut LeanObject {
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    v___x_3741_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__2;
    v___x_3742_ = lean_unsigned_to_nat(9);
    v___x_3743_ = lean_unsigned_to_nat(641);
    v___x_3744_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__1;
    v___x_3745_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__0;
    v___x_3746_ = l_mkPanicMessageWithDecl(
        v___x_3745_,
        v___x_3744_,
        v___x_3743_,
        v___x_3742_,
        v___x_3741_,
    );
    return v___x_3746_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
    mut v_code_3749_: *mut LeanObject,
    mut v_a_3750_: *mut LeanObject,
    mut v_a_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
    mut v_a_3754_: *mut LeanObject,
    mut v_a_3755_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3760_: u8 = 0;
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3763_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3765_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3767_: u8 = 0;
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3785_: u8 = 0;
    let mut v___x_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3792_: usize = 0;
    let mut v___x_3793_: usize = 0;
    let mut v___x_3794_: u8 = 0;
    let mut v___x_3795_: usize = 0;
    let mut v___x_3796_: usize = 0;
    let mut v___x_3797_: u8 = 0;
    let mut v_a_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: usize = 0;
    let mut v___x_3802_: usize = 0;
    let mut v___x_3803_: u8 = 0;
    let mut v___x_3804_: usize = 0;
    let mut v___x_3805_: usize = 0;
    let mut v___x_3806_: u8 = 0;
    let mut v___x_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3809_: u8 = 0;
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3815_: u8 = 0;
    let mut v_unused_3816_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3817_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3820_: u8 = 0;
    let mut v___x_3822_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3824_: u8 = 0;
    let mut v___y_3826_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3828_: u8 = 0;
    let mut v___x_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3833_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3835_: u8 = 0;
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3842_: u8 = 0;
    let mut v___x_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3844_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3849_: u8 = 0;
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3854_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3856_: u8 = 0;
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: u8 = 0;
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3867_: u8 = 0;
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3872_: u8 = 0;
    let mut v_unused_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3878_: u8 = 0;
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3881_: u8 = 0;
    let mut v___x_3883_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3886_: u8 = 0;
    let mut v_unused_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3892_: u8 = 0;
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3895_: u8 = 0;
    let mut v___x_3897_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3900_: u8 = 0;
    let mut v_unused_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: u8 = 0;
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: usize = 0;
    let mut v___x_3928_: usize = 0;
    let mut v___x_3929_: u8 = 0;
    let mut v___x_3930_: usize = 0;
    let mut v___x_3931_: usize = 0;
    let mut v___x_3932_: u8 = 0;
    let mut v_a_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3936_: u8 = 0;
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3940_: u8 = 0;
    let mut v_a_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3944_: u8 = 0;
    let mut v___x_3946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3948_: u8 = 0;
    let mut v___x_3949_: u8 = 0;
    let mut v___x_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: u8 = 0;
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3955_: usize = 0;
    let mut v___x_3956_: usize = 0;
    let mut v___x_3957_: u8 = 0;
    let mut v___x_3958_: usize = 0;
    let mut v___x_3959_: u8 = 0;
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: u8 = 0;
    let mut v___x_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3964_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3970_: usize = 0;
    let mut v___x_3971_: usize = 0;
    let mut v___x_3972_: u8 = 0;
    let mut v___x_3973_: usize = 0;
    let mut v___x_3974_: usize = 0;
    let mut v___x_3975_: u8 = 0;
    let mut v_a_3976_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3978_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3979_: u8 = 0;
    let mut v___x_3981_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3982_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3983_: u8 = 0;
    let mut v_a_3984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3986_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3987_: u8 = 0;
    let mut v___x_3989_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3990_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3991_: u8 = 0;
    let mut v_a_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3995_: u8 = 0;
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3999_: u8 = 0;
    let mut v_a_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4003_: u8 = 0;
    let mut v___x_4005_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4006_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4007_: u8 = 0;
    let mut v_declName_4008_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4009_: *mut LeanObject = core::ptr::null_mut();
    let mut v_pre_4010_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_4011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4012_: *mut LeanObject = core::ptr::null_mut();
    let mut v_str_4013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4015_: u8 = 0;
    let mut v___y_4017_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4018_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4020_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v_val_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4033_: u8 = 0;
    let mut v___x_4034_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: usize = 0;
    let mut v___x_4043_: usize = 0;
    let mut v___x_4044_: u8 = 0;
    let mut v___x_4045_: usize = 0;
    let mut v___x_4046_: usize = 0;
    let mut v___x_4047_: u8 = 0;
    let mut v_a_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4051_: u8 = 0;
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4055_: u8 = 0;
    let mut v_reuseFailAlloc_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v_isSharedCheck_4065_: u8 = 0;
    let mut v_unused_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4067_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: u8 = 0;
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: usize = 0;
    let mut v___x_4075_: usize = 0;
    let mut v___x_4076_: u8 = 0;
    let mut v___x_4077_: usize = 0;
    let mut v___x_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: u8 = 0;
    let mut v___x_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: usize = 0;
    let mut v___x_4090_: usize = 0;
    let mut v___x_4091_: u8 = 0;
    let mut v___x_4092_: usize = 0;
    let mut v___x_4093_: usize = 0;
    let mut v___x_4094_: u8 = 0;
    let mut v_a_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4098_: u8 = 0;
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4102_: u8 = 0;
    let mut v_a_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4106_: u8 = 0;
    let mut v___x_4108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4110_: u8 = 0;
    let mut v_a_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4114_: u8 = 0;
    let mut v___x_4116_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4118_: u8 = 0;
    let mut v_a_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4122_: u8 = 0;
    let mut v___x_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4126_: u8 = 0;
    let mut v_sizeId_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: u8 = 0;
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4141_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4142_: u8 = 0;
    let mut v_val_4143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4144_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4145_: u8 = 0;
    let mut v___x_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: usize = 0;
    let mut v___x_4149_: usize = 0;
    let mut v___x_4150_: u8 = 0;
    let mut v___x_4151_: usize = 0;
    let mut v___x_4152_: u8 = 0;
    let mut v___x_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: usize = 0;
    let mut v___x_4164_: usize = 0;
    let mut v___x_4165_: u8 = 0;
    let mut v___x_4166_: usize = 0;
    let mut v___x_4167_: usize = 0;
    let mut v___x_4168_: u8 = 0;
    let mut v_a_4169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4172_: u8 = 0;
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4176_: u8 = 0;
    let mut v_reuseFailAlloc_4177_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4181_: u8 = 0;
    let mut v___x_4183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4185_: u8 = 0;
    let mut v_isSharedCheck_4186_: u8 = 0;
    let mut v_unused_4187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4193_: u8 = 0;
    let mut v___x_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4197_: u8 = 0;
    let mut v___x_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: u8 = 0;
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: u8 = 0;
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: u8 = 0;
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4210_: u8 = 0;
    let mut v___x_4211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_4213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_4214_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4215_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_4216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_4217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_4218_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_4219_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_4220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_4221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_4222_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4225_: u8 = 0;
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4231_: u8 = 0;
    let mut v___x_4232_: usize = 0;
    let mut v___x_4233_: usize = 0;
    let mut v___x_4234_: u8 = 0;
    let mut v___x_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4237_: u8 = 0;
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4247_: u8 = 0;
    let mut v_unused_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4252_: u8 = 0;
    let mut v_a_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4255_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4256_: u8 = 0;
    let mut v___x_4258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4260_: u8 = 0;
    let mut v_isSharedCheck_4261_: u8 = 0;
    let mut v___x_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_3749_) {
                0 => {
                    v_decl_3860_ = lean_ctor_get(v_code_3749_, 0);
                    v_k_3861_ = lean_ctor_get(v_code_3749_, 1);
                    v_value_3904_ = lean_ctor_get(v_decl_3860_, 3);
                    lean_inc(v_value_3904_);
                    if lean_obj_tag(v_value_3904_) == 3 {
                        v_declName_4008_ = lean_ctor_get(v_value_3904_, 0);
                        if lean_obj_tag(v_declName_4008_) == 1 {
                            v_pre_4009_ = lean_ctor_get(v_declName_4008_, 0);
                            if lean_obj_tag(v_pre_4009_) == 1 {
                                v_pre_4010_ = lean_ctor_get(v_pre_4009_, 0);
                                if lean_obj_tag(v_pre_4010_) == 0 {
                                    v_args_4011_ = lean_ctor_get(v_value_3904_, 2);
                                    v_str_4012_ = lean_ctor_get(v_declName_4008_, 1);
                                    v_str_4013_ = lean_ctor_get(v_pre_4009_, 1);
                                    v___x_4014_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral_identifyChain___closed__0;
                                    v___x_4015_ = lean_string_dec_eq(v_str_4013_, v___x_4014_);
                                    if v___x_4015_ == 0 {
                                        v___y_3906_ = v_a_3750_;
                                        v___y_3907_ = v_a_3751_;
                                        v___y_3908_ = v_a_3752_;
                                        v___y_3909_ = v_a_3753_;
                                        v___y_3910_ = v_a_3754_;
                                        v___y_3911_ = v_a_3755_;
                                        state = 22;
                                        continue;
                                    } else {
                                        v___x_4198_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__0;
                                        v___x_4199_ = lean_string_dec_eq(v_str_4012_, v___x_4198_);
                                        if v___x_4199_ == 0 {
                                            v___x_4200_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral___closed__1;
                                            v___x_4201_ =
                                                lean_string_dec_eq(v_str_4012_, v___x_4200_);
                                            if v___x_4201_ == 0 {
                                                v___y_3906_ = v_a_3750_;
                                                v___y_3907_ = v_a_3751_;
                                                v___y_3908_ = v_a_3752_;
                                                v___y_3909_ = v_a_3753_;
                                                v___y_3910_ = v_a_3754_;
                                                v___y_3911_ = v_a_3755_;
                                                state = 22;
                                                continue;
                                            } else {
                                                v___x_4202_ = lean_array_get_size(v_args_4011_);
                                                v___x_4203_ = lean_unsigned_to_nat(2);
                                                v___x_4204_ =
                                                    lean_nat_dec_eq(v___x_4202_, v___x_4203_);
                                                if v___x_4204_ == 0 {
                                                    v___y_3906_ = v_a_3750_;
                                                    v___y_3907_ = v_a_3751_;
                                                    v___y_3908_ = v_a_3752_;
                                                    v___y_3909_ = v_a_3753_;
                                                    v___y_3910_ = v_a_3754_;
                                                    v___y_3911_ = v_a_3755_;
                                                    state = 22;
                                                    continue;
                                                } else {
                                                    v___x_4205_ = lean_unsigned_to_nat(1);
                                                    v___x_4206_ = lean_array_fget_borrowed(
                                                        v_args_4011_,
                                                        v___x_4205_,
                                                    );
                                                    if lean_obj_tag(v___x_4206_) == 1 {
                                                        v_fvarId_4207_ =
                                                            lean_ctor_get(v___x_4206_, 0);
                                                        lean_inc(v_fvarId_4207_);
                                                        v_sizeId_4128_ = v_fvarId_4207_;
                                                        v___y_4129_ = v_a_3750_;
                                                        v___y_4130_ = v_a_3751_;
                                                        v___y_4131_ = v_a_3752_;
                                                        v___y_4132_ = v_a_3753_;
                                                        v___y_4133_ = v_a_3754_;
                                                        v___y_4134_ = v_a_3755_;
                                                        state = 50;
                                                        continue;
                                                    } else {
                                                        v___y_3906_ = v_a_3750_;
                                                        v___y_3907_ = v_a_3751_;
                                                        v___y_3908_ = v_a_3752_;
                                                        v___y_3909_ = v_a_3753_;
                                                        v___y_3910_ = v_a_3754_;
                                                        v___y_3911_ = v_a_3755_;
                                                        state = 22;
                                                        continue;
                                                    }
                                                }
                                            }
                                        } else {
                                            v___x_4208_ = lean_array_get_size(v_args_4011_);
                                            v___x_4209_ = lean_unsigned_to_nat(2);
                                            v___x_4210_ = lean_nat_dec_eq(v___x_4208_, v___x_4209_);
                                            if v___x_4210_ == 0 {
                                                v___y_3906_ = v_a_3750_;
                                                v___y_3907_ = v_a_3751_;
                                                v___y_3908_ = v_a_3752_;
                                                v___y_3909_ = v_a_3753_;
                                                v___y_3910_ = v_a_3754_;
                                                v___y_3911_ = v_a_3755_;
                                                state = 22;
                                                continue;
                                            } else {
                                                v___x_4211_ = lean_unsigned_to_nat(1);
                                                v___x_4212_ = lean_array_fget_borrowed(
                                                    v_args_4011_,
                                                    v___x_4211_,
                                                );
                                                if lean_obj_tag(v___x_4212_) == 1 {
                                                    v_fvarId_4213_ = lean_ctor_get(v___x_4212_, 0);
                                                    lean_inc(v_fvarId_4213_);
                                                    v_sizeId_4128_ = v_fvarId_4213_;
                                                    v___y_4129_ = v_a_3750_;
                                                    v___y_4130_ = v_a_3751_;
                                                    v___y_4131_ = v_a_3752_;
                                                    v___y_4132_ = v_a_3753_;
                                                    v___y_4133_ = v_a_3754_;
                                                    v___y_4134_ = v_a_3755_;
                                                    state = 50;
                                                    continue;
                                                } else {
                                                    v___y_3906_ = v_a_3750_;
                                                    v___y_3907_ = v_a_3751_;
                                                    v___y_3908_ = v_a_3752_;
                                                    v___y_3909_ = v_a_3753_;
                                                    v___y_3910_ = v_a_3754_;
                                                    v___y_3911_ = v_a_3755_;
                                                    state = 22;
                                                    continue;
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    v___y_3906_ = v_a_3750_;
                                    v___y_3907_ = v_a_3751_;
                                    v___y_3908_ = v_a_3752_;
                                    v___y_3909_ = v_a_3753_;
                                    v___y_3910_ = v_a_3754_;
                                    v___y_3911_ = v_a_3755_;
                                    state = 22;
                                    continue;
                                }
                            } else {
                                v___y_3906_ = v_a_3750_;
                                v___y_3907_ = v_a_3751_;
                                v___y_3908_ = v_a_3752_;
                                v___y_3909_ = v_a_3753_;
                                v___y_3910_ = v_a_3754_;
                                v___y_3911_ = v_a_3755_;
                                state = 22;
                                continue;
                            }
                        } else {
                            v___y_3906_ = v_a_3750_;
                            v___y_3907_ = v_a_3751_;
                            v___y_3908_ = v_a_3752_;
                            v___y_3909_ = v_a_3753_;
                            v___y_3910_ = v_a_3754_;
                            v___y_3911_ = v_a_3755_;
                            state = 22;
                            continue;
                        }
                    } else {
                        v___y_3906_ = v_a_3750_;
                        v___y_3907_ = v_a_3751_;
                        v___y_3908_ = v_a_3752_;
                        v___y_3909_ = v_a_3753_;
                        v___y_3910_ = v_a_3754_;
                        v___y_3911_ = v_a_3755_;
                        state = 22;
                        continue;
                    }
                }
                1 => {
                    v_decl_4214_ = lean_ctor_get(v_code_3749_, 0);
                    v_k_4215_ = lean_ctor_get(v_code_3749_, 1);
                    lean_inc_ref(v_k_4215_);
                    lean_inc_ref(v_decl_4214_);
                    v_decl_3772_ = v_decl_4214_;
                    v_k_3773_ = v_k_4215_;
                    v___y_3774_ = v_a_3750_;
                    v___y_3775_ = v_a_3751_;
                    v___y_3776_ = v_a_3752_;
                    v___y_3777_ = v_a_3753_;
                    v___y_3778_ = v_a_3754_;
                    v___y_3779_ = v_a_3755_;
                    state = 3;
                    continue;
                }
                2 => {
                    v_decl_4216_ = lean_ctor_get(v_code_3749_, 0);
                    v_k_4217_ = lean_ctor_get(v_code_3749_, 1);
                    lean_inc_ref(v_k_4217_);
                    lean_inc_ref(v_decl_4216_);
                    v_decl_3772_ = v_decl_4216_;
                    v_k_3773_ = v_k_4217_;
                    v___y_3774_ = v_a_3750_;
                    v___y_3775_ = v_a_3751_;
                    v___y_3776_ = v_a_3752_;
                    v___y_3777_ = v_a_3753_;
                    v___y_3778_ = v_a_3754_;
                    v___y_3779_ = v_a_3755_;
                    state = 3;
                    continue;
                }
                4 => {
                    v_cases_4218_ = lean_ctor_get(v_code_3749_, 0);
                    lean_inc_ref(v_cases_4218_);
                    v_typeName_4219_ = lean_ctor_get(v_cases_4218_, 0);
                    v_resultType_4220_ = lean_ctor_get(v_cases_4218_, 1);
                    v_discr_4221_ = lean_ctor_get(v_cases_4218_, 2);
                    v_alts_4222_ = lean_ctor_get(v_cases_4218_, 3);
                    v_isSharedCheck_4261_ = (!lean_is_exclusive(v_cases_4218_)) as u8;
                    if v_isSharedCheck_4261_ == 0 {
                        v___x_4224_ = v_cases_4218_;
                        v_isShared_4225_ = v_isSharedCheck_4261_;
                        state = 59;
                        continue;
                    } else {
                        lean_inc(v_alts_4222_);
                        lean_inc(v_discr_4221_);
                        lean_inc(v_resultType_4220_);
                        lean_inc(v_typeName_4219_);
                        lean_dec(v_cases_4218_);
                        v___x_4224_ = lean_box(0);
                        v_isShared_4225_ = v_isSharedCheck_4261_;
                        state = 59;
                        continue;
                    }
                }
                _ => {
                    v___x_4262_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4262_, 0, v_code_3749_);
                    return v___x_4262_;
                }
            },
            1 => {
                if v___y_3760_ == 0 {
                    lean_dec_ref(v_code_3749_);
                    v___x_3761_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v___x_3761_, 0, v___y_3758_);
                    lean_ctor_set(v___x_3761_, 1, v___y_3759_);
                    v___x_3762_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3762_, 0, v___x_3761_);
                    return v___x_3762_;
                } else {
                    lean_dec_ref(v___y_3759_);
                    lean_dec_ref(v___y_3758_);
                    v___x_3763_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3763_, 0, v_code_3749_);
                    return v___x_3763_;
                }
            }
            2 => {
                if v___y_3767_ == 0 {
                    lean_dec_ref(v_code_3749_);
                    v___x_3768_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3768_, 0, v___y_3765_);
                    lean_ctor_set(v___x_3768_, 1, v___y_3766_);
                    v___x_3769_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3769_, 0, v___x_3768_);
                    return v___x_3769_;
                } else {
                    lean_dec_ref(v___y_3766_);
                    lean_dec_ref(v___y_3765_);
                    v___x_3770_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3770_, 0, v_code_3749_);
                    return v___x_3770_;
                }
            }
            3 => {
                v_params_3780_ = lean_ctor_get(v_decl_3772_, 2);
                lean_inc_ref(v_params_3780_);
                v_type_3781_ = lean_ctor_get(v_decl_3772_, 3);
                lean_inc_ref(v_type_3781_);
                v_value_3782_ = lean_ctor_get(v_decl_3772_, 4);
                lean_inc_ref(v_value_3782_);
                v___x_3783_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                    v_value_3782_,
                    v___y_3774_,
                    v___y_3775_,
                    v___y_3776_,
                    v___y_3777_,
                    v___y_3778_,
                    v___y_3779_,
                );
                if lean_obj_tag(v___x_3783_) == 0 {
                    v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
                    lean_inc(v_a_3784_);
                    lean_dec_ref_known(v___x_3783_, 1);
                    v___x_3785_ = 0;
                    v___x_3786_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3785_, v_decl_3772_, v_type_3781_, v_params_3780_, v_a_3784_, v___y_3777_);
                    if lean_obj_tag(v___x_3786_) == 0 {
                        v_a_3787_ = lean_ctor_get(v___x_3786_, 0);
                        lean_inc(v_a_3787_);
                        lean_dec_ref_known(v___x_3786_, 1);
                        v___x_3788_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                            v_k_3773_,
                            v___y_3774_,
                            v___y_3775_,
                            v___y_3776_,
                            v___y_3777_,
                            v___y_3778_,
                            v___y_3779_,
                        );
                        if lean_obj_tag(v___x_3788_) == 0 {
                            match lean_obj_tag(v_code_3749_) {
                                1 => {
                                    v_a_3789_ = lean_ctor_get(v___x_3788_, 0);
                                    lean_inc(v_a_3789_);
                                    lean_dec_ref_known(v___x_3788_, 1);
                                    v_decl_3790_ = lean_ctor_get(v_code_3749_, 0);
                                    v_k_3791_ = lean_ctor_get(v_code_3749_, 1);
                                    v___x_3792_ = lean_ptr_addr(v_k_3791_);
                                    v___x_3793_ = lean_ptr_addr(v_a_3789_);
                                    v___x_3794_ = lean_usize_dec_eq(v___x_3792_, v___x_3793_);
                                    if v___x_3794_ == 0 {
                                        v___y_3765_ = v_a_3787_;
                                        v___y_3766_ = v_a_3789_;
                                        v___y_3767_ = v___x_3794_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3795_ = lean_ptr_addr(v_decl_3790_);
                                        v___x_3796_ = lean_ptr_addr(v_a_3787_);
                                        v___x_3797_ = lean_usize_dec_eq(v___x_3795_, v___x_3796_);
                                        v___y_3765_ = v_a_3787_;
                                        v___y_3766_ = v_a_3789_;
                                        v___y_3767_ = v___x_3797_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                2 => {
                                    v_a_3798_ = lean_ctor_get(v___x_3788_, 0);
                                    lean_inc(v_a_3798_);
                                    lean_dec_ref_known(v___x_3788_, 1);
                                    v_decl_3799_ = lean_ctor_get(v_code_3749_, 0);
                                    v_k_3800_ = lean_ctor_get(v_code_3749_, 1);
                                    v___x_3801_ = lean_ptr_addr(v_k_3800_);
                                    v___x_3802_ = lean_ptr_addr(v_a_3798_);
                                    v___x_3803_ = lean_usize_dec_eq(v___x_3801_, v___x_3802_);
                                    if v___x_3803_ == 0 {
                                        v___y_3758_ = v_a_3787_;
                                        v___y_3759_ = v_a_3798_;
                                        v___y_3760_ = v___x_3803_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3804_ = lean_ptr_addr(v_decl_3799_);
                                        v___x_3805_ = lean_ptr_addr(v_a_3787_);
                                        v___x_3806_ = lean_usize_dec_eq(v___x_3804_, v___x_3805_);
                                        v___y_3758_ = v_a_3787_;
                                        v___y_3759_ = v_a_3798_;
                                        v___y_3760_ = v___x_3806_;
                                        state = 1;
                                        continue;
                                    }
                                }
                                _ => {
                                    lean_dec(v_a_3787_);
                                    lean_dec_ref(v_code_3749_);
                                    v_isSharedCheck_3815_ = (!lean_is_exclusive(v___x_3788_)) as u8;
                                    if v_isSharedCheck_3815_ == 0 {
                                        v_unused_3816_ = lean_ctor_get(v___x_3788_, 0);
                                        lean_dec(v_unused_3816_);
                                        v___x_3808_ = v___x_3788_;
                                        v_isShared_3809_ = v_isSharedCheck_3815_;
                                        state = 4;
                                        continue;
                                    } else {
                                        lean_dec(v___x_3788_);
                                        v___x_3808_ = lean_box(0);
                                        v_isShared_3809_ = v_isSharedCheck_3815_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_a_3787_);
                            lean_dec_ref(v_code_3749_);
                            return v___x_3788_;
                        }
                    } else {
                        lean_dec_ref(v_k_3773_);
                        lean_dec_ref(v_code_3749_);
                        v_a_3817_ = lean_ctor_get(v___x_3786_, 0);
                        v_isSharedCheck_3824_ = (!lean_is_exclusive(v___x_3786_)) as u8;
                        if v_isSharedCheck_3824_ == 0 {
                            v___x_3819_ = v___x_3786_;
                            v_isShared_3820_ = v_isSharedCheck_3824_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3817_);
                            lean_dec(v___x_3786_);
                            v___x_3819_ = lean_box(0);
                            v_isShared_3820_ = v_isSharedCheck_3824_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_type_3781_);
                    lean_dec_ref(v_params_3780_);
                    lean_dec_ref(v_k_3773_);
                    lean_dec_ref(v_decl_3772_);
                    lean_dec_ref(v_code_3749_);
                    return v___x_3783_;
                }
            }
            4 => {
                v___x_3810_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__3,
                );
                v___x_3811_ = l_panic___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__0(
                    v___x_3810_,
                );
                if v_isShared_3809_ == 0 {
                    lean_ctor_set(v___x_3808_, 0, v___x_3811_);
                    v___x_3813_ = v___x_3808_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3814_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3814_, 0, v___x_3811_);
                    v___x_3813_ = v_reuseFailAlloc_3814_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3813_;
            }
            6 => {
                if v_isShared_3820_ == 0 {
                    v___x_3822_ = v___x_3819_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3823_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3823_, 0, v_a_3817_);
                    v___x_3822_ = v_reuseFailAlloc_3823_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3822_;
            }
            8 => {
                if v___y_3828_ == 0 {
                    lean_dec_ref(v_code_3749_);
                    v___x_3829_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3829_, 0, v___y_3826_);
                    lean_ctor_set(v___x_3829_, 1, v___y_3827_);
                    v___x_3830_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3830_, 0, v___x_3829_);
                    return v___x_3830_;
                } else {
                    lean_dec_ref(v___y_3827_);
                    lean_dec_ref(v___y_3826_);
                    v___x_3831_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3831_, 0, v_code_3749_);
                    return v___x_3831_;
                }
            }
            9 => {
                if v___y_3835_ == 0 {
                    lean_dec_ref(v_code_3749_);
                    v___x_3836_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3836_, 0, v___y_3834_);
                    lean_ctor_set(v___x_3836_, 1, v___y_3833_);
                    v___x_3837_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3837_, 0, v___x_3836_);
                    return v___x_3837_;
                } else {
                    lean_dec_ref(v___y_3834_);
                    lean_dec_ref(v___y_3833_);
                    v___x_3838_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3838_, 0, v_code_3749_);
                    return v___x_3838_;
                }
            }
            10 => {
                if v___y_3842_ == 0 {
                    lean_dec_ref(v_code_3749_);
                    v___x_3843_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3843_, 0, v___y_3840_);
                    lean_ctor_set(v___x_3843_, 1, v___y_3841_);
                    v___x_3844_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3844_, 0, v___x_3843_);
                    return v___x_3844_;
                } else {
                    lean_dec_ref(v___y_3841_);
                    lean_dec_ref(v___y_3840_);
                    v___x_3845_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3845_, 0, v_code_3749_);
                    return v___x_3845_;
                }
            }
            11 => {
                if v___y_3849_ == 0 {
                    lean_dec_ref(v_code_3749_);
                    v___x_3850_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3850_, 0, v___y_3848_);
                    lean_ctor_set(v___x_3850_, 1, v___y_3847_);
                    v___x_3851_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3851_, 0, v___x_3850_);
                    return v___x_3851_;
                } else {
                    lean_dec_ref(v___y_3848_);
                    lean_dec_ref(v___y_3847_);
                    v___x_3852_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3852_, 0, v_code_3749_);
                    return v___x_3852_;
                }
            }
            12 => {
                if v___y_3856_ == 0 {
                    lean_dec_ref(v_code_3749_);
                    v___x_3857_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3857_, 0, v___y_3854_);
                    lean_ctor_set(v___x_3857_, 1, v___y_3855_);
                    v___x_3858_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3858_, 0, v___x_3857_);
                    return v___x_3858_;
                } else {
                    lean_dec_ref(v___y_3855_);
                    lean_dec_ref(v___y_3854_);
                    v___x_3859_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3859_, 0, v_code_3749_);
                    return v___x_3859_;
                }
            }
            13 => {
                if v___y_3864_ == 0 {
                    lean_inc_ref(v_decl_3860_);
                    v_isSharedCheck_3872_ = (!lean_is_exclusive(v_code_3749_)) as u8;
                    if v_isSharedCheck_3872_ == 0 {
                        v_unused_3873_ = lean_ctor_get(v_code_3749_, 1);
                        lean_dec(v_unused_3873_);
                        v_unused_3874_ = lean_ctor_get(v_code_3749_, 0);
                        lean_dec(v_unused_3874_);
                        v___x_3866_ = v_code_3749_;
                        v_isShared_3867_ = v_isSharedCheck_3872_;
                        state = 14;
                        continue;
                    } else {
                        lean_dec(v_code_3749_);
                        v___x_3866_ = lean_box(0);
                        v_isShared_3867_ = v_isSharedCheck_3872_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_3863_);
                    v___x_3875_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3875_, 0, v_code_3749_);
                    return v___x_3875_;
                }
            }
            14 => {
                if v_isShared_3867_ == 0 {
                    lean_ctor_set(v___x_3866_, 1, v___y_3863_);
                    v___x_3869_ = v___x_3866_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3871_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3871_, 0, v_decl_3860_);
                    lean_ctor_set(v_reuseFailAlloc_3871_, 1, v___y_3863_);
                    v___x_3869_ = v_reuseFailAlloc_3871_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                v___x_3870_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3870_, 0, v___x_3869_);
                return v___x_3870_;
            }
            16 => {
                if v___y_3878_ == 0 {
                    lean_inc_ref(v_decl_3860_);
                    v_isSharedCheck_3886_ = (!lean_is_exclusive(v_code_3749_)) as u8;
                    if v_isSharedCheck_3886_ == 0 {
                        v_unused_3887_ = lean_ctor_get(v_code_3749_, 1);
                        lean_dec(v_unused_3887_);
                        v_unused_3888_ = lean_ctor_get(v_code_3749_, 0);
                        lean_dec(v_unused_3888_);
                        v___x_3880_ = v_code_3749_;
                        v_isShared_3881_ = v_isSharedCheck_3886_;
                        state = 17;
                        continue;
                    } else {
                        lean_dec(v_code_3749_);
                        v___x_3880_ = lean_box(0);
                        v_isShared_3881_ = v_isSharedCheck_3886_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_3877_);
                    v___x_3889_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3889_, 0, v_code_3749_);
                    return v___x_3889_;
                }
            }
            17 => {
                if v_isShared_3881_ == 0 {
                    lean_ctor_set(v___x_3880_, 1, v___y_3877_);
                    v___x_3883_ = v___x_3880_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3885_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 0, v_decl_3860_);
                    lean_ctor_set(v_reuseFailAlloc_3885_, 1, v___y_3877_);
                    v___x_3883_ = v_reuseFailAlloc_3885_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___x_3884_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3884_, 0, v___x_3883_);
                return v___x_3884_;
            }
            19 => {
                if v___y_3892_ == 0 {
                    lean_inc_ref(v_decl_3860_);
                    v_isSharedCheck_3900_ = (!lean_is_exclusive(v_code_3749_)) as u8;
                    if v_isSharedCheck_3900_ == 0 {
                        v_unused_3901_ = lean_ctor_get(v_code_3749_, 1);
                        lean_dec(v_unused_3901_);
                        v_unused_3902_ = lean_ctor_get(v_code_3749_, 0);
                        lean_dec(v_unused_3902_);
                        v___x_3894_ = v_code_3749_;
                        v_isShared_3895_ = v_isSharedCheck_3900_;
                        state = 20;
                        continue;
                    } else {
                        lean_dec(v_code_3749_);
                        v___x_3894_ = lean_box(0);
                        v_isShared_3895_ = v_isSharedCheck_3900_;
                        state = 20;
                        continue;
                    }
                } else {
                    lean_dec_ref(v___y_3891_);
                    v___x_3903_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3903_, 0, v_code_3749_);
                    return v___x_3903_;
                }
            }
            20 => {
                if v_isShared_3895_ == 0 {
                    lean_ctor_set(v___x_3894_, 1, v___y_3891_);
                    v___x_3897_ = v___x_3894_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_decl_3860_);
                    lean_ctor_set(v_reuseFailAlloc_3899_, 1, v___y_3891_);
                    v___x_3897_ = v_reuseFailAlloc_3899_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3898_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3898_, 0, v___x_3897_);
                return v___x_3898_;
            }
            22 => {
                lean_inc_ref(v_k_3861_);
                lean_inc_ref(v_decl_3860_);
                v___x_3912_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(
                    v_decl_3860_,
                    v_k_3861_,
                    v___y_3906_,
                    v___y_3907_,
                    v___y_3908_,
                    v___y_3909_,
                    v___y_3910_,
                    v___y_3911_,
                );
                if lean_obj_tag(v___x_3912_) == 0 {
                    v_a_3913_ = lean_ctor_get(v___x_3912_, 0);
                    lean_inc(v_a_3913_);
                    lean_dec_ref_known(v___x_3912_, 1);
                    if lean_obj_tag(v_a_3913_) == 1 {
                        lean_dec(v_value_3904_);
                        v_val_3914_ = lean_ctor_get(v_a_3913_, 0);
                        lean_inc(v_val_3914_);
                        lean_dec_ref_known(v_a_3913_, 1);
                        v_fst_3915_ = lean_ctor_get(v_val_3914_, 0);
                        lean_inc_n(v_fst_3915_, 2);
                        v_snd_3916_ = lean_ctor_get(v_val_3914_, 1);
                        lean_inc(v_snd_3916_);
                        lean_dec(v_val_3914_);
                        v___x_3917_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_3915_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
                        if lean_obj_tag(v___x_3917_) == 0 {
                            v_a_3918_ = lean_ctor_get(v___x_3917_, 0);
                            lean_inc(v_a_3918_);
                            lean_dec_ref_known(v___x_3917_, 1);
                            v___x_3919_ = 0;
                            v___x_3920_ = lean_box(0);
                            v___x_3921_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
                            v___x_3922_ = lean_alloc_ctor(3, 3, (0) as u32);
                            lean_ctor_set(v___x_3922_, 0, v_a_3918_);
                            lean_ctor_set(v___x_3922_, 1, v___x_3920_);
                            lean_ctor_set(v___x_3922_, 2, v___x_3921_);
                            v___x_3923_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                v___x_3919_,
                                v_fst_3915_,
                                v___x_3922_,
                                v___y_3909_,
                            );
                            if lean_obj_tag(v___x_3923_) == 0 {
                                v_a_3924_ = lean_ctor_get(v___x_3923_, 0);
                                lean_inc(v_a_3924_);
                                lean_dec_ref_known(v___x_3923_, 1);
                                v___x_3925_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                                    v_snd_3916_,
                                    v___y_3906_,
                                    v___y_3907_,
                                    v___y_3908_,
                                    v___y_3909_,
                                    v___y_3910_,
                                    v___y_3911_,
                                );
                                if lean_obj_tag(v___x_3925_) == 0 {
                                    v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
                                    lean_inc(v_a_3926_);
                                    lean_dec_ref_known(v___x_3925_, 1);
                                    v___x_3927_ = lean_ptr_addr(v_k_3861_);
                                    v___x_3928_ = lean_ptr_addr(v_a_3926_);
                                    v___x_3929_ = lean_usize_dec_eq(v___x_3927_, v___x_3928_);
                                    if v___x_3929_ == 0 {
                                        v___y_3833_ = v_a_3926_;
                                        v___y_3834_ = v_a_3924_;
                                        v___y_3835_ = v___x_3929_;
                                        state = 9;
                                        continue;
                                    } else {
                                        v___x_3930_ = lean_ptr_addr(v_decl_3860_);
                                        v___x_3931_ = lean_ptr_addr(v_a_3924_);
                                        v___x_3932_ = lean_usize_dec_eq(v___x_3930_, v___x_3931_);
                                        v___y_3833_ = v_a_3926_;
                                        v___y_3834_ = v_a_3924_;
                                        v___y_3835_ = v___x_3932_;
                                        state = 9;
                                        continue;
                                    }
                                } else {
                                    lean_dec(v_a_3924_);
                                    lean_dec_ref_known(v_code_3749_, 2);
                                    return v___x_3925_;
                                }
                            } else {
                                lean_dec(v_snd_3916_);
                                lean_dec_ref_known(v_code_3749_, 2);
                                v_a_3933_ = lean_ctor_get(v___x_3923_, 0);
                                v_isSharedCheck_3940_ = (!lean_is_exclusive(v___x_3923_)) as u8;
                                if v_isSharedCheck_3940_ == 0 {
                                    v___x_3935_ = v___x_3923_;
                                    v_isShared_3936_ = v_isSharedCheck_3940_;
                                    state = 23;
                                    continue;
                                } else {
                                    lean_inc(v_a_3933_);
                                    lean_dec(v___x_3923_);
                                    v___x_3935_ = lean_box(0);
                                    v_isShared_3936_ = v_isSharedCheck_3940_;
                                    state = 23;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_snd_3916_);
                            lean_dec(v_fst_3915_);
                            lean_dec_ref_known(v_code_3749_, 2);
                            v_a_3941_ = lean_ctor_get(v___x_3917_, 0);
                            v_isSharedCheck_3948_ = (!lean_is_exclusive(v___x_3917_)) as u8;
                            if v_isSharedCheck_3948_ == 0 {
                                v___x_3943_ = v___x_3917_;
                                v_isShared_3944_ = v_isSharedCheck_3948_;
                                state = 25;
                                continue;
                            } else {
                                lean_inc(v_a_3941_);
                                lean_dec(v___x_3917_);
                                v___x_3943_ = lean_box(0);
                                v_isShared_3944_ = v_isSharedCheck_3948_;
                                state = 25;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3913_);
                        v___x_3949_ = 1;
                        v___x_3950_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(
                            v___x_3949_,
                            v_value_3904_,
                            v___y_3906_,
                            v___y_3907_,
                            v___y_3908_,
                            v___y_3909_,
                            v___y_3910_,
                            v___y_3911_,
                        );
                        if lean_obj_tag(v___x_3950_) == 0 {
                            v_a_3951_ = lean_ctor_get(v___x_3950_, 0);
                            lean_inc(v_a_3951_);
                            lean_dec_ref_known(v___x_3950_, 1);
                            v___x_3952_ = (lean_unbox(v_a_3951_) as u8);
                            lean_dec(v_a_3951_);
                            if v___x_3952_ == 0 {
                                lean_inc_ref(v_k_3861_);
                                v___x_3953_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                                    v_k_3861_,
                                    v___y_3906_,
                                    v___y_3907_,
                                    v___y_3908_,
                                    v___y_3909_,
                                    v___y_3910_,
                                    v___y_3911_,
                                );
                                if lean_obj_tag(v___x_3953_) == 0 {
                                    v_a_3954_ = lean_ctor_get(v___x_3953_, 0);
                                    lean_inc(v_a_3954_);
                                    lean_dec_ref_known(v___x_3953_, 1);
                                    v___x_3955_ = lean_ptr_addr(v_k_3861_);
                                    v___x_3956_ = lean_ptr_addr(v_a_3954_);
                                    v___x_3957_ = lean_usize_dec_eq(v___x_3955_, v___x_3956_);
                                    if v___x_3957_ == 0 {
                                        v___y_3863_ = v_a_3954_;
                                        v___y_3864_ = v___x_3957_;
                                        state = 13;
                                        continue;
                                    } else {
                                        v___x_3958_ = lean_ptr_addr(v_decl_3860_);
                                        v___x_3959_ = lean_usize_dec_eq(v___x_3958_, v___x_3958_);
                                        v___y_3863_ = v_a_3954_;
                                        v___y_3864_ = v___x_3959_;
                                        state = 13;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_code_3749_, 2);
                                    return v___x_3953_;
                                }
                            } else {
                                lean_inc_ref(v_decl_3860_);
                                v___x_3960_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_3860_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_);
                                if lean_obj_tag(v___x_3960_) == 0 {
                                    v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
                                    lean_inc(v_a_3961_);
                                    lean_dec_ref_known(v___x_3960_, 1);
                                    v___x_3962_ = 0;
                                    v___x_3963_ = lean_box(0);
                                    v___x_3964_ =
                                        l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
                                    v___x_3965_ = lean_alloc_ctor(3, 3, (0) as u32);
                                    lean_ctor_set(v___x_3965_, 0, v_a_3961_);
                                    lean_ctor_set(v___x_3965_, 1, v___x_3963_);
                                    lean_ctor_set(v___x_3965_, 2, v___x_3964_);
                                    lean_inc_ref(v_decl_3860_);
                                    v___x_3966_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                        v___x_3962_,
                                        v_decl_3860_,
                                        v___x_3965_,
                                        v___y_3909_,
                                    );
                                    if lean_obj_tag(v___x_3966_) == 0 {
                                        v_a_3967_ = lean_ctor_get(v___x_3966_, 0);
                                        lean_inc(v_a_3967_);
                                        lean_dec_ref_known(v___x_3966_, 1);
                                        lean_inc_ref(v_k_3861_);
                                        v___x_3968_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                                            v_k_3861_,
                                            v___y_3906_,
                                            v___y_3907_,
                                            v___y_3908_,
                                            v___y_3909_,
                                            v___y_3910_,
                                            v___y_3911_,
                                        );
                                        if lean_obj_tag(v___x_3968_) == 0 {
                                            v_a_3969_ = lean_ctor_get(v___x_3968_, 0);
                                            lean_inc(v_a_3969_);
                                            lean_dec_ref_known(v___x_3968_, 1);
                                            v___x_3970_ = lean_ptr_addr(v_k_3861_);
                                            v___x_3971_ = lean_ptr_addr(v_a_3969_);
                                            v___x_3972_ =
                                                lean_usize_dec_eq(v___x_3970_, v___x_3971_);
                                            if v___x_3972_ == 0 {
                                                v___y_3826_ = v_a_3967_;
                                                v___y_3827_ = v_a_3969_;
                                                v___y_3828_ = v___x_3972_;
                                                state = 8;
                                                continue;
                                            } else {
                                                v___x_3973_ = lean_ptr_addr(v_decl_3860_);
                                                v___x_3974_ = lean_ptr_addr(v_a_3967_);
                                                v___x_3975_ =
                                                    lean_usize_dec_eq(v___x_3973_, v___x_3974_);
                                                v___y_3826_ = v_a_3967_;
                                                v___y_3827_ = v_a_3969_;
                                                v___y_3828_ = v___x_3975_;
                                                state = 8;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_3967_);
                                            lean_dec_ref_known(v_code_3749_, 2);
                                            return v___x_3968_;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_code_3749_, 2);
                                        v_a_3976_ = lean_ctor_get(v___x_3966_, 0);
                                        v_isSharedCheck_3983_ =
                                            (!lean_is_exclusive(v___x_3966_)) as u8;
                                        if v_isSharedCheck_3983_ == 0 {
                                            v___x_3978_ = v___x_3966_;
                                            v_isShared_3979_ = v_isSharedCheck_3983_;
                                            state = 27;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3976_);
                                            lean_dec(v___x_3966_);
                                            v___x_3978_ = lean_box(0);
                                            v_isShared_3979_ = v_isSharedCheck_3983_;
                                            state = 27;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v_code_3749_, 2);
                                    v_a_3984_ = lean_ctor_get(v___x_3960_, 0);
                                    v_isSharedCheck_3991_ = (!lean_is_exclusive(v___x_3960_)) as u8;
                                    if v_isSharedCheck_3991_ == 0 {
                                        v___x_3986_ = v___x_3960_;
                                        v_isShared_3987_ = v_isSharedCheck_3991_;
                                        state = 29;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3984_);
                                        lean_dec(v___x_3960_);
                                        v___x_3986_ = lean_box(0);
                                        v_isShared_3987_ = v_isSharedCheck_3991_;
                                        state = 29;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_3749_, 2);
                            v_a_3992_ = lean_ctor_get(v___x_3950_, 0);
                            v_isSharedCheck_3999_ = (!lean_is_exclusive(v___x_3950_)) as u8;
                            if v_isSharedCheck_3999_ == 0 {
                                v___x_3994_ = v___x_3950_;
                                v_isShared_3995_ = v_isSharedCheck_3999_;
                                state = 31;
                                continue;
                            } else {
                                lean_inc(v_a_3992_);
                                lean_dec(v___x_3950_);
                                v___x_3994_ = lean_box(0);
                                v_isShared_3995_ = v_isSharedCheck_3999_;
                                state = 31;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec(v_value_3904_);
                    lean_dec_ref_known(v_code_3749_, 2);
                    v_a_4000_ = lean_ctor_get(v___x_3912_, 0);
                    v_isSharedCheck_4007_ = (!lean_is_exclusive(v___x_3912_)) as u8;
                    if v_isSharedCheck_4007_ == 0 {
                        v___x_4002_ = v___x_3912_;
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_4000_);
                        lean_dec(v___x_3912_);
                        v___x_4002_ = lean_box(0);
                        v_isShared_4003_ = v_isSharedCheck_4007_;
                        state = 33;
                        continue;
                    }
                }
            }
            23 => {
                if v_isShared_3936_ == 0 {
                    v___x_3938_ = v___x_3935_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3939_, 0, v_a_3933_);
                    v___x_3938_ = v_reuseFailAlloc_3939_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3938_;
            }
            25 => {
                if v_isShared_3944_ == 0 {
                    v___x_3946_ = v___x_3943_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_a_3941_);
                    v___x_3946_ = v_reuseFailAlloc_3947_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3946_;
            }
            27 => {
                if v_isShared_3979_ == 0 {
                    v___x_3981_ = v___x_3978_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3982_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3982_, 0, v_a_3976_);
                    v___x_3981_ = v_reuseFailAlloc_3982_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3981_;
            }
            29 => {
                if v_isShared_3987_ == 0 {
                    v___x_3989_ = v___x_3986_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3984_);
                    v___x_3989_ = v_reuseFailAlloc_3990_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3989_;
            }
            31 => {
                if v_isShared_3995_ == 0 {
                    v___x_3997_ = v___x_3994_;
                    state = 32;
                    continue;
                } else {
                    v_reuseFailAlloc_3998_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_a_3992_);
                    v___x_3997_ = v_reuseFailAlloc_3998_;
                    state = 32;
                    continue;
                }
            }
            32 => {
                return v___x_3997_;
            }
            33 => {
                if v_isShared_4003_ == 0 {
                    v___x_4005_ = v___x_4002_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_4006_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4006_, 0, v_a_4000_);
                    v___x_4005_ = v_reuseFailAlloc_4006_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                return v___x_4005_;
            }
            35 => {
                lean_inc_ref(v_k_3861_);
                lean_inc_ref(v_decl_3860_);
                v___x_4023_ = l_Lean_Compiler_LCNF_ExtractClosed_searchArrayLiteral(
                    v_decl_3860_,
                    v_k_3861_,
                    v___y_4017_,
                    v___y_4018_,
                    v___y_4019_,
                    v___y_4020_,
                    v___y_4021_,
                    v___y_4022_,
                );
                if lean_obj_tag(v___x_4023_) == 0 {
                    v_a_4024_ = lean_ctor_get(v___x_4023_, 0);
                    lean_inc(v_a_4024_);
                    lean_dec_ref_known(v___x_4023_, 1);
                    if lean_obj_tag(v_a_4024_) == 1 {
                        v_isSharedCheck_4065_ = (!lean_is_exclusive(v_value_3904_)) as u8;
                        if v_isSharedCheck_4065_ == 0 {
                            v_unused_4066_ = lean_ctor_get(v_value_3904_, 2);
                            lean_dec(v_unused_4066_);
                            v_unused_4067_ = lean_ctor_get(v_value_3904_, 1);
                            lean_dec(v_unused_4067_);
                            v_unused_4068_ = lean_ctor_get(v_value_3904_, 0);
                            lean_dec(v_unused_4068_);
                            v___x_4026_ = v_value_3904_;
                            v_isShared_4027_ = v_isSharedCheck_4065_;
                            state = 36;
                            continue;
                        } else {
                            lean_dec(v_value_3904_);
                            v___x_4026_ = lean_box(0);
                            v_isShared_4027_ = v_isSharedCheck_4065_;
                            state = 36;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4024_);
                        v___x_4069_ = l_Lean_Compiler_LCNF_ExtractClosed_shouldExtractLetValue(
                            v___x_4015_,
                            v_value_3904_,
                            v___y_4017_,
                            v___y_4018_,
                            v___y_4019_,
                            v___y_4020_,
                            v___y_4021_,
                            v___y_4022_,
                        );
                        if lean_obj_tag(v___x_4069_) == 0 {
                            v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
                            lean_inc(v_a_4070_);
                            lean_dec_ref_known(v___x_4069_, 1);
                            v___x_4071_ = (lean_unbox(v_a_4070_) as u8);
                            lean_dec(v_a_4070_);
                            if v___x_4071_ == 0 {
                                lean_inc_ref(v_k_3861_);
                                v___x_4072_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                                    v_k_3861_,
                                    v___y_4017_,
                                    v___y_4018_,
                                    v___y_4019_,
                                    v___y_4020_,
                                    v___y_4021_,
                                    v___y_4022_,
                                );
                                if lean_obj_tag(v___x_4072_) == 0 {
                                    v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
                                    lean_inc(v_a_4073_);
                                    lean_dec_ref_known(v___x_4072_, 1);
                                    v___x_4074_ = lean_ptr_addr(v_k_3861_);
                                    v___x_4075_ = lean_ptr_addr(v_a_4073_);
                                    v___x_4076_ = lean_usize_dec_eq(v___x_4074_, v___x_4075_);
                                    if v___x_4076_ == 0 {
                                        v___y_3891_ = v_a_4073_;
                                        v___y_3892_ = v___x_4076_;
                                        state = 19;
                                        continue;
                                    } else {
                                        v___x_4077_ = lean_ptr_addr(v_decl_3860_);
                                        v___x_4078_ = lean_usize_dec_eq(v___x_4077_, v___x_4077_);
                                        v___y_3891_ = v_a_4073_;
                                        v___y_3892_ = v___x_4078_;
                                        state = 19;
                                        continue;
                                    }
                                } else {
                                    lean_dec_ref_known(v_code_3749_, 2);
                                    return v___x_4072_;
                                }
                            } else {
                                lean_inc_ref(v_decl_3860_);
                                v___x_4079_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_3860_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
                                if lean_obj_tag(v___x_4079_) == 0 {
                                    v_a_4080_ = lean_ctor_get(v___x_4079_, 0);
                                    lean_inc(v_a_4080_);
                                    lean_dec_ref_known(v___x_4079_, 1);
                                    v___x_4081_ = 0;
                                    v___x_4082_ = lean_box(0);
                                    v___x_4083_ =
                                        l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
                                    v___x_4084_ = lean_alloc_ctor(3, 3, (0) as u32);
                                    lean_ctor_set(v___x_4084_, 0, v_a_4080_);
                                    lean_ctor_set(v___x_4084_, 1, v___x_4082_);
                                    lean_ctor_set(v___x_4084_, 2, v___x_4083_);
                                    lean_inc_ref(v_decl_3860_);
                                    v___x_4085_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                                        v___x_4081_,
                                        v_decl_3860_,
                                        v___x_4084_,
                                        v___y_4020_,
                                    );
                                    if lean_obj_tag(v___x_4085_) == 0 {
                                        v_a_4086_ = lean_ctor_get(v___x_4085_, 0);
                                        lean_inc(v_a_4086_);
                                        lean_dec_ref_known(v___x_4085_, 1);
                                        lean_inc_ref(v_k_3861_);
                                        v___x_4087_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                                            v_k_3861_,
                                            v___y_4017_,
                                            v___y_4018_,
                                            v___y_4019_,
                                            v___y_4020_,
                                            v___y_4021_,
                                            v___y_4022_,
                                        );
                                        if lean_obj_tag(v___x_4087_) == 0 {
                                            v_a_4088_ = lean_ctor_get(v___x_4087_, 0);
                                            lean_inc(v_a_4088_);
                                            lean_dec_ref_known(v___x_4087_, 1);
                                            v___x_4089_ = lean_ptr_addr(v_k_3861_);
                                            v___x_4090_ = lean_ptr_addr(v_a_4088_);
                                            v___x_4091_ =
                                                lean_usize_dec_eq(v___x_4089_, v___x_4090_);
                                            if v___x_4091_ == 0 {
                                                v___y_3847_ = v_a_4088_;
                                                v___y_3848_ = v_a_4086_;
                                                v___y_3849_ = v___x_4091_;
                                                state = 11;
                                                continue;
                                            } else {
                                                v___x_4092_ = lean_ptr_addr(v_decl_3860_);
                                                v___x_4093_ = lean_ptr_addr(v_a_4086_);
                                                v___x_4094_ =
                                                    lean_usize_dec_eq(v___x_4092_, v___x_4093_);
                                                v___y_3847_ = v_a_4088_;
                                                v___y_3848_ = v_a_4086_;
                                                v___y_3849_ = v___x_4094_;
                                                state = 11;
                                                continue;
                                            }
                                        } else {
                                            lean_dec(v_a_4086_);
                                            lean_dec_ref_known(v_code_3749_, 2);
                                            return v___x_4087_;
                                        }
                                    } else {
                                        lean_dec_ref_known(v_code_3749_, 2);
                                        v_a_4095_ = lean_ctor_get(v___x_4085_, 0);
                                        v_isSharedCheck_4102_ =
                                            (!lean_is_exclusive(v___x_4085_)) as u8;
                                        if v_isSharedCheck_4102_ == 0 {
                                            v___x_4097_ = v___x_4085_;
                                            v_isShared_4098_ = v_isSharedCheck_4102_;
                                            state = 42;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4095_);
                                            lean_dec(v___x_4085_);
                                            v___x_4097_ = lean_box(0);
                                            v_isShared_4098_ = v_isSharedCheck_4102_;
                                            state = 42;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v_code_3749_, 2);
                                    v_a_4103_ = lean_ctor_get(v___x_4079_, 0);
                                    v_isSharedCheck_4110_ = (!lean_is_exclusive(v___x_4079_)) as u8;
                                    if v_isSharedCheck_4110_ == 0 {
                                        v___x_4105_ = v___x_4079_;
                                        v_isShared_4106_ = v_isSharedCheck_4110_;
                                        state = 44;
                                        continue;
                                    } else {
                                        lean_inc(v_a_4103_);
                                        lean_dec(v___x_4079_);
                                        v___x_4105_ = lean_box(0);
                                        v_isShared_4106_ = v_isSharedCheck_4110_;
                                        state = 44;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref_known(v_code_3749_, 2);
                            v_a_4111_ = lean_ctor_get(v___x_4069_, 0);
                            v_isSharedCheck_4118_ = (!lean_is_exclusive(v___x_4069_)) as u8;
                            if v_isSharedCheck_4118_ == 0 {
                                v___x_4113_ = v___x_4069_;
                                v_isShared_4114_ = v_isSharedCheck_4118_;
                                state = 46;
                                continue;
                            } else {
                                lean_inc(v_a_4111_);
                                lean_dec(v___x_4069_);
                                v___x_4113_ = lean_box(0);
                                v_isShared_4114_ = v_isSharedCheck_4118_;
                                state = 46;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref_known(v_value_3904_, 3);
                    lean_dec_ref_known(v_code_3749_, 2);
                    v_a_4119_ = lean_ctor_get(v___x_4023_, 0);
                    v_isSharedCheck_4126_ = (!lean_is_exclusive(v___x_4023_)) as u8;
                    if v_isSharedCheck_4126_ == 0 {
                        v___x_4121_ = v___x_4023_;
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 48;
                        continue;
                    } else {
                        lean_inc(v_a_4119_);
                        lean_dec(v___x_4023_);
                        v___x_4121_ = lean_box(0);
                        v_isShared_4122_ = v_isSharedCheck_4126_;
                        state = 48;
                        continue;
                    }
                }
            }
            36 => {
                v_val_4028_ = lean_ctor_get(v_a_4024_, 0);
                lean_inc(v_val_4028_);
                lean_dec_ref_known(v_a_4024_, 1);
                v_fst_4029_ = lean_ctor_get(v_val_4028_, 0);
                lean_inc_n(v_fst_4029_, 2);
                v_snd_4030_ = lean_ctor_get(v_val_4028_, 1);
                lean_inc(v_snd_4030_);
                lean_dec(v_val_4028_);
                v___x_4031_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_fst_4029_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_, v___y_4021_, v___y_4022_);
                if lean_obj_tag(v___x_4031_) == 0 {
                    v_a_4032_ = lean_ctor_get(v___x_4031_, 0);
                    lean_inc(v_a_4032_);
                    lean_dec_ref_known(v___x_4031_, 1);
                    v___x_4033_ = 0;
                    v___x_4034_ = lean_box(0);
                    v___x_4035_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
                    if v_isShared_4027_ == 0 {
                        lean_ctor_set(v___x_4026_, 2, v___x_4035_);
                        lean_ctor_set(v___x_4026_, 1, v___x_4034_);
                        lean_ctor_set(v___x_4026_, 0, v_a_4032_);
                        v___x_4037_ = v___x_4026_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_4056_ = lean_alloc_ctor(3, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4056_, 0, v_a_4032_);
                        lean_ctor_set(v_reuseFailAlloc_4056_, 1, v___x_4034_);
                        lean_ctor_set(v_reuseFailAlloc_4056_, 2, v___x_4035_);
                        v___x_4037_ = v_reuseFailAlloc_4056_;
                        state = 37;
                        continue;
                    }
                } else {
                    lean_dec(v_snd_4030_);
                    lean_dec(v_fst_4029_);
                    lean_del_object(v___x_4026_);
                    lean_dec_ref_known(v_code_3749_, 2);
                    v_a_4057_ = lean_ctor_get(v___x_4031_, 0);
                    v_isSharedCheck_4064_ = (!lean_is_exclusive(v___x_4031_)) as u8;
                    if v_isSharedCheck_4064_ == 0 {
                        v___x_4059_ = v___x_4031_;
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 40;
                        continue;
                    } else {
                        lean_inc(v_a_4057_);
                        lean_dec(v___x_4031_);
                        v___x_4059_ = lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 40;
                        continue;
                    }
                }
            }
            37 => {
                v___x_4038_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                    v___x_4033_,
                    v_fst_4029_,
                    v___x_4037_,
                    v___y_4020_,
                );
                if lean_obj_tag(v___x_4038_) == 0 {
                    v_a_4039_ = lean_ctor_get(v___x_4038_, 0);
                    lean_inc(v_a_4039_);
                    lean_dec_ref_known(v___x_4038_, 1);
                    v___x_4040_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                        v_snd_4030_,
                        v___y_4017_,
                        v___y_4018_,
                        v___y_4019_,
                        v___y_4020_,
                        v___y_4021_,
                        v___y_4022_,
                    );
                    if lean_obj_tag(v___x_4040_) == 0 {
                        v_a_4041_ = lean_ctor_get(v___x_4040_, 0);
                        lean_inc(v_a_4041_);
                        lean_dec_ref_known(v___x_4040_, 1);
                        v___x_4042_ = lean_ptr_addr(v_k_3861_);
                        v___x_4043_ = lean_ptr_addr(v_a_4041_);
                        v___x_4044_ = lean_usize_dec_eq(v___x_4042_, v___x_4043_);
                        if v___x_4044_ == 0 {
                            v___y_3854_ = v_a_4039_;
                            v___y_3855_ = v_a_4041_;
                            v___y_3856_ = v___x_4044_;
                            state = 12;
                            continue;
                        } else {
                            v___x_4045_ = lean_ptr_addr(v_decl_3860_);
                            v___x_4046_ = lean_ptr_addr(v_a_4039_);
                            v___x_4047_ = lean_usize_dec_eq(v___x_4045_, v___x_4046_);
                            v___y_3854_ = v_a_4039_;
                            v___y_3855_ = v_a_4041_;
                            v___y_3856_ = v___x_4047_;
                            state = 12;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4039_);
                        lean_dec_ref_known(v_code_3749_, 2);
                        return v___x_4040_;
                    }
                } else {
                    lean_dec(v_snd_4030_);
                    lean_dec_ref_known(v_code_3749_, 2);
                    v_a_4048_ = lean_ctor_get(v___x_4038_, 0);
                    v_isSharedCheck_4055_ = (!lean_is_exclusive(v___x_4038_)) as u8;
                    if v_isSharedCheck_4055_ == 0 {
                        v___x_4050_ = v___x_4038_;
                        v_isShared_4051_ = v_isSharedCheck_4055_;
                        state = 38;
                        continue;
                    } else {
                        lean_inc(v_a_4048_);
                        lean_dec(v___x_4038_);
                        v___x_4050_ = lean_box(0);
                        v_isShared_4051_ = v_isSharedCheck_4055_;
                        state = 38;
                        continue;
                    }
                }
            }
            38 => {
                if v_isShared_4051_ == 0 {
                    v___x_4053_ = v___x_4050_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4048_);
                    v___x_4053_ = v_reuseFailAlloc_4054_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                return v___x_4053_;
            }
            40 => {
                if v_isShared_4060_ == 0 {
                    v___x_4062_ = v___x_4059_;
                    state = 41;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 41;
                    continue;
                }
            }
            41 => {
                return v___x_4062_;
            }
            42 => {
                if v_isShared_4098_ == 0 {
                    v___x_4100_ = v___x_4097_;
                    state = 43;
                    continue;
                } else {
                    v_reuseFailAlloc_4101_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4101_, 0, v_a_4095_);
                    v___x_4100_ = v_reuseFailAlloc_4101_;
                    state = 43;
                    continue;
                }
            }
            43 => {
                return v___x_4100_;
            }
            44 => {
                if v_isShared_4106_ == 0 {
                    v___x_4108_ = v___x_4105_;
                    state = 45;
                    continue;
                } else {
                    v_reuseFailAlloc_4109_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4109_, 0, v_a_4103_);
                    v___x_4108_ = v_reuseFailAlloc_4109_;
                    state = 45;
                    continue;
                }
            }
            45 => {
                return v___x_4108_;
            }
            46 => {
                if v_isShared_4114_ == 0 {
                    v___x_4116_ = v___x_4113_;
                    state = 47;
                    continue;
                } else {
                    v_reuseFailAlloc_4117_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4117_, 0, v_a_4111_);
                    v___x_4116_ = v_reuseFailAlloc_4117_;
                    state = 47;
                    continue;
                }
            }
            47 => {
                return v___x_4116_;
            }
            48 => {
                if v_isShared_4122_ == 0 {
                    v___x_4124_ = v___x_4121_;
                    state = 49;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_a_4119_);
                    v___x_4124_ = v_reuseFailAlloc_4125_;
                    state = 49;
                    continue;
                }
            }
            49 => {
                return v___x_4124_;
            }
            50 => {
                v___x_4135_ = 0;
                v___x_4136_ = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(
                    v___x_4135_,
                    v_sizeId_4128_,
                    v___y_4132_,
                );
                lean_dec(v_sizeId_4128_);
                if lean_obj_tag(v___x_4136_) == 0 {
                    v_a_4137_ = lean_ctor_get(v___x_4136_, 0);
                    lean_inc(v_a_4137_);
                    lean_dec_ref_known(v___x_4136_, 1);
                    if lean_obj_tag(v_a_4137_) == 1 {
                        v_val_4138_ = lean_ctor_get(v_a_4137_, 0);
                        lean_inc(v_val_4138_);
                        lean_dec_ref_known(v_a_4137_, 1);
                        if lean_obj_tag(v_val_4138_) == 0 {
                            v_value_4139_ = lean_ctor_get(v_val_4138_, 0);
                            lean_inc_ref(v_value_4139_);
                            lean_dec_ref_known(v_val_4138_, 1);
                            if lean_obj_tag(v_value_4139_) == 0 {
                                v_isSharedCheck_4186_ = (!lean_is_exclusive(v_value_3904_)) as u8;
                                if v_isSharedCheck_4186_ == 0 {
                                    v_unused_4187_ = lean_ctor_get(v_value_3904_, 2);
                                    lean_dec(v_unused_4187_);
                                    v_unused_4188_ = lean_ctor_get(v_value_3904_, 1);
                                    lean_dec(v_unused_4188_);
                                    v_unused_4189_ = lean_ctor_get(v_value_3904_, 0);
                                    lean_dec(v_unused_4189_);
                                    v___x_4141_ = v_value_3904_;
                                    v_isShared_4142_ = v_isSharedCheck_4186_;
                                    state = 51;
                                    continue;
                                } else {
                                    lean_dec(v_value_3904_);
                                    v___x_4141_ = lean_box(0);
                                    v_isShared_4142_ = v_isSharedCheck_4186_;
                                    state = 51;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_value_4139_);
                                v___y_4017_ = v___y_4129_;
                                v___y_4018_ = v___y_4130_;
                                v___y_4019_ = v___y_4131_;
                                v___y_4020_ = v___y_4132_;
                                v___y_4021_ = v___y_4133_;
                                v___y_4022_ = v___y_4134_;
                                state = 35;
                                continue;
                            }
                        } else {
                            lean_dec(v_val_4138_);
                            v___y_4017_ = v___y_4129_;
                            v___y_4018_ = v___y_4130_;
                            v___y_4019_ = v___y_4131_;
                            v___y_4020_ = v___y_4132_;
                            v___y_4021_ = v___y_4133_;
                            v___y_4022_ = v___y_4134_;
                            state = 35;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4137_);
                        v___y_4017_ = v___y_4129_;
                        v___y_4018_ = v___y_4130_;
                        v___y_4019_ = v___y_4131_;
                        v___y_4020_ = v___y_4132_;
                        v___y_4021_ = v___y_4133_;
                        v___y_4022_ = v___y_4134_;
                        state = 35;
                        continue;
                    }
                } else {
                    lean_dec_ref_known(v_value_3904_, 3);
                    lean_dec_ref_known(v_code_3749_, 2);
                    v_a_4190_ = lean_ctor_get(v___x_4136_, 0);
                    v_isSharedCheck_4197_ = (!lean_is_exclusive(v___x_4136_)) as u8;
                    if v_isSharedCheck_4197_ == 0 {
                        v___x_4192_ = v___x_4136_;
                        v_isShared_4193_ = v_isSharedCheck_4197_;
                        state = 57;
                        continue;
                    } else {
                        lean_inc(v_a_4190_);
                        lean_dec(v___x_4136_);
                        v___x_4192_ = lean_box(0);
                        v_isShared_4193_ = v_isSharedCheck_4197_;
                        state = 57;
                        continue;
                    }
                }
            }
            51 => {
                v_val_4143_ = lean_ctor_get(v_value_4139_, 0);
                lean_inc(v_val_4143_);
                lean_dec_ref_known(v_value_4139_, 1);
                v___x_4144_ = lean_unsigned_to_nat(0);
                v___x_4145_ = lean_nat_dec_eq(v_val_4143_, v___x_4144_);
                lean_dec(v_val_4143_);
                if v___x_4145_ == 0 {
                    lean_del_object(v___x_4141_);
                    lean_inc_ref(v_k_3861_);
                    v___x_4146_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                        v_k_3861_,
                        v___y_4129_,
                        v___y_4130_,
                        v___y_4131_,
                        v___y_4132_,
                        v___y_4133_,
                        v___y_4134_,
                    );
                    if lean_obj_tag(v___x_4146_) == 0 {
                        v_a_4147_ = lean_ctor_get(v___x_4146_, 0);
                        lean_inc(v_a_4147_);
                        lean_dec_ref_known(v___x_4146_, 1);
                        v___x_4148_ = lean_ptr_addr(v_k_3861_);
                        v___x_4149_ = lean_ptr_addr(v_a_4147_);
                        v___x_4150_ = lean_usize_dec_eq(v___x_4148_, v___x_4149_);
                        if v___x_4150_ == 0 {
                            v___y_3877_ = v_a_4147_;
                            v___y_3878_ = v___x_4150_;
                            state = 16;
                            continue;
                        } else {
                            v___x_4151_ = lean_ptr_addr(v_decl_3860_);
                            v___x_4152_ = lean_usize_dec_eq(v___x_4151_, v___x_4151_);
                            v___y_3877_ = v_a_4147_;
                            v___y_3878_ = v___x_4152_;
                            state = 16;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_3749_, 2);
                        return v___x_4146_;
                    }
                } else {
                    lean_inc_ref(v_decl_3860_);
                    v___x_4153_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction(v_decl_3860_, v___y_4129_, v___y_4130_, v___y_4131_, v___y_4132_, v___y_4133_, v___y_4134_);
                    if lean_obj_tag(v___x_4153_) == 0 {
                        v_a_4154_ = lean_ctor_get(v___x_4153_, 0);
                        lean_inc(v_a_4154_);
                        lean_dec_ref_known(v___x_4153_, 1);
                        v___x_4155_ = lean_box(0);
                        v___x_4156_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode___closed__4;
                        if v_isShared_4142_ == 0 {
                            lean_ctor_set(v___x_4141_, 2, v___x_4156_);
                            lean_ctor_set(v___x_4141_, 1, v___x_4155_);
                            lean_ctor_set(v___x_4141_, 0, v_a_4154_);
                            v___x_4158_ = v___x_4141_;
                            state = 52;
                            continue;
                        } else {
                            v_reuseFailAlloc_4177_ = lean_alloc_ctor(3, 3, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4177_, 0, v_a_4154_);
                            lean_ctor_set(v_reuseFailAlloc_4177_, 1, v___x_4155_);
                            lean_ctor_set(v_reuseFailAlloc_4177_, 2, v___x_4156_);
                            v___x_4158_ = v_reuseFailAlloc_4177_;
                            state = 52;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_4141_);
                        lean_dec_ref_known(v_code_3749_, 2);
                        v_a_4178_ = lean_ctor_get(v___x_4153_, 0);
                        v_isSharedCheck_4185_ = (!lean_is_exclusive(v___x_4153_)) as u8;
                        if v_isSharedCheck_4185_ == 0 {
                            v___x_4180_ = v___x_4153_;
                            v_isShared_4181_ = v_isSharedCheck_4185_;
                            state = 55;
                            continue;
                        } else {
                            lean_inc(v_a_4178_);
                            lean_dec(v___x_4153_);
                            v___x_4180_ = lean_box(0);
                            v_isShared_4181_ = v_isSharedCheck_4185_;
                            state = 55;
                            continue;
                        }
                    }
                }
            }
            52 => {
                lean_inc_ref(v_decl_3860_);
                v___x_4159_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                    v___x_4135_,
                    v_decl_3860_,
                    v___x_4158_,
                    v___y_4132_,
                );
                if lean_obj_tag(v___x_4159_) == 0 {
                    v_a_4160_ = lean_ctor_get(v___x_4159_, 0);
                    lean_inc(v_a_4160_);
                    lean_dec_ref_known(v___x_4159_, 1);
                    lean_inc_ref(v_k_3861_);
                    v___x_4161_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                        v_k_3861_,
                        v___y_4129_,
                        v___y_4130_,
                        v___y_4131_,
                        v___y_4132_,
                        v___y_4133_,
                        v___y_4134_,
                    );
                    if lean_obj_tag(v___x_4161_) == 0 {
                        v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
                        lean_inc(v_a_4162_);
                        lean_dec_ref_known(v___x_4161_, 1);
                        v___x_4163_ = lean_ptr_addr(v_k_3861_);
                        v___x_4164_ = lean_ptr_addr(v_a_4162_);
                        v___x_4165_ = lean_usize_dec_eq(v___x_4163_, v___x_4164_);
                        if v___x_4165_ == 0 {
                            v___y_3840_ = v_a_4160_;
                            v___y_3841_ = v_a_4162_;
                            v___y_3842_ = v___x_4165_;
                            state = 10;
                            continue;
                        } else {
                            v___x_4166_ = lean_ptr_addr(v_decl_3860_);
                            v___x_4167_ = lean_ptr_addr(v_a_4160_);
                            v___x_4168_ = lean_usize_dec_eq(v___x_4166_, v___x_4167_);
                            v___y_3840_ = v_a_4160_;
                            v___y_3841_ = v_a_4162_;
                            v___y_3842_ = v___x_4168_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4160_);
                        lean_dec_ref_known(v_code_3749_, 2);
                        return v___x_4161_;
                    }
                } else {
                    lean_dec_ref_known(v_code_3749_, 2);
                    v_a_4169_ = lean_ctor_get(v___x_4159_, 0);
                    v_isSharedCheck_4176_ = (!lean_is_exclusive(v___x_4159_)) as u8;
                    if v_isSharedCheck_4176_ == 0 {
                        v___x_4171_ = v___x_4159_;
                        v_isShared_4172_ = v_isSharedCheck_4176_;
                        state = 53;
                        continue;
                    } else {
                        lean_inc(v_a_4169_);
                        lean_dec(v___x_4159_);
                        v___x_4171_ = lean_box(0);
                        v_isShared_4172_ = v_isSharedCheck_4176_;
                        state = 53;
                        continue;
                    }
                }
            }
            53 => {
                if v_isShared_4172_ == 0 {
                    v___x_4174_ = v___x_4171_;
                    state = 54;
                    continue;
                } else {
                    v_reuseFailAlloc_4175_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4175_, 0, v_a_4169_);
                    v___x_4174_ = v_reuseFailAlloc_4175_;
                    state = 54;
                    continue;
                }
            }
            54 => {
                return v___x_4174_;
            }
            55 => {
                if v_isShared_4181_ == 0 {
                    v___x_4183_ = v___x_4180_;
                    state = 56;
                    continue;
                } else {
                    v_reuseFailAlloc_4184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4184_, 0, v_a_4178_);
                    v___x_4183_ = v_reuseFailAlloc_4184_;
                    state = 56;
                    continue;
                }
            }
            56 => {
                return v___x_4183_;
            }
            57 => {
                if v_isShared_4193_ == 0 {
                    v___x_4195_ = v___x_4192_;
                    state = 58;
                    continue;
                } else {
                    v_reuseFailAlloc_4196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4196_, 0, v_a_4190_);
                    v___x_4195_ = v_reuseFailAlloc_4196_;
                    state = 58;
                    continue;
                }
            }
            58 => {
                return v___x_4195_;
            }
            59 => {
                v___x_4226_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_4222_);
                v___x_4227_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v___x_4226_, v_alts_4222_, v_a_3750_, v_a_3751_, v_a_3752_, v_a_3753_, v_a_3754_, v_a_3755_);
                if lean_obj_tag(v___x_4227_) == 0 {
                    v_a_4228_ = lean_ctor_get(v___x_4227_, 0);
                    v_isSharedCheck_4252_ = (!lean_is_exclusive(v___x_4227_)) as u8;
                    if v_isSharedCheck_4252_ == 0 {
                        v___x_4230_ = v___x_4227_;
                        v_isShared_4231_ = v_isSharedCheck_4252_;
                        state = 60;
                        continue;
                    } else {
                        lean_inc(v_a_4228_);
                        lean_dec(v___x_4227_);
                        v___x_4230_ = lean_box(0);
                        v_isShared_4231_ = v_isSharedCheck_4252_;
                        state = 60;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4224_);
                    lean_dec_ref(v_alts_4222_);
                    lean_dec(v_discr_4221_);
                    lean_dec_ref(v_resultType_4220_);
                    lean_dec(v_typeName_4219_);
                    lean_dec_ref_known(v_code_3749_, 1);
                    v_a_4253_ = lean_ctor_get(v___x_4227_, 0);
                    v_isSharedCheck_4260_ = (!lean_is_exclusive(v___x_4227_)) as u8;
                    if v_isSharedCheck_4260_ == 0 {
                        v___x_4255_ = v___x_4227_;
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 66;
                        continue;
                    } else {
                        lean_inc(v_a_4253_);
                        lean_dec(v___x_4227_);
                        v___x_4255_ = lean_box(0);
                        v_isShared_4256_ = v_isSharedCheck_4260_;
                        state = 66;
                        continue;
                    }
                }
            }
            60 => {
                v___x_4232_ = lean_ptr_addr(v_alts_4222_);
                lean_dec_ref(v_alts_4222_);
                v___x_4233_ = lean_ptr_addr(v_a_4228_);
                v___x_4234_ = lean_usize_dec_eq(v___x_4232_, v___x_4233_);
                if v___x_4234_ == 0 {
                    v_isSharedCheck_4247_ = (!lean_is_exclusive(v_code_3749_)) as u8;
                    if v_isSharedCheck_4247_ == 0 {
                        v_unused_4248_ = lean_ctor_get(v_code_3749_, 0);
                        lean_dec(v_unused_4248_);
                        v___x_4236_ = v_code_3749_;
                        v_isShared_4237_ = v_isSharedCheck_4247_;
                        state = 61;
                        continue;
                    } else {
                        lean_dec(v_code_3749_);
                        v___x_4236_ = lean_box(0);
                        v_isShared_4237_ = v_isSharedCheck_4247_;
                        state = 61;
                        continue;
                    }
                } else {
                    lean_dec(v_a_4228_);
                    lean_del_object(v___x_4224_);
                    lean_dec(v_discr_4221_);
                    lean_dec_ref(v_resultType_4220_);
                    lean_dec(v_typeName_4219_);
                    if v_isShared_4231_ == 0 {
                        lean_ctor_set(v___x_4230_, 0, v_code_3749_);
                        v___x_4250_ = v___x_4230_;
                        state = 65;
                        continue;
                    } else {
                        v_reuseFailAlloc_4251_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4251_, 0, v_code_3749_);
                        v___x_4250_ = v_reuseFailAlloc_4251_;
                        state = 65;
                        continue;
                    }
                }
            }
            61 => {
                if v_isShared_4225_ == 0 {
                    lean_ctor_set(v___x_4224_, 3, v_a_4228_);
                    v___x_4239_ = v___x_4224_;
                    state = 62;
                    continue;
                } else {
                    v_reuseFailAlloc_4246_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4246_, 0, v_typeName_4219_);
                    lean_ctor_set(v_reuseFailAlloc_4246_, 1, v_resultType_4220_);
                    lean_ctor_set(v_reuseFailAlloc_4246_, 2, v_discr_4221_);
                    lean_ctor_set(v_reuseFailAlloc_4246_, 3, v_a_4228_);
                    v___x_4239_ = v_reuseFailAlloc_4246_;
                    state = 62;
                    continue;
                }
            }
            62 => {
                if v_isShared_4237_ == 0 {
                    lean_ctor_set(v___x_4236_, 0, v___x_4239_);
                    v___x_4241_ = v___x_4236_;
                    state = 63;
                    continue;
                } else {
                    v_reuseFailAlloc_4245_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4245_, 0, v___x_4239_);
                    v___x_4241_ = v_reuseFailAlloc_4245_;
                    state = 63;
                    continue;
                }
            }
            63 => {
                if v_isShared_4231_ == 0 {
                    lean_ctor_set(v___x_4230_, 0, v___x_4241_);
                    v___x_4243_ = v___x_4230_;
                    state = 64;
                    continue;
                } else {
                    v_reuseFailAlloc_4244_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4244_, 0, v___x_4241_);
                    v___x_4243_ = v_reuseFailAlloc_4244_;
                    state = 64;
                    continue;
                }
            }
            64 => {
                return v___x_4243_;
            }
            65 => {
                return v___x_4250_;
            }
            66 => {
                if v_isShared_4256_ == 0 {
                    v___x_4258_ = v___x_4255_;
                    state = 67;
                    continue;
                } else {
                    v_reuseFailAlloc_4259_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_a_4253_);
                    v___x_4258_ = v_reuseFailAlloc_4259_;
                    state = 67;
                    continue;
                }
            }
            67 => {
                return v___x_4258_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(
    mut v_i_4263_: *mut LeanObject,
    mut v_as_4264_: *mut LeanObject,
    mut v___y_4265_: *mut LeanObject,
    mut v___y_4266_: *mut LeanObject,
    mut v___y_4267_: *mut LeanObject,
    mut v___y_4268_: *mut LeanObject,
    mut v___y_4269_: *mut LeanObject,
    mut v___y_4270_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4273_: u8 = 0;
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: usize = 0;
    let mut v___x_4282_: usize = 0;
    let mut v___x_4283_: u8 = 0;
    let mut v___x_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4294_: u8 = 0;
    let mut v___x_4296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4298_: u8 = 0;
    let mut v_code_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4272_ = lean_array_get_size(v_as_4264_);
                v___x_4273_ = lean_nat_dec_lt(v_i_4263_, v___x_4272_);
                if v___x_4273_ == 0 {
                    lean_dec(v_i_4263_);
                    v___x_4274_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4274_, 0, v_as_4264_);
                    return v___x_4274_;
                } else {
                    v_a_4275_ = lean_array_fget_borrowed(v_as_4264_, v_i_4263_);
                    match lean_obj_tag(v_a_4275_) {
                        0 => {
                            v_code_4299_ = lean_ctor_get(v_a_4275_, 2);
                            lean_inc_ref(v_code_4299_);
                            v___y_4277_ = v_code_4299_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_4300_ = lean_ctor_get(v_a_4275_, 1);
                            lean_inc_ref(v_code_4300_);
                            v___y_4277_ = v_code_4300_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_4301_ = lean_ctor_get(v_a_4275_, 0);
                            lean_inc_ref(v_code_4301_);
                            v___y_4277_ = v_code_4301_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_4278_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
                    v___y_4277_,
                    v___y_4265_,
                    v___y_4266_,
                    v___y_4267_,
                    v___y_4268_,
                    v___y_4269_,
                    v___y_4270_,
                );
                if lean_obj_tag(v___x_4278_) == 0 {
                    v_a_4279_ = lean_ctor_get(v___x_4278_, 0);
                    lean_inc(v_a_4279_);
                    lean_dec_ref_known(v___x_4278_, 1);
                    lean_inc(v_a_4275_);
                    v___x_4280_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_4275_, v_a_4279_);
                    v___x_4281_ = lean_ptr_addr(v_a_4275_);
                    v___x_4282_ = lean_ptr_addr(v___x_4280_);
                    v___x_4283_ = lean_usize_dec_eq(v___x_4281_, v___x_4282_);
                    if v___x_4283_ == 0 {
                        v___x_4284_ = lean_unsigned_to_nat(1);
                        v___x_4285_ = lean_nat_add(v_i_4263_, v___x_4284_);
                        v___x_4286_ = lean_array_fset(v_as_4264_, v_i_4263_, v___x_4280_);
                        lean_dec(v_i_4263_);
                        v_i_4263_ = v___x_4285_;
                        v_as_4264_ = v___x_4286_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v___x_4280_);
                        v___x_4288_ = lean_unsigned_to_nat(1);
                        v___x_4289_ = lean_nat_add(v_i_4263_, v___x_4288_);
                        lean_dec(v_i_4263_);
                        v_i_4263_ = v___x_4289_;
                        state = 0;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_as_4264_);
                    lean_dec(v_i_4263_);
                    v_a_4291_ = lean_ctor_get(v___x_4278_, 0);
                    v_isSharedCheck_4298_ = (!lean_is_exclusive(v___x_4278_)) as u8;
                    if v_isSharedCheck_4298_ == 0 {
                        v___x_4293_ = v___x_4278_;
                        v_isShared_4294_ = v_isSharedCheck_4298_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4291_);
                        lean_dec(v___x_4278_);
                        v___x_4293_ = lean_box(0);
                        v_isShared_4294_ = v_isSharedCheck_4298_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4294_ == 0 {
                    v___x_4296_ = v___x_4293_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4297_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4297_, 0, v_a_4291_);
                    v___x_4296_ = v_reuseFailAlloc_4297_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1___boxed(
    mut v_i_4302_: *mut LeanObject,
    mut v_as_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
    mut v___y_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
    mut v___y_4309_: *mut LeanObject,
    mut v___y_4310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4311_: *mut LeanObject = core::ptr::null_mut();
    v_res_4311_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ExtractClosed_visitCode_spec__1(v_i_4302_, v_as_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
    lean_dec(v___y_4309_);
    lean_dec_ref(v___y_4308_);
    lean_dec(v___y_4307_);
    lean_dec_ref(v___y_4306_);
    lean_dec(v___y_4305_);
    lean_dec_ref(v___y_4304_);
    return v_res_4311_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_visitCode___boxed(
    mut v_code_4312_: *mut LeanObject,
    mut v_a_4313_: *mut LeanObject,
    mut v_a_4314_: *mut LeanObject,
    mut v_a_4315_: *mut LeanObject,
    mut v_a_4316_: *mut LeanObject,
    mut v_a_4317_: *mut LeanObject,
    mut v_a_4318_: *mut LeanObject,
    mut v_a_4319_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4320_: *mut LeanObject = core::ptr::null_mut();
    v_res_4320_ = l_Lean_Compiler_LCNF_ExtractClosed_visitCode(
        v_code_4312_,
        v_a_4313_,
        v_a_4314_,
        v_a_4315_,
        v_a_4316_,
        v_a_4317_,
        v_a_4318_,
    );
    lean_dec(v_a_4318_);
    lean_dec_ref(v_a_4317_);
    lean_dec(v_a_4316_);
    lean_dec_ref(v_a_4315_);
    lean_dec(v_a_4314_);
    lean_dec_ref(v_a_4313_);
    return v_res_4320_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(
    mut v_f_4321_: *mut LeanObject,
    mut v_v_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
    mut v___y_4327_: *mut LeanObject,
    mut v___y_4328_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_code_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4333_: u8 = 0;
    let mut v___x_4334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4335_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4338_: u8 = 0;
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_a_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4353_: u8 = 0;
    let mut v_isSharedCheck_4354_: u8 = 0;
    let mut v___x_4355_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_v_4322_) == 0 {
                    v_code_4330_ = lean_ctor_get(v_v_4322_, 0);
                    v_isSharedCheck_4354_ = (!lean_is_exclusive(v_v_4322_)) as u8;
                    if v_isSharedCheck_4354_ == 0 {
                        v___x_4332_ = v_v_4322_;
                        v_isShared_4333_ = v_isSharedCheck_4354_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_code_4330_);
                        lean_dec(v_v_4322_);
                        v___x_4332_ = lean_box(0);
                        v_isShared_4333_ = v_isSharedCheck_4354_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_4321_);
                    v___x_4355_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4355_, 0, v_v_4322_);
                    return v___x_4355_;
                }
            }
            1 => {
                lean_inc(v___y_4328_);
                lean_inc_ref(v___y_4327_);
                lean_inc(v___y_4326_);
                lean_inc_ref(v___y_4325_);
                lean_inc(v___y_4324_);
                lean_inc_ref(v___y_4323_);
                v___x_4334_ = lean_apply_8(
                    v_f_4321_,
                    v_code_4330_,
                    v___y_4323_,
                    v___y_4324_,
                    v___y_4325_,
                    v___y_4326_,
                    v___y_4327_,
                    v___y_4328_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_4334_) == 0 {
                    v_a_4335_ = lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4345_ = (!lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4345_ == 0 {
                        v___x_4337_ = v___x_4334_;
                        v_isShared_4338_ = v_isSharedCheck_4345_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4335_);
                        lean_dec(v___x_4334_);
                        v___x_4337_ = lean_box(0);
                        v_isShared_4338_ = v_isSharedCheck_4345_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4332_);
                    v_a_4346_ = lean_ctor_get(v___x_4334_, 0);
                    v_isSharedCheck_4353_ = (!lean_is_exclusive(v___x_4334_)) as u8;
                    if v_isSharedCheck_4353_ == 0 {
                        v___x_4348_ = v___x_4334_;
                        v_isShared_4349_ = v_isSharedCheck_4353_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4346_);
                        lean_dec(v___x_4334_);
                        v___x_4348_ = lean_box(0);
                        v_isShared_4349_ = v_isSharedCheck_4353_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4333_ == 0 {
                    lean_ctor_set(v___x_4332_, 0, v_a_4335_);
                    v___x_4340_ = v___x_4332_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4335_);
                    v___x_4340_ = v_reuseFailAlloc_4344_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4338_ == 0 {
                    lean_ctor_set(v___x_4337_, 0, v___x_4340_);
                    v___x_4342_ = v___x_4337_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4343_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4343_, 0, v___x_4340_);
                    v___x_4342_ = v_reuseFailAlloc_4343_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4342_;
            }
            5 => {
                if v_isShared_4349_ == 0 {
                    v___x_4351_ = v___x_4348_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4352_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
                    v___x_4351_ = v_reuseFailAlloc_4352_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4351_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg___boxed(
    mut v_f_4356_: *mut LeanObject,
    mut v_v_4357_: *mut LeanObject,
    mut v___y_4358_: *mut LeanObject,
    mut v___y_4359_: *mut LeanObject,
    mut v___y_4360_: *mut LeanObject,
    mut v___y_4361_: *mut LeanObject,
    mut v___y_4362_: *mut LeanObject,
    mut v___y_4363_: *mut LeanObject,
    mut v___y_4364_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4365_: *mut LeanObject = core::ptr::null_mut();
    v_res_4365_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_4356_, v_v_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
    lean_dec(v___y_4363_);
    lean_dec_ref(v___y_4362_);
    lean_dec(v___y_4361_);
    lean_dec_ref(v___y_4360_);
    lean_dec(v___y_4359_);
    lean_dec_ref(v___y_4358_);
    return v_res_4365_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(
    mut v_pu_4366_: u8,
    mut v_f_4367_: *mut LeanObject,
    mut v_v_4368_: *mut LeanObject,
    mut v___y_4369_: *mut LeanObject,
    mut v___y_4370_: *mut LeanObject,
    mut v___y_4371_: *mut LeanObject,
    mut v___y_4372_: *mut LeanObject,
    mut v___y_4373_: *mut LeanObject,
    mut v___y_4374_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4376_: *mut LeanObject = core::ptr::null_mut();
    v___x_4376_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v_f_4367_, v_v_4368_, v___y_4369_, v___y_4370_, v___y_4371_, v___y_4372_, v___y_4373_, v___y_4374_);
    return v___x_4376_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___boxed(
    mut v_pu_4377_: *mut LeanObject,
    mut v_f_4378_: *mut LeanObject,
    mut v_v_4379_: *mut LeanObject,
    mut v___y_4380_: *mut LeanObject,
    mut v___y_4381_: *mut LeanObject,
    mut v___y_4382_: *mut LeanObject,
    mut v___y_4383_: *mut LeanObject,
    mut v___y_4384_: *mut LeanObject,
    mut v___y_4385_: *mut LeanObject,
    mut v___y_4386_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_pu_boxed_4387_: u8 = 0;
    let mut v_res_4388_: *mut LeanObject = core::ptr::null_mut();
    v_pu_boxed_4387_ = (lean_unbox(v_pu_4377_) as u8);
    v_res_4388_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0(v_pu_boxed_4387_, v_f_4378_, v_v_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
    lean_dec(v___y_4385_);
    lean_dec_ref(v___y_4384_);
    lean_dec(v___y_4383_);
    lean_dec_ref(v___y_4382_);
    lean_dec(v___y_4381_);
    lean_dec_ref(v___y_4380_);
    return v_res_4388_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(
    mut v_decl_4390_: *mut LeanObject,
    mut v_a_4391_: *mut LeanObject,
    mut v_a_4392_: *mut LeanObject,
    mut v_a_4393_: *mut LeanObject,
    mut v_a_4394_: *mut LeanObject,
    mut v_a_4395_: *mut LeanObject,
    mut v_a_4396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_toSignature_4398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_4399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_recursive_4400_: u8 = 0;
    let mut v_inlineAttr_x3f_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4404_: u8 = 0;
    let mut v___x_4405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4407_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4410_: u8 = 0;
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4417_: u8 = 0;
    let mut v_a_4418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4421_: u8 = 0;
    let mut v___x_4423_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4425_: u8 = 0;
    let mut v_isSharedCheck_4426_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_4398_ = lean_ctor_get(v_decl_4390_, 0);
                v_value_4399_ = lean_ctor_get(v_decl_4390_, 1);
                v_recursive_4400_ = lean_ctor_get_uint8(
                    v_decl_4390_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                );
                v_inlineAttr_x3f_4401_ = lean_ctor_get(v_decl_4390_, 2);
                v_isSharedCheck_4426_ = (!lean_is_exclusive(v_decl_4390_)) as u8;
                if v_isSharedCheck_4426_ == 0 {
                    v___x_4403_ = v_decl_4390_;
                    v_isShared_4404_ = v_isSharedCheck_4426_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_inlineAttr_x3f_4401_);
                    lean_inc(v_value_4399_);
                    lean_inc(v_toSignature_4398_);
                    lean_dec(v_decl_4390_);
                    v___x_4403_ = lean_box(0);
                    v_isShared_4404_ = v_isSharedCheck_4426_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4405_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___closed__0;
                v___x_4406_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_ExtractClosed_visitDecl_spec__0___redArg(v___x_4405_, v_value_4399_, v_a_4391_, v_a_4392_, v_a_4393_, v_a_4394_, v_a_4395_, v_a_4396_);
                if lean_obj_tag(v___x_4406_) == 0 {
                    v_a_4407_ = lean_ctor_get(v___x_4406_, 0);
                    v_isSharedCheck_4417_ = (!lean_is_exclusive(v___x_4406_)) as u8;
                    if v_isSharedCheck_4417_ == 0 {
                        v___x_4409_ = v___x_4406_;
                        v_isShared_4410_ = v_isSharedCheck_4417_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4407_);
                        lean_dec(v___x_4406_);
                        v___x_4409_ = lean_box(0);
                        v_isShared_4410_ = v_isSharedCheck_4417_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4403_);
                    lean_dec(v_inlineAttr_x3f_4401_);
                    lean_dec_ref(v_toSignature_4398_);
                    v_a_4418_ = lean_ctor_get(v___x_4406_, 0);
                    v_isSharedCheck_4425_ = (!lean_is_exclusive(v___x_4406_)) as u8;
                    if v_isSharedCheck_4425_ == 0 {
                        v___x_4420_ = v___x_4406_;
                        v_isShared_4421_ = v_isSharedCheck_4425_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4418_);
                        lean_dec(v___x_4406_);
                        v___x_4420_ = lean_box(0);
                        v_isShared_4421_ = v_isSharedCheck_4425_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4404_ == 0 {
                    lean_ctor_set(v___x_4403_, 1, v_a_4407_);
                    v___x_4412_ = v___x_4403_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4416_ = lean_alloc_ctor(0, 3, (1) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4416_, 0, v_toSignature_4398_);
                    lean_ctor_set(v_reuseFailAlloc_4416_, 1, v_a_4407_);
                    lean_ctor_set(v_reuseFailAlloc_4416_, 2, v_inlineAttr_x3f_4401_);
                    lean_ctor_set_uint8(
                        v_reuseFailAlloc_4416_,
                        (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                        v_recursive_4400_,
                    );
                    v___x_4412_ = v_reuseFailAlloc_4416_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4410_ == 0 {
                    lean_ctor_set(v___x_4409_, 0, v___x_4412_);
                    v___x_4414_ = v___x_4409_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4415_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4415_, 0, v___x_4412_);
                    v___x_4414_ = v_reuseFailAlloc_4415_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4414_;
            }
            5 => {
                if v_isShared_4421_ == 0 {
                    v___x_4423_ = v___x_4420_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4424_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4424_, 0, v_a_4418_);
                    v___x_4423_ = v_reuseFailAlloc_4424_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4423_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_ExtractClosed_visitDecl___boxed(
    mut v_decl_4427_: *mut LeanObject,
    mut v_a_4428_: *mut LeanObject,
    mut v_a_4429_: *mut LeanObject,
    mut v_a_4430_: *mut LeanObject,
    mut v_a_4431_: *mut LeanObject,
    mut v_a_4432_: *mut LeanObject,
    mut v_a_4433_: *mut LeanObject,
    mut v_a_4434_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4435_: *mut LeanObject = core::ptr::null_mut();
    v_res_4435_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(
        v_decl_4427_,
        v_a_4428_,
        v_a_4429_,
        v_a_4430_,
        v_a_4431_,
        v_a_4432_,
        v_a_4433_,
    );
    lean_dec(v_a_4433_);
    lean_dec_ref(v_a_4432_);
    lean_dec(v_a_4431_);
    lean_dec_ref(v_a_4430_);
    lean_dec(v_a_4429_);
    lean_dec_ref(v_a_4428_);
    return v_res_4435_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1() -> *mut LeanObject {
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4440_: *mut LeanObject = core::ptr::null_mut();
    v___x_4438_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2_once), _init_l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_ExtractClosed_visitCode_performExtraction___closed__2);
    v___x_4439_ = l_Lean_Compiler_LCNF_Decl_extractClosed___closed__0;
    v___x_4440_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_4440_, 0, v___x_4439_);
    lean_ctor_set(v___x_4440_, 1, v___x_4438_);
    return v___x_4440_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_extractClosed(
    mut v_decl_4441_: *mut LeanObject,
    mut v_sccDecls_4442_: *mut LeanObject,
    mut v_a_4443_: *mut LeanObject,
    mut v_a_4444_: *mut LeanObject,
    mut v_a_4445_: *mut LeanObject,
    mut v_a_4446_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4450_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toSignature_4451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_name_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4458_: u8 = 0;
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decls_4460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: u8 = 0;
    let mut v___x_4469_: u8 = 0;
    let mut v___x_4470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4475_: u8 = 0;
    let mut v___x_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_isSharedCheck_4480_: u8 = 0;
    let mut v_a_4481_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4484_: u8 = 0;
    let mut v___x_4486_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4487_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4488_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4448_ = lean_unsigned_to_nat(0);
                v___x_4449_ = lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Decl_extractClosed___closed__1,
                );
                v___x_4450_ = lean_st_mk_ref(v___x_4449_);
                v_toSignature_4451_ = lean_ctor_get(v_decl_4441_, 0);
                v_name_4452_ = lean_ctor_get(v_toSignature_4451_, 0);
                lean_inc(v_name_4452_);
                v___x_4453_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4453_, 0, v_name_4452_);
                lean_ctor_set(v___x_4453_, 1, v_sccDecls_4442_);
                v___x_4454_ = l_Lean_Compiler_LCNF_ExtractClosed_visitDecl(
                    v_decl_4441_,
                    v___x_4453_,
                    v___x_4450_,
                    v_a_4443_,
                    v_a_4444_,
                    v_a_4445_,
                    v_a_4446_,
                );
                lean_dec_ref_known(v___x_4453_, 2);
                if lean_obj_tag(v___x_4454_) == 0 {
                    v_a_4455_ = lean_ctor_get(v___x_4454_, 0);
                    v_isSharedCheck_4480_ = (!lean_is_exclusive(v___x_4454_)) as u8;
                    if v_isSharedCheck_4480_ == 0 {
                        v___x_4457_ = v___x_4454_;
                        v_isShared_4458_ = v_isSharedCheck_4480_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4455_);
                        lean_dec(v___x_4454_);
                        v___x_4457_ = lean_box(0);
                        v_isShared_4458_ = v_isSharedCheck_4480_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4450_);
                    v_a_4481_ = lean_ctor_get(v___x_4454_, 0);
                    v_isSharedCheck_4488_ = (!lean_is_exclusive(v___x_4454_)) as u8;
                    if v_isSharedCheck_4488_ == 0 {
                        v___x_4483_ = v___x_4454_;
                        v_isShared_4484_ = v_isSharedCheck_4488_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4481_);
                        lean_dec(v___x_4454_);
                        v___x_4483_ = lean_box(0);
                        v_isShared_4484_ = v_isSharedCheck_4488_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4459_ = lean_st_ref_get(v___x_4450_);
                lean_dec(v___x_4450_);
                v_decls_4460_ = lean_ctor_get(v___x_4459_, 0);
                lean_inc_ref(v_decls_4460_);
                lean_dec(v___x_4459_);
                v___x_4467_ = lean_array_get_size(v_decls_4460_);
                v___x_4468_ = lean_nat_dec_eq(v___x_4467_, v___x_4448_);
                if v___x_4468_ == 0 {
                    v___x_4469_ = 0;
                    v___x_4470_ = l_Lean_Compiler_LCNF_Decl_elimDeadVars(
                        v___x_4469_,
                        v_a_4455_,
                        v_a_4443_,
                        v_a_4444_,
                        v_a_4445_,
                        v_a_4446_,
                    );
                    if lean_obj_tag(v___x_4470_) == 0 {
                        v_a_4471_ = lean_ctor_get(v___x_4470_, 0);
                        lean_inc(v_a_4471_);
                        lean_dec_ref_known(v___x_4470_, 1);
                        v_decl_4462_ = v_a_4471_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec_ref(v_decls_4460_);
                        lean_del_object(v___x_4457_);
                        v_a_4472_ = lean_ctor_get(v___x_4470_, 0);
                        v_isSharedCheck_4479_ = (!lean_is_exclusive(v___x_4470_)) as u8;
                        if v_isSharedCheck_4479_ == 0 {
                            v___x_4474_ = v___x_4470_;
                            v_isShared_4475_ = v_isSharedCheck_4479_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4472_);
                            lean_dec(v___x_4470_);
                            v___x_4474_ = lean_box(0);
                            v_isShared_4475_ = v_isSharedCheck_4479_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_decl_4462_ = v_a_4455_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4463_ = lean_array_push(v_decls_4460_, v_decl_4462_);
                if v_isShared_4458_ == 0 {
                    lean_ctor_set(v___x_4457_, 0, v___x_4463_);
                    v___x_4465_ = v___x_4457_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4466_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4466_, 0, v___x_4463_);
                    v___x_4465_ = v_reuseFailAlloc_4466_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4465_;
            }
            4 => {
                if v_isShared_4475_ == 0 {
                    v___x_4477_ = v___x_4474_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_a_4472_);
                    v___x_4477_ = v_reuseFailAlloc_4478_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4477_;
            }
            6 => {
                if v_isShared_4484_ == 0 {
                    v___x_4486_ = v___x_4483_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4487_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4487_, 0, v_a_4481_);
                    v___x_4486_ = v_reuseFailAlloc_4487_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4486_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_extractClosed___boxed(
    mut v_decl_4489_: *mut LeanObject,
    mut v_sccDecls_4490_: *mut LeanObject,
    mut v_a_4491_: *mut LeanObject,
    mut v_a_4492_: *mut LeanObject,
    mut v_a_4493_: *mut LeanObject,
    mut v_a_4494_: *mut LeanObject,
    mut v_a_4495_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4496_: *mut LeanObject = core::ptr::null_mut();
    v_res_4496_ = l_Lean_Compiler_LCNF_Decl_extractClosed(
        v_decl_4489_,
        v_sccDecls_4490_,
        v_a_4491_,
        v_a_4492_,
        v_a_4493_,
        v_a_4494_,
    );
    lean_dec(v_a_4494_);
    lean_dec_ref(v_a_4493_);
    lean_dec(v_a_4492_);
    lean_dec_ref(v_a_4491_);
    return v_res_4496_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(
    mut v_decls_4497_: *mut LeanObject,
    mut v_as_4498_: *mut LeanObject,
    mut v_i_4499_: usize,
    mut v_stop_4500_: usize,
    mut v_b_4501_: *mut LeanObject,
    mut v___y_4502_: *mut LeanObject,
    mut v___y_4503_: *mut LeanObject,
    mut v___y_4504_: *mut LeanObject,
    mut v___y_4505_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4508_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4509_: usize = 0;
    let mut v___x_4510_: usize = 0;
    let mut v___x_4512_: u8 = 0;
    let mut v___x_4513_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4518_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4512_ = lean_usize_dec_eq(v_i_4499_, v_stop_4500_);
                if v___x_4512_ == 0 {
                    v___x_4513_ = lean_array_uget_borrowed(v_as_4498_, v_i_4499_);
                    lean_inc_ref(v_decls_4497_);
                    lean_inc(v___x_4513_);
                    v___x_4514_ = l_Lean_Compiler_LCNF_Decl_extractClosed(
                        v___x_4513_,
                        v_decls_4497_,
                        v___y_4502_,
                        v___y_4503_,
                        v___y_4504_,
                        v___y_4505_,
                    );
                    if lean_obj_tag(v___x_4514_) == 0 {
                        v_a_4515_ = lean_ctor_get(v___x_4514_, 0);
                        lean_inc(v_a_4515_);
                        lean_dec_ref_known(v___x_4514_, 1);
                        v___x_4516_ = l_Array_append___redArg(v_b_4501_, v_a_4515_);
                        lean_dec(v_a_4515_);
                        v_a_4508_ = v___x_4516_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec_ref(v_b_4501_);
                        if lean_obj_tag(v___x_4514_) == 0 {
                            v_a_4517_ = lean_ctor_get(v___x_4514_, 0);
                            lean_inc(v_a_4517_);
                            lean_dec_ref_known(v___x_4514_, 1);
                            v_a_4508_ = v_a_4517_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_decls_4497_);
                            return v___x_4514_;
                        }
                    }
                } else {
                    lean_dec_ref(v_decls_4497_);
                    v___x_4518_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4518_, 0, v_b_4501_);
                    return v___x_4518_;
                }
            }
            1 => {
                v___x_4509_ = 1usize;
                v___x_4510_ = lean_usize_add(v_i_4499_, v___x_4509_);
                v_i_4499_ = v___x_4510_;
                v_b_4501_ = v_a_4508_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0___boxed(
    mut v_decls_4519_: *mut LeanObject,
    mut v_as_4520_: *mut LeanObject,
    mut v_i_4521_: *mut LeanObject,
    mut v_stop_4522_: *mut LeanObject,
    mut v_b_4523_: *mut LeanObject,
    mut v___y_4524_: *mut LeanObject,
    mut v___y_4525_: *mut LeanObject,
    mut v___y_4526_: *mut LeanObject,
    mut v___y_4527_: *mut LeanObject,
    mut v___y_4528_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_4529_: usize = 0;
    let mut v_stop_boxed_4530_: usize = 0;
    let mut v_res_4531_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_4529_ = lean_unbox_usize(v_i_4521_);
    lean_dec(v_i_4521_);
    v_stop_boxed_4530_ = lean_unbox_usize(v_stop_4522_);
    lean_dec(v_stop_4522_);
    v_res_4531_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_4519_, v_as_4520_, v_i_boxed_4529_, v_stop_boxed_4530_, v_b_4523_, v___y_4524_, v___y_4525_, v___y_4526_, v___y_4527_);
    lean_dec(v___y_4527_);
    lean_dec_ref(v___y_4526_);
    lean_dec(v___y_4525_);
    lean_dec_ref(v___y_4524_);
    lean_dec_ref(v_as_4520_);
    return v_res_4531_;
}
pub unsafe fn l_Lean_Compiler_LCNF_extractClosed___lam__0(
    mut v___x_4532_: *mut LeanObject,
    mut v_decls_4533_: *mut LeanObject,
    mut v___y_4534_: *mut LeanObject,
    mut v___y_4535_: *mut LeanObject,
    mut v___y_4536_: *mut LeanObject,
    mut v___y_4537_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4543_: u8 = 0;
    let mut v_extractClosed_4544_: u8 = 0;
    let mut v___x_4546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4550_: u8 = 0;
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4554_: u8 = 0;
    let mut v___x_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: usize = 0;
    let mut v___x_4559_: usize = 0;
    let mut v___x_4560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4561_: usize = 0;
    let mut v___x_4562_: usize = 0;
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4564_: u8 = 0;
    let mut v_a_4565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4568_: u8 = 0;
    let mut v___x_4570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4572_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4539_ = l_Lean_Compiler_LCNF_getConfig___redArg(v___y_4534_);
                if lean_obj_tag(v___x_4539_) == 0 {
                    v_a_4540_ = lean_ctor_get(v___x_4539_, 0);
                    v_isSharedCheck_4564_ = (!lean_is_exclusive(v___x_4539_)) as u8;
                    if v_isSharedCheck_4564_ == 0 {
                        v___x_4542_ = v___x_4539_;
                        v_isShared_4543_ = v_isSharedCheck_4564_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4540_);
                        lean_dec(v___x_4539_);
                        v___x_4542_ = lean_box(0);
                        v_isShared_4543_ = v_isSharedCheck_4564_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decls_4533_);
                    v_a_4565_ = lean_ctor_get(v___x_4539_, 0);
                    v_isSharedCheck_4572_ = (!lean_is_exclusive(v___x_4539_)) as u8;
                    if v_isSharedCheck_4572_ == 0 {
                        v___x_4567_ = v___x_4539_;
                        v_isShared_4568_ = v_isSharedCheck_4572_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4565_);
                        lean_dec(v___x_4539_);
                        v___x_4567_ = lean_box(0);
                        v_isShared_4568_ = v_isSharedCheck_4572_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_extractClosed_4544_ = lean_ctor_get_uint8(
                    v_a_4540_,
                    (core::mem::size_of::<*mut LeanObject>() * 4 + 1) as u32,
                );
                lean_dec(v_a_4540_);
                if v_extractClosed_4544_ == 0 {
                    if v_isShared_4543_ == 0 {
                        lean_ctor_set(v___x_4542_, 0, v_decls_4533_);
                        v___x_4546_ = v___x_4542_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4547_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4547_, 0, v_decls_4533_);
                        v___x_4546_ = v_reuseFailAlloc_4547_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_4548_ = lean_mk_empty_array_with_capacity(v___x_4532_);
                    v___x_4549_ = lean_array_get_size(v_decls_4533_);
                    v___x_4550_ = lean_nat_dec_lt(v___x_4532_, v___x_4549_);
                    if v___x_4550_ == 0 {
                        lean_dec_ref(v_decls_4533_);
                        if v_isShared_4543_ == 0 {
                            lean_ctor_set(v___x_4542_, 0, v___x_4548_);
                            v___x_4552_ = v___x_4542_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4553_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_4553_, 0, v___x_4548_);
                            v___x_4552_ = v_reuseFailAlloc_4553_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4554_ = lean_nat_dec_le(v___x_4549_, v___x_4549_);
                        if v___x_4554_ == 0 {
                            if v___x_4550_ == 0 {
                                lean_dec_ref(v_decls_4533_);
                                if v_isShared_4543_ == 0 {
                                    lean_ctor_set(v___x_4542_, 0, v___x_4548_);
                                    v___x_4556_ = v___x_4542_;
                                    state = 4;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4557_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_4557_, 0, v___x_4548_);
                                    v___x_4556_ = v_reuseFailAlloc_4557_;
                                    state = 4;
                                    continue;
                                }
                            } else {
                                lean_del_object(v___x_4542_);
                                v___x_4558_ = 0usize;
                                v___x_4559_ = lean_usize_of_nat(v___x_4549_);
                                lean_inc_ref(v_decls_4533_);
                                v___x_4560_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_4533_, v_decls_4533_, v___x_4558_, v___x_4559_, v___x_4548_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
                                lean_dec_ref(v_decls_4533_);
                                return v___x_4560_;
                            }
                        } else {
                            lean_del_object(v___x_4542_);
                            v___x_4561_ = 0usize;
                            v___x_4562_ = lean_usize_of_nat(v___x_4549_);
                            lean_inc_ref(v_decls_4533_);
                            v___x_4563_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_extractClosed_spec__0(v_decls_4533_, v_decls_4533_, v___x_4561_, v___x_4562_, v___x_4548_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
                            lean_dec_ref(v_decls_4533_);
                            return v___x_4563_;
                        }
                    }
                }
            }
            2 => {
                return v___x_4546_;
            }
            3 => {
                return v___x_4552_;
            }
            4 => {
                return v___x_4556_;
            }
            5 => {
                if v_isShared_4568_ == 0 {
                    v___x_4570_ = v___x_4567_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4571_, 0, v_a_4565_);
                    v___x_4570_ = v_reuseFailAlloc_4571_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4570_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_extractClosed___lam__0___boxed(
    mut v___x_4573_: *mut LeanObject,
    mut v_decls_4574_: *mut LeanObject,
    mut v___y_4575_: *mut LeanObject,
    mut v___y_4576_: *mut LeanObject,
    mut v___y_4577_: *mut LeanObject,
    mut v___y_4578_: *mut LeanObject,
    mut v___y_4579_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4580_: *mut LeanObject = core::ptr::null_mut();
    v_res_4580_ = l_Lean_Compiler_LCNF_extractClosed___lam__0(
        v___x_4573_,
        v_decls_4574_,
        v___y_4575_,
        v___y_4576_,
        v___y_4577_,
        v___y_4578_,
    );
    lean_dec(v___y_4578_);
    lean_dec_ref(v___y_4577_);
    lean_dec(v___y_4576_);
    lean_dec_ref(v___y_4575_);
    lean_dec(v___x_4573_);
    return v_res_4580_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4664_: u8 = 0;
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4666_: *mut LeanObject = core::ptr::null_mut();
    v___x_4663_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_;
    v___x_4664_ = 1;
    v___x_4665_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_;
    v___x_4666_ = l_Lean_registerTraceClass(v___x_4663_, v___x_4664_, v___x_4665_);
    return v___x_4666_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2____boxed(
    mut v_a_4667_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4668_: *mut LeanObject = core::ptr::null_mut();
    v_res_4668_ = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
    return v_res_4668_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_ClosedTermCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_NeverExtractAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ExtractClosed_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ExtractClosed_998081055____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    res = runtime_initialize_Init_Data_FloatArray_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_ExtractClosed(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_ClosedTermCache(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_NeverExtractAttr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_ElimDead(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_FloatArray_Basic(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ExtractClosed(builtin);
}
