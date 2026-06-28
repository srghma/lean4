// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceArity
// Imports: Lean.Compiler.LCNF.Internalize
use crate::r#gen::Init::Data::Array::Basic::l_Array_append___redArg;
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr2, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Param_toArg___redArg, l_Lean_Compiler_LCNF_instInhabitedCode_default__1,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg, l_Lean_Compiler_LCNF_eraseParams___redArg,
    l_Lean_Compiler_LCNF_getPurity___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    l_Lean_Compiler_LCNF_Code_inferType, l_Lean_Compiler_LCNF_mkAuxLetDecl,
    l_Lean_Compiler_LCNF_mkForallParams,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize, l_Lean_Compiler_LCNF_Internalize_internalizeParam,
    runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::PhaseExt::l_Lean_Compiler_LCNF_Decl_saveMono___redArg;
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_FVarIdSet_insert, l_Lean_instBEqFVarId_beq, l_Lean_instEmptyCollectionFVarIdHashSet,
    l_Lean_instHashableFVarId_hash, l_Lean_mkFVar,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
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
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_size, lean_array_push,
    lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_panic_fn_borrowed,
    lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
pub static l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value:
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
    m_fun: l_Lean_Compiler_LCNF_FindUsed_visit___boxed as *const core::ffi::c_void,
    m_arity: 8,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value:
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
        117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115,
        32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value:
    crate::leanh::LeanStringObject<68> = crate::leanh::LeanStringObject {
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
        108, 101, 114, 46, 76, 67, 78, 70, 46, 66, 97, 115, 105, 99, 46, 48, 46, 76, 101, 97, 110,
        46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 117, 112, 100, 97, 116,
        101, 70, 117, 110, 73, 109, 112, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value:
    crate::leanh::LeanStringObject<25> = crate::leanh::LeanStringObject {
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
        76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 66,
        97, 115, 105, 99, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4_value:
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
static mut l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4_value: crate::leanh::LeanStringObject<1> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value: crate::leanh::LeanStringObject<
    3,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__1_value)
            as *mut crate::leanh::LeanObject,
        7699194985028780469 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value: crate::leanh::LeanCtorObject<
    1,
> = crate::leanh::LeanCtorObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
            + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 1,
    },
    m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value:
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
    m_fun: l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value: crate::leanh::LeanStringObject<
    8,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [95, 114, 101, 100, 65, 114, 103, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__5_value)
            as *mut crate::leanh::LeanObject,
        13427258015795454894 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value: crate::leanh::LeanArrayObject<
    0,
> = crate::leanh::LeanArrayObject {
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
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value: crate::leanh::LeanStringObject<
    9,
> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value: crate::leanh::LeanStringObject<
    12,
> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [114, 101, 100, 117, 99, 101, 65, 114, 105, 116, 121, 0],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value)
            as *mut crate::leanh::LeanObject,
        2042452093243897853 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value)
            as *mut crate::leanh::LeanObject,
        17070998189071160153 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value:
    crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject {
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
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__11_value)
            as *mut crate::leanh::LeanObject,
        14231257465488249300 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value:
    crate::leanh::LeanStringObject<16> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        44, 32, 117, 115, 101, 100, 32, 112, 97, 114, 97, 109, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_reduceArity___closed__0_value: crate::leanh::LeanClosureObject<1> =
    crate::leanh::LeanClosureObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*const core::ffi::c_void>()
                + 4
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1)
                as u16,
            other: 0,
            tag: 245,
        },
        m_fun: l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed as *const core::ffi::c_void,
        m_arity: 7,
        m_num_fixed: 1,
        m_objs: [(((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject],
    };
static mut l_Lean_Compiler_LCNF_reduceArity___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_reduceArity___closed__1_value: crate::leanh::LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__9_value)
                as *mut crate::leanh::LeanObject,
            6230351632210813039 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_reduceArity___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__1_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Compiler_LCNF_reduceArity___closed__2_value: crate::leanh::LeanCtorObject<4> =
    crate::leanh::LeanCtorObject {
        m_header: crate::leanh::LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<crate::leanh::LeanObject>()
                + core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3
                + 8) as u16,
            other: 3,
            tag: 0,
        },
        m_objs: [
            (((0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__1_value)
                as *mut crate::leanh::LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__0_value)
                as *mut crate::leanh::LeanObject,
            257 as *mut crate::leanh::LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_reduceArity___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static mut l_Lean_Compiler_LCNF_reduceArity: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_reduceArity___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,11079354408986465895 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,10352885018404983386 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value) as *mut crate::leanh::LeanObject,1501781890156459336 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4203849195465939425 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [82, 101, 100, 117, 99, 101, 65, 114, 105, 116, 121, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13109072740202689192 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,4920082522366582657 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,14590473376816633124 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value) as *mut crate::leanh::LeanObject,4817029385054651662 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,4895640151090576375 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<7> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,855462560601428038 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<3> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,8803284079650313463 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,13950663889180613002 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__8_value) as *mut crate::leanh::LeanObject,3409869455520383320 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,75999622856309905 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject,18075986562369520856 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(
    mut v_a_2150_: *mut crate::leanh::LeanObject,
    mut v_x_2151_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2152_: u8 = 0;
    let mut v_key_2153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2155_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2151_) == 0 {
                    v___x_2152_ = 0;
                    return v___x_2152_;
                } else {
                    v_key_2153_ = crate::leanh::lean_ctor_get(v_x_2151_, 0);
                    v_tail_2154_ = crate::leanh::lean_ctor_get(v_x_2151_, 2);
                    v___x_2155_ = l_Lean_instBEqFVarId_beq(v_key_2153_, v_a_2150_);
                    if v___x_2155_ == 0 {
                        v_x_2151_ = v_tail_2154_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2155_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg___boxed(
    mut v_a_2157_: *mut crate::leanh::LeanObject,
    mut v_x_2158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2159_: u8 = 0;
    let mut v_r_2160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2159_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_2157_, v_x_2158_);
    crate::leanh::lean_dec(v_x_2158_);
    crate::leanh::lean_dec(v_a_2157_);
    v_r_2160_ = crate::leanh::lean_box((v_res_2159_) as usize);
    return v_r_2160_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_2161_: *mut crate::leanh::LeanObject,
    mut v_x_2162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_2163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2168_: u8 = 0;
    let mut v___x_2169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2170_: u64 = 0;
    let mut v___x_2171_: u64 = 0;
    let mut v___x_2172_: u64 = 0;
    let mut v_fold_2173_: u64 = 0;
    let mut v___x_2174_: u64 = 0;
    let mut v___x_2175_: u64 = 0;
    let mut v___x_2176_: u64 = 0;
    let mut v___x_2177_: usize = 0;
    let mut v___x_2178_: usize = 0;
    let mut v___x_2179_: usize = 0;
    let mut v___x_2180_: usize = 0;
    let mut v___x_2181_: usize = 0;
    let mut v___x_2182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2188_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2162_) == 0 {
                    return v_x_2161_;
                } else {
                    v_key_2163_ = crate::leanh::lean_ctor_get(v_x_2162_, 0);
                    v_value_2164_ = crate::leanh::lean_ctor_get(v_x_2162_, 1);
                    v_tail_2165_ = crate::leanh::lean_ctor_get(v_x_2162_, 2);
                    v_isSharedCheck_2188_ = (!crate::leanh::lean_is_exclusive(v_x_2162_)) as u8;
                    if v_isSharedCheck_2188_ == 0 {
                        v___x_2167_ = v_x_2162_;
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_2165_);
                        crate::leanh::lean_inc(v_value_2164_);
                        crate::leanh::lean_inc(v_key_2163_);
                        crate::leanh::lean_dec(v_x_2162_);
                        v___x_2167_ = crate::leanh::lean_box(0);
                        v_isShared_2168_ = v_isSharedCheck_2188_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2169_ = lean_array_get_size(v_x_2161_);
                v___x_2170_ = l_Lean_instHashableFVarId_hash(v_key_2163_);
                v___x_2171_ = 32u64;
                v___x_2172_ = lean_uint64_shift_right(v___x_2170_, v___x_2171_);
                v_fold_2173_ = lean_uint64_xor(v___x_2170_, v___x_2172_);
                v___x_2174_ = 16u64;
                v___x_2175_ = lean_uint64_shift_right(v_fold_2173_, v___x_2174_);
                v___x_2176_ = lean_uint64_xor(v_fold_2173_, v___x_2175_);
                v___x_2177_ = lean_uint64_to_usize(v___x_2176_);
                v___x_2178_ = lean_usize_of_nat(v___x_2169_);
                v___x_2179_ = 1usize;
                v___x_2180_ = lean_usize_sub(v___x_2178_, v___x_2179_);
                v___x_2181_ = lean_usize_land(v___x_2177_, v___x_2180_);
                v___x_2182_ = lean_array_uget_borrowed(v_x_2161_, v___x_2181_);
                crate::leanh::lean_inc(v___x_2182_);
                if v_isShared_2168_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2167_, 2, v___x_2182_);
                    v___x_2184_ = v___x_2167_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2187_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 0, v_key_2163_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_value_2164_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2187_, 2, v___x_2182_);
                    v___x_2184_ = v_reuseFailAlloc_2187_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_2185_ = lean_array_uset(v_x_2161_, v___x_2181_, v___x_2184_);
                v_x_2161_ = v___x_2185_;
                v_x_2162_ = v_tail_2165_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(
    mut v_i_2189_: *mut crate::leanh::LeanObject,
    mut v_source_2190_: *mut crate::leanh::LeanObject,
    mut v_target_2191_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2193_: u8 = 0;
    let mut v_es_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_2197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2192_ = lean_array_get_size(v_source_2190_);
                v___x_2193_ = lean_nat_dec_lt(v_i_2189_, v___x_2192_);
                if v___x_2193_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_2190_);
                    crate::leanh::lean_dec(v_i_2189_);
                    return v_target_2191_;
                } else {
                    v_es_2194_ = lean_array_fget(v_source_2190_, v_i_2189_);
                    v___x_2195_ = crate::leanh::lean_box(0);
                    v_source_2196_ = lean_array_fset(v_source_2190_, v_i_2189_, v___x_2195_);
                    v_target_2197_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_target_2191_, v_es_2194_);
                    v___x_2198_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2199_ = lean_nat_add(v_i_2189_, v___x_2198_);
                    crate::leanh::lean_dec(v_i_2189_);
                    v_i_2189_ = v___x_2199_;
                    v_source_2190_ = v_source_2196_;
                    v_target_2191_ = v_target_2197_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(
    mut v_data_2201_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2202_ = lean_array_get_size(v_data_2201_);
    v___x_2203_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_2204_ = lean_nat_mul(v___x_2202_, v___x_2203_);
    v___x_2205_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2206_ = crate::leanh::lean_box(0);
    v___x_2207_ = lean_mk_array(v_nbuckets_2204_, v___x_2206_);
    v___x_2208_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v___x_2205_, v_data_2201_, v___x_2207_);
    return v___x_2208_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(
    mut v_m_2209_: *mut crate::leanh::LeanObject,
    mut v_a_2210_: *mut crate::leanh::LeanObject,
    mut v_b_2211_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_2213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: u64 = 0;
    let mut v___x_2216_: u64 = 0;
    let mut v___x_2217_: u64 = 0;
    let mut v_fold_2218_: u64 = 0;
    let mut v___x_2219_: u64 = 0;
    let mut v___x_2220_: u64 = 0;
    let mut v___x_2221_: u64 = 0;
    let mut v___x_2222_: usize = 0;
    let mut v___x_2223_: usize = 0;
    let mut v___x_2224_: usize = 0;
    let mut v___x_2225_: usize = 0;
    let mut v___x_2226_: usize = 0;
    let mut v_bkt_2227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: u8 = 0;
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2241_: u8 = 0;
    let mut v_val_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2249_: u8 = 0;
    let mut v_unused_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_2212_ = crate::leanh::lean_ctor_get(v_m_2209_, 0);
                v_buckets_2213_ = crate::leanh::lean_ctor_get(v_m_2209_, 1);
                v___x_2214_ = lean_array_get_size(v_buckets_2213_);
                v___x_2215_ = l_Lean_instHashableFVarId_hash(v_a_2210_);
                v___x_2216_ = 32u64;
                v___x_2217_ = lean_uint64_shift_right(v___x_2215_, v___x_2216_);
                v_fold_2218_ = lean_uint64_xor(v___x_2215_, v___x_2217_);
                v___x_2219_ = 16u64;
                v___x_2220_ = lean_uint64_shift_right(v_fold_2218_, v___x_2219_);
                v___x_2221_ = lean_uint64_xor(v_fold_2218_, v___x_2220_);
                v___x_2222_ = lean_uint64_to_usize(v___x_2221_);
                v___x_2223_ = lean_usize_of_nat(v___x_2214_);
                v___x_2224_ = 1usize;
                v___x_2225_ = lean_usize_sub(v___x_2223_, v___x_2224_);
                v___x_2226_ = lean_usize_land(v___x_2222_, v___x_2225_);
                v_bkt_2227_ = lean_array_uget_borrowed(v_buckets_2213_, v___x_2226_);
                v___x_2228_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_2210_, v_bkt_2227_);
                if v___x_2228_ == 0 {
                    crate::leanh::lean_inc_ref(v_buckets_2213_);
                    crate::leanh::lean_inc(v_size_2212_);
                    v_isSharedCheck_2249_ = (!crate::leanh::lean_is_exclusive(v_m_2209_)) as u8;
                    if v_isSharedCheck_2249_ == 0 {
                        v_unused_2250_ = crate::leanh::lean_ctor_get(v_m_2209_, 1);
                        crate::leanh::lean_dec(v_unused_2250_);
                        v_unused_2251_ = crate::leanh::lean_ctor_get(v_m_2209_, 0);
                        crate::leanh::lean_dec(v_unused_2251_);
                        v___x_2230_ = v_m_2209_;
                        v_isShared_2231_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_m_2209_);
                        v___x_2230_ = crate::leanh::lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2249_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_b_2211_);
                    crate::leanh::lean_dec(v_a_2210_);
                    return v_m_2209_;
                }
            }
            1 => {
                v___x_2232_ = crate::leanh::lean_unsigned_to_nat(1);
                v_size_x27_2233_ = lean_nat_add(v_size_2212_, v___x_2232_);
                crate::leanh::lean_dec(v_size_2212_);
                crate::leanh::lean_inc(v_bkt_2227_);
                v___x_2234_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2234_, 0, v_a_2210_);
                crate::leanh::lean_ctor_set(v___x_2234_, 1, v_b_2211_);
                crate::leanh::lean_ctor_set(v___x_2234_, 2, v_bkt_2227_);
                v_buckets_x27_2235_ = lean_array_uset(v_buckets_2213_, v___x_2226_, v___x_2234_);
                v___x_2236_ = crate::leanh::lean_unsigned_to_nat(4);
                v___x_2237_ = lean_nat_mul(v_size_x27_2233_, v___x_2236_);
                v___x_2238_ = crate::leanh::lean_unsigned_to_nat(3);
                v___x_2239_ = lean_nat_div(v___x_2237_, v___x_2238_);
                crate::leanh::lean_dec(v___x_2237_);
                v___x_2240_ = lean_array_get_size(v_buckets_x27_2235_);
                v___x_2241_ = lean_nat_dec_le(v___x_2239_, v___x_2240_);
                crate::leanh::lean_dec(v___x_2239_);
                if v___x_2241_ == 0 {
                    v_val_2242_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_buckets_x27_2235_);
                    if v_isShared_2231_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2230_, 1, v_val_2242_);
                        crate::leanh::lean_ctor_set(v___x_2230_, 0, v_size_x27_2233_);
                        v___x_2244_ = v___x_2230_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2245_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 0, v_size_x27_2233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2245_, 1, v_val_2242_);
                        v___x_2244_ = v_reuseFailAlloc_2245_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_2231_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2230_, 1, v_buckets_x27_2235_);
                        crate::leanh::lean_ctor_set(v___x_2230_, 0, v_size_x27_2233_);
                        v___x_2247_ = v___x_2230_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2248_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 0, v_size_x27_2233_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2248_, 1, v_buckets_x27_2235_);
                        v___x_2247_ = v_reuseFailAlloc_2248_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2244_;
            }
            3 => {
                return v___x_2247_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(
    mut v_k_2252_: *mut crate::leanh::LeanObject,
    mut v_t_2253_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_2255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_2256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2257_: u8 = 0;
    let mut v___x_2259_: u8 = 0;
    let mut v___x_2261_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_2253_) == 0 {
                    v_k_2254_ = crate::leanh::lean_ctor_get(v_t_2253_, 1);
                    v_l_2255_ = crate::leanh::lean_ctor_get(v_t_2253_, 3);
                    v_r_2256_ = crate::leanh::lean_ctor_get(v_t_2253_, 4);
                    v___x_2257_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2252_, v_k_2254_);
                    match v___x_2257_ {
                        0 => {
                            v_t_2253_ = v_l_2255_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            v___x_2259_ = 1;
                            return v___x_2259_;
                        }
                        _ => {
                            v_t_2253_ = v_r_2256_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2261_ = 0;
                    return v___x_2261_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg___boxed(
    mut v_k_2262_: *mut crate::leanh::LeanObject,
    mut v_t_2263_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2264_: u8 = 0;
    let mut v_r_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2264_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_2262_, v_t_2263_);
    crate::leanh::lean_dec(v_t_2263_);
    crate::leanh::lean_dec(v_k_2262_);
    v_r_2265_ = crate::leanh::lean_box((v_res_2264_) as usize);
    return v_r_2265_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
    mut v_fvarId_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_params_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: u8 = 0;
    v_params_2270_ = crate::leanh::lean_ctor_get(v_a_2267_, 1);
    v___x_2271_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_fvarId_2266_, v_params_2270_);
    if v___x_2271_ == 0 {
        let mut v___x_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_fvarId_2266_);
        v___x_2272_ = crate::leanh::lean_box(0);
        v___x_2273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2273_, 0, v___x_2272_);
        return v___x_2273_;
    } else {
        let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_2274_ = lean_st_ref_take(v_a_2268_);
        v___x_2275_ = crate::leanh::lean_box(0);
        v___x_2276_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v___x_2274_, v_fvarId_2266_, v___x_2275_);
        v___x_2277_ = lean_st_ref_set(v_a_2268_, v___x_2276_);
        v___x_2278_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2278_, 0, v___x_2275_);
        return v___x_2278_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(
    mut v_fvarId_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2283_ =
        l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_2279_, v_a_2280_, v_a_2281_);
    crate::leanh::lean_dec(v_a_2281_);
    crate::leanh::lean_dec_ref(v_a_2280_);
    return v_res_2283_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar(
    mut v_fvarId_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
    mut v_a_2286_: *mut crate::leanh::LeanObject,
    mut v_a_2287_: *mut crate::leanh::LeanObject,
    mut v_a_2288_: *mut crate::leanh::LeanObject,
    mut v_a_2289_: *mut crate::leanh::LeanObject,
    mut v_a_2290_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ =
        l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_2284_, v_a_2285_, v_a_2286_);
    return v___x_2292_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(
    mut v_fvarId_2293_: *mut crate::leanh::LeanObject,
    mut v_a_2294_: *mut crate::leanh::LeanObject,
    mut v_a_2295_: *mut crate::leanh::LeanObject,
    mut v_a_2296_: *mut crate::leanh::LeanObject,
    mut v_a_2297_: *mut crate::leanh::LeanObject,
    mut v_a_2298_: *mut crate::leanh::LeanObject,
    mut v_a_2299_: *mut crate::leanh::LeanObject,
    mut v_a_2300_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2301_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar(
        v_fvarId_2293_,
        v_a_2294_,
        v_a_2295_,
        v_a_2296_,
        v_a_2297_,
        v_a_2298_,
        v_a_2299_,
    );
    crate::leanh::lean_dec(v_a_2299_);
    crate::leanh::lean_dec_ref(v_a_2298_);
    crate::leanh::lean_dec(v_a_2297_);
    crate::leanh::lean_dec_ref(v_a_2296_);
    crate::leanh::lean_dec(v_a_2295_);
    crate::leanh::lean_dec_ref(v_a_2294_);
    return v_res_2301_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(
    mut v_00_u03b2_2302_: *mut crate::leanh::LeanObject,
    mut v_k_2303_: *mut crate::leanh::LeanObject,
    mut v_t_2304_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2305_: u8 = 0;
    v___x_2305_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___redArg(v_k_2303_, v_t_2304_);
    return v___x_2305_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0___boxed(
    mut v_00_u03b2_2306_: *mut crate::leanh::LeanObject,
    mut v_k_2307_: *mut crate::leanh::LeanObject,
    mut v_t_2308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2309_: u8 = 0;
    let mut v_r_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2309_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__0(v_00_u03b2_2306_, v_k_2307_, v_t_2308_);
    crate::leanh::lean_dec(v_t_2308_);
    crate::leanh::lean_dec(v_k_2307_);
    v_r_2310_ = crate::leanh::lean_box((v_res_2309_) as usize);
    return v_r_2310_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1(
    mut v_00_u03b2_2311_: *mut crate::leanh::LeanObject,
    mut v_m_2312_: *mut crate::leanh::LeanObject,
    mut v_a_2313_: *mut crate::leanh::LeanObject,
    mut v_b_2314_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2315_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1___redArg(v_m_2312_, v_a_2313_, v_b_2314_);
    return v___x_2315_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(
    mut v_00_u03b2_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_x_2318_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2319_: u8 = 0;
    v___x_2319_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_2317_, v_x_2318_);
    return v___x_2319_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___boxed(
    mut v_00_u03b2_2320_: *mut crate::leanh::LeanObject,
    mut v_a_2321_: *mut crate::leanh::LeanObject,
    mut v_x_2322_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2323_: u8 = 0;
    let mut v_r_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2323_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1(v_00_u03b2_2320_, v_a_2321_, v_x_2322_);
    crate::leanh::lean_dec(v_x_2322_);
    crate::leanh::lean_dec(v_a_2321_);
    v_r_2324_ = crate::leanh::lean_box((v_res_2323_) as usize);
    return v_r_2324_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2(
    mut v_00_u03b2_2325_: *mut crate::leanh::LeanObject,
    mut v_data_2326_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2327_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2___redArg(v_data_2326_);
    return v___x_2327_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3(
    mut v_00_u03b2_2328_: *mut crate::leanh::LeanObject,
    mut v_i_2329_: *mut crate::leanh::LeanObject,
    mut v_source_2330_: *mut crate::leanh::LeanObject,
    mut v_target_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2332_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3___redArg(v_i_2329_, v_source_2330_, v_target_2331_);
    return v___x_2332_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_2333_: *mut crate::leanh::LeanObject,
    mut v_x_2334_: *mut crate::leanh::LeanObject,
    mut v_x_2335_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2336_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__2_spec__3_spec__4___redArg(v_x_2334_, v_x_2335_);
    return v___x_2336_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(
    mut v_arg_2337_: *mut crate::leanh::LeanObject,
    mut v_a_2338_: *mut crate::leanh::LeanObject,
    mut v_a_2339_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_arg_2337_) == 1 {
        let mut v_fvarId_2341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_fvarId_2341_ = crate::leanh::lean_ctor_get(v_arg_2337_, 0);
        crate::leanh::lean_inc(v_fvarId_2341_);
        crate::leanh::lean_dec_ref_known(v_arg_2337_, 1);
        v___x_2342_ =
            l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(v_fvarId_2341_, v_a_2338_, v_a_2339_);
        return v___x_2342_;
    } else {
        let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec(v_arg_2337_);
        v___x_2343_ = crate::leanh::lean_box(0);
        v___x_2344_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_2344_, 0, v___x_2343_);
        return v___x_2344_;
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(
    mut v_arg_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
    mut v_a_2347_: *mut crate::leanh::LeanObject,
    mut v_a_2348_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2349_ =
        l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_2345_, v_a_2346_, v_a_2347_);
    crate::leanh::lean_dec(v_a_2347_);
    crate::leanh::lean_dec_ref(v_a_2346_);
    return v_res_2349_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg(
    mut v_arg_2350_: *mut crate::leanh::LeanObject,
    mut v_a_2351_: *mut crate::leanh::LeanObject,
    mut v_a_2352_: *mut crate::leanh::LeanObject,
    mut v_a_2353_: *mut crate::leanh::LeanObject,
    mut v_a_2354_: *mut crate::leanh::LeanObject,
    mut v_a_2355_: *mut crate::leanh::LeanObject,
    mut v_a_2356_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2358_ =
        l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(v_arg_2350_, v_a_2351_, v_a_2352_);
    return v___x_2358_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(
    mut v_arg_2359_: *mut crate::leanh::LeanObject,
    mut v_a_2360_: *mut crate::leanh::LeanObject,
    mut v_a_2361_: *mut crate::leanh::LeanObject,
    mut v_a_2362_: *mut crate::leanh::LeanObject,
    mut v_a_2363_: *mut crate::leanh::LeanObject,
    mut v_a_2364_: *mut crate::leanh::LeanObject,
    mut v_a_2365_: *mut crate::leanh::LeanObject,
    mut v_a_2366_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2367_ = l_Lean_Compiler_LCNF_FindUsed_visitArg(
        v_arg_2359_,
        v_a_2360_,
        v_a_2361_,
        v_a_2362_,
        v_a_2363_,
        v_a_2364_,
        v_a_2365_,
    );
    crate::leanh::lean_dec(v_a_2365_);
    crate::leanh::lean_dec_ref(v_a_2364_);
    crate::leanh::lean_dec(v_a_2363_);
    crate::leanh::lean_dec_ref(v_a_2362_);
    crate::leanh::lean_dec(v_a_2361_);
    crate::leanh::lean_dec_ref(v_a_2360_);
    return v_res_2367_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(
    mut v_as_2368_: *mut crate::leanh::LeanObject,
    mut v_sz_2369_: usize,
    mut v_i_2370_: usize,
    mut v_b_2371_: *mut crate::leanh::LeanObject,
    mut v___y_2372_: *mut crate::leanh::LeanObject,
    mut v___y_2373_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: usize = 0;
    let mut v___x_2378_: usize = 0;
    let mut v___x_2380_: u8 = 0;
    let mut v___x_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_array_2382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: u8 = 0;
    let mut v___x_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2389_: u8 = 0;
    let mut v___x_2390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2407_: u8 = 0;
    let mut v_reuseFailAlloc_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2409_: u8 = 0;
    let mut v_unused_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2380_ = lean_usize_dec_lt(v_i_2370_, v_sz_2369_);
                if v___x_2380_ == 0 {
                    v___x_2381_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2381_, 0, v_b_2371_);
                    return v___x_2381_;
                } else {
                    v_array_2382_ = crate::leanh::lean_ctor_get(v_b_2371_, 0);
                    v_start_2383_ = crate::leanh::lean_ctor_get(v_b_2371_, 1);
                    v_stop_2384_ = crate::leanh::lean_ctor_get(v_b_2371_, 2);
                    v___x_2385_ = lean_nat_dec_lt(v_start_2383_, v_stop_2384_);
                    if v___x_2385_ == 0 {
                        v___x_2386_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2386_, 0, v_b_2371_);
                        return v___x_2386_;
                    } else {
                        crate::leanh::lean_inc(v_stop_2384_);
                        crate::leanh::lean_inc(v_start_2383_);
                        crate::leanh::lean_inc_ref(v_array_2382_);
                        v_isSharedCheck_2409_ = (!crate::leanh::lean_is_exclusive(v_b_2371_)) as u8;
                        if v_isSharedCheck_2409_ == 0 {
                            v_unused_2410_ = crate::leanh::lean_ctor_get(v_b_2371_, 2);
                            crate::leanh::lean_dec(v_unused_2410_);
                            v_unused_2411_ = crate::leanh::lean_ctor_get(v_b_2371_, 1);
                            crate::leanh::lean_dec(v_unused_2411_);
                            v_unused_2412_ = crate::leanh::lean_ctor_get(v_b_2371_, 0);
                            crate::leanh::lean_dec(v_unused_2412_);
                            v___x_2388_ = v_b_2371_;
                            v_isShared_2389_ = v_isSharedCheck_2409_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_b_2371_);
                            v___x_2388_ = crate::leanh::lean_box(0);
                            v_isShared_2389_ = v_isSharedCheck_2409_;
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2377_ = 1usize;
                v___x_2378_ = lean_usize_add(v_i_2370_, v___x_2377_);
                v_i_2370_ = v___x_2378_;
                v_b_2371_ = v_a_2376_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2390_ = lean_array_fget(v_array_2382_, v_start_2383_);
                v___x_2391_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2392_ = lean_nat_add(v_start_2383_, v___x_2391_);
                crate::leanh::lean_dec(v_start_2383_);
                if v_isShared_2389_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2388_, 1, v___x_2392_);
                    v___x_2394_ = v___x_2388_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2408_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 0, v_array_2382_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 1, v___x_2392_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2408_, 2, v_stop_2384_);
                    v___x_2394_ = v_reuseFailAlloc_2408_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if crate::leanh::lean_obj_tag(v___x_2390_) == 1 {
                    v_fvarId_2395_ = crate::leanh::lean_ctor_get(v___x_2390_, 0);
                    crate::leanh::lean_inc(v_fvarId_2395_);
                    crate::leanh::lean_dec_ref_known(v___x_2390_, 1);
                    v_a_2396_ = lean_array_uget_borrowed(v_as_2368_, v_i_2370_);
                    v_fvarId_2397_ = crate::leanh::lean_ctor_get(v_a_2396_, 0);
                    v___x_2398_ = l_Lean_instBEqFVarId_beq(v_fvarId_2395_, v_fvarId_2397_);
                    if v___x_2398_ == 0 {
                        v___x_2399_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                            v_fvarId_2395_,
                            v___y_2372_,
                            v___y_2373_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2399_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2399_, 1);
                            v_a_2376_ = v___x_2394_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2394_);
                            v_a_2400_ = crate::leanh::lean_ctor_get(v___x_2399_, 0);
                            v_isSharedCheck_2407_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2399_)) as u8;
                            if v_isSharedCheck_2407_ == 0 {
                                v___x_2402_ = v___x_2399_;
                                v_isShared_2403_ = v_isSharedCheck_2407_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2400_);
                                crate::leanh::lean_dec(v___x_2399_);
                                v___x_2402_ = crate::leanh::lean_box(0);
                                v_isShared_2403_ = v_isSharedCheck_2407_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_fvarId_2395_);
                        v_a_2376_ = v___x_2394_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2390_);
                    v_a_2376_ = v___x_2394_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                if v_isShared_2403_ == 0 {
                    v___x_2405_ = v___x_2402_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2406_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2406_, 0, v_a_2400_);
                    v___x_2405_ = v_reuseFailAlloc_2406_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(
    mut v_as_2413_: *mut crate::leanh::LeanObject,
    mut v_sz_2414_: *mut crate::leanh::LeanObject,
    mut v_i_2415_: *mut crate::leanh::LeanObject,
    mut v_b_2416_: *mut crate::leanh::LeanObject,
    mut v___y_2417_: *mut crate::leanh::LeanObject,
    mut v___y_2418_: *mut crate::leanh::LeanObject,
    mut v___y_2419_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2420_: usize = 0;
    let mut v_i_boxed_2421_: usize = 0;
    let mut v_res_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2420_ = crate::leanh::lean_unbox_usize(v_sz_2414_);
    crate::leanh::lean_dec(v_sz_2414_);
    v_i_boxed_2421_ = crate::leanh::lean_unbox_usize(v_i_2415_);
    crate::leanh::lean_dec(v_i_2415_);
    v_res_2422_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_2413_, v_sz_boxed_2420_, v_i_boxed_2421_, v_b_2416_, v___y_2417_, v___y_2418_);
    crate::leanh::lean_dec(v___y_2418_);
    crate::leanh::lean_dec_ref(v___y_2417_);
    crate::leanh::lean_dec_ref(v_as_2413_);
    return v_res_2422_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_b_2424_: *mut crate::leanh::LeanObject,
    mut v___y_2425_: *mut crate::leanh::LeanObject,
    mut v___y_2426_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2434_: u8 = 0;
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2428_ = crate::leanh::lean_ctor_get(v_a_2423_, 0);
                v_start_2429_ = crate::leanh::lean_ctor_get(v_a_2423_, 1);
                v_stop_2430_ = crate::leanh::lean_ctor_get(v_a_2423_, 2);
                v_isSharedCheck_2446_ = (!crate::leanh::lean_is_exclusive(v_a_2423_)) as u8;
                if v_isSharedCheck_2446_ == 0 {
                    v___x_2432_ = v_a_2423_;
                    v_isShared_2433_ = v_isSharedCheck_2446_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_2430_);
                    crate::leanh::lean_inc(v_start_2429_);
                    crate::leanh::lean_inc(v_array_2428_);
                    crate::leanh::lean_dec(v_a_2423_);
                    v___x_2432_ = crate::leanh::lean_box(0);
                    v_isShared_2433_ = v_isSharedCheck_2446_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2434_ = lean_nat_dec_lt(v_start_2429_, v_stop_2430_);
                if v___x_2434_ == 0 {
                    crate::leanh::lean_del_object(v___x_2432_);
                    crate::leanh::lean_dec(v_stop_2430_);
                    crate::leanh::lean_dec(v_start_2429_);
                    crate::leanh::lean_dec_ref(v_array_2428_);
                    v___x_2435_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2435_, 0, v_b_2424_);
                    return v___x_2435_;
                } else {
                    v___x_2436_ = lean_array_fget_borrowed(v_array_2428_, v_start_2429_);
                    v_fvarId_2437_ = crate::leanh::lean_ctor_get(v___x_2436_, 0);
                    crate::leanh::lean_inc(v_fvarId_2437_);
                    v___x_2438_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_fvarId_2437_,
                        v___y_2425_,
                        v___y_2426_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2438_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2438_, 1);
                        v___x_2439_ = crate::leanh::lean_box(0);
                        v___x_2440_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2441_ = lean_nat_add(v_start_2429_, v___x_2440_);
                        crate::leanh::lean_dec(v_start_2429_);
                        if v_isShared_2433_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2432_, 1, v___x_2441_);
                            v___x_2443_ = v___x_2432_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2445_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2445_, 0, v_array_2428_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2445_, 1, v___x_2441_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2445_, 2, v_stop_2430_);
                            v___x_2443_ = v_reuseFailAlloc_2445_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2432_);
                        crate::leanh::lean_dec(v_stop_2430_);
                        crate::leanh::lean_dec(v_start_2429_);
                        crate::leanh::lean_dec_ref(v_array_2428_);
                        return v___x_2438_;
                    }
                }
            }
            2 => {
                v_a_2423_ = v___x_2443_;
                v_b_2424_ = v___x_2439_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_b_2448_: *mut crate::leanh::LeanObject,
    mut v___y_2449_: *mut crate::leanh::LeanObject,
    mut v___y_2450_: *mut crate::leanh::LeanObject,
    mut v___y_2451_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2452_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_2447_, v_b_2448_, v___y_2449_, v___y_2450_);
    crate::leanh::lean_dec(v___y_2450_);
    crate::leanh::lean_dec_ref(v___y_2449_);
    return v_res_2452_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(
    mut v_as_2453_: *mut crate::leanh::LeanObject,
    mut v_i_2454_: usize,
    mut v_stop_2455_: usize,
    mut v_b_2456_: *mut crate::leanh::LeanObject,
    mut v___y_2457_: *mut crate::leanh::LeanObject,
    mut v___y_2458_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2460_: u8 = 0;
    let mut v___x_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: usize = 0;
    let mut v___x_2465_: usize = 0;
    let mut v___x_2467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2460_ = lean_usize_dec_eq(v_i_2454_, v_stop_2455_);
                if v___x_2460_ == 0 {
                    v___x_2461_ = lean_array_uget_borrowed(v_as_2453_, v_i_2454_);
                    crate::leanh::lean_inc(v___x_2461_);
                    v___x_2462_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(
                        v___x_2461_,
                        v___y_2457_,
                        v___y_2458_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2462_) == 0 {
                        v_a_2463_ = crate::leanh::lean_ctor_get(v___x_2462_, 0);
                        crate::leanh::lean_inc(v_a_2463_);
                        crate::leanh::lean_dec_ref_known(v___x_2462_, 1);
                        v___x_2464_ = 1usize;
                        v___x_2465_ = lean_usize_add(v_i_2454_, v___x_2464_);
                        v_i_2454_ = v___x_2465_;
                        v_b_2456_ = v_a_2463_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2462_;
                    }
                } else {
                    v___x_2467_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2467_, 0, v_b_2456_);
                    return v___x_2467_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(
    mut v_as_2468_: *mut crate::leanh::LeanObject,
    mut v_i_2469_: *mut crate::leanh::LeanObject,
    mut v_stop_2470_: *mut crate::leanh::LeanObject,
    mut v_b_2471_: *mut crate::leanh::LeanObject,
    mut v___y_2472_: *mut crate::leanh::LeanObject,
    mut v___y_2473_: *mut crate::leanh::LeanObject,
    mut v___y_2474_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2475_: usize = 0;
    let mut v_stop_boxed_2476_: usize = 0;
    let mut v_res_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2475_ = crate::leanh::lean_unbox_usize(v_i_2469_);
    crate::leanh::lean_dec(v_i_2469_);
    v_stop_boxed_2476_ = crate::leanh::lean_unbox_usize(v_stop_2470_);
    crate::leanh::lean_dec(v_stop_2470_);
    v_res_2477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_2468_, v_i_boxed_2475_, v_stop_boxed_2476_, v_b_2471_, v___y_2472_, v___y_2473_);
    crate::leanh::lean_dec(v___y_2473_);
    crate::leanh::lean_dec_ref(v___y_2472_);
    crate::leanh::lean_dec_ref(v_as_2468_);
    return v_res_2477_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(
    mut v_a_2478_: *mut crate::leanh::LeanObject,
    mut v_b_2479_: *mut crate::leanh::LeanObject,
    mut v___y_2480_: *mut crate::leanh::LeanObject,
    mut v___y_2481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_array_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_2485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2488_: u8 = 0;
    let mut v___x_2489_: u8 = 0;
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2500_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_array_2483_ = crate::leanh::lean_ctor_get(v_a_2478_, 0);
                v_start_2484_ = crate::leanh::lean_ctor_get(v_a_2478_, 1);
                v_stop_2485_ = crate::leanh::lean_ctor_get(v_a_2478_, 2);
                v_isSharedCheck_2500_ = (!crate::leanh::lean_is_exclusive(v_a_2478_)) as u8;
                if v_isSharedCheck_2500_ == 0 {
                    v___x_2487_ = v_a_2478_;
                    v_isShared_2488_ = v_isSharedCheck_2500_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_stop_2485_);
                    crate::leanh::lean_inc(v_start_2484_);
                    crate::leanh::lean_inc(v_array_2483_);
                    crate::leanh::lean_dec(v_a_2478_);
                    v___x_2487_ = crate::leanh::lean_box(0);
                    v_isShared_2488_ = v_isSharedCheck_2500_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2489_ = lean_nat_dec_lt(v_start_2484_, v_stop_2485_);
                if v___x_2489_ == 0 {
                    crate::leanh::lean_del_object(v___x_2487_);
                    crate::leanh::lean_dec(v_stop_2485_);
                    crate::leanh::lean_dec(v_start_2484_);
                    crate::leanh::lean_dec_ref(v_array_2483_);
                    v___x_2490_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2490_, 0, v_b_2479_);
                    return v___x_2490_;
                } else {
                    v___x_2491_ = lean_array_fget_borrowed(v_array_2483_, v_start_2484_);
                    crate::leanh::lean_inc(v___x_2491_);
                    v___x_2492_ = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(
                        v___x_2491_,
                        v___y_2480_,
                        v___y_2481_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2492_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2492_, 1);
                        v___x_2493_ = crate::leanh::lean_box(0);
                        v___x_2494_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2495_ = lean_nat_add(v_start_2484_, v___x_2494_);
                        crate::leanh::lean_dec(v_start_2484_);
                        if v_isShared_2488_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2487_, 1, v___x_2495_);
                            v___x_2497_ = v___x_2487_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_2499_ =
                                crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_array_2483_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 1, v___x_2495_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2499_, 2, v_stop_2485_);
                            v___x_2497_ = v_reuseFailAlloc_2499_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2487_);
                        crate::leanh::lean_dec(v_stop_2485_);
                        crate::leanh::lean_dec(v_start_2484_);
                        crate::leanh::lean_dec_ref(v_array_2483_);
                        return v___x_2492_;
                    }
                }
            }
            2 => {
                v_a_2478_ = v___x_2497_;
                v_b_2479_ = v___x_2493_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(
    mut v_a_2501_: *mut crate::leanh::LeanObject,
    mut v_b_2502_: *mut crate::leanh::LeanObject,
    mut v___y_2503_: *mut crate::leanh::LeanObject,
    mut v___y_2504_: *mut crate::leanh::LeanObject,
    mut v___y_2505_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2506_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_2501_, v_b_2502_, v___y_2503_, v___y_2504_);
    crate::leanh::lean_dec(v___y_2504_);
    crate::leanh::lean_dec_ref(v___y_2503_);
    return v_res_2506_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitLetValue(
    mut v_e_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
    mut v_a_2513_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2522_: u8 = 0;
    let mut v_unused_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_struct_2526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_2529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2542_: u8 = 0;
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2546_: u8 = 0;
    let mut v_unused_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2548_: u8 = 0;
    let mut v___x_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: u8 = 0;
    let mut v___x_2553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: u8 = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: usize = 0;
    let mut v___x_2557_: usize = 0;
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: usize = 0;
    let mut v___x_2560_: usize = 0;
    let mut v___x_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2565_: usize = 0;
    let mut v___x_2566_: usize = 0;
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: u8 = 0;
    let mut v_a_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2581_: u8 = 0;
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2585_: u8 = 0;
    let mut v_fvarId_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2591_: u8 = 0;
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2595_: u8 = 0;
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: u8 = 0;
    let mut v___x_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2603_: usize = 0;
    let mut v___x_2604_: usize = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: usize = 0;
    let mut v___x_2607_: usize = 0;
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2609_: u8 = 0;
    let mut v_unused_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_e_2507_) {
                0 => {
                    v_isSharedCheck_2522_ = (!crate::leanh::lean_is_exclusive(v_e_2507_)) as u8;
                    if v_isSharedCheck_2522_ == 0 {
                        v_unused_2523_ = crate::leanh::lean_ctor_get(v_e_2507_, 0);
                        crate::leanh::lean_dec(v_unused_2523_);
                        v___x_2516_ = v_e_2507_;
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_e_2507_);
                        v___x_2516_ = crate::leanh::lean_box(0);
                        v_isShared_2517_ = v_isSharedCheck_2522_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_2524_ = crate::leanh::lean_box(0);
                    v___x_2525_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2525_, 0, v___x_2524_);
                    return v___x_2525_;
                }
                2 => {
                    v_struct_2526_ = crate::leanh::lean_ctor_get(v_e_2507_, 2);
                    crate::leanh::lean_inc(v_struct_2526_);
                    crate::leanh::lean_dec_ref_known(v_e_2507_, 3);
                    v___x_2527_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_struct_2526_,
                        v_a_2508_,
                        v_a_2509_,
                    );
                    return v___x_2527_;
                }
                3 => {
                    v_decl_2528_ = crate::leanh::lean_ctor_get(v_a_2508_, 0);
                    v_toSignature_2529_ = crate::leanh::lean_ctor_get(v_decl_2528_, 0);
                    v_declName_2530_ = crate::leanh::lean_ctor_get(v_e_2507_, 0);
                    crate::leanh::lean_inc(v_declName_2530_);
                    v_args_2531_ = crate::leanh::lean_ctor_get(v_e_2507_, 2);
                    crate::leanh::lean_inc_ref(v_args_2531_);
                    crate::leanh::lean_dec_ref_known(v_e_2507_, 3);
                    v_name_2532_ = crate::leanh::lean_ctor_get(v_toSignature_2529_, 0);
                    v_params_2533_ = crate::leanh::lean_ctor_get(v_toSignature_2529_, 3);
                    v___x_2548_ = lean_name_eq(v_declName_2530_, v_name_2532_);
                    crate::leanh::lean_dec(v_declName_2530_);
                    if v___x_2548_ == 0 {
                        v___x_2549_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2550_ = lean_array_get_size(v_args_2531_);
                        v___x_2551_ = crate::leanh::lean_box(0);
                        v___x_2552_ = lean_nat_dec_lt(v___x_2549_, v___x_2550_);
                        if v___x_2552_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_2531_);
                            v___x_2553_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_2553_, 0, v___x_2551_);
                            return v___x_2553_;
                        } else {
                            v___x_2554_ = lean_nat_dec_le(v___x_2550_, v___x_2550_);
                            if v___x_2554_ == 0 {
                                if v___x_2552_ == 0 {
                                    crate::leanh::lean_dec_ref(v_args_2531_);
                                    v___x_2555_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2555_, 0, v___x_2551_);
                                    return v___x_2555_;
                                } else {
                                    v___x_2556_ = 0usize;
                                    v___x_2557_ = lean_usize_of_nat(v___x_2550_);
                                    v___x_2558_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2531_, v___x_2556_, v___x_2557_, v___x_2551_, v_a_2508_, v_a_2509_);
                                    crate::leanh::lean_dec_ref(v_args_2531_);
                                    return v___x_2558_;
                                }
                            } else {
                                v___x_2559_ = 0usize;
                                v___x_2560_ = lean_usize_of_nat(v___x_2550_);
                                v___x_2561_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2531_, v___x_2559_, v___x_2560_, v___x_2551_, v_a_2508_, v_a_2509_);
                                crate::leanh::lean_dec_ref(v_args_2531_);
                                return v___x_2561_;
                            }
                        }
                    } else {
                        v___x_2562_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_2563_ = lean_array_get_size(v_args_2531_);
                        crate::leanh::lean_inc_ref(v_args_2531_);
                        v___x_2564_ =
                            l_Array_toSubarray___redArg(v_args_2531_, v___x_2562_, v___x_2563_);
                        v_sz_2565_ = lean_array_size(v_params_2533_);
                        v___x_2566_ = 0usize;
                        v___x_2567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_params_2533_, v_sz_2565_, v___x_2566_, v___x_2564_, v_a_2508_, v_a_2509_);
                        if crate::leanh::lean_obj_tag(v___x_2567_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_2567_, 1);
                            v___x_2576_ = lean_array_get_size(v_params_2533_);
                            v___x_2577_ = lean_nat_dec_le(v___x_2576_, v___x_2562_);
                            if v___x_2577_ == 0 {
                                v_lower_2569_ = v___x_2576_;
                                v_upper_2570_ = v___x_2563_;
                                state = 6;
                                continue;
                            } else {
                                v_lower_2569_ = v___x_2562_;
                                v_upper_2570_ = v___x_2563_;
                                state = 6;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_args_2531_);
                            v_a_2578_ = crate::leanh::lean_ctor_get(v___x_2567_, 0);
                            v_isSharedCheck_2585_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2567_)) as u8;
                            if v_isSharedCheck_2585_ == 0 {
                                v___x_2580_ = v___x_2567_;
                                v_isShared_2581_ = v_isSharedCheck_2585_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2578_);
                                crate::leanh::lean_dec(v___x_2567_);
                                v___x_2580_ = crate::leanh::lean_box(0);
                                v_isShared_2581_ = v_isSharedCheck_2585_;
                                state = 7;
                                continue;
                            }
                        }
                    }
                }
                _ => {
                    v_fvarId_2586_ = crate::leanh::lean_ctor_get(v_e_2507_, 0);
                    crate::leanh::lean_inc(v_fvarId_2586_);
                    v_args_2587_ = crate::leanh::lean_ctor_get(v_e_2507_, 1);
                    crate::leanh::lean_inc_ref(v_args_2587_);
                    crate::leanh::lean_dec_ref_known(v_e_2507_, 2);
                    v___x_2588_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_fvarId_2586_,
                        v_a_2508_,
                        v_a_2509_,
                    );
                    v_isSharedCheck_2609_ = (!crate::leanh::lean_is_exclusive(v___x_2588_)) as u8;
                    if v_isSharedCheck_2609_ == 0 {
                        v_unused_2610_ = crate::leanh::lean_ctor_get(v___x_2588_, 0);
                        crate::leanh::lean_dec(v_unused_2610_);
                        v___x_2590_ = v___x_2588_;
                        v_isShared_2591_ = v_isSharedCheck_2609_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2588_);
                        v___x_2590_ = crate::leanh::lean_box(0);
                        v_isShared_2591_ = v_isSharedCheck_2609_;
                        state = 9;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2518_ = crate::leanh::lean_box(0);
                if v_isShared_2517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2516_, 0, v___x_2518_);
                    v___x_2520_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2521_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2521_, 0, v___x_2518_);
                    v___x_2520_ = v_reuseFailAlloc_2521_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2520_;
            }
            3 => {
                crate::leanh::lean_inc_ref(v_params_2533_);
                v___x_2538_ =
                    l_Array_toSubarray___redArg(v_params_2533_, v_lower_2536_, v_upper_2537_);
                v___x_2539_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v___x_2538_, v___y_2535_, v_a_2508_, v_a_2509_);
                if crate::leanh::lean_obj_tag(v___x_2539_) == 0 {
                    v_isSharedCheck_2546_ = (!crate::leanh::lean_is_exclusive(v___x_2539_)) as u8;
                    if v_isSharedCheck_2546_ == 0 {
                        v_unused_2547_ = crate::leanh::lean_ctor_get(v___x_2539_, 0);
                        crate::leanh::lean_dec(v_unused_2547_);
                        v___x_2541_ = v___x_2539_;
                        v_isShared_2542_ = v_isSharedCheck_2546_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2539_);
                        v___x_2541_ = crate::leanh::lean_box(0);
                        v_isShared_2542_ = v_isSharedCheck_2546_;
                        state = 4;
                        continue;
                    }
                } else {
                    return v___x_2539_;
                }
            }
            4 => {
                if v_isShared_2542_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2541_, 0, v___y_2535_);
                    v___x_2544_ = v___x_2541_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2545_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2545_, 0, v___y_2535_);
                    v___x_2544_ = v_reuseFailAlloc_2545_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2544_;
            }
            6 => {
                v___x_2571_ =
                    l_Array_toSubarray___redArg(v_args_2531_, v_lower_2569_, v_upper_2570_);
                v___x_2572_ = crate::leanh::lean_box(0);
                v___x_2573_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v___x_2571_, v___x_2572_, v_a_2508_, v_a_2509_);
                if crate::leanh::lean_obj_tag(v___x_2573_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2573_, 1);
                    v___x_2574_ = lean_array_get_size(v_params_2533_);
                    v___x_2575_ = lean_nat_dec_le(v___x_2563_, v___x_2562_);
                    if v___x_2575_ == 0 {
                        v___y_2535_ = v___x_2572_;
                        v_lower_2536_ = v___x_2563_;
                        v_upper_2537_ = v___x_2574_;
                        state = 3;
                        continue;
                    } else {
                        v___y_2535_ = v___x_2572_;
                        v_lower_2536_ = v___x_2562_;
                        v_upper_2537_ = v___x_2574_;
                        state = 3;
                        continue;
                    }
                } else {
                    return v___x_2573_;
                }
            }
            7 => {
                if v_isShared_2581_ == 0 {
                    v___x_2583_ = v___x_2580_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2584_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2584_, 0, v_a_2578_);
                    v___x_2583_ = v_reuseFailAlloc_2584_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2583_;
            }
            9 => {
                v___x_2592_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2593_ = lean_array_get_size(v_args_2587_);
                v___x_2594_ = crate::leanh::lean_box(0);
                v___x_2595_ = lean_nat_dec_lt(v___x_2592_, v___x_2593_);
                if v___x_2595_ == 0 {
                    crate::leanh::lean_dec_ref(v_args_2587_);
                    if v_isShared_2591_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2590_, 0, v___x_2594_);
                        v___x_2597_ = v___x_2590_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_2598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v___x_2594_);
                        v___x_2597_ = v_reuseFailAlloc_2598_;
                        state = 10;
                        continue;
                    }
                } else {
                    v___x_2599_ = lean_nat_dec_le(v___x_2593_, v___x_2593_);
                    if v___x_2599_ == 0 {
                        if v___x_2595_ == 0 {
                            crate::leanh::lean_dec_ref(v_args_2587_);
                            if v_isShared_2591_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2590_, 0, v___x_2594_);
                                v___x_2601_ = v___x_2590_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_2602_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2602_, 0, v___x_2594_);
                                v___x_2601_ = v_reuseFailAlloc_2602_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2590_);
                            v___x_2603_ = 0usize;
                            v___x_2604_ = lean_usize_of_nat(v___x_2593_);
                            v___x_2605_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2587_, v___x_2603_, v___x_2604_, v___x_2594_, v_a_2508_, v_a_2509_);
                            crate::leanh::lean_dec_ref(v_args_2587_);
                            return v___x_2605_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2590_);
                        v___x_2606_ = 0usize;
                        v___x_2607_ = lean_usize_of_nat(v___x_2593_);
                        v___x_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2587_, v___x_2606_, v___x_2607_, v___x_2594_, v_a_2508_, v_a_2509_);
                        crate::leanh::lean_dec_ref(v_args_2587_);
                        return v___x_2608_;
                    }
                }
            }
            10 => {
                return v___x_2597_;
            }
            11 => {
                return v___x_2601_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(
    mut v_e_2611_: *mut crate::leanh::LeanObject,
    mut v_a_2612_: *mut crate::leanh::LeanObject,
    mut v_a_2613_: *mut crate::leanh::LeanObject,
    mut v_a_2614_: *mut crate::leanh::LeanObject,
    mut v_a_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2619_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(
        v_e_2611_, v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_,
    );
    crate::leanh::lean_dec(v_a_2617_);
    crate::leanh::lean_dec_ref(v_a_2616_);
    crate::leanh::lean_dec(v_a_2615_);
    crate::leanh::lean_dec_ref(v_a_2614_);
    crate::leanh::lean_dec(v_a_2613_);
    crate::leanh::lean_dec_ref(v_a_2612_);
    return v_res_2619_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(
    mut v_as_2620_: *mut crate::leanh::LeanObject,
    mut v_i_2621_: usize,
    mut v_stop_2622_: usize,
    mut v_b_2623_: *mut crate::leanh::LeanObject,
    mut v___y_2624_: *mut crate::leanh::LeanObject,
    mut v___y_2625_: *mut crate::leanh::LeanObject,
    mut v___y_2626_: *mut crate::leanh::LeanObject,
    mut v___y_2627_: *mut crate::leanh::LeanObject,
    mut v___y_2628_: *mut crate::leanh::LeanObject,
    mut v___y_2629_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2631_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_as_2620_, v_i_2621_, v_stop_2622_, v_b_2623_, v___y_2624_, v___y_2625_);
    return v___x_2631_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(
    mut v_as_2632_: *mut crate::leanh::LeanObject,
    mut v_i_2633_: *mut crate::leanh::LeanObject,
    mut v_stop_2634_: *mut crate::leanh::LeanObject,
    mut v_b_2635_: *mut crate::leanh::LeanObject,
    mut v___y_2636_: *mut crate::leanh::LeanObject,
    mut v___y_2637_: *mut crate::leanh::LeanObject,
    mut v___y_2638_: *mut crate::leanh::LeanObject,
    mut v___y_2639_: *mut crate::leanh::LeanObject,
    mut v___y_2640_: *mut crate::leanh::LeanObject,
    mut v___y_2641_: *mut crate::leanh::LeanObject,
    mut v___y_2642_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2643_: usize = 0;
    let mut v_stop_boxed_2644_: usize = 0;
    let mut v_res_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2643_ = crate::leanh::lean_unbox_usize(v_i_2633_);
    crate::leanh::lean_dec(v_i_2633_);
    v_stop_boxed_2644_ = crate::leanh::lean_unbox_usize(v_stop_2634_);
    crate::leanh::lean_dec(v_stop_2634_);
    v_res_2645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(v_as_2632_, v_i_boxed_2643_, v_stop_boxed_2644_, v_b_2635_, v___y_2636_, v___y_2637_, v___y_2638_, v___y_2639_, v___y_2640_, v___y_2641_);
    crate::leanh::lean_dec(v___y_2641_);
    crate::leanh::lean_dec_ref(v___y_2640_);
    crate::leanh::lean_dec(v___y_2639_);
    crate::leanh::lean_dec_ref(v___y_2638_);
    crate::leanh::lean_dec(v___y_2637_);
    crate::leanh::lean_dec_ref(v___y_2636_);
    crate::leanh::lean_dec_ref(v_as_2632_);
    return v_res_2645_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(
    mut v_as_2646_: *mut crate::leanh::LeanObject,
    mut v_sz_2647_: usize,
    mut v_i_2648_: usize,
    mut v_b_2649_: *mut crate::leanh::LeanObject,
    mut v___y_2650_: *mut crate::leanh::LeanObject,
    mut v___y_2651_: *mut crate::leanh::LeanObject,
    mut v___y_2652_: *mut crate::leanh::LeanObject,
    mut v___y_2653_: *mut crate::leanh::LeanObject,
    mut v___y_2654_: *mut crate::leanh::LeanObject,
    mut v___y_2655_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2657_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(v_as_2646_, v_sz_2647_, v_i_2648_, v_b_2649_, v___y_2650_, v___y_2651_);
    return v___x_2657_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(
    mut v_as_2658_: *mut crate::leanh::LeanObject,
    mut v_sz_2659_: *mut crate::leanh::LeanObject,
    mut v_i_2660_: *mut crate::leanh::LeanObject,
    mut v_b_2661_: *mut crate::leanh::LeanObject,
    mut v___y_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
    mut v___y_2665_: *mut crate::leanh::LeanObject,
    mut v___y_2666_: *mut crate::leanh::LeanObject,
    mut v___y_2667_: *mut crate::leanh::LeanObject,
    mut v___y_2668_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2669_: usize = 0;
    let mut v_i_boxed_2670_: usize = 0;
    let mut v_res_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2669_ = crate::leanh::lean_unbox_usize(v_sz_2659_);
    crate::leanh::lean_dec(v_sz_2659_);
    v_i_boxed_2670_ = crate::leanh::lean_unbox_usize(v_i_2660_);
    crate::leanh::lean_dec(v_i_2660_);
    v_res_2671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(v_as_2658_, v_sz_boxed_2669_, v_i_boxed_2670_, v_b_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_);
    crate::leanh::lean_dec(v___y_2667_);
    crate::leanh::lean_dec_ref(v___y_2666_);
    crate::leanh::lean_dec(v___y_2665_);
    crate::leanh::lean_dec_ref(v___y_2664_);
    crate::leanh::lean_dec(v___y_2663_);
    crate::leanh::lean_dec_ref(v___y_2662_);
    crate::leanh::lean_dec_ref(v_as_2658_);
    return v_res_2671_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(
    mut v_inst_2672_: *mut crate::leanh::LeanObject,
    mut v_R_2673_: *mut crate::leanh::LeanObject,
    mut v_a_2674_: *mut crate::leanh::LeanObject,
    mut v_b_2675_: *mut crate::leanh::LeanObject,
    mut v_c_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
    mut v___y_2678_: *mut crate::leanh::LeanObject,
    mut v___y_2679_: *mut crate::leanh::LeanObject,
    mut v___y_2680_: *mut crate::leanh::LeanObject,
    mut v___y_2681_: *mut crate::leanh::LeanObject,
    mut v___y_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2684_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(v_a_2674_, v_b_2675_, v___y_2677_, v___y_2678_);
    return v___x_2684_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(
    mut v_inst_2685_: *mut crate::leanh::LeanObject,
    mut v_R_2686_: *mut crate::leanh::LeanObject,
    mut v_a_2687_: *mut crate::leanh::LeanObject,
    mut v_b_2688_: *mut crate::leanh::LeanObject,
    mut v_c_2689_: *mut crate::leanh::LeanObject,
    mut v___y_2690_: *mut crate::leanh::LeanObject,
    mut v___y_2691_: *mut crate::leanh::LeanObject,
    mut v___y_2692_: *mut crate::leanh::LeanObject,
    mut v___y_2693_: *mut crate::leanh::LeanObject,
    mut v___y_2694_: *mut crate::leanh::LeanObject,
    mut v___y_2695_: *mut crate::leanh::LeanObject,
    mut v___y_2696_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2697_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(
            v_inst_2685_,
            v_R_2686_,
            v_a_2687_,
            v_b_2688_,
            v_c_2689_,
            v___y_2690_,
            v___y_2691_,
            v___y_2692_,
            v___y_2693_,
            v___y_2694_,
            v___y_2695_,
        );
    crate::leanh::lean_dec(v___y_2695_);
    crate::leanh::lean_dec_ref(v___y_2694_);
    crate::leanh::lean_dec(v___y_2693_);
    crate::leanh::lean_dec_ref(v___y_2692_);
    crate::leanh::lean_dec(v___y_2691_);
    crate::leanh::lean_dec_ref(v___y_2690_);
    return v_res_2697_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(
    mut v_inst_2698_: *mut crate::leanh::LeanObject,
    mut v_R_2699_: *mut crate::leanh::LeanObject,
    mut v_a_2700_: *mut crate::leanh::LeanObject,
    mut v_b_2701_: *mut crate::leanh::LeanObject,
    mut v_c_2702_: *mut crate::leanh::LeanObject,
    mut v___y_2703_: *mut crate::leanh::LeanObject,
    mut v___y_2704_: *mut crate::leanh::LeanObject,
    mut v___y_2705_: *mut crate::leanh::LeanObject,
    mut v___y_2706_: *mut crate::leanh::LeanObject,
    mut v___y_2707_: *mut crate::leanh::LeanObject,
    mut v___y_2708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2710_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(v_a_2700_, v_b_2701_, v___y_2703_, v___y_2704_);
    return v___x_2710_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(
    mut v_inst_2711_: *mut crate::leanh::LeanObject,
    mut v_R_2712_: *mut crate::leanh::LeanObject,
    mut v_a_2713_: *mut crate::leanh::LeanObject,
    mut v_b_2714_: *mut crate::leanh::LeanObject,
    mut v_c_2715_: *mut crate::leanh::LeanObject,
    mut v___y_2716_: *mut crate::leanh::LeanObject,
    mut v___y_2717_: *mut crate::leanh::LeanObject,
    mut v___y_2718_: *mut crate::leanh::LeanObject,
    mut v___y_2719_: *mut crate::leanh::LeanObject,
    mut v___y_2720_: *mut crate::leanh::LeanObject,
    mut v___y_2721_: *mut crate::leanh::LeanObject,
    mut v___y_2722_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2723_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(
            v_inst_2711_,
            v_R_2712_,
            v_a_2713_,
            v_b_2714_,
            v_c_2715_,
            v___y_2716_,
            v___y_2717_,
            v___y_2718_,
            v___y_2719_,
            v___y_2720_,
            v___y_2721_,
        );
    crate::leanh::lean_dec(v___y_2721_);
    crate::leanh::lean_dec_ref(v___y_2720_);
    crate::leanh::lean_dec(v___y_2719_);
    crate::leanh::lean_dec_ref(v___y_2718_);
    crate::leanh::lean_dec(v___y_2717_);
    crate::leanh::lean_dec_ref(v___y_2716_);
    return v_res_2723_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visit(
    mut v_code_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_decl_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_2749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: u8 = 0;
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: u8 = 0;
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2757_: usize = 0;
    let mut v___x_2758_: usize = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: usize = 0;
    let mut v___x_2761_: usize = 0;
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_2765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2769_: u8 = 0;
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: u8 = 0;
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2777_: u8 = 0;
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2781_: usize = 0;
    let mut v___x_2782_: usize = 0;
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2784_: usize = 0;
    let mut v___x_2785_: usize = 0;
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2787_: u8 = 0;
    let mut v_unused_2788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2793_: u8 = 0;
    let mut v___x_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2798_: u8 = 0;
    let mut v_unused_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_2724_) {
                0 => {
                    v_decl_2744_ = crate::leanh::lean_ctor_get(v_code_2724_, 0);
                    crate::leanh::lean_inc_ref(v_decl_2744_);
                    v_k_2745_ = crate::leanh::lean_ctor_get(v_code_2724_, 1);
                    crate::leanh::lean_inc_ref(v_k_2745_);
                    crate::leanh::lean_dec_ref_known(v_code_2724_, 2);
                    v_value_2746_ = crate::leanh::lean_ctor_get(v_decl_2744_, 3);
                    crate::leanh::lean_inc(v_value_2746_);
                    crate::leanh::lean_dec_ref(v_decl_2744_);
                    v___x_2747_ = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(
                        v_value_2746_,
                        v_a_2725_,
                        v_a_2726_,
                        v_a_2727_,
                        v_a_2728_,
                        v_a_2729_,
                        v_a_2730_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2747_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_2747_, 1);
                        v_code_2724_ = v_k_2745_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_k_2745_);
                        return v___x_2747_;
                    }
                }
                3 => {
                    v_args_2749_ = crate::leanh::lean_ctor_get(v_code_2724_, 1);
                    crate::leanh::lean_inc_ref(v_args_2749_);
                    crate::leanh::lean_dec_ref_known(v_code_2724_, 2);
                    v___x_2750_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2751_ = lean_array_get_size(v_args_2749_);
                    v___x_2752_ = crate::leanh::lean_box(0);
                    v___x_2753_ = lean_nat_dec_lt(v___x_2750_, v___x_2751_);
                    if v___x_2753_ == 0 {
                        crate::leanh::lean_dec_ref(v_args_2749_);
                        v___x_2754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2754_, 0, v___x_2752_);
                        return v___x_2754_;
                    } else {
                        v___x_2755_ = lean_nat_dec_le(v___x_2751_, v___x_2751_);
                        if v___x_2755_ == 0 {
                            if v___x_2753_ == 0 {
                                crate::leanh::lean_dec_ref(v_args_2749_);
                                v___x_2756_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2756_, 0, v___x_2752_);
                                return v___x_2756_;
                            } else {
                                v___x_2757_ = 0usize;
                                v___x_2758_ = lean_usize_of_nat(v___x_2751_);
                                v___x_2759_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2749_, v___x_2757_, v___x_2758_, v___x_2752_, v_a_2725_, v_a_2726_);
                                crate::leanh::lean_dec_ref(v_args_2749_);
                                return v___x_2759_;
                            }
                        } else {
                            v___x_2760_ = 0usize;
                            v___x_2761_ = lean_usize_of_nat(v___x_2751_);
                            v___x_2762_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(v_args_2749_, v___x_2760_, v___x_2761_, v___x_2752_, v_a_2725_, v_a_2726_);
                            crate::leanh::lean_dec_ref(v_args_2749_);
                            return v___x_2762_;
                        }
                    }
                }
                4 => {
                    v_cases_2763_ = crate::leanh::lean_ctor_get(v_code_2724_, 0);
                    crate::leanh::lean_inc_ref(v_cases_2763_);
                    crate::leanh::lean_dec_ref_known(v_code_2724_, 1);
                    v_discr_2764_ = crate::leanh::lean_ctor_get(v_cases_2763_, 2);
                    crate::leanh::lean_inc(v_discr_2764_);
                    v_alts_2765_ = crate::leanh::lean_ctor_get(v_cases_2763_, 3);
                    crate::leanh::lean_inc_ref(v_alts_2765_);
                    crate::leanh::lean_dec_ref(v_cases_2763_);
                    v___x_2766_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_discr_2764_,
                        v_a_2725_,
                        v_a_2726_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2766_) == 0 {
                        v_isSharedCheck_2787_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2766_)) as u8;
                        if v_isSharedCheck_2787_ == 0 {
                            v_unused_2788_ = crate::leanh::lean_ctor_get(v___x_2766_, 0);
                            crate::leanh::lean_dec(v_unused_2788_);
                            v___x_2768_ = v___x_2766_;
                            v_isShared_2769_ = v_isSharedCheck_2787_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_2766_);
                            v___x_2768_ = crate::leanh::lean_box(0);
                            v_isShared_2769_ = v_isSharedCheck_2787_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_alts_2765_);
                        return v___x_2766_;
                    }
                }
                5 => {
                    v_fvarId_2789_ = crate::leanh::lean_ctor_get(v_code_2724_, 0);
                    crate::leanh::lean_inc(v_fvarId_2789_);
                    crate::leanh::lean_dec_ref_known(v_code_2724_, 1);
                    v___x_2790_ = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(
                        v_fvarId_2789_,
                        v_a_2725_,
                        v_a_2726_,
                    );
                    return v___x_2790_;
                }
                6 => {
                    v_isSharedCheck_2798_ = (!crate::leanh::lean_is_exclusive(v_code_2724_)) as u8;
                    if v_isSharedCheck_2798_ == 0 {
                        v_unused_2799_ = crate::leanh::lean_ctor_get(v_code_2724_, 0);
                        crate::leanh::lean_dec(v_unused_2799_);
                        v___x_2792_ = v_code_2724_;
                        v_isShared_2793_ = v_isSharedCheck_2798_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_2724_);
                        v___x_2792_ = crate::leanh::lean_box(0);
                        v_isShared_2793_ = v_isSharedCheck_2798_;
                        state = 5;
                        continue;
                    }
                }
                _ => {
                    v_decl_2800_ = crate::leanh::lean_ctor_get(v_code_2724_, 0);
                    crate::leanh::lean_inc_ref(v_decl_2800_);
                    v_k_2801_ = crate::leanh::lean_ctor_get(v_code_2724_, 1);
                    crate::leanh::lean_inc_ref(v_k_2801_);
                    crate::leanh::lean_dec_ref(v_code_2724_);
                    v_decl_2733_ = v_decl_2800_;
                    v_k_2734_ = v_k_2801_;
                    v___y_2735_ = v_a_2725_;
                    v___y_2736_ = v_a_2726_;
                    v___y_2737_ = v_a_2727_;
                    v___y_2738_ = v_a_2728_;
                    v___y_2739_ = v_a_2729_;
                    v___y_2740_ = v_a_2730_;
                    state = 1;
                    continue;
                }
            },
            1 => {
                v_value_2741_ = crate::leanh::lean_ctor_get(v_decl_2733_, 4);
                crate::leanh::lean_inc_ref(v_value_2741_);
                crate::leanh::lean_dec_ref(v_decl_2733_);
                v___x_2742_ = l_Lean_Compiler_LCNF_FindUsed_visit(
                    v_value_2741_,
                    v___y_2735_,
                    v___y_2736_,
                    v___y_2737_,
                    v___y_2738_,
                    v___y_2739_,
                    v___y_2740_,
                );
                if crate::leanh::lean_obj_tag(v___x_2742_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_2742_, 1);
                    v_code_2724_ = v_k_2734_;
                    v_a_2725_ = v___y_2735_;
                    v_a_2726_ = v___y_2736_;
                    v_a_2727_ = v___y_2737_;
                    v_a_2728_ = v___y_2738_;
                    v_a_2729_ = v___y_2739_;
                    v_a_2730_ = v___y_2740_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec_ref(v_k_2734_);
                    return v___x_2742_;
                }
            }
            2 => {
                v___x_2770_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2771_ = lean_array_get_size(v_alts_2765_);
                v___x_2772_ = crate::leanh::lean_box(0);
                v___x_2773_ = lean_nat_dec_lt(v___x_2770_, v___x_2771_);
                if v___x_2773_ == 0 {
                    crate::leanh::lean_dec_ref(v_alts_2765_);
                    if v_isShared_2769_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2768_, 0, v___x_2772_);
                        v___x_2775_ = v___x_2768_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2776_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
                        v___x_2775_ = v_reuseFailAlloc_2776_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_2777_ = lean_nat_dec_le(v___x_2771_, v___x_2771_);
                    if v___x_2777_ == 0 {
                        if v___x_2773_ == 0 {
                            crate::leanh::lean_dec_ref(v_alts_2765_);
                            if v_isShared_2769_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_2768_, 0, v___x_2772_);
                                v___x_2779_ = v___x_2768_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_2780_ =
                                    crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v___x_2772_);
                                v___x_2779_ = v_reuseFailAlloc_2780_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_2768_);
                            v___x_2781_ = 0usize;
                            v___x_2782_ = lean_usize_of_nat(v___x_2771_);
                            v___x_2783_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_2765_, v___x_2781_, v___x_2782_, v___x_2772_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
                            crate::leanh::lean_dec_ref(v_alts_2765_);
                            return v___x_2783_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2768_);
                        v___x_2784_ = 0usize;
                        v___x_2785_ = lean_usize_of_nat(v___x_2771_);
                        v___x_2786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_alts_2765_, v___x_2784_, v___x_2785_, v___x_2772_, v_a_2725_, v_a_2726_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
                        crate::leanh::lean_dec_ref(v_alts_2765_);
                        return v___x_2786_;
                    }
                }
            }
            3 => {
                return v___x_2775_;
            }
            4 => {
                return v___x_2779_;
            }
            5 => {
                v___x_2794_ = crate::leanh::lean_box(0);
                if v_isShared_2793_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2792_, 0);
                    crate::leanh::lean_ctor_set(v___x_2792_, 0, v___x_2794_);
                    v___x_2796_ = v___x_2792_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2797_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
                    v___x_2796_ = v_reuseFailAlloc_2797_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2796_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(
    mut v_as_2802_: *mut crate::leanh::LeanObject,
    mut v_i_2803_: usize,
    mut v_stop_2804_: usize,
    mut v_b_2805_: *mut crate::leanh::LeanObject,
    mut v___y_2806_: *mut crate::leanh::LeanObject,
    mut v___y_2807_: *mut crate::leanh::LeanObject,
    mut v___y_2808_: *mut crate::leanh::LeanObject,
    mut v___y_2809_: *mut crate::leanh::LeanObject,
    mut v___y_2810_: *mut crate::leanh::LeanObject,
    mut v___y_2811_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: usize = 0;
    let mut v___x_2818_: usize = 0;
    let mut v___x_2820_: u8 = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2820_ = lean_usize_dec_eq(v_i_2803_, v_stop_2804_);
                if v___x_2820_ == 0 {
                    v___x_2821_ = lean_array_uget_borrowed(v_as_2802_, v_i_2803_);
                    match crate::leanh::lean_obj_tag(v___x_2821_) {
                        0 => {
                            v_code_2822_ = crate::leanh::lean_ctor_get(v___x_2821_, 2);
                            crate::leanh::lean_inc_ref(v_code_2822_);
                            v___y_2814_ = v_code_2822_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_2823_ = crate::leanh::lean_ctor_get(v___x_2821_, 1);
                            crate::leanh::lean_inc_ref(v_code_2823_);
                            v___y_2814_ = v_code_2823_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_2824_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                            crate::leanh::lean_inc_ref(v_code_2824_);
                            v___y_2814_ = v_code_2824_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_2825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2825_, 0, v_b_2805_);
                    return v___x_2825_;
                }
            }
            1 => {
                v___x_2815_ = l_Lean_Compiler_LCNF_FindUsed_visit(
                    v___y_2814_,
                    v___y_2806_,
                    v___y_2807_,
                    v___y_2808_,
                    v___y_2809_,
                    v___y_2810_,
                    v___y_2811_,
                );
                if crate::leanh::lean_obj_tag(v___x_2815_) == 0 {
                    v_a_2816_ = crate::leanh::lean_ctor_get(v___x_2815_, 0);
                    crate::leanh::lean_inc(v_a_2816_);
                    crate::leanh::lean_dec_ref_known(v___x_2815_, 1);
                    v___x_2817_ = 1usize;
                    v___x_2818_ = lean_usize_add(v_i_2803_, v___x_2817_);
                    v_i_2803_ = v___x_2818_;
                    v_b_2805_ = v_a_2816_;
                    state = 0;
                    continue;
                } else {
                    return v___x_2815_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(
    mut v_as_2826_: *mut crate::leanh::LeanObject,
    mut v_i_2827_: *mut crate::leanh::LeanObject,
    mut v_stop_2828_: *mut crate::leanh::LeanObject,
    mut v_b_2829_: *mut crate::leanh::LeanObject,
    mut v___y_2830_: *mut crate::leanh::LeanObject,
    mut v___y_2831_: *mut crate::leanh::LeanObject,
    mut v___y_2832_: *mut crate::leanh::LeanObject,
    mut v___y_2833_: *mut crate::leanh::LeanObject,
    mut v___y_2834_: *mut crate::leanh::LeanObject,
    mut v___y_2835_: *mut crate::leanh::LeanObject,
    mut v___y_2836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2837_: usize = 0;
    let mut v_stop_boxed_2838_: usize = 0;
    let mut v_res_2839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2837_ = crate::leanh::lean_unbox_usize(v_i_2827_);
    crate::leanh::lean_dec(v_i_2827_);
    v_stop_boxed_2838_ = crate::leanh::lean_unbox_usize(v_stop_2828_);
    crate::leanh::lean_dec(v_stop_2828_);
    v_res_2839_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_visit_spec__0(v_as_2826_, v_i_boxed_2837_, v_stop_boxed_2838_, v_b_2829_, v___y_2830_, v___y_2831_, v___y_2832_, v___y_2833_, v___y_2834_, v___y_2835_);
    crate::leanh::lean_dec(v___y_2835_);
    crate::leanh::lean_dec_ref(v___y_2834_);
    crate::leanh::lean_dec(v___y_2833_);
    crate::leanh::lean_dec_ref(v___y_2832_);
    crate::leanh::lean_dec(v___y_2831_);
    crate::leanh::lean_dec_ref(v___y_2830_);
    crate::leanh::lean_dec_ref(v_as_2826_);
    return v_res_2839_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_visit___boxed(
    mut v_code_2840_: *mut crate::leanh::LeanObject,
    mut v_a_2841_: *mut crate::leanh::LeanObject,
    mut v_a_2842_: *mut crate::leanh::LeanObject,
    mut v_a_2843_: *mut crate::leanh::LeanObject,
    mut v_a_2844_: *mut crate::leanh::LeanObject,
    mut v_a_2845_: *mut crate::leanh::LeanObject,
    mut v_a_2846_: *mut crate::leanh::LeanObject,
    mut v_a_2847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2848_ = l_Lean_Compiler_LCNF_FindUsed_visit(
        v_code_2840_,
        v_a_2841_,
        v_a_2842_,
        v_a_2843_,
        v_a_2844_,
        v_a_2845_,
        v_a_2846_,
    );
    crate::leanh::lean_dec(v_a_2846_);
    crate::leanh::lean_dec_ref(v_a_2845_);
    crate::leanh::lean_dec(v_a_2844_);
    crate::leanh::lean_dec_ref(v_a_2843_);
    crate::leanh::lean_dec(v_a_2842_);
    crate::leanh::lean_dec_ref(v_a_2841_);
    return v_res_2848_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(
    mut v_f_2849_: *mut crate::leanh::LeanObject,
    mut v_v_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
    mut v___y_2852_: *mut crate::leanh::LeanObject,
    mut v___y_2853_: *mut crate::leanh::LeanObject,
    mut v___y_2854_: *mut crate::leanh::LeanObject,
    mut v___y_2855_: *mut crate::leanh::LeanObject,
    mut v___y_2856_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2867_: u8 = 0;
    let mut v_unused_2868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_2850_) == 0 {
                    v_code_2858_ = crate::leanh::lean_ctor_get(v_v_2850_, 0);
                    crate::leanh::lean_inc_ref(v_code_2858_);
                    crate::leanh::lean_dec_ref_known(v_v_2850_, 1);
                    crate::leanh::lean_inc(v___y_2856_);
                    crate::leanh::lean_inc_ref(v___y_2855_);
                    crate::leanh::lean_inc(v___y_2854_);
                    crate::leanh::lean_inc_ref(v___y_2853_);
                    crate::leanh::lean_inc(v___y_2852_);
                    crate::leanh::lean_inc_ref(v___y_2851_);
                    v___x_2859_ = crate::leanh::lean_apply_8(
                        v_f_2849_,
                        v_code_2858_,
                        v___y_2851_,
                        v___y_2852_,
                        v___y_2853_,
                        v___y_2854_,
                        v___y_2855_,
                        v___y_2856_,
                        crate::leanh::lean_box(0),
                    );
                    return v___x_2859_;
                } else {
                    crate::leanh::lean_dec_ref(v_f_2849_);
                    v_isSharedCheck_2867_ = (!crate::leanh::lean_is_exclusive(v_v_2850_)) as u8;
                    if v_isSharedCheck_2867_ == 0 {
                        v_unused_2868_ = crate::leanh::lean_ctor_get(v_v_2850_, 0);
                        crate::leanh::lean_dec(v_unused_2868_);
                        v___x_2861_ = v_v_2850_;
                        v_isShared_2862_ = v_isSharedCheck_2867_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_v_2850_);
                        v___x_2861_ = crate::leanh::lean_box(0);
                        v_isShared_2862_ = v_isSharedCheck_2867_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2863_ = crate::leanh::lean_box(0);
                if v_isShared_2862_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2861_, 0);
                    crate::leanh::lean_ctor_set(v___x_2861_, 0, v___x_2863_);
                    v___x_2865_ = v___x_2861_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2866_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
                    v___x_2865_ = v_reuseFailAlloc_2866_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2865_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg___boxed(
    mut v_f_2869_: *mut crate::leanh::LeanObject,
    mut v_v_2870_: *mut crate::leanh::LeanObject,
    mut v___y_2871_: *mut crate::leanh::LeanObject,
    mut v___y_2872_: *mut crate::leanh::LeanObject,
    mut v___y_2873_: *mut crate::leanh::LeanObject,
    mut v___y_2874_: *mut crate::leanh::LeanObject,
    mut v___y_2875_: *mut crate::leanh::LeanObject,
    mut v___y_2876_: *mut crate::leanh::LeanObject,
    mut v___y_2877_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2878_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_2869_, v_v_2870_, v___y_2871_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_, v___y_2876_);
    crate::leanh::lean_dec(v___y_2876_);
    crate::leanh::lean_dec_ref(v___y_2875_);
    crate::leanh::lean_dec(v___y_2874_);
    crate::leanh::lean_dec_ref(v___y_2873_);
    crate::leanh::lean_dec(v___y_2872_);
    crate::leanh::lean_dec_ref(v___y_2871_);
    return v_res_2878_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(
    mut v_pu_2879_: u8,
    mut v_f_2880_: *mut crate::leanh::LeanObject,
    mut v_v_2881_: *mut crate::leanh::LeanObject,
    mut v___y_2882_: *mut crate::leanh::LeanObject,
    mut v___y_2883_: *mut crate::leanh::LeanObject,
    mut v___y_2884_: *mut crate::leanh::LeanObject,
    mut v___y_2885_: *mut crate::leanh::LeanObject,
    mut v___y_2886_: *mut crate::leanh::LeanObject,
    mut v___y_2887_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2889_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v_f_2880_, v_v_2881_, v___y_2882_, v___y_2883_, v___y_2884_, v___y_2885_, v___y_2886_, v___y_2887_);
    return v___x_2889_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___boxed(
    mut v_pu_2890_: *mut crate::leanh::LeanObject,
    mut v_f_2891_: *mut crate::leanh::LeanObject,
    mut v_v_2892_: *mut crate::leanh::LeanObject,
    mut v___y_2893_: *mut crate::leanh::LeanObject,
    mut v___y_2894_: *mut crate::leanh::LeanObject,
    mut v___y_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_2900_: u8 = 0;
    let mut v_res_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_2900_ = (crate::leanh::lean_unbox(v_pu_2890_) as u8);
    v_res_2901_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(v_pu_boxed_2900_, v_f_2891_, v_v_2892_, v___y_2893_, v___y_2894_, v___y_2895_, v___y_2896_, v___y_2897_, v___y_2898_);
    crate::leanh::lean_dec(v___y_2898_);
    crate::leanh::lean_dec_ref(v___y_2897_);
    crate::leanh::lean_dec(v___y_2896_);
    crate::leanh::lean_dec_ref(v___y_2895_);
    crate::leanh::lean_dec(v___y_2894_);
    crate::leanh::lean_dec_ref(v___y_2893_);
    return v_res_2901_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(
    mut v_as_2902_: *mut crate::leanh::LeanObject,
    mut v_i_2903_: usize,
    mut v_stop_2904_: usize,
    mut v_b_2905_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2906_: u8 = 0;
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: usize = 0;
    let mut v___x_2911_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2906_ = lean_usize_dec_eq(v_i_2903_, v_stop_2904_);
                if v___x_2906_ == 0 {
                    v___x_2907_ = lean_array_uget_borrowed(v_as_2902_, v_i_2903_);
                    v_fvarId_2908_ = crate::leanh::lean_ctor_get(v___x_2907_, 0);
                    crate::leanh::lean_inc(v_fvarId_2908_);
                    v___x_2909_ = l_Lean_FVarIdSet_insert(v_b_2905_, v_fvarId_2908_);
                    v___x_2910_ = 1usize;
                    v___x_2911_ = lean_usize_add(v_i_2903_, v___x_2910_);
                    v_i_2903_ = v___x_2911_;
                    v_b_2905_ = v___x_2909_;
                    state = 0;
                    continue;
                } else {
                    return v_b_2905_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(
    mut v_as_2913_: *mut crate::leanh::LeanObject,
    mut v_i_2914_: *mut crate::leanh::LeanObject,
    mut v_stop_2915_: *mut crate::leanh::LeanObject,
    mut v_b_2916_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_2917_: usize = 0;
    let mut v_stop_boxed_2918_: usize = 0;
    let mut v_res_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_2917_ = crate::leanh::lean_unbox_usize(v_i_2914_);
    crate::leanh::lean_dec(v_i_2914_);
    v_stop_boxed_2918_ = crate::leanh::lean_unbox_usize(v_stop_2915_);
    crate::leanh::lean_dec(v_stop_2915_);
    v_res_2919_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_as_2913_, v_i_boxed_2917_, v_stop_boxed_2918_, v_b_2916_);
    crate::leanh::lean_dec_ref(v_as_2913_);
    return v_res_2919_;
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(
    mut v_decl_2921_: *mut crate::leanh::LeanObject,
    mut v_a_2922_: *mut crate::leanh::LeanObject,
    mut v_a_2923_: *mut crate::leanh::LeanObject,
    mut v_a_2924_: *mut crate::leanh::LeanObject,
    mut v_a_2925_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toSignature_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2940_: u8 = 0;
    let mut v___x_2941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2945_: u8 = 0;
    let mut v_unused_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2950_: u8 = 0;
    let mut v___x_2952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2954_: u8 = 0;
    let mut v___x_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2957_: u8 = 0;
    let mut v___x_2958_: u8 = 0;
    let mut v___x_2959_: usize = 0;
    let mut v___x_2960_: usize = 0;
    let mut v___x_2961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: usize = 0;
    let mut v___x_2963_: usize = 0;
    let mut v___x_2964_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toSignature_2927_ = crate::leanh::lean_ctor_get(v_decl_2921_, 0);
                v_value_2928_ = crate::leanh::lean_ctor_get(v_decl_2921_, 1);
                crate::leanh::lean_inc_ref(v_value_2928_);
                v_params_2929_ = crate::leanh::lean_ctor_get(v_toSignature_2927_, 3);
                v___x_2930_ = crate::leanh::lean_box(1);
                v___x_2931_ = l_Lean_instEmptyCollectionFVarIdHashSet;
                v___x_2955_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_2956_ = lean_array_get_size(v_params_2929_);
                v___x_2957_ = lean_nat_dec_lt(v___x_2955_, v___x_2956_);
                if v___x_2957_ == 0 {
                    v___y_2933_ = v___x_2930_;
                    state = 1;
                    continue;
                } else {
                    v___x_2958_ = lean_nat_dec_le(v___x_2956_, v___x_2956_);
                    if v___x_2958_ == 0 {
                        if v___x_2957_ == 0 {
                            v___y_2933_ = v___x_2930_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2959_ = 0usize;
                            v___x_2960_ = lean_usize_of_nat(v___x_2956_);
                            v___x_2961_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_2929_, v___x_2959_, v___x_2960_, v___x_2930_);
                            v___y_2933_ = v___x_2961_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_2962_ = 0usize;
                        v___x_2963_ = lean_usize_of_nat(v___x_2956_);
                        v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(v_params_2929_, v___x_2962_, v___x_2963_, v___x_2930_);
                        v___y_2933_ = v___x_2964_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2934_ = lean_st_mk_ref(v___x_2931_);
                v___x_2935_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___closed__0;
                v___x_2936_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2936_, 0, v_decl_2921_);
                crate::leanh::lean_ctor_set(v___x_2936_, 1, v___y_2933_);
                v___x_2937_ = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___00Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0___redArg(v___x_2935_, v_value_2928_, v___x_2936_, v___x_2934_, v_a_2922_, v_a_2923_, v_a_2924_, v_a_2925_);
                crate::leanh::lean_dec_ref_known(v___x_2936_, 2);
                if crate::leanh::lean_obj_tag(v___x_2937_) == 0 {
                    v_isSharedCheck_2945_ = (!crate::leanh::lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2945_ == 0 {
                        v_unused_2946_ = crate::leanh::lean_ctor_get(v___x_2937_, 0);
                        crate::leanh::lean_dec(v_unused_2946_);
                        v___x_2939_ = v___x_2937_;
                        v_isShared_2940_ = v_isSharedCheck_2945_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_2937_);
                        v___x_2939_ = crate::leanh::lean_box(0);
                        v_isShared_2940_ = v_isSharedCheck_2945_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2934_);
                    v_a_2947_ = crate::leanh::lean_ctor_get(v___x_2937_, 0);
                    v_isSharedCheck_2954_ = (!crate::leanh::lean_is_exclusive(v___x_2937_)) as u8;
                    if v_isSharedCheck_2954_ == 0 {
                        v___x_2949_ = v___x_2937_;
                        v_isShared_2950_ = v_isSharedCheck_2954_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2947_);
                        crate::leanh::lean_dec(v___x_2937_);
                        v___x_2949_ = crate::leanh::lean_box(0);
                        v_isShared_2950_ = v_isSharedCheck_2954_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2941_ = lean_st_ref_get(v___x_2934_);
                crate::leanh::lean_dec(v___x_2934_);
                if v_isShared_2940_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2939_, 0, v___x_2941_);
                    v___x_2943_ = v___x_2939_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2944_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2941_);
                    v___x_2943_ = v_reuseFailAlloc_2944_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2943_;
            }
            4 => {
                if v_isShared_2950_ == 0 {
                    v___x_2952_ = v___x_2949_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2953_, 0, v_a_2947_);
                    v___x_2952_ = v_reuseFailAlloc_2953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_FindUsed_collectUsedParams___boxed(
    mut v_decl_2965_: *mut crate::leanh::LeanObject,
    mut v_a_2966_: *mut crate::leanh::LeanObject,
    mut v_a_2967_: *mut crate::leanh::LeanObject,
    mut v_a_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2971_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(
        v_decl_2965_,
        v_a_2966_,
        v_a_2967_,
        v_a_2968_,
        v_a_2969_,
    );
    crate::leanh::lean_dec(v_a_2969_);
    crate::leanh::lean_dec_ref(v_a_2968_);
    crate::leanh::lean_dec(v_a_2967_);
    crate::leanh::lean_dec_ref(v_a_2966_);
    return v_res_2971_;
}
pub unsafe fn _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2972_: u8 = 0;
    let mut v___x_2973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2972_ = 0;
    v___x_2973_ = l_Lean_Compiler_LCNF_instInhabitedCode_default__1(v___x_2972_);
    return v___x_2973_;
}
pub unsafe fn l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(
    mut v_msg_2974_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2975_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0_once
        ),
        _init_l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___closed__0,
    );
    v___x_2976_ = lean_panic_fn_borrowed(v___x_2975_, v_msg_2974_);
    return v___x_2976_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(
    mut v_args_2977_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2978_: *mut crate::leanh::LeanObject,
    mut v___x_2979_: *mut crate::leanh::LeanObject,
    mut v_a_2980_: *mut crate::leanh::LeanObject,
    mut v_b_2981_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_2984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: u8 = 0;
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2994_: u8 = 0;
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2991_ = lean_nat_dec_lt(v_a_2980_, v_upperBound_2978_);
                if v___x_2991_ == 0 {
                    crate::leanh::lean_dec(v_a_2980_);
                    v___x_2992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2992_, 0, v_b_2981_);
                    return v___x_2992_;
                } else {
                    v___x_2993_ = lean_array_get_size(v___x_2979_);
                    v___x_2994_ = lean_nat_dec_lt(v_a_2980_, v___x_2993_);
                    if v___x_2994_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v___x_2995_ = lean_array_fget_borrowed(v___x_2979_, v_a_2980_);
                        v___x_2996_ = (crate::leanh::lean_unbox(v___x_2995_) as u8);
                        if v___x_2996_ == 0 {
                            v_a_2984_ = v_b_2981_;
                            state = 1;
                            continue;
                        } else {
                            state = 2;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2985_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2986_ = lean_nat_add(v_a_2980_, v___x_2985_);
                crate::leanh::lean_dec(v_a_2980_);
                v_a_2980_ = v___x_2986_;
                v_b_2981_ = v_a_2984_;
                state = 0;
                continue;
            }
            2 => {
                v___x_2989_ = lean_array_fget_borrowed(v_args_2977_, v_a_2980_);
                crate::leanh::lean_inc(v___x_2989_);
                v___x_2990_ = lean_array_push(v_b_2981_, v___x_2989_);
                v_a_2984_ = v___x_2990_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg___boxed(
    mut v_args_2997_: *mut crate::leanh::LeanObject,
    mut v_upperBound_2998_: *mut crate::leanh::LeanObject,
    mut v___x_2999_: *mut crate::leanh::LeanObject,
    mut v_a_3000_: *mut crate::leanh::LeanObject,
    mut v_b_3001_: *mut crate::leanh::LeanObject,
    mut v___y_3002_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3003_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_2997_, v_upperBound_2998_, v___x_2999_, v_a_3000_, v_b_3001_);
    crate::leanh::lean_dec_ref(v___x_2999_);
    crate::leanh::lean_dec(v_upperBound_2998_);
    crate::leanh::lean_dec_ref(v_args_2997_);
    return v_res_3003_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3007_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__2;
    v___x_3008_ = crate::leanh::lean_unsigned_to_nat(9);
    v___x_3009_ = crate::leanh::lean_unsigned_to_nat(641);
    v___x_3010_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__1;
    v___x_3011_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__0;
    v___x_3012_ = l_mkPanicMessageWithDecl(
        v___x_3011_,
        v___x_3010_,
        v___x_3009_,
        v___x_3008_,
        v___x_3007_,
    );
    return v___x_3012_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ReduceArity_reduce(
    mut v_code_3015_: *mut crate::leanh::LeanObject,
    mut v_a_3016_: *mut crate::leanh::LeanObject,
    mut v_a_3017_: *mut crate::leanh::LeanObject,
    mut v_a_3018_: *mut crate::leanh::LeanObject,
    mut v_a_3019_: *mut crate::leanh::LeanObject,
    mut v_a_3020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3025_: u8 = 0;
    let mut v___x_3026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3032_: u8 = 0;
    let mut v___x_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3049_: u8 = 0;
    let mut v___x_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3056_: usize = 0;
    let mut v___x_3057_: usize = 0;
    let mut v___x_3058_: u8 = 0;
    let mut v___x_3059_: usize = 0;
    let mut v___x_3060_: usize = 0;
    let mut v___x_3061_: u8 = 0;
    let mut v_a_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: usize = 0;
    let mut v___x_3066_: usize = 0;
    let mut v___x_3067_: u8 = 0;
    let mut v___x_3068_: usize = 0;
    let mut v___x_3069_: usize = 0;
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3073_: u8 = 0;
    let mut v___x_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3079_: u8 = 0;
    let mut v_unused_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3084_: u8 = 0;
    let mut v___x_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3088_: u8 = 0;
    let mut v_decl_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_3092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3096_: u8 = 0;
    let mut v_declName_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclName_3098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_paramMask_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: u8 = 0;
    let mut v___x_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3105_: u8 = 0;
    let mut v___y_3107_: u8 = 0;
    let mut v___x_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3110_: u8 = 0;
    let mut v___x_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3117_: u8 = 0;
    let mut v_unused_3118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3123_: usize = 0;
    let mut v___x_3124_: usize = 0;
    let mut v___x_3125_: u8 = 0;
    let mut v___x_3126_: usize = 0;
    let mut v___x_3127_: u8 = 0;
    let mut v_isSharedCheck_3128_: u8 = 0;
    let mut v___x_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3134_: u8 = 0;
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3144_: u8 = 0;
    let mut v___y_3146_: u8 = 0;
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3149_: u8 = 0;
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3156_: u8 = 0;
    let mut v_unused_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3162_: usize = 0;
    let mut v___x_3163_: usize = 0;
    let mut v___x_3164_: u8 = 0;
    let mut v___x_3165_: usize = 0;
    let mut v___x_3166_: usize = 0;
    let mut v___x_3167_: u8 = 0;
    let mut v_isSharedCheck_3168_: u8 = 0;
    let mut v_a_3169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3172_: u8 = 0;
    let mut v___x_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3176_: u8 = 0;
    let mut v_reuseFailAlloc_3177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3181_: u8 = 0;
    let mut v___x_3183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3185_: u8 = 0;
    let mut v_isSharedCheck_3186_: u8 = 0;
    let mut v_unused_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___y_3195_: u8 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3198_: u8 = 0;
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_unused_3206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: usize = 0;
    let mut v___x_3212_: usize = 0;
    let mut v___x_3213_: u8 = 0;
    let mut v___x_3214_: usize = 0;
    let mut v___x_3215_: u8 = 0;
    let mut v_isSharedCheck_3216_: u8 = 0;
    let mut v_decl_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_decl_3219_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_3220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cases_3221_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeName_3222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_resultType_3223_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_discr_3224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_alts_3225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3228_: u8 = 0;
    let mut v___x_3229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3234_: u8 = 0;
    let mut v___x_3235_: usize = 0;
    let mut v___x_3236_: usize = 0;
    let mut v___x_3237_: u8 = 0;
    let mut v___x_3239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3240_: u8 = 0;
    let mut v___x_3242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3250_: u8 = 0;
    let mut v_unused_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3255_: u8 = 0;
    let mut v_a_3256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3259_: u8 = 0;
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3263_: u8 = 0;
    let mut v_isSharedCheck_3264_: u8 = 0;
    let mut v___x_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match crate::leanh::lean_obj_tag(v_code_3015_) {
                0 => {
                    v_decl_3089_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                    v_value_3090_ = crate::leanh::lean_ctor_get(v_decl_3089_, 3);
                    crate::leanh::lean_inc(v_value_3090_);
                    if crate::leanh::lean_obj_tag(v_value_3090_) == 3 {
                        v_k_3091_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                        v_declName_3092_ = crate::leanh::lean_ctor_get(v_value_3090_, 0);
                        v_args_3093_ = crate::leanh::lean_ctor_get(v_value_3090_, 2);
                        v_isSharedCheck_3186_ =
                            (!crate::leanh::lean_is_exclusive(v_value_3090_)) as u8;
                        if v_isSharedCheck_3186_ == 0 {
                            v_unused_3187_ = crate::leanh::lean_ctor_get(v_value_3090_, 1);
                            crate::leanh::lean_dec(v_unused_3187_);
                            v___x_3095_ = v_value_3090_;
                            v_isShared_3096_ = v_isSharedCheck_3186_;
                            state = 8;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_args_3093_);
                            crate::leanh::lean_inc(v_declName_3092_);
                            crate::leanh::lean_dec(v_value_3090_);
                            v___x_3095_ = crate::leanh::lean_box(0);
                            v_isShared_3096_ = v_isSharedCheck_3186_;
                            state = 8;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_value_3090_);
                        v_k_3188_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                        crate::leanh::lean_inc_ref(v_k_3188_);
                        v___x_3189_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                            v_k_3188_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3189_) == 0 {
                            v_a_3190_ = crate::leanh::lean_ctor_get(v___x_3189_, 0);
                            v_isSharedCheck_3216_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3189_)) as u8;
                            if v_isSharedCheck_3216_ == 0 {
                                v___x_3192_ = v___x_3189_;
                                v_isShared_3193_ = v_isSharedCheck_3216_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3190_);
                                crate::leanh::lean_dec(v___x_3189_);
                                v___x_3192_ = crate::leanh::lean_box(0);
                                v_isShared_3193_ = v_isSharedCheck_3216_;
                                state = 26;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v_code_3015_, 2);
                            return v___x_3189_;
                        }
                    }
                }
                1 => {
                    v_decl_3217_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                    v_k_3218_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                    crate::leanh::lean_inc_ref(v_k_3218_);
                    crate::leanh::lean_inc_ref(v_decl_3217_);
                    v_decl_3037_ = v_decl_3217_;
                    v_k_3038_ = v_k_3218_;
                    v___y_3039_ = v_a_3016_;
                    v___y_3040_ = v_a_3017_;
                    v___y_3041_ = v_a_3018_;
                    v___y_3042_ = v_a_3019_;
                    v___y_3043_ = v_a_3020_;
                    state = 3;
                    continue;
                }
                2 => {
                    v_decl_3219_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                    v_k_3220_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                    crate::leanh::lean_inc_ref(v_k_3220_);
                    crate::leanh::lean_inc_ref(v_decl_3219_);
                    v_decl_3037_ = v_decl_3219_;
                    v_k_3038_ = v_k_3220_;
                    v___y_3039_ = v_a_3016_;
                    v___y_3040_ = v_a_3017_;
                    v___y_3041_ = v_a_3018_;
                    v___y_3042_ = v_a_3019_;
                    v___y_3043_ = v_a_3020_;
                    state = 3;
                    continue;
                }
                4 => {
                    v_cases_3221_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                    crate::leanh::lean_inc_ref(v_cases_3221_);
                    v_typeName_3222_ = crate::leanh::lean_ctor_get(v_cases_3221_, 0);
                    v_resultType_3223_ = crate::leanh::lean_ctor_get(v_cases_3221_, 1);
                    v_discr_3224_ = crate::leanh::lean_ctor_get(v_cases_3221_, 2);
                    v_alts_3225_ = crate::leanh::lean_ctor_get(v_cases_3221_, 3);
                    v_isSharedCheck_3264_ = (!crate::leanh::lean_is_exclusive(v_cases_3221_)) as u8;
                    if v_isSharedCheck_3264_ == 0 {
                        v___x_3227_ = v_cases_3221_;
                        v_isShared_3228_ = v_isSharedCheck_3264_;
                        state = 32;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_alts_3225_);
                        crate::leanh::lean_inc(v_discr_3224_);
                        crate::leanh::lean_inc(v_resultType_3223_);
                        crate::leanh::lean_inc(v_typeName_3222_);
                        crate::leanh::lean_dec(v_cases_3221_);
                        v___x_3227_ = crate::leanh::lean_box(0);
                        v_isShared_3228_ = v_isSharedCheck_3264_;
                        state = 32;
                        continue;
                    }
                }
                _ => {
                    v___x_3265_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3265_, 0, v_code_3015_);
                    return v___x_3265_;
                }
            },
            1 => {
                if v___y_3025_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_3015_);
                    v___x_3026_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3026_, 0, v___y_3024_);
                    crate::leanh::lean_ctor_set(v___x_3026_, 1, v___y_3023_);
                    v___x_3027_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3027_, 0, v___x_3026_);
                    return v___x_3027_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3024_);
                    crate::leanh::lean_dec_ref(v___y_3023_);
                    v___x_3028_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3028_, 0, v_code_3015_);
                    return v___x_3028_;
                }
            }
            2 => {
                if v___y_3032_ == 0 {
                    crate::leanh::lean_dec_ref(v_code_3015_);
                    v___x_3033_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3033_, 0, v___y_3031_);
                    crate::leanh::lean_ctor_set(v___x_3033_, 1, v___y_3030_);
                    v___x_3034_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3034_, 0, v___x_3033_);
                    return v___x_3034_;
                } else {
                    crate::leanh::lean_dec_ref(v___y_3031_);
                    crate::leanh::lean_dec_ref(v___y_3030_);
                    v___x_3035_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3035_, 0, v_code_3015_);
                    return v___x_3035_;
                }
            }
            3 => {
                v_params_3044_ = crate::leanh::lean_ctor_get(v_decl_3037_, 2);
                crate::leanh::lean_inc_ref(v_params_3044_);
                v_type_3045_ = crate::leanh::lean_ctor_get(v_decl_3037_, 3);
                crate::leanh::lean_inc_ref(v_type_3045_);
                v_value_3046_ = crate::leanh::lean_ctor_get(v_decl_3037_, 4);
                crate::leanh::lean_inc_ref(v_value_3046_);
                v___x_3047_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                    v_value_3046_,
                    v___y_3039_,
                    v___y_3040_,
                    v___y_3041_,
                    v___y_3042_,
                    v___y_3043_,
                );
                if crate::leanh::lean_obj_tag(v___x_3047_) == 0 {
                    v_a_3048_ = crate::leanh::lean_ctor_get(v___x_3047_, 0);
                    crate::leanh::lean_inc(v_a_3048_);
                    crate::leanh::lean_dec_ref_known(v___x_3047_, 1);
                    v___x_3049_ = 0;
                    v___x_3050_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3049_, v_decl_3037_, v_type_3045_, v_params_3044_, v_a_3048_, v___y_3041_);
                    if crate::leanh::lean_obj_tag(v___x_3050_) == 0 {
                        v_a_3051_ = crate::leanh::lean_ctor_get(v___x_3050_, 0);
                        crate::leanh::lean_inc(v_a_3051_);
                        crate::leanh::lean_dec_ref_known(v___x_3050_, 1);
                        v___x_3052_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                            v_k_3038_,
                            v___y_3039_,
                            v___y_3040_,
                            v___y_3041_,
                            v___y_3042_,
                            v___y_3043_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3052_) == 0 {
                            match crate::leanh::lean_obj_tag(v_code_3015_) {
                                1 => {
                                    v_a_3053_ = crate::leanh::lean_ctor_get(v___x_3052_, 0);
                                    crate::leanh::lean_inc(v_a_3053_);
                                    crate::leanh::lean_dec_ref_known(v___x_3052_, 1);
                                    v_decl_3054_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                                    v_k_3055_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                                    v___x_3056_ = lean_ptr_addr(v_k_3055_);
                                    v___x_3057_ = lean_ptr_addr(v_a_3053_);
                                    v___x_3058_ = lean_usize_dec_eq(v___x_3056_, v___x_3057_);
                                    if v___x_3058_ == 0 {
                                        v___y_3023_ = v_a_3053_;
                                        v___y_3024_ = v_a_3051_;
                                        v___y_3025_ = v___x_3058_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v___x_3059_ = lean_ptr_addr(v_decl_3054_);
                                        v___x_3060_ = lean_ptr_addr(v_a_3051_);
                                        v___x_3061_ = lean_usize_dec_eq(v___x_3059_, v___x_3060_);
                                        v___y_3023_ = v_a_3053_;
                                        v___y_3024_ = v_a_3051_;
                                        v___y_3025_ = v___x_3061_;
                                        state = 1;
                                        continue;
                                    }
                                }
                                2 => {
                                    v_a_3062_ = crate::leanh::lean_ctor_get(v___x_3052_, 0);
                                    crate::leanh::lean_inc(v_a_3062_);
                                    crate::leanh::lean_dec_ref_known(v___x_3052_, 1);
                                    v_decl_3063_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                                    v_k_3064_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                                    v___x_3065_ = lean_ptr_addr(v_k_3064_);
                                    v___x_3066_ = lean_ptr_addr(v_a_3062_);
                                    v___x_3067_ = lean_usize_dec_eq(v___x_3065_, v___x_3066_);
                                    if v___x_3067_ == 0 {
                                        v___y_3030_ = v_a_3062_;
                                        v___y_3031_ = v_a_3051_;
                                        v___y_3032_ = v___x_3067_;
                                        state = 2;
                                        continue;
                                    } else {
                                        v___x_3068_ = lean_ptr_addr(v_decl_3063_);
                                        v___x_3069_ = lean_ptr_addr(v_a_3051_);
                                        v___x_3070_ = lean_usize_dec_eq(v___x_3068_, v___x_3069_);
                                        v___y_3030_ = v_a_3062_;
                                        v___y_3031_ = v_a_3051_;
                                        v___y_3032_ = v___x_3070_;
                                        state = 2;
                                        continue;
                                    }
                                }
                                _ => {
                                    crate::leanh::lean_dec(v_a_3051_);
                                    crate::leanh::lean_dec_ref(v_code_3015_);
                                    v_isSharedCheck_3079_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3052_)) as u8;
                                    if v_isSharedCheck_3079_ == 0 {
                                        v_unused_3080_ =
                                            crate::leanh::lean_ctor_get(v___x_3052_, 0);
                                        crate::leanh::lean_dec(v_unused_3080_);
                                        v___x_3072_ = v___x_3052_;
                                        v_isShared_3073_ = v_isSharedCheck_3079_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v___x_3052_);
                                        v___x_3072_ = crate::leanh::lean_box(0);
                                        v_isShared_3073_ = v_isSharedCheck_3079_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3051_);
                            crate::leanh::lean_dec_ref(v_code_3015_);
                            return v___x_3052_;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_k_3038_);
                        crate::leanh::lean_dec_ref(v_code_3015_);
                        v_a_3081_ = crate::leanh::lean_ctor_get(v___x_3050_, 0);
                        v_isSharedCheck_3088_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3050_)) as u8;
                        if v_isSharedCheck_3088_ == 0 {
                            v___x_3083_ = v___x_3050_;
                            v_isShared_3084_ = v_isSharedCheck_3088_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3081_);
                            crate::leanh::lean_dec(v___x_3050_);
                            v___x_3083_ = crate::leanh::lean_box(0);
                            v_isShared_3084_ = v_isSharedCheck_3088_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_type_3045_);
                    crate::leanh::lean_dec_ref(v_params_3044_);
                    crate::leanh::lean_dec_ref(v_k_3038_);
                    crate::leanh::lean_dec_ref(v_decl_3037_);
                    crate::leanh::lean_dec_ref(v_code_3015_);
                    return v___x_3047_;
                }
            }
            4 => {
                v___x_3074_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3_once
                    ),
                    _init_l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__3,
                );
                v___x_3075_ =
                    l_panic___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(v___x_3074_);
                if v_isShared_3073_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3072_, 0, v___x_3075_);
                    v___x_3077_ = v___x_3072_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3078_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3078_, 0, v___x_3075_);
                    v___x_3077_ = v_reuseFailAlloc_3078_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3077_;
            }
            6 => {
                if v_isShared_3084_ == 0 {
                    v___x_3086_ = v___x_3083_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3087_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3087_, 0, v_a_3081_);
                    v___x_3086_ = v_reuseFailAlloc_3087_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3086_;
            }
            8 => {
                v_declName_3097_ = crate::leanh::lean_ctor_get(v_a_3016_, 0);
                v_auxDeclName_3098_ = crate::leanh::lean_ctor_get(v_a_3016_, 1);
                v_paramMask_3099_ = crate::leanh::lean_ctor_get(v_a_3016_, 2);
                v___x_3100_ = lean_name_eq(v_declName_3092_, v_declName_3097_);
                crate::leanh::lean_dec(v_declName_3092_);
                if v___x_3100_ == 0 {
                    crate::leanh::lean_del_object(v___x_3095_);
                    crate::leanh::lean_dec_ref(v_args_3093_);
                    crate::leanh::lean_inc_ref(v_k_3091_);
                    v___x_3101_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                        v_k_3091_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3101_) == 0 {
                        v_a_3102_ = crate::leanh::lean_ctor_get(v___x_3101_, 0);
                        v_isSharedCheck_3128_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3101_)) as u8;
                        if v_isSharedCheck_3128_ == 0 {
                            v___x_3104_ = v___x_3101_;
                            v_isShared_3105_ = v_isSharedCheck_3128_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3102_);
                            crate::leanh::lean_dec(v___x_3101_);
                            v___x_3104_ = crate::leanh::lean_box(0);
                            v_isShared_3105_ = v_isSharedCheck_3128_;
                            state = 9;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_code_3015_, 2);
                        return v___x_3101_;
                    }
                } else {
                    v___x_3129_ = lean_array_get_size(v_args_3093_);
                    v___x_3130_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_3131_ = l_Lean_Compiler_LCNF_ReduceArity_reduce___closed__4;
                    v___x_3132_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_3093_, v___x_3129_, v_paramMask_3099_, v___x_3130_, v___x_3131_);
                    crate::leanh::lean_dec_ref(v_args_3093_);
                    if crate::leanh::lean_obj_tag(v___x_3132_) == 0 {
                        v_a_3133_ = crate::leanh::lean_ctor_get(v___x_3132_, 0);
                        crate::leanh::lean_inc(v_a_3133_);
                        crate::leanh::lean_dec_ref_known(v___x_3132_, 1);
                        v___x_3134_ = 0;
                        v___x_3135_ = crate::leanh::lean_box(0);
                        crate::leanh::lean_inc(v_auxDeclName_3098_);
                        if v_isShared_3096_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3095_, 2, v_a_3133_);
                            crate::leanh::lean_ctor_set(v___x_3095_, 1, v___x_3135_);
                            crate::leanh::lean_ctor_set(v___x_3095_, 0, v_auxDeclName_3098_);
                            v___x_3137_ = v___x_3095_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_3177_ =
                                crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3177_,
                                0,
                                v_auxDeclName_3098_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 1, v___x_3135_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3177_, 2, v_a_3133_);
                            v___x_3137_ = v_reuseFailAlloc_3177_;
                            state = 15;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3095_);
                        crate::leanh::lean_dec_ref_known(v_code_3015_, 2);
                        v_a_3178_ = crate::leanh::lean_ctor_get(v___x_3132_, 0);
                        v_isSharedCheck_3185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3132_)) as u8;
                        if v_isSharedCheck_3185_ == 0 {
                            v___x_3180_ = v___x_3132_;
                            v_isShared_3181_ = v_isSharedCheck_3185_;
                            state = 24;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3178_);
                            crate::leanh::lean_dec(v___x_3132_);
                            v___x_3180_ = crate::leanh::lean_box(0);
                            v_isShared_3181_ = v_isSharedCheck_3185_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            9 => {
                v___x_3123_ = lean_ptr_addr(v_k_3091_);
                v___x_3124_ = lean_ptr_addr(v_a_3102_);
                v___x_3125_ = lean_usize_dec_eq(v___x_3123_, v___x_3124_);
                if v___x_3125_ == 0 {
                    v___y_3107_ = v___x_3125_;
                    state = 10;
                    continue;
                } else {
                    v___x_3126_ = lean_ptr_addr(v_decl_3089_);
                    v___x_3127_ = lean_usize_dec_eq(v___x_3126_, v___x_3126_);
                    v___y_3107_ = v___x_3127_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_3107_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_3089_);
                    v_isSharedCheck_3117_ = (!crate::leanh::lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3117_ == 0 {
                        v_unused_3118_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                        crate::leanh::lean_dec(v_unused_3118_);
                        v_unused_3119_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                        crate::leanh::lean_dec(v_unused_3119_);
                        v___x_3109_ = v_code_3015_;
                        v_isShared_3110_ = v_isSharedCheck_3117_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_3015_);
                        v___x_3109_ = crate::leanh::lean_box(0);
                        v_isShared_3110_ = v_isSharedCheck_3117_;
                        state = 11;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3102_);
                    if v_isShared_3105_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3104_, 0, v_code_3015_);
                        v___x_3121_ = v___x_3104_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3122_, 0, v_code_3015_);
                        v___x_3121_ = v_reuseFailAlloc_3122_;
                        state = 14;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_3110_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3109_, 1, v_a_3102_);
                    v___x_3112_ = v___x_3109_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3116_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 0, v_decl_3089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3116_, 1, v_a_3102_);
                    v___x_3112_ = v_reuseFailAlloc_3116_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3105_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3104_, 0, v___x_3112_);
                    v___x_3114_ = v___x_3104_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3115_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3115_, 0, v___x_3112_);
                    v___x_3114_ = v_reuseFailAlloc_3115_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3114_;
            }
            14 => {
                return v___x_3121_;
            }
            15 => {
                crate::leanh::lean_inc_ref(v_decl_3089_);
                v___x_3138_ = l_Lean_Compiler_LCNF_LetDecl_updateValue___redArg(
                    v___x_3134_,
                    v_decl_3089_,
                    v___x_3137_,
                    v_a_3018_,
                );
                if crate::leanh::lean_obj_tag(v___x_3138_) == 0 {
                    v_a_3139_ = crate::leanh::lean_ctor_get(v___x_3138_, 0);
                    crate::leanh::lean_inc(v_a_3139_);
                    crate::leanh::lean_dec_ref_known(v___x_3138_, 1);
                    crate::leanh::lean_inc_ref(v_k_3091_);
                    v___x_3140_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                        v_k_3091_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3140_) == 0 {
                        v_a_3141_ = crate::leanh::lean_ctor_get(v___x_3140_, 0);
                        v_isSharedCheck_3168_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3140_)) as u8;
                        if v_isSharedCheck_3168_ == 0 {
                            v___x_3143_ = v___x_3140_;
                            v_isShared_3144_ = v_isSharedCheck_3168_;
                            state = 16;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3141_);
                            crate::leanh::lean_dec(v___x_3140_);
                            v___x_3143_ = crate::leanh::lean_box(0);
                            v_isShared_3144_ = v_isSharedCheck_3168_;
                            state = 16;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3139_);
                        crate::leanh::lean_dec_ref_known(v_code_3015_, 2);
                        return v___x_3140_;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v_code_3015_, 2);
                    v_a_3169_ = crate::leanh::lean_ctor_get(v___x_3138_, 0);
                    v_isSharedCheck_3176_ = (!crate::leanh::lean_is_exclusive(v___x_3138_)) as u8;
                    if v_isSharedCheck_3176_ == 0 {
                        v___x_3171_ = v___x_3138_;
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 22;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3169_);
                        crate::leanh::lean_dec(v___x_3138_);
                        v___x_3171_ = crate::leanh::lean_box(0);
                        v_isShared_3172_ = v_isSharedCheck_3176_;
                        state = 22;
                        continue;
                    }
                }
            }
            16 => {
                v___x_3162_ = lean_ptr_addr(v_k_3091_);
                v___x_3163_ = lean_ptr_addr(v_a_3141_);
                v___x_3164_ = lean_usize_dec_eq(v___x_3162_, v___x_3163_);
                if v___x_3164_ == 0 {
                    v___y_3146_ = v___x_3164_;
                    state = 17;
                    continue;
                } else {
                    v___x_3165_ = lean_ptr_addr(v_decl_3089_);
                    v___x_3166_ = lean_ptr_addr(v_a_3139_);
                    v___x_3167_ = lean_usize_dec_eq(v___x_3165_, v___x_3166_);
                    v___y_3146_ = v___x_3167_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                if v___y_3146_ == 0 {
                    v_isSharedCheck_3156_ = (!crate::leanh::lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3156_ == 0 {
                        v_unused_3157_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                        crate::leanh::lean_dec(v_unused_3157_);
                        v_unused_3158_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                        crate::leanh::lean_dec(v_unused_3158_);
                        v___x_3148_ = v_code_3015_;
                        v_isShared_3149_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_3015_);
                        v___x_3148_ = crate::leanh::lean_box(0);
                        v_isShared_3149_ = v_isSharedCheck_3156_;
                        state = 18;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3141_);
                    crate::leanh::lean_dec(v_a_3139_);
                    if v_isShared_3144_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3143_, 0, v_code_3015_);
                        v___x_3160_ = v___x_3143_;
                        state = 21;
                        continue;
                    } else {
                        v_reuseFailAlloc_3161_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3161_, 0, v_code_3015_);
                        v___x_3160_ = v_reuseFailAlloc_3161_;
                        state = 21;
                        continue;
                    }
                }
            }
            18 => {
                if v_isShared_3149_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3148_, 1, v_a_3141_);
                    crate::leanh::lean_ctor_set(v___x_3148_, 0, v_a_3139_);
                    v___x_3151_ = v___x_3148_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3139_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3155_, 1, v_a_3141_);
                    v___x_3151_ = v_reuseFailAlloc_3155_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_3144_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3143_, 0, v___x_3151_);
                    v___x_3153_ = v___x_3143_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3154_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3154_, 0, v___x_3151_);
                    v___x_3153_ = v_reuseFailAlloc_3154_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3153_;
            }
            21 => {
                return v___x_3160_;
            }
            22 => {
                if v_isShared_3172_ == 0 {
                    v___x_3174_ = v___x_3171_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3175_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3175_, 0, v_a_3169_);
                    v___x_3174_ = v_reuseFailAlloc_3175_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_3174_;
            }
            24 => {
                if v_isShared_3181_ == 0 {
                    v___x_3183_ = v___x_3180_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
                    v___x_3183_ = v_reuseFailAlloc_3184_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_3183_;
            }
            26 => {
                v___x_3211_ = lean_ptr_addr(v_k_3188_);
                v___x_3212_ = lean_ptr_addr(v_a_3190_);
                v___x_3213_ = lean_usize_dec_eq(v___x_3211_, v___x_3212_);
                if v___x_3213_ == 0 {
                    v___y_3195_ = v___x_3213_;
                    state = 27;
                    continue;
                } else {
                    v___x_3214_ = lean_ptr_addr(v_decl_3089_);
                    v___x_3215_ = lean_usize_dec_eq(v___x_3214_, v___x_3214_);
                    v___y_3195_ = v___x_3215_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                if v___y_3195_ == 0 {
                    crate::leanh::lean_inc_ref(v_decl_3089_);
                    v_isSharedCheck_3205_ = (!crate::leanh::lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3205_ == 0 {
                        v_unused_3206_ = crate::leanh::lean_ctor_get(v_code_3015_, 1);
                        crate::leanh::lean_dec(v_unused_3206_);
                        v_unused_3207_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                        crate::leanh::lean_dec(v_unused_3207_);
                        v___x_3197_ = v_code_3015_;
                        v_isShared_3198_ = v_isSharedCheck_3205_;
                        state = 28;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_3015_);
                        v___x_3197_ = crate::leanh::lean_box(0);
                        v_isShared_3198_ = v_isSharedCheck_3205_;
                        state = 28;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3190_);
                    if v_isShared_3193_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3192_, 0, v_code_3015_);
                        v___x_3209_ = v___x_3192_;
                        state = 31;
                        continue;
                    } else {
                        v_reuseFailAlloc_3210_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3210_, 0, v_code_3015_);
                        v___x_3209_ = v_reuseFailAlloc_3210_;
                        state = 31;
                        continue;
                    }
                }
            }
            28 => {
                if v_isShared_3198_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3197_, 1, v_a_3190_);
                    v___x_3200_ = v___x_3197_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_decl_3089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 1, v_a_3190_);
                    v___x_3200_ = v_reuseFailAlloc_3204_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                if v_isShared_3193_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3192_, 0, v___x_3200_);
                    v___x_3202_ = v___x_3192_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3203_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3203_, 0, v___x_3200_);
                    v___x_3202_ = v_reuseFailAlloc_3203_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                return v___x_3202_;
            }
            31 => {
                return v___x_3209_;
            }
            32 => {
                v___x_3229_ = crate::leanh::lean_unsigned_to_nat(0);
                crate::leanh::lean_inc_ref(v_alts_3225_);
                v___x_3230_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v___x_3229_, v_alts_3225_, v_a_3016_, v_a_3017_, v_a_3018_, v_a_3019_, v_a_3020_);
                if crate::leanh::lean_obj_tag(v___x_3230_) == 0 {
                    v_a_3231_ = crate::leanh::lean_ctor_get(v___x_3230_, 0);
                    v_isSharedCheck_3255_ = (!crate::leanh::lean_is_exclusive(v___x_3230_)) as u8;
                    if v_isSharedCheck_3255_ == 0 {
                        v___x_3233_ = v___x_3230_;
                        v_isShared_3234_ = v_isSharedCheck_3255_;
                        state = 33;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3231_);
                        crate::leanh::lean_dec(v___x_3230_);
                        v___x_3233_ = crate::leanh::lean_box(0);
                        v_isShared_3234_ = v_isSharedCheck_3255_;
                        state = 33;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3227_);
                    crate::leanh::lean_dec_ref(v_alts_3225_);
                    crate::leanh::lean_dec(v_discr_3224_);
                    crate::leanh::lean_dec_ref(v_resultType_3223_);
                    crate::leanh::lean_dec(v_typeName_3222_);
                    crate::leanh::lean_dec_ref_known(v_code_3015_, 1);
                    v_a_3256_ = crate::leanh::lean_ctor_get(v___x_3230_, 0);
                    v_isSharedCheck_3263_ = (!crate::leanh::lean_is_exclusive(v___x_3230_)) as u8;
                    if v_isSharedCheck_3263_ == 0 {
                        v___x_3258_ = v___x_3230_;
                        v_isShared_3259_ = v_isSharedCheck_3263_;
                        state = 39;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3256_);
                        crate::leanh::lean_dec(v___x_3230_);
                        v___x_3258_ = crate::leanh::lean_box(0);
                        v_isShared_3259_ = v_isSharedCheck_3263_;
                        state = 39;
                        continue;
                    }
                }
            }
            33 => {
                v___x_3235_ = lean_ptr_addr(v_alts_3225_);
                crate::leanh::lean_dec_ref(v_alts_3225_);
                v___x_3236_ = lean_ptr_addr(v_a_3231_);
                v___x_3237_ = lean_usize_dec_eq(v___x_3235_, v___x_3236_);
                if v___x_3237_ == 0 {
                    v_isSharedCheck_3250_ = (!crate::leanh::lean_is_exclusive(v_code_3015_)) as u8;
                    if v_isSharedCheck_3250_ == 0 {
                        v_unused_3251_ = crate::leanh::lean_ctor_get(v_code_3015_, 0);
                        crate::leanh::lean_dec(v_unused_3251_);
                        v___x_3239_ = v_code_3015_;
                        v_isShared_3240_ = v_isSharedCheck_3250_;
                        state = 34;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_code_3015_);
                        v___x_3239_ = crate::leanh::lean_box(0);
                        v_isShared_3240_ = v_isSharedCheck_3250_;
                        state = 34;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_3231_);
                    crate::leanh::lean_del_object(v___x_3227_);
                    crate::leanh::lean_dec(v_discr_3224_);
                    crate::leanh::lean_dec_ref(v_resultType_3223_);
                    crate::leanh::lean_dec(v_typeName_3222_);
                    if v_isShared_3234_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3233_, 0, v_code_3015_);
                        v___x_3253_ = v___x_3233_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3254_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3254_, 0, v_code_3015_);
                        v___x_3253_ = v_reuseFailAlloc_3254_;
                        state = 38;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_3228_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3227_, 3, v_a_3231_);
                    v___x_3242_ = v___x_3227_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3249_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 0, v_typeName_3222_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 1, v_resultType_3223_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 2, v_discr_3224_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3249_, 3, v_a_3231_);
                    v___x_3242_ = v_reuseFailAlloc_3249_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3240_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3239_, 0, v___x_3242_);
                    v___x_3244_ = v___x_3239_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3248_ = crate::leanh::lean_alloc_ctor(4, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3248_, 0, v___x_3242_);
                    v___x_3244_ = v_reuseFailAlloc_3248_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_3234_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3233_, 0, v___x_3244_);
                    v___x_3246_ = v___x_3233_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3247_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3247_, 0, v___x_3244_);
                    v___x_3246_ = v_reuseFailAlloc_3247_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3246_;
            }
            38 => {
                return v___x_3253_;
            }
            39 => {
                if v_isShared_3259_ == 0 {
                    v___x_3261_ = v___x_3258_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3262_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_a_3256_);
                    v___x_3261_ = v_reuseFailAlloc_3262_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3261_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(
    mut v_i_3266_: *mut crate::leanh::LeanObject,
    mut v_as_3267_: *mut crate::leanh::LeanObject,
    mut v___y_3268_: *mut crate::leanh::LeanObject,
    mut v___y_3269_: *mut crate::leanh::LeanObject,
    mut v___y_3270_: *mut crate::leanh::LeanObject,
    mut v___y_3271_: *mut crate::leanh::LeanObject,
    mut v___y_3272_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: u8 = 0;
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3283_: usize = 0;
    let mut v___x_3284_: usize = 0;
    let mut v___x_3285_: u8 = 0;
    let mut v___x_3286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3296_: u8 = 0;
    let mut v___x_3298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3300_: u8 = 0;
    let mut v_code_3301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3274_ = lean_array_get_size(v_as_3267_);
                v___x_3275_ = lean_nat_dec_lt(v_i_3266_, v___x_3274_);
                if v___x_3275_ == 0 {
                    crate::leanh::lean_dec(v_i_3266_);
                    v___x_3276_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3276_, 0, v_as_3267_);
                    return v___x_3276_;
                } else {
                    v_a_3277_ = lean_array_fget_borrowed(v_as_3267_, v_i_3266_);
                    match crate::leanh::lean_obj_tag(v_a_3277_) {
                        0 => {
                            v_code_3301_ = crate::leanh::lean_ctor_get(v_a_3277_, 2);
                            crate::leanh::lean_inc_ref(v_code_3301_);
                            v___y_3279_ = v_code_3301_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_code_3302_ = crate::leanh::lean_ctor_get(v_a_3277_, 1);
                            crate::leanh::lean_inc_ref(v_code_3302_);
                            v___y_3279_ = v_code_3302_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v_code_3303_ = crate::leanh::lean_ctor_get(v_a_3277_, 0);
                            crate::leanh::lean_inc_ref(v_code_3303_);
                            v___y_3279_ = v_code_3303_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3280_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
                    v___y_3279_,
                    v___y_3268_,
                    v___y_3269_,
                    v___y_3270_,
                    v___y_3271_,
                    v___y_3272_,
                );
                if crate::leanh::lean_obj_tag(v___x_3280_) == 0 {
                    v_a_3281_ = crate::leanh::lean_ctor_get(v___x_3280_, 0);
                    crate::leanh::lean_inc(v_a_3281_);
                    crate::leanh::lean_dec_ref_known(v___x_3280_, 1);
                    crate::leanh::lean_inc(v_a_3277_);
                    v___x_3282_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3277_, v_a_3281_);
                    v___x_3283_ = lean_ptr_addr(v_a_3277_);
                    v___x_3284_ = lean_ptr_addr(v___x_3282_);
                    v___x_3285_ = lean_usize_dec_eq(v___x_3283_, v___x_3284_);
                    if v___x_3285_ == 0 {
                        v___x_3286_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3287_ = lean_nat_add(v_i_3266_, v___x_3286_);
                        v___x_3288_ = lean_array_fset(v_as_3267_, v_i_3266_, v___x_3282_);
                        crate::leanh::lean_dec(v_i_3266_);
                        v_i_3266_ = v___x_3287_;
                        v_as_3267_ = v___x_3288_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v___x_3282_);
                        v___x_3290_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_3291_ = lean_nat_add(v_i_3266_, v___x_3290_);
                        crate::leanh::lean_dec(v_i_3266_);
                        v_i_3266_ = v___x_3291_;
                        state = 0;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_as_3267_);
                    crate::leanh::lean_dec(v_i_3266_);
                    v_a_3293_ = crate::leanh::lean_ctor_get(v___x_3280_, 0);
                    v_isSharedCheck_3300_ = (!crate::leanh::lean_is_exclusive(v___x_3280_)) as u8;
                    if v_isSharedCheck_3300_ == 0 {
                        v___x_3295_ = v___x_3280_;
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3293_);
                        crate::leanh::lean_dec(v___x_3280_);
                        v___x_3295_ = crate::leanh::lean_box(0);
                        v_isShared_3296_ = v_isSharedCheck_3300_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3296_ == 0 {
                    v___x_3298_ = v___x_3295_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3299_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
                    v___x_3298_ = v_reuseFailAlloc_3299_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2___boxed(
    mut v_i_3304_: *mut crate::leanh::LeanObject,
    mut v_as_3305_: *mut crate::leanh::LeanObject,
    mut v___y_3306_: *mut crate::leanh::LeanObject,
    mut v___y_3307_: *mut crate::leanh::LeanObject,
    mut v___y_3308_: *mut crate::leanh::LeanObject,
    mut v___y_3309_: *mut crate::leanh::LeanObject,
    mut v___y_3310_: *mut crate::leanh::LeanObject,
    mut v___y_3311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3312_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__2(v_i_3304_, v_as_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_, v___y_3310_);
    crate::leanh::lean_dec(v___y_3310_);
    crate::leanh::lean_dec_ref(v___y_3309_);
    crate::leanh::lean_dec(v___y_3308_);
    crate::leanh::lean_dec_ref(v___y_3307_);
    crate::leanh::lean_dec_ref(v___y_3306_);
    return v_res_3312_;
}
pub unsafe fn l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(
    mut v_code_3313_: *mut crate::leanh::LeanObject,
    mut v_a_3314_: *mut crate::leanh::LeanObject,
    mut v_a_3315_: *mut crate::leanh::LeanObject,
    mut v_a_3316_: *mut crate::leanh::LeanObject,
    mut v_a_3317_: *mut crate::leanh::LeanObject,
    mut v_a_3318_: *mut crate::leanh::LeanObject,
    mut v_a_3319_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3320_ = l_Lean_Compiler_LCNF_ReduceArity_reduce(
        v_code_3313_,
        v_a_3314_,
        v_a_3315_,
        v_a_3316_,
        v_a_3317_,
        v_a_3318_,
    );
    crate::leanh::lean_dec(v_a_3318_);
    crate::leanh::lean_dec_ref(v_a_3317_);
    crate::leanh::lean_dec(v_a_3316_);
    crate::leanh::lean_dec_ref(v_a_3315_);
    crate::leanh::lean_dec_ref(v_a_3314_);
    return v_res_3320_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(
    mut v_args_3321_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3322_: *mut crate::leanh::LeanObject,
    mut v___x_3323_: *mut crate::leanh::LeanObject,
    mut v_inst_3324_: *mut crate::leanh::LeanObject,
    mut v_R_3325_: *mut crate::leanh::LeanObject,
    mut v_a_3326_: *mut crate::leanh::LeanObject,
    mut v_b_3327_: *mut crate::leanh::LeanObject,
    mut v_c_3328_: *mut crate::leanh::LeanObject,
    mut v___y_3329_: *mut crate::leanh::LeanObject,
    mut v___y_3330_: *mut crate::leanh::LeanObject,
    mut v___y_3331_: *mut crate::leanh::LeanObject,
    mut v___y_3332_: *mut crate::leanh::LeanObject,
    mut v___y_3333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3335_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___redArg(v_args_3321_, v_upperBound_3322_, v___x_3323_, v_a_3326_, v_b_3327_);
    return v___x_3335_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(
    mut v_args_3336_: *mut crate::leanh::LeanObject,
    mut v_upperBound_3337_: *mut crate::leanh::LeanObject,
    mut v___x_3338_: *mut crate::leanh::LeanObject,
    mut v_inst_3339_: *mut crate::leanh::LeanObject,
    mut v_R_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_b_3342_: *mut crate::leanh::LeanObject,
    mut v_c_3343_: *mut crate::leanh::LeanObject,
    mut v___y_3344_: *mut crate::leanh::LeanObject,
    mut v___y_3345_: *mut crate::leanh::LeanObject,
    mut v___y_3346_: *mut crate::leanh::LeanObject,
    mut v___y_3347_: *mut crate::leanh::LeanObject,
    mut v___y_3348_: *mut crate::leanh::LeanObject,
    mut v___y_3349_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3350_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(
            v_args_3336_,
            v_upperBound_3337_,
            v___x_3338_,
            v_inst_3339_,
            v_R_3340_,
            v_a_3341_,
            v_b_3342_,
            v_c_3343_,
            v___y_3344_,
            v___y_3345_,
            v___y_3346_,
            v___y_3347_,
            v___y_3348_,
        );
    crate::leanh::lean_dec(v___y_3348_);
    crate::leanh::lean_dec_ref(v___y_3347_);
    crate::leanh::lean_dec(v___y_3346_);
    crate::leanh::lean_dec_ref(v___y_3345_);
    crate::leanh::lean_dec_ref(v___y_3344_);
    crate::leanh::lean_dec_ref(v___x_3338_);
    crate::leanh::lean_dec(v_upperBound_3337_);
    crate::leanh::lean_dec_ref(v_args_3336_);
    return v_res_3350_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(
    mut v_f_3351_: *mut crate::leanh::LeanObject,
    mut v_v_3352_: *mut crate::leanh::LeanObject,
    mut v___y_3353_: *mut crate::leanh::LeanObject,
    mut v___y_3354_: *mut crate::leanh::LeanObject,
    mut v___y_3355_: *mut crate::leanh::LeanObject,
    mut v___y_3356_: *mut crate::leanh::LeanObject,
    mut v___y_3357_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_code_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v___x_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3374_: u8 = 0;
    let mut v_a_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3378_: u8 = 0;
    let mut v___x_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3382_: u8 = 0;
    let mut v_isSharedCheck_3383_: u8 = 0;
    let mut v___x_3384_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_v_3352_) == 0 {
                    v_code_3359_ = crate::leanh::lean_ctor_get(v_v_3352_, 0);
                    v_isSharedCheck_3383_ = (!crate::leanh::lean_is_exclusive(v_v_3352_)) as u8;
                    if v_isSharedCheck_3383_ == 0 {
                        v___x_3361_ = v_v_3352_;
                        v_isShared_3362_ = v_isSharedCheck_3383_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_code_3359_);
                        crate::leanh::lean_dec(v_v_3352_);
                        v___x_3361_ = crate::leanh::lean_box(0);
                        v_isShared_3362_ = v_isSharedCheck_3383_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_3351_);
                    v___x_3384_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3384_, 0, v_v_3352_);
                    return v___x_3384_;
                }
            }
            1 => {
                crate::leanh::lean_inc(v___y_3357_);
                crate::leanh::lean_inc_ref(v___y_3356_);
                crate::leanh::lean_inc(v___y_3355_);
                crate::leanh::lean_inc_ref(v___y_3354_);
                crate::leanh::lean_inc_ref(v___y_3353_);
                v___x_3363_ = crate::leanh::lean_apply_7(
                    v_f_3351_,
                    v_code_3359_,
                    v___y_3353_,
                    v___y_3354_,
                    v___y_3355_,
                    v___y_3356_,
                    v___y_3357_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3363_) == 0 {
                    v_a_3364_ = crate::leanh::lean_ctor_get(v___x_3363_, 0);
                    v_isSharedCheck_3374_ = (!crate::leanh::lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3374_ == 0 {
                        v___x_3366_ = v___x_3363_;
                        v_isShared_3367_ = v_isSharedCheck_3374_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3364_);
                        crate::leanh::lean_dec(v___x_3363_);
                        v___x_3366_ = crate::leanh::lean_box(0);
                        v_isShared_3367_ = v_isSharedCheck_3374_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3361_);
                    v_a_3375_ = crate::leanh::lean_ctor_get(v___x_3363_, 0);
                    v_isSharedCheck_3382_ = (!crate::leanh::lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3382_ == 0 {
                        v___x_3377_ = v___x_3363_;
                        v_isShared_3378_ = v_isSharedCheck_3382_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3375_);
                        crate::leanh::lean_dec(v___x_3363_);
                        v___x_3377_ = crate::leanh::lean_box(0);
                        v_isShared_3378_ = v_isSharedCheck_3382_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3362_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3361_, 0, v_a_3364_);
                    v___x_3369_ = v___x_3361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3373_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3373_, 0, v_a_3364_);
                    v___x_3369_ = v_reuseFailAlloc_3373_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_3367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3366_, 0, v___x_3369_);
                    v___x_3371_ = v___x_3366_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3372_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3372_, 0, v___x_3369_);
                    v___x_3371_ = v_reuseFailAlloc_3372_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3371_;
            }
            5 => {
                if v_isShared_3378_ == 0 {
                    v___x_3380_ = v___x_3377_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3381_, 0, v_a_3375_);
                    v___x_3380_ = v_reuseFailAlloc_3381_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(
    mut v_f_3385_: *mut crate::leanh::LeanObject,
    mut v_v_3386_: *mut crate::leanh::LeanObject,
    mut v___y_3387_: *mut crate::leanh::LeanObject,
    mut v___y_3388_: *mut crate::leanh::LeanObject,
    mut v___y_3389_: *mut crate::leanh::LeanObject,
    mut v___y_3390_: *mut crate::leanh::LeanObject,
    mut v___y_3391_: *mut crate::leanh::LeanObject,
    mut v___y_3392_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3393_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_3385_, v_v_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
    crate::leanh::lean_dec(v___y_3391_);
    crate::leanh::lean_dec_ref(v___y_3390_);
    crate::leanh::lean_dec(v___y_3389_);
    crate::leanh::lean_dec_ref(v___y_3388_);
    crate::leanh::lean_dec_ref(v___y_3387_);
    return v_res_3393_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(
    mut v_pu_3394_: u8,
    mut v_f_3395_: *mut crate::leanh::LeanObject,
    mut v_v_3396_: *mut crate::leanh::LeanObject,
    mut v___y_3397_: *mut crate::leanh::LeanObject,
    mut v___y_3398_: *mut crate::leanh::LeanObject,
    mut v___y_3399_: *mut crate::leanh::LeanObject,
    mut v___y_3400_: *mut crate::leanh::LeanObject,
    mut v___y_3401_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3403_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v_f_3395_, v_v_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
    return v___x_3403_;
}
pub unsafe fn l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(
    mut v_pu_3404_: *mut crate::leanh::LeanObject,
    mut v_f_3405_: *mut crate::leanh::LeanObject,
    mut v_v_3406_: *mut crate::leanh::LeanObject,
    mut v___y_3407_: *mut crate::leanh::LeanObject,
    mut v___y_3408_: *mut crate::leanh::LeanObject,
    mut v___y_3409_: *mut crate::leanh::LeanObject,
    mut v___y_3410_: *mut crate::leanh::LeanObject,
    mut v___y_3411_: *mut crate::leanh::LeanObject,
    mut v___y_3412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_pu_boxed_3413_: u8 = 0;
    let mut v_res_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_pu_boxed_3413_ = (crate::leanh::lean_unbox(v_pu_3404_) as u8);
    v_res_3414_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2(v_pu_boxed_3413_, v_f_3405_, v_v_3406_, v___y_3407_, v___y_3408_, v___y_3409_, v___y_3410_, v___y_3411_);
    crate::leanh::lean_dec(v___y_3411_);
    crate::leanh::lean_dec_ref(v___y_3410_);
    crate::leanh::lean_dec(v___y_3409_);
    crate::leanh::lean_dec_ref(v___y_3408_);
    crate::leanh::lean_dec_ref(v___y_3407_);
    return v_res_3414_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3415_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_3415_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3416_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__0,
    );
    v___x_3417_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3417_, 0, v___x_3416_);
    return v___x_3417_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3418_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1_once
        ),
        _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__1,
    );
    v___x_3419_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3420_ = crate::leanh::lean_alloc_ctor(0, 10, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3420_, 0, v___x_3419_);
    crate::leanh::lean_ctor_set(v___x_3420_, 1, v___x_3419_);
    crate::leanh::lean_ctor_set(v___x_3420_, 2, v___x_3419_);
    crate::leanh::lean_ctor_set(v___x_3420_, 3, v___x_3419_);
    crate::leanh::lean_ctor_set(v___x_3420_, 4, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3420_, 5, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3420_, 6, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3420_, 7, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3420_, 8, v___x_3418_);
    crate::leanh::lean_ctor_set(v___x_3420_, 9, v___x_3418_);
    return v___x_3420_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3()
-> f64 {
    let mut v___x_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3422_: f64 = 0.0;
    v___x_3421_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3422_ = lean_float_of_nat(v___x_3421_);
    return v___x_3422_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(
    mut v_cls_3426_: *mut crate::leanh::LeanObject,
    mut v_msg_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
    mut v___y_3430_: *mut crate::leanh::LeanObject,
    mut v___y_3431_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_options_3433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3441_: u8 = 0;
    let mut v_env_3442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3446_: u8 = 0;
    let mut v___x_3447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_3449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_3454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3460_: u8 = 0;
    let mut v_tid_3461_: u64 = 0;
    let mut v_traces_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3465_: u8 = 0;
    let mut v___x_3466_: u8 = 0;
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: f64 = 0.0;
    let mut v___x_3473_: u8 = 0;
    let mut v___x_3474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3492_: u8 = 0;
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut v_isSharedCheck_3494_: u8 = 0;
    let mut v_unused_3495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3496_: u8 = 0;
    let mut v_a_3497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3500_: u8 = 0;
    let mut v___x_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3504_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_3433_ = crate::leanh::lean_ctor_get(v___y_3430_, 2);
                v_ref_3434_ = crate::leanh::lean_ctor_get(v___y_3430_, 5);
                v___x_3435_ = lean_st_ref_get(v___y_3431_);
                v___x_3436_ = lean_st_ref_get(v___y_3429_);
                v___x_3437_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_3428_);
                if crate::leanh::lean_obj_tag(v___x_3437_) == 0 {
                    v_a_3438_ = crate::leanh::lean_ctor_get(v___x_3437_, 0);
                    v_isSharedCheck_3496_ = (!crate::leanh::lean_is_exclusive(v___x_3437_)) as u8;
                    if v_isSharedCheck_3496_ == 0 {
                        v___x_3440_ = v___x_3437_;
                        v_isShared_3441_ = v_isSharedCheck_3496_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3438_);
                        crate::leanh::lean_dec(v___x_3437_);
                        v___x_3440_ = crate::leanh::lean_box(0);
                        v_isShared_3441_ = v_isSharedCheck_3496_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3436_);
                    crate::leanh::lean_dec(v___x_3435_);
                    crate::leanh::lean_dec_ref(v_msg_3427_);
                    crate::leanh::lean_dec(v_cls_3426_);
                    v_a_3497_ = crate::leanh::lean_ctor_get(v___x_3437_, 0);
                    v_isSharedCheck_3504_ = (!crate::leanh::lean_is_exclusive(v___x_3437_)) as u8;
                    if v_isSharedCheck_3504_ == 0 {
                        v___x_3499_ = v___x_3437_;
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3497_);
                        crate::leanh::lean_dec(v___x_3437_);
                        v___x_3499_ = crate::leanh::lean_box(0);
                        v_isShared_3500_ = v_isSharedCheck_3504_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_3442_ = crate::leanh::lean_ctor_get(v___x_3435_, 0);
                crate::leanh::lean_inc_ref(v_env_3442_);
                crate::leanh::lean_dec(v___x_3435_);
                v_lctx_3443_ = crate::leanh::lean_ctor_get(v___x_3436_, 0);
                v_isSharedCheck_3494_ = (!crate::leanh::lean_is_exclusive(v___x_3436_)) as u8;
                if v_isSharedCheck_3494_ == 0 {
                    v_unused_3495_ = crate::leanh::lean_ctor_get(v___x_3436_, 1);
                    crate::leanh::lean_dec(v_unused_3495_);
                    v___x_3445_ = v___x_3436_;
                    v_isShared_3446_ = v_isSharedCheck_3494_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_lctx_3443_);
                    crate::leanh::lean_dec(v___x_3436_);
                    v___x_3445_ = crate::leanh::lean_box(0);
                    v_isShared_3446_ = v_isSharedCheck_3494_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3447_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__2);
                v___x_3448_ = lean_st_ref_take(v___y_3431_);
                v_traceState_3449_ = crate::leanh::lean_ctor_get(v___x_3448_, 4);
                v_env_3450_ = crate::leanh::lean_ctor_get(v___x_3448_, 0);
                v_nextMacroScope_3451_ = crate::leanh::lean_ctor_get(v___x_3448_, 1);
                v_ngen_3452_ = crate::leanh::lean_ctor_get(v___x_3448_, 2);
                v_auxDeclNGen_3453_ = crate::leanh::lean_ctor_get(v___x_3448_, 3);
                v_cache_3454_ = crate::leanh::lean_ctor_get(v___x_3448_, 5);
                v_messages_3455_ = crate::leanh::lean_ctor_get(v___x_3448_, 6);
                v_infoState_3456_ = crate::leanh::lean_ctor_get(v___x_3448_, 7);
                v_snapshotTasks_3457_ = crate::leanh::lean_ctor_get(v___x_3448_, 8);
                v_isSharedCheck_3493_ = (!crate::leanh::lean_is_exclusive(v___x_3448_)) as u8;
                if v_isSharedCheck_3493_ == 0 {
                    v___x_3459_ = v___x_3448_;
                    v_isShared_3460_ = v_isSharedCheck_3493_;
                    state = 3;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snapshotTasks_3457_);
                    crate::leanh::lean_inc(v_infoState_3456_);
                    crate::leanh::lean_inc(v_messages_3455_);
                    crate::leanh::lean_inc(v_cache_3454_);
                    crate::leanh::lean_inc(v_traceState_3449_);
                    crate::leanh::lean_inc(v_auxDeclNGen_3453_);
                    crate::leanh::lean_inc(v_ngen_3452_);
                    crate::leanh::lean_inc(v_nextMacroScope_3451_);
                    crate::leanh::lean_inc(v_env_3450_);
                    crate::leanh::lean_dec(v___x_3448_);
                    v___x_3459_ = crate::leanh::lean_box(0);
                    v_isShared_3460_ = v_isSharedCheck_3493_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_3461_ = crate::leanh::lean_ctor_get_uint64(
                    v_traceState_3449_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                );
                v_traces_3462_ = crate::leanh::lean_ctor_get(v_traceState_3449_, 0);
                v_isSharedCheck_3492_ =
                    (!crate::leanh::lean_is_exclusive(v_traceState_3449_)) as u8;
                if v_isSharedCheck_3492_ == 0 {
                    v___x_3464_ = v_traceState_3449_;
                    v_isShared_3465_ = v_isSharedCheck_3492_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_traces_3462_);
                    crate::leanh::lean_dec(v_traceState_3449_);
                    v___x_3464_ = crate::leanh::lean_box(0);
                    v_isShared_3465_ = v_isSharedCheck_3492_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3466_ = (crate::leanh::lean_unbox(v_a_3438_) as u8);
                crate::leanh::lean_dec(v_a_3438_);
                v___x_3467_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_3443_, v___x_3466_);
                crate::leanh::lean_dec_ref(v_lctx_3443_);
                crate::leanh::lean_inc_ref(v_options_3433_);
                v___x_3468_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3468_, 0, v_env_3442_);
                crate::leanh::lean_ctor_set(v___x_3468_, 1, v___x_3447_);
                crate::leanh::lean_ctor_set(v___x_3468_, 2, v___x_3467_);
                crate::leanh::lean_ctor_set(v___x_3468_, 3, v_options_3433_);
                if v_isShared_3446_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3445_, 3);
                    crate::leanh::lean_ctor_set(v___x_3445_, 1, v_msg_3427_);
                    crate::leanh::lean_ctor_set(v___x_3445_, 0, v___x_3468_);
                    v___x_3470_ = v___x_3445_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3491_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3468_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3491_, 1, v_msg_3427_);
                    v___x_3470_ = v_reuseFailAlloc_3491_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3471_ = crate::leanh::lean_box(0);
                v___x_3472_ = crate::leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__3);
                v___x_3473_ = 0;
                v___x_3474_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__4;
                v___x_3475_ = crate::leanh::lean_alloc_ctor(0, 3, (17) as u32);
                crate::leanh::lean_ctor_set(v___x_3475_, 0, v_cls_3426_);
                crate::leanh::lean_ctor_set(v___x_3475_, 1, v___x_3471_);
                crate::leanh::lean_ctor_set(v___x_3475_, 2, v___x_3474_);
                crate::leanh::lean_ctor_set_float(
                    v___x_3475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___x_3472_,
                );
                crate::leanh::lean_ctor_set_float(
                    v___x_3475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_3472_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3475_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_3473_,
                );
                v___x_3476_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___closed__5;
                v___x_3477_ = crate::leanh::lean_alloc_ctor(9, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3477_, 0, v___x_3475_);
                crate::leanh::lean_ctor_set(v___x_3477_, 1, v___x_3470_);
                crate::leanh::lean_ctor_set(v___x_3477_, 2, v___x_3476_);
                crate::leanh::lean_inc(v_ref_3434_);
                v___x_3478_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3478_, 0, v_ref_3434_);
                crate::leanh::lean_ctor_set(v___x_3478_, 1, v___x_3477_);
                v___x_3479_ = l_Lean_PersistentArray_push___redArg(v_traces_3462_, v___x_3478_);
                if v_isShared_3465_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3464_, 0, v___x_3479_);
                    v___x_3481_ = v___x_3464_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3490_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3490_, 0, v___x_3479_);
                    crate::leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_3490_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                        v_tid_3461_,
                    );
                    v___x_3481_ = v_reuseFailAlloc_3490_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3460_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3459_, 4, v___x_3481_);
                    v___x_3483_ = v___x_3459_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3489_ = crate::leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 0, v_env_3450_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 1, v_nextMacroScope_3451_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 2, v_ngen_3452_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 3, v_auxDeclNGen_3453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 4, v___x_3481_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 5, v_cache_3454_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 6, v_messages_3455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 7, v_infoState_3456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3489_, 8, v_snapshotTasks_3457_);
                    v___x_3483_ = v_reuseFailAlloc_3489_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_3484_ = lean_st_ref_set(v___y_3431_, v___x_3483_);
                v___x_3485_ = crate::leanh::lean_box(0);
                if v_isShared_3441_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3440_, 0, v___x_3485_);
                    v___x_3487_ = v___x_3440_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3488_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3488_, 0, v___x_3485_);
                    v___x_3487_ = v_reuseFailAlloc_3488_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3487_;
            }
            9 => {
                if v_isShared_3500_ == 0 {
                    v___x_3502_ = v___x_3499_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3503_, 0, v_a_3497_);
                    v___x_3502_ = v_reuseFailAlloc_3503_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3502_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9___boxed(
    mut v_cls_3505_: *mut crate::leanh::LeanObject,
    mut v_msg_3506_: *mut crate::leanh::LeanObject,
    mut v___y_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3512_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(
        v_cls_3505_,
        v_msg_3506_,
        v___y_3507_,
        v___y_3508_,
        v___y_3509_,
        v___y_3510_,
    );
    crate::leanh::lean_dec(v___y_3510_);
    crate::leanh::lean_dec_ref(v___y_3509_);
    crate::leanh::lean_dec(v___y_3508_);
    crate::leanh::lean_dec_ref(v___y_3507_);
    return v_res_3512_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(
    mut v_x_3513_: *mut crate::leanh::LeanObject,
    mut v_x_3514_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_x_3514_) == 0 {
        crate::leanh::lean_inc(v_x_3513_);
        return v_x_3513_;
    } else {
        let mut v_key_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_tail_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_key_3515_ = crate::leanh::lean_ctor_get(v_x_3514_, 0);
        v_tail_3516_ = crate::leanh::lean_ctor_get(v_x_3514_, 2);
        v___x_3517_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_3513_, v_tail_3516_);
        crate::leanh::lean_inc(v_key_3515_);
        v___x_3518_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3518_, 0, v_key_3515_);
        crate::leanh::lean_ctor_set(v___x_3518_, 1, v___x_3517_);
        return v___x_3518_;
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10___boxed(
    mut v_x_3519_: *mut crate::leanh::LeanObject,
    mut v_x_3520_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3521_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_x_3519_, v_x_3520_);
    crate::leanh::lean_dec(v_x_3520_);
    crate::leanh::lean_dec(v_x_3519_);
    return v_res_3521_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(
    mut v_as_3522_: *mut crate::leanh::LeanObject,
    mut v_i_3523_: usize,
    mut v_stop_3524_: usize,
    mut v_b_3525_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3526_: u8 = 0;
    let mut v___x_3527_: usize = 0;
    let mut v___x_3528_: usize = 0;
    let mut v___x_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3526_ = lean_usize_dec_eq(v_i_3523_, v_stop_3524_);
                if v___x_3526_ == 0 {
                    v___x_3527_ = 1usize;
                    v___x_3528_ = lean_usize_sub(v_i_3523_, v___x_3527_);
                    v___x_3529_ = lean_array_uget_borrowed(v_as_3522_, v___x_3528_);
                    v___x_3530_ = l_Std_DHashMap_Internal_AssocList_foldrM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__10(v_b_3525_, v___x_3529_);
                    crate::leanh::lean_dec(v_b_3525_);
                    v_i_3523_ = v___x_3528_;
                    v_b_3525_ = v___x_3530_;
                    state = 0;
                    continue;
                } else {
                    return v_b_3525_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(
    mut v_as_3532_: *mut crate::leanh::LeanObject,
    mut v_i_3533_: *mut crate::leanh::LeanObject,
    mut v_stop_3534_: *mut crate::leanh::LeanObject,
    mut v_b_3535_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3536_: usize = 0;
    let mut v_stop_boxed_3537_: usize = 0;
    let mut v_res_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3536_ = crate::leanh::lean_unbox_usize(v_i_3533_);
    crate::leanh::lean_dec(v_i_3533_);
    v_stop_boxed_3537_ = crate::leanh::lean_unbox_usize(v_stop_3534_);
    crate::leanh::lean_dec(v_stop_3534_);
    v_res_3538_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_as_3532_, v_i_boxed_3536_, v_stop_boxed_3537_, v_b_3535_);
    crate::leanh::lean_dec_ref(v_as_3532_);
    return v_res_3538_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(
    mut v_m_3539_: *mut crate::leanh::LeanObject,
    mut v_a_3540_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: u64 = 0;
    let mut v___x_3544_: u64 = 0;
    let mut v___x_3545_: u64 = 0;
    let mut v_fold_3546_: u64 = 0;
    let mut v___x_3547_: u64 = 0;
    let mut v___x_3548_: u64 = 0;
    let mut v___x_3549_: u64 = 0;
    let mut v___x_3550_: usize = 0;
    let mut v___x_3551_: usize = 0;
    let mut v___x_3552_: usize = 0;
    let mut v___x_3553_: usize = 0;
    let mut v___x_3554_: usize = 0;
    let mut v___x_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: u8 = 0;
    v_buckets_3541_ = crate::leanh::lean_ctor_get(v_m_3539_, 1);
    v___x_3542_ = lean_array_get_size(v_buckets_3541_);
    v___x_3543_ = l_Lean_instHashableFVarId_hash(v_a_3540_);
    v___x_3544_ = 32u64;
    v___x_3545_ = lean_uint64_shift_right(v___x_3543_, v___x_3544_);
    v_fold_3546_ = lean_uint64_xor(v___x_3543_, v___x_3545_);
    v___x_3547_ = 16u64;
    v___x_3548_ = lean_uint64_shift_right(v_fold_3546_, v___x_3547_);
    v___x_3549_ = lean_uint64_xor(v_fold_3546_, v___x_3548_);
    v___x_3550_ = lean_uint64_to_usize(v___x_3549_);
    v___x_3551_ = lean_usize_of_nat(v___x_3542_);
    v___x_3552_ = 1usize;
    v___x_3553_ = lean_usize_sub(v___x_3551_, v___x_3552_);
    v___x_3554_ = lean_usize_land(v___x_3550_, v___x_3553_);
    v___x_3555_ = lean_array_uget_borrowed(v_buckets_3541_, v___x_3554_);
    v___x_3556_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Compiler_LCNF_FindUsed_visitFVar_spec__1_spec__1___redArg(v_a_3540_, v___x_3555_);
    return v___x_3556_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg___boxed(
    mut v_m_3557_: *mut crate::leanh::LeanObject,
    mut v_a_3558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3559_: u8 = 0;
    let mut v_r_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3559_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_3557_, v_a_3558_);
    crate::leanh::lean_dec(v_a_3558_);
    crate::leanh::lean_dec_ref(v_m_3557_);
    v_r_3560_ = crate::leanh::lean_box((v_res_3559_) as usize);
    return v_r_3560_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(
    mut v_a_3561_: *mut crate::leanh::LeanObject,
    mut v_as_3562_: *mut crate::leanh::LeanObject,
    mut v_i_3563_: usize,
    mut v_stop_3564_: usize,
    mut v_b_3565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3568_: usize = 0;
    let mut v___x_3569_: usize = 0;
    let mut v___x_3571_: u8 = 0;
    let mut v___x_3572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3574_: u8 = 0;
    let mut v___x_3575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3571_ = lean_usize_dec_eq(v_i_3563_, v_stop_3564_);
                if v___x_3571_ == 0 {
                    v___x_3572_ = lean_array_uget_borrowed(v_as_3562_, v_i_3563_);
                    v_fvarId_3573_ = crate::leanh::lean_ctor_get(v___x_3572_, 0);
                    v___x_3574_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3561_, v_fvarId_3573_);
                    if v___x_3574_ == 0 {
                        v___y_3567_ = v_b_3565_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_3572_);
                        v___x_3575_ = lean_array_push(v_b_3565_, v___x_3572_);
                        v___y_3567_ = v___x_3575_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3565_;
                }
            }
            1 => {
                v___x_3568_ = 1usize;
                v___x_3569_ = lean_usize_add(v_i_3563_, v___x_3568_);
                v_i_3563_ = v___x_3569_;
                v_b_3565_ = v___y_3567_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7___boxed(
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_as_3577_: *mut crate::leanh::LeanObject,
    mut v_i_3578_: *mut crate::leanh::LeanObject,
    mut v_stop_3579_: *mut crate::leanh::LeanObject,
    mut v_b_3580_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3581_: usize = 0;
    let mut v_stop_boxed_3582_: usize = 0;
    let mut v_res_3583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3581_ = crate::leanh::lean_unbox_usize(v_i_3578_);
    crate::leanh::lean_dec(v_i_3578_);
    v_stop_boxed_3582_ = crate::leanh::lean_unbox_usize(v_stop_3579_);
    crate::leanh::lean_dec(v_stop_3579_);
    v_res_3583_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_3576_, v_as_3577_, v_i_boxed_3581_, v_stop_boxed_3582_, v_b_3580_);
    crate::leanh::lean_dec_ref(v_as_3577_);
    crate::leanh::lean_dec_ref(v_a_3576_);
    return v_res_3583_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(
    mut v_a_3584_: *mut crate::leanh::LeanObject,
    mut v_as_3585_: *mut crate::leanh::LeanObject,
    mut v_i_3586_: usize,
    mut v_stop_3587_: usize,
    mut v_b_3588_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3591_: usize = 0;
    let mut v___x_3592_: usize = 0;
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3594_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: u8 = 0;
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3594_ = lean_usize_dec_eq(v_i_3586_, v_stop_3587_);
                if v___x_3594_ == 0 {
                    v___x_3595_ = lean_array_uget_borrowed(v_as_3585_, v_i_3586_);
                    v_fvarId_3596_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                    v___x_3597_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3584_, v_fvarId_3596_);
                    if v___x_3597_ == 0 {
                        v___y_3590_ = v_b_3588_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v___x_3595_);
                        v___x_3598_ = lean_array_push(v_b_3588_, v___x_3595_);
                        v___y_3590_ = v___x_3598_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3588_;
                }
            }
            1 => {
                v___x_3591_ = 1usize;
                v___x_3592_ = lean_usize_add(v_i_3586_, v___x_3591_);
                v___x_3593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6_spec__7(v_a_3584_, v_as_3585_, v___x_3592_, v_stop_3587_, v___y_3590_);
                return v___x_3593_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(
    mut v_a_3599_: *mut crate::leanh::LeanObject,
    mut v_as_3600_: *mut crate::leanh::LeanObject,
    mut v_i_3601_: *mut crate::leanh::LeanObject,
    mut v_stop_3602_: *mut crate::leanh::LeanObject,
    mut v_b_3603_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3604_: usize = 0;
    let mut v_stop_boxed_3605_: usize = 0;
    let mut v_res_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3604_ = crate::leanh::lean_unbox_usize(v_i_3601_);
    crate::leanh::lean_dec(v_i_3601_);
    v_stop_boxed_3605_ = crate::leanh::lean_unbox_usize(v_stop_3602_);
    crate::leanh::lean_dec(v_stop_3602_);
    v_res_3606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_3599_, v_as_3600_, v_i_boxed_3604_, v_stop_boxed_3605_, v_b_3603_);
    crate::leanh::lean_dec_ref(v_as_3600_);
    crate::leanh::lean_dec_ref(v_a_3599_);
    return v_res_3606_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(
    mut v_a_3607_: *mut crate::leanh::LeanObject,
    mut v_a_3608_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3620_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3607_) == 0 {
                    v___x_3609_ = l_List_reverse___redArg(v_a_3608_);
                    return v___x_3609_;
                } else {
                    v_head_3610_ = crate::leanh::lean_ctor_get(v_a_3607_, 0);
                    v_tail_3611_ = crate::leanh::lean_ctor_get(v_a_3607_, 1);
                    v_isSharedCheck_3620_ = (!crate::leanh::lean_is_exclusive(v_a_3607_)) as u8;
                    if v_isSharedCheck_3620_ == 0 {
                        v___x_3613_ = v_a_3607_;
                        v_isShared_3614_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3611_);
                        crate::leanh::lean_inc(v_head_3610_);
                        crate::leanh::lean_dec(v_a_3607_);
                        v___x_3613_ = crate::leanh::lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3620_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3615_ = l_Lean_MessageData_ofExpr(v_head_3610_);
                if v_isShared_3614_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3613_, 1, v_a_3608_);
                    crate::leanh::lean_ctor_set(v___x_3613_, 0, v___x_3615_);
                    v___x_3617_ = v___x_3613_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3619_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3619_, 0, v___x_3615_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3619_, 1, v_a_3608_);
                    v___x_3617_ = v_reuseFailAlloc_3619_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3607_ = v_tail_3611_;
                v_a_3608_ = v___x_3617_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(
    mut v_as_3621_: *mut crate::leanh::LeanObject,
    mut v_sz_3622_: usize,
    mut v_i_3623_: usize,
    mut v_b_3624_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: usize = 0;
    let mut v___x_3629_: usize = 0;
    let mut v___x_3631_: u8 = 0;
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3637_: u8 = 0;
    let mut v_array_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: u8 = 0;
    let mut v___x_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3648_: u8 = 0;
    let mut v_a_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3655_: u8 = 0;
    let mut v___x_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3665_: u8 = 0;
    let mut v_unused_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3669_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3631_ = lean_usize_dec_lt(v_i_3623_, v_sz_3622_);
                if v___x_3631_ == 0 {
                    v___x_3632_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3632_, 0, v_b_3624_);
                    return v___x_3632_;
                } else {
                    v_snd_3633_ = crate::leanh::lean_ctor_get(v_b_3624_, 1);
                    v_fst_3634_ = crate::leanh::lean_ctor_get(v_b_3624_, 0);
                    v_isSharedCheck_3669_ = (!crate::leanh::lean_is_exclusive(v_b_3624_)) as u8;
                    if v_isSharedCheck_3669_ == 0 {
                        v___x_3636_ = v_b_3624_;
                        v_isShared_3637_ = v_isSharedCheck_3669_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3633_);
                        crate::leanh::lean_inc(v_fst_3634_);
                        crate::leanh::lean_dec(v_b_3624_);
                        v___x_3636_ = crate::leanh::lean_box(0);
                        v_isShared_3637_ = v_isSharedCheck_3669_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3628_ = 1usize;
                v___x_3629_ = lean_usize_add(v_i_3623_, v___x_3628_);
                v_i_3623_ = v___x_3629_;
                v_b_3624_ = v_a_3627_;
                state = 0;
                continue;
            }
            2 => {
                v_array_3638_ = crate::leanh::lean_ctor_get(v_snd_3633_, 0);
                v_start_3639_ = crate::leanh::lean_ctor_get(v_snd_3633_, 1);
                v_stop_3640_ = crate::leanh::lean_ctor_get(v_snd_3633_, 2);
                v___x_3641_ = lean_nat_dec_lt(v_start_3639_, v_stop_3640_);
                if v___x_3641_ == 0 {
                    if v_isShared_3637_ == 0 {
                        v___x_3643_ = v___x_3636_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3645_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 0, v_fst_3634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3645_, 1, v_snd_3633_);
                        v___x_3643_ = v_reuseFailAlloc_3645_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc(v_stop_3640_);
                    crate::leanh::lean_inc(v_start_3639_);
                    crate::leanh::lean_inc_ref(v_array_3638_);
                    v_isSharedCheck_3665_ = (!crate::leanh::lean_is_exclusive(v_snd_3633_)) as u8;
                    if v_isSharedCheck_3665_ == 0 {
                        v_unused_3666_ = crate::leanh::lean_ctor_get(v_snd_3633_, 2);
                        crate::leanh::lean_dec(v_unused_3666_);
                        v_unused_3667_ = crate::leanh::lean_ctor_get(v_snd_3633_, 1);
                        crate::leanh::lean_dec(v_unused_3667_);
                        v_unused_3668_ = crate::leanh::lean_ctor_get(v_snd_3633_, 0);
                        crate::leanh::lean_dec(v_unused_3668_);
                        v___x_3647_ = v_snd_3633_;
                        v_isShared_3648_ = v_isSharedCheck_3665_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_snd_3633_);
                        v___x_3647_ = crate::leanh::lean_box(0);
                        v_isShared_3648_ = v_isSharedCheck_3665_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v___x_3644_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3644_, 0, v___x_3643_);
                return v___x_3644_;
            }
            4 => {
                v_a_3649_ = lean_array_uget_borrowed(v_as_3621_, v_i_3623_);
                v___x_3650_ = lean_array_fget(v_array_3638_, v_start_3639_);
                v___x_3651_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_3652_ = lean_nat_add(v_start_3639_, v___x_3651_);
                crate::leanh::lean_dec(v_start_3639_);
                if v_isShared_3648_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3647_, 1, v___x_3652_);
                    v___x_3654_ = v___x_3647_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3664_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 0, v_array_3638_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 1, v___x_3652_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3664_, 2, v_stop_3640_);
                    v___x_3654_ = v_reuseFailAlloc_3664_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3655_ = (crate::leanh::lean_unbox(v_a_3649_) as u8);
                if v___x_3655_ == 0 {
                    crate::leanh::lean_dec(v___x_3650_);
                    if v_isShared_3637_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3636_, 1, v___x_3654_);
                        v___x_3657_ = v___x_3636_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3658_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 0, v_fst_3634_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3658_, 1, v___x_3654_);
                        v___x_3657_ = v_reuseFailAlloc_3658_;
                        state = 6;
                        continue;
                    }
                } else {
                    v___x_3659_ = l_Lean_Compiler_LCNF_Param_toArg___redArg(v___x_3650_);
                    crate::leanh::lean_dec(v___x_3650_);
                    v___x_3660_ = lean_array_push(v_fst_3634_, v___x_3659_);
                    if v_isShared_3637_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3636_, 1, v___x_3654_);
                        crate::leanh::lean_ctor_set(v___x_3636_, 0, v___x_3660_);
                        v___x_3662_ = v___x_3636_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3663_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3660_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3663_, 1, v___x_3654_);
                        v___x_3662_ = v_reuseFailAlloc_3663_;
                        state = 7;
                        continue;
                    }
                }
            }
            6 => {
                v_a_3627_ = v___x_3657_;
                state = 1;
                continue;
            }
            7 => {
                v_a_3627_ = v___x_3662_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg___boxed(
    mut v_as_3670_: *mut crate::leanh::LeanObject,
    mut v_sz_3671_: *mut crate::leanh::LeanObject,
    mut v_i_3672_: *mut crate::leanh::LeanObject,
    mut v_b_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3675_: usize = 0;
    let mut v_i_boxed_3676_: usize = 0;
    let mut v_res_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3675_ = crate::leanh::lean_unbox_usize(v_sz_3671_);
    crate::leanh::lean_dec(v_sz_3671_);
    v_i_boxed_3676_ = crate::leanh::lean_unbox_usize(v_i_3672_);
    crate::leanh::lean_dec(v_i_3672_);
    v_res_3677_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_3670_, v_sz_boxed_3675_, v_i_boxed_3676_, v_b_3673_);
    crate::leanh::lean_dec_ref(v_as_3670_);
    return v_res_3677_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(
    mut v_sz_3678_: usize,
    mut v_i_3679_: usize,
    mut v_bs_3680_: *mut crate::leanh::LeanObject,
    mut v___y_3681_: u8,
    mut v___y_3682_: *mut crate::leanh::LeanObject,
    mut v___y_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3688_: u8 = 0;
    let mut v___x_3689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3690_: u8 = 0;
    let mut v_v_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: usize = 0;
    let mut v___x_3697_: usize = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3703_: u8 = 0;
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3707_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3688_ = lean_usize_dec_lt(v_i_3679_, v_sz_3678_);
                if v___x_3688_ == 0 {
                    v___x_3689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3689_, 0, v_bs_3680_);
                    return v___x_3689_;
                } else {
                    v___x_3690_ = 0;
                    v_v_3691_ = lean_array_uget_borrowed(v_bs_3680_, v_i_3679_);
                    crate::leanh::lean_inc(v_v_3691_);
                    v___x_3692_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
                        v___x_3690_,
                        v_v_3691_,
                        v___y_3681_,
                        v___y_3682_,
                        v___y_3683_,
                        v___y_3684_,
                        v___y_3685_,
                        v___y_3686_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3692_) == 0 {
                        v_a_3693_ = crate::leanh::lean_ctor_get(v___x_3692_, 0);
                        crate::leanh::lean_inc(v_a_3693_);
                        crate::leanh::lean_dec_ref_known(v___x_3692_, 1);
                        v___x_3694_ = crate::leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_3695_ = lean_array_uset(v_bs_3680_, v_i_3679_, v___x_3694_);
                        v___x_3696_ = 1usize;
                        v___x_3697_ = lean_usize_add(v_i_3679_, v___x_3696_);
                        v___x_3698_ = lean_array_uset(v_bs_x27_3695_, v_i_3679_, v_a_3693_);
                        v_i_3679_ = v___x_3697_;
                        v_bs_3680_ = v___x_3698_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_bs_3680_);
                        v_a_3700_ = crate::leanh::lean_ctor_get(v___x_3692_, 0);
                        v_isSharedCheck_3707_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3692_)) as u8;
                        if v_isSharedCheck_3707_ == 0 {
                            v___x_3702_ = v___x_3692_;
                            v_isShared_3703_ = v_isSharedCheck_3707_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3700_);
                            crate::leanh::lean_dec(v___x_3692_);
                            v___x_3702_ = crate::leanh::lean_box(0);
                            v_isShared_3703_ = v_isSharedCheck_3707_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3703_ == 0 {
                    v___x_3705_ = v___x_3702_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3706_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
                    v___x_3705_ = v_reuseFailAlloc_3706_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3705_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(
    mut v_sz_3708_: *mut crate::leanh::LeanObject,
    mut v_i_3709_: *mut crate::leanh::LeanObject,
    mut v_bs_3710_: *mut crate::leanh::LeanObject,
    mut v___y_3711_: *mut crate::leanh::LeanObject,
    mut v___y_3712_: *mut crate::leanh::LeanObject,
    mut v___y_3713_: *mut crate::leanh::LeanObject,
    mut v___y_3714_: *mut crate::leanh::LeanObject,
    mut v___y_3715_: *mut crate::leanh::LeanObject,
    mut v___y_3716_: *mut crate::leanh::LeanObject,
    mut v___y_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3718_: usize = 0;
    let mut v_i_boxed_3719_: usize = 0;
    let mut v___y_12534__boxed_3720_: u8 = 0;
    let mut v_res_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3718_ = crate::leanh::lean_unbox_usize(v_sz_3708_);
    crate::leanh::lean_dec(v_sz_3708_);
    v_i_boxed_3719_ = crate::leanh::lean_unbox_usize(v_i_3709_);
    crate::leanh::lean_dec(v_i_3709_);
    v___y_12534__boxed_3720_ = (crate::leanh::lean_unbox(v___y_3711_) as u8);
    v_res_3721_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v_sz_boxed_3718_, v_i_boxed_3719_, v_bs_3710_, v___y_12534__boxed_3720_, v___y_3712_, v___y_3713_, v___y_3714_, v___y_3715_, v___y_3716_);
    crate::leanh::lean_dec(v___y_3716_);
    crate::leanh::lean_dec_ref(v___y_3715_);
    crate::leanh::lean_dec(v___y_3714_);
    crate::leanh::lean_dec_ref(v___y_3713_);
    crate::leanh::lean_dec(v___y_3712_);
    return v_res_3721_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(
    mut v_a_3722_: *mut crate::leanh::LeanObject,
    mut v_a_3723_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_3725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3729_: u8 = 0;
    let mut v___x_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3735_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3722_) == 0 {
                    v___x_3724_ = l_List_reverse___redArg(v_a_3723_);
                    return v___x_3724_;
                } else {
                    v_head_3725_ = crate::leanh::lean_ctor_get(v_a_3722_, 0);
                    v_tail_3726_ = crate::leanh::lean_ctor_get(v_a_3722_, 1);
                    v_isSharedCheck_3735_ = (!crate::leanh::lean_is_exclusive(v_a_3722_)) as u8;
                    if v_isSharedCheck_3735_ == 0 {
                        v___x_3728_ = v_a_3722_;
                        v_isShared_3729_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3726_);
                        crate::leanh::lean_inc(v_head_3725_);
                        crate::leanh::lean_dec(v_a_3722_);
                        v___x_3728_ = crate::leanh::lean_box(0);
                        v_isShared_3729_ = v_isSharedCheck_3735_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3730_ = l_Lean_mkFVar(v_head_3725_);
                if v_isShared_3729_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3728_, 1, v_a_3723_);
                    crate::leanh::lean_ctor_set(v___x_3728_, 0, v___x_3730_);
                    v___x_3732_ = v___x_3728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3734_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 0, v___x_3730_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3734_, 1, v_a_3723_);
                    v___x_3732_ = v_reuseFailAlloc_3734_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_3722_ = v_tail_3726_;
                v_a_3723_ = v___x_3732_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_sz_3737_: usize,
    mut v_i_3738_: usize,
    mut v_bs_3739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3740_: u8 = 0;
    let mut v_v_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3745_: u8 = 0;
    let mut v___x_3746_: usize = 0;
    let mut v___x_3747_: usize = 0;
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3740_ = lean_usize_dec_lt(v_i_3738_, v_sz_3737_);
                if v___x_3740_ == 0 {
                    return v_bs_3739_;
                } else {
                    v_v_3741_ = lean_array_uget_borrowed(v_bs_3739_, v_i_3738_);
                    v_fvarId_3742_ = crate::leanh::lean_ctor_get(v_v_3741_, 0);
                    crate::leanh::lean_inc(v_fvarId_3742_);
                    v___x_3743_ = crate::leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_3744_ = lean_array_uset(v_bs_3739_, v_i_3738_, v___x_3743_);
                    v___x_3745_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3736_, v_fvarId_3742_);
                    crate::leanh::lean_dec(v_fvarId_3742_);
                    v___x_3746_ = 1usize;
                    v___x_3747_ = lean_usize_add(v_i_3738_, v___x_3746_);
                    v___x_3748_ = crate::leanh::lean_box((v___x_3745_) as usize);
                    v___x_3749_ = lean_array_uset(v_bs_x27_3744_, v_i_3738_, v___x_3748_);
                    v_i_3738_ = v___x_3747_;
                    v_bs_3739_ = v___x_3749_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1___boxed(
    mut v_a_3751_: *mut crate::leanh::LeanObject,
    mut v_sz_3752_: *mut crate::leanh::LeanObject,
    mut v_i_3753_: *mut crate::leanh::LeanObject,
    mut v_bs_3754_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3755_: usize = 0;
    let mut v_i_boxed_3756_: usize = 0;
    let mut v_res_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3755_ = crate::leanh::lean_unbox_usize(v_sz_3752_);
    crate::leanh::lean_dec(v_sz_3752_);
    v_i_boxed_3756_ = crate::leanh::lean_unbox_usize(v_i_3753_);
    crate::leanh::lean_dec(v_i_3753_);
    v_res_3757_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_3751_, v_sz_boxed_3755_, v_i_boxed_3756_, v_bs_3754_);
    crate::leanh::lean_dec_ref(v_a_3751_);
    return v_res_3757_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(
    mut v_a_3758_: *mut crate::leanh::LeanObject,
    mut v_sz_3759_: usize,
    mut v_i_3760_: usize,
    mut v_bs_3761_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3762_: u8 = 0;
    v___x_3762_ = lean_usize_dec_lt(v_i_3760_, v_sz_3759_);
    if v___x_3762_ == 0 {
        return v_bs_3761_;
    } else {
        let mut v_v_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_fvarId_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_bs_x27_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3767_: u8 = 0;
        let mut v___x_3768_: usize = 0;
        let mut v___x_3769_: usize = 0;
        let mut v___x_3770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_3763_ = lean_array_uget_borrowed(v_bs_3761_, v_i_3760_);
        v_fvarId_3764_ = crate::leanh::lean_ctor_get(v_v_3763_, 0);
        crate::leanh::lean_inc(v_fvarId_3764_);
        v___x_3765_ = crate::leanh::lean_unsigned_to_nat(0);
        v_bs_x27_3766_ = lean_array_uset(v_bs_3761_, v_i_3760_, v___x_3765_);
        v___x_3767_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3758_, v_fvarId_3764_);
        crate::leanh::lean_dec(v_fvarId_3764_);
        v___x_3768_ = 1usize;
        v___x_3769_ = lean_usize_add(v_i_3760_, v___x_3768_);
        v___x_3770_ = crate::leanh::lean_box((v___x_3767_) as usize);
        v___x_3771_ = lean_array_uset(v_bs_x27_3766_, v_i_3760_, v___x_3770_);
        v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1_spec__1(v_a_3758_, v_sz_3759_, v___x_3769_, v___x_3771_);
        return v___x_3772_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1___boxed(
    mut v_a_3773_: *mut crate::leanh::LeanObject,
    mut v_sz_3774_: *mut crate::leanh::LeanObject,
    mut v_i_3775_: *mut crate::leanh::LeanObject,
    mut v_bs_3776_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3777_: usize = 0;
    let mut v_i_boxed_3778_: usize = 0;
    let mut v_res_3779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3777_ = crate::leanh::lean_unbox_usize(v_sz_3774_);
    crate::leanh::lean_dec(v_sz_3774_);
    v_i_boxed_3778_ = crate::leanh::lean_unbox_usize(v_i_3775_);
    crate::leanh::lean_dec(v_i_3775_);
    v_res_3779_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_3773_, v_sz_boxed_3777_, v_i_boxed_3778_, v_bs_3776_);
    crate::leanh::lean_dec_ref(v_a_3773_);
    return v_res_3779_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(
    mut v_a_3780_: *mut crate::leanh::LeanObject,
    mut v_as_3781_: *mut crate::leanh::LeanObject,
    mut v_i_3782_: usize,
    mut v_stop_3783_: usize,
    mut v_b_3784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3787_: usize = 0;
    let mut v___x_3788_: usize = 0;
    let mut v___x_3790_: u8 = 0;
    let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: u8 = 0;
    let mut v___x_3794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3790_ = lean_usize_dec_eq(v_i_3782_, v_stop_3783_);
                if v___x_3790_ == 0 {
                    v___x_3791_ = lean_array_uget_borrowed(v_as_3781_, v_i_3782_);
                    v_fvarId_3792_ = crate::leanh::lean_ctor_get(v___x_3791_, 0);
                    v___x_3793_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_a_3780_, v_fvarId_3792_);
                    if v___x_3793_ == 0 {
                        crate::leanh::lean_inc(v___x_3791_);
                        v___x_3794_ = lean_array_push(v_b_3784_, v___x_3791_);
                        v___y_3786_ = v___x_3794_;
                        state = 1;
                        continue;
                    } else {
                        v___y_3786_ = v_b_3784_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_b_3784_;
                }
            }
            1 => {
                v___x_3787_ = 1usize;
                v___x_3788_ = lean_usize_add(v_i_3782_, v___x_3787_);
                v_i_3782_ = v___x_3788_;
                v_b_3784_ = v___y_3786_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5___boxed(
    mut v_a_3795_: *mut crate::leanh::LeanObject,
    mut v_as_3796_: *mut crate::leanh::LeanObject,
    mut v_i_3797_: *mut crate::leanh::LeanObject,
    mut v_stop_3798_: *mut crate::leanh::LeanObject,
    mut v_b_3799_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_3800_: usize = 0;
    let mut v_stop_boxed_3801_: usize = 0;
    let mut v_res_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_3800_ = crate::leanh::lean_unbox_usize(v_i_3797_);
    crate::leanh::lean_dec(v_i_3797_);
    v_stop_boxed_3801_ = crate::leanh::lean_unbox_usize(v_stop_3798_);
    crate::leanh::lean_dec(v_stop_3798_);
    v_res_3802_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_3795_, v_as_3796_, v_i_boxed_3800_, v_stop_boxed_3801_, v_b_3799_);
    crate::leanh::lean_dec_ref(v_as_3796_);
    crate::leanh::lean_dec_ref(v_a_3795_);
    return v_res_3802_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3803_ = crate::leanh::lean_box(0);
    v___x_3804_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3805_ = lean_mk_array(v___x_3804_, v___x_3803_);
    return v___x_3805_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3826_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
    v___x_3827_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__12;
    v___x_3828_ = l_Lean_Name_append(v___x_3827_, v___x_3826_);
    return v___x_3828_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3830_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__14;
    v___x_3831_ = l_Lean_stringToMessageData(v___x_3830_);
    return v___x_3831_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_reduceArity(
    mut v_decl_3832_: *mut crate::leanh::LeanObject,
    mut v_a_3833_: *mut crate::leanh::LeanObject,
    mut v_a_3834_: *mut crate::leanh::LeanObject,
    mut v_a_3835_: *mut crate::leanh::LeanObject,
    mut v_a_3836_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_value_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toSignature_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_recursive_3840_: u8 = 0;
    let mut v_inlineAttr_x3f_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_code_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3844_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3847_: u8 = 0;
    let mut v_size_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_name_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_levelParams_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_params_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_safe_3854_: u8 = 0;
    let mut v___x_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3857_: u8 = 0;
    let mut v___y_3859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3866_: usize = 0;
    let mut v___y_3867_: u8 = 0;
    let mut v___y_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3869_: u8 = 0;
    let mut v___y_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3871_: usize = 0;
    let mut v___y_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3894_: usize = 0;
    let mut v___x_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3900_: u8 = 0;
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3918_: u8 = 0;
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3926_: u8 = 0;
    let mut v_unused_3927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3931_: u8 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3935_: u8 = 0;
    let mut v_a_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3939_: u8 = 0;
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3943_: u8 = 0;
    let mut v_reuseFailAlloc_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3948_: u8 = 0;
    let mut v___x_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3952_: u8 = 0;
    let mut v_isSharedCheck_3953_: u8 = 0;
    let mut v_unused_3954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3958_: u8 = 0;
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3962_: u8 = 0;
    let mut v_a_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut v_a_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3974_: u8 = 0;
    let mut v___x_3976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3978_: u8 = 0;
    let mut v_reuseFailAlloc_3979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3983_: u8 = 0;
    let mut v___x_3985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3987_: u8 = 0;
    let mut v_a_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3991_: u8 = 0;
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3995_: u8 = 0;
    let mut v_a_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3999_: u8 = 0;
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4003_: u8 = 0;
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4010_: usize = 0;
    let mut v___y_4011_: u8 = 0;
    let mut v___y_4012_: usize = 0;
    let mut v___y_4013_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4015_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4017_: u8 = 0;
    let mut v___x_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4021_: u8 = 0;
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: usize = 0;
    let mut v___x_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4025_: usize = 0;
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4028_: u8 = 0;
    let mut v___y_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4033_: usize = 0;
    let mut v___x_4034_: usize = 0;
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4038_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4040_: u8 = 0;
    let mut v___x_4041_: u8 = 0;
    let mut v___x_4042_: usize = 0;
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4044_: usize = 0;
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4048_: u8 = 0;
    let mut v___y_4049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4060_: u8 = 0;
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4064_: u8 = 0;
    let mut v___y_4066_: u8 = 0;
    let mut v_options_4067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4068_: u8 = 0;
    let mut v_inheritedTraceOptions_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: u8 = 0;
    let mut v___x_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4079_: u8 = 0;
    let mut v___x_4080_: usize = 0;
    let mut v___x_4081_: usize = 0;
    let mut v___x_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4091_: u8 = 0;
    let mut v_isSharedCheck_4092_: u8 = 0;
    let mut v_isSharedCheck_4093_: u8 = 0;
    let mut v_a_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4097_: u8 = 0;
    let mut v___x_4099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4101_: u8 = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4111_: u8 = 0;
    let mut v_unused_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_value_3838_ = crate::leanh::lean_ctor_get(v_decl_3832_, 1);
                crate::leanh::lean_inc_ref(v_value_3838_);
                if crate::leanh::lean_obj_tag(v_value_3838_) == 0 {
                    v_toSignature_3839_ = crate::leanh::lean_ctor_get(v_decl_3832_, 0);
                    crate::leanh::lean_inc_ref(v_toSignature_3839_);
                    v_recursive_3840_ = crate::leanh::lean_ctor_get_uint8(
                        v_decl_3832_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    );
                    v_inlineAttr_x3f_3841_ = crate::leanh::lean_ctor_get(v_decl_3832_, 2);
                    v_code_3842_ = crate::leanh::lean_ctor_get(v_value_3838_, 0);
                    crate::leanh::lean_inc_ref(v_code_3842_);
                    crate::leanh::lean_inc_ref(v_decl_3832_);
                    v___x_3843_ = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(
                        v_decl_3832_,
                        v_a_3833_,
                        v_a_3834_,
                        v_a_3835_,
                        v_a_3836_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3843_) == 0 {
                        v_a_3844_ = crate::leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_4093_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_4093_ == 0 {
                            v___x_3846_ = v___x_3843_;
                            v_isShared_3847_ = v_isSharedCheck_4093_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3844_);
                            crate::leanh::lean_dec(v___x_3843_);
                            v___x_3846_ = crate::leanh::lean_box(0);
                            v_isShared_3847_ = v_isSharedCheck_4093_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_code_3842_);
                        crate::leanh::lean_dec_ref(v_toSignature_3839_);
                        crate::leanh::lean_dec_ref_known(v_value_3838_, 1);
                        crate::leanh::lean_dec_ref(v_decl_3832_);
                        v_a_4094_ = crate::leanh::lean_ctor_get(v___x_3843_, 0);
                        v_isSharedCheck_4101_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3843_)) as u8;
                        if v_isSharedCheck_4101_ == 0 {
                            v___x_4096_ = v___x_3843_;
                            v_isShared_4097_ = v_isSharedCheck_4101_;
                            state = 34;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4094_);
                            crate::leanh::lean_dec(v___x_3843_);
                            v___x_4096_ = crate::leanh::lean_box(0);
                            v_isShared_4097_ = v_isSharedCheck_4101_;
                            state = 34;
                            continue;
                        }
                    }
                } else {
                    v_isSharedCheck_4111_ = (!crate::leanh::lean_is_exclusive(v_value_3838_)) as u8;
                    if v_isSharedCheck_4111_ == 0 {
                        v_unused_4112_ = crate::leanh::lean_ctor_get(v_value_3838_, 0);
                        crate::leanh::lean_dec(v_unused_4112_);
                        v___x_4103_ = v_value_3838_;
                        v_isShared_4104_ = v_isSharedCheck_4111_;
                        state = 36;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_value_3838_);
                        v___x_4103_ = crate::leanh::lean_box(0);
                        v_isShared_4104_ = v_isSharedCheck_4111_;
                        state = 36;
                        continue;
                    }
                }
            }
            1 => {
                v_size_3848_ = crate::leanh::lean_ctor_get(v_a_3844_, 0);
                v_buckets_3849_ = crate::leanh::lean_ctor_get(v_a_3844_, 1);
                v_name_3850_ = crate::leanh::lean_ctor_get(v_toSignature_3839_, 0);
                v_levelParams_3851_ = crate::leanh::lean_ctor_get(v_toSignature_3839_, 1);
                v_type_3852_ = crate::leanh::lean_ctor_get(v_toSignature_3839_, 2);
                v_params_3853_ = crate::leanh::lean_ctor_get(v_toSignature_3839_, 3);
                v_safe_3854_ = crate::leanh::lean_ctor_get_uint8(
                    v_toSignature_3839_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                );
                v_isSharedCheck_4092_ =
                    (!crate::leanh::lean_is_exclusive(v_toSignature_3839_)) as u8;
                if v_isSharedCheck_4092_ == 0 {
                    v___x_3856_ = v_toSignature_3839_;
                    v_isShared_3857_ = v_isSharedCheck_4092_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_params_3853_);
                    crate::leanh::lean_inc(v_type_3852_);
                    crate::leanh::lean_inc(v_levelParams_3851_);
                    crate::leanh::lean_inc(v_name_3850_);
                    crate::leanh::lean_dec(v_toSignature_3839_);
                    v___x_3856_ = crate::leanh::lean_box(0);
                    v_isShared_3857_ = v_isSharedCheck_4092_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4004_ = lean_array_get_size(v_params_3853_);
                v___x_4089_ = lean_nat_dec_eq(v_size_3848_, v___x_4004_);
                if v___x_4089_ == 0 {
                    v___x_4090_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_4091_ = lean_nat_dec_eq(v_size_3848_, v___x_4090_);
                    v___y_4066_ = v___x_4091_;
                    state = 32;
                    continue;
                } else {
                    v___y_4066_ = v___x_4089_;
                    state = 32;
                    continue;
                }
            }
            3 => {
                crate::leanh::lean_inc_ref(v___y_3864_);
                v___x_3874_ = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(v___y_3864_, v_value_3838_, v___y_3868_, v___y_3865_, v___y_3862_, v___y_3860_, v___y_3870_);
                crate::leanh::lean_dec_ref(v___y_3868_);
                if crate::leanh::lean_obj_tag(v___x_3874_) == 0 {
                    v_a_3875_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
                    crate::leanh::lean_inc(v_a_3875_);
                    crate::leanh::lean_dec_ref_known(v___x_3874_, 1);
                    v___x_3876_ = l_Lean_Compiler_LCNF_Code_inferType(
                        v___y_3869_,
                        v_code_3842_,
                        v___y_3865_,
                        v___y_3862_,
                        v___y_3860_,
                        v___y_3870_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3876_) == 0 {
                        v_a_3877_ = crate::leanh::lean_ctor_get(v___x_3876_, 0);
                        crate::leanh::lean_inc(v_a_3877_);
                        crate::leanh::lean_dec_ref_known(v___x_3876_, 1);
                        crate::leanh::lean_inc_ref(v___y_3861_);
                        v___x_3878_ = l_Lean_Compiler_LCNF_mkForallParams(
                            v___y_3869_,
                            v___y_3861_,
                            v_a_3877_,
                            v___y_3865_,
                            v___y_3862_,
                            v___y_3860_,
                            v___y_3870_,
                        );
                        crate::leanh::lean_dec(v_a_3877_);
                        if crate::leanh::lean_obj_tag(v___x_3878_) == 0 {
                            v_a_3879_ = crate::leanh::lean_ctor_get(v___x_3878_, 0);
                            crate::leanh::lean_inc(v_a_3879_);
                            crate::leanh::lean_dec_ref_known(v___x_3878_, 1);
                            v___x_3880_ = crate::leanh::lean_box(0);
                            crate::leanh::lean_inc(v___y_3859_);
                            if v_isShared_3857_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3856_, 3, v___y_3861_);
                                crate::leanh::lean_ctor_set(v___x_3856_, 2, v_a_3879_);
                                crate::leanh::lean_ctor_set(v___x_3856_, 1, v___x_3880_);
                                crate::leanh::lean_ctor_set(v___x_3856_, 0, v___y_3859_);
                                v___x_3882_ = v___x_3856_;
                                state = 4;
                                continue;
                            } else {
                                v_reuseFailAlloc_3979_ =
                                    crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 0, v___y_3859_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 1, v___x_3880_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 2, v_a_3879_);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3979_, 3, v___y_3861_);
                                crate::leanh::lean_ctor_set_uint8(
                                    v_reuseFailAlloc_3979_,
                                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4)
                                        as u32,
                                    v_safe_3854_,
                                );
                                v___x_3882_ = v_reuseFailAlloc_3979_;
                                state = 4;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3875_);
                            crate::leanh::lean_dec_ref(v___y_3873_);
                            crate::leanh::lean_dec(v___y_3872_);
                            crate::leanh::lean_dec_ref(v___y_3863_);
                            crate::leanh::lean_dec_ref(v___y_3861_);
                            crate::leanh::lean_dec(v___y_3859_);
                            crate::leanh::lean_del_object(v___x_3856_);
                            crate::leanh::lean_dec_ref(v_params_3853_);
                            crate::leanh::lean_dec_ref(v_type_3852_);
                            crate::leanh::lean_dec(v_levelParams_3851_);
                            crate::leanh::lean_dec(v_name_3850_);
                            crate::leanh::lean_dec(v_inlineAttr_x3f_3841_);
                            v_a_3980_ = crate::leanh::lean_ctor_get(v___x_3878_, 0);
                            v_isSharedCheck_3987_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3878_)) as u8;
                            if v_isSharedCheck_3987_ == 0 {
                                v___x_3982_ = v___x_3878_;
                                v_isShared_3983_ = v_isSharedCheck_3987_;
                                state = 21;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3980_);
                                crate::leanh::lean_dec(v___x_3878_);
                                v___x_3982_ = crate::leanh::lean_box(0);
                                v_isShared_3983_ = v_isSharedCheck_3987_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3875_);
                        crate::leanh::lean_dec_ref(v___y_3873_);
                        crate::leanh::lean_dec(v___y_3872_);
                        crate::leanh::lean_dec_ref(v___y_3863_);
                        crate::leanh::lean_dec_ref(v___y_3861_);
                        crate::leanh::lean_dec(v___y_3859_);
                        crate::leanh::lean_del_object(v___x_3856_);
                        crate::leanh::lean_dec_ref(v_params_3853_);
                        crate::leanh::lean_dec_ref(v_type_3852_);
                        crate::leanh::lean_dec(v_levelParams_3851_);
                        crate::leanh::lean_dec(v_name_3850_);
                        crate::leanh::lean_dec(v_inlineAttr_x3f_3841_);
                        v_a_3988_ = crate::leanh::lean_ctor_get(v___x_3876_, 0);
                        v_isSharedCheck_3995_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3876_)) as u8;
                        if v_isSharedCheck_3995_ == 0 {
                            v___x_3990_ = v___x_3876_;
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 23;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3988_);
                            crate::leanh::lean_dec(v___x_3876_);
                            v___x_3990_ = crate::leanh::lean_box(0);
                            v_isShared_3991_ = v_isSharedCheck_3995_;
                            state = 23;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___y_3873_);
                    crate::leanh::lean_dec(v___y_3872_);
                    crate::leanh::lean_dec_ref(v___y_3863_);
                    crate::leanh::lean_dec_ref(v___y_3861_);
                    crate::leanh::lean_dec(v___y_3859_);
                    crate::leanh::lean_del_object(v___x_3856_);
                    crate::leanh::lean_dec_ref(v_params_3853_);
                    crate::leanh::lean_dec_ref(v_type_3852_);
                    crate::leanh::lean_dec(v_levelParams_3851_);
                    crate::leanh::lean_dec(v_name_3850_);
                    crate::leanh::lean_dec_ref(v_code_3842_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_3841_);
                    v_a_3996_ = crate::leanh::lean_ctor_get(v___x_3874_, 0);
                    v_isSharedCheck_4003_ = (!crate::leanh::lean_is_exclusive(v___x_3874_)) as u8;
                    if v_isSharedCheck_4003_ == 0 {
                        v___x_3998_ = v___x_3874_;
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 25;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3996_);
                        crate::leanh::lean_dec(v___x_3874_);
                        v___x_3998_ = crate::leanh::lean_box(0);
                        v_isShared_3999_ = v_isSharedCheck_4003_;
                        state = 25;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3883_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3883_, 0, v___x_3882_);
                crate::leanh::lean_ctor_set(v___x_3883_, 1, v_a_3875_);
                crate::leanh::lean_ctor_set(v___x_3883_, 2, v_inlineAttr_x3f_3841_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3883_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v_recursive_3840_,
                );
                crate::leanh::lean_inc_ref(v___x_3883_);
                v___x_3884_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_3883_, v___y_3870_);
                if crate::leanh::lean_obj_tag(v___x_3884_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3884_, 1);
                    v___x_3885_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0),
                        core::ptr::addr_of_mut!(
                            l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0_once
                        ),
                        _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__0,
                    );
                    crate::leanh::lean_inc(v___y_3872_);
                    v___x_3886_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3886_, 0, v___y_3872_);
                    crate::leanh::lean_ctor_set(v___x_3886_, 1, v___x_3885_);
                    v___x_3887_ = lean_st_mk_ref(v___x_3886_);
                    v___x_3888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__3(v___y_3866_, v___y_3871_, v_params_3853_, v___y_3867_, v___x_3887_, v___y_3865_, v___y_3862_, v___y_3860_, v___y_3870_);
                    if crate::leanh::lean_obj_tag(v___x_3888_) == 0 {
                        v_a_3889_ = crate::leanh::lean_ctor_get(v___x_3888_, 0);
                        crate::leanh::lean_inc_n(v_a_3889_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_3888_, 1);
                        v___x_3890_ = lean_mk_empty_array_with_capacity(v___y_3872_);
                        v___x_3891_ = lean_array_get_size(v_a_3889_);
                        v___x_3892_ =
                            l_Array_toSubarray___redArg(v_a_3889_, v___y_3872_, v___x_3891_);
                        v___x_3893_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3893_, 0, v___x_3890_);
                        crate::leanh::lean_ctor_set(v___x_3893_, 1, v___x_3892_);
                        v_sz_3894_ = lean_array_size(v___y_3863_);
                        v___x_3895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v___y_3863_, v_sz_3894_, v___y_3871_, v___x_3893_);
                        crate::leanh::lean_dec_ref(v___y_3863_);
                        if crate::leanh::lean_obj_tag(v___x_3895_) == 0 {
                            v_a_3896_ = crate::leanh::lean_ctor_get(v___x_3895_, 0);
                            crate::leanh::lean_inc(v_a_3896_);
                            crate::leanh::lean_dec_ref_known(v___x_3895_, 1);
                            v_fst_3897_ = crate::leanh::lean_ctor_get(v_a_3896_, 0);
                            v_isSharedCheck_3953_ =
                                (!crate::leanh::lean_is_exclusive(v_a_3896_)) as u8;
                            if v_isSharedCheck_3953_ == 0 {
                                v_unused_3954_ = crate::leanh::lean_ctor_get(v_a_3896_, 1);
                                crate::leanh::lean_dec(v_unused_3954_);
                                v___x_3899_ = v_a_3896_;
                                v_isShared_3900_ = v_isSharedCheck_3953_;
                                state = 5;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_fst_3897_);
                                crate::leanh::lean_dec(v_a_3896_);
                                v___x_3899_ = crate::leanh::lean_box(0);
                                v_isShared_3900_ = v_isSharedCheck_3953_;
                                state = 5;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3889_);
                            crate::leanh::lean_dec(v___x_3887_);
                            crate::leanh::lean_dec_ref_known(v___x_3883_, 3);
                            crate::leanh::lean_dec_ref(v___y_3873_);
                            crate::leanh::lean_dec(v___y_3859_);
                            crate::leanh::lean_dec_ref(v_type_3852_);
                            crate::leanh::lean_dec(v_levelParams_3851_);
                            crate::leanh::lean_dec(v_name_3850_);
                            v_a_3955_ = crate::leanh::lean_ctor_get(v___x_3895_, 0);
                            v_isSharedCheck_3962_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3895_)) as u8;
                            if v_isSharedCheck_3962_ == 0 {
                                v___x_3957_ = v___x_3895_;
                                v_isShared_3958_ = v_isSharedCheck_3962_;
                                state = 15;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3955_);
                                crate::leanh::lean_dec(v___x_3895_);
                                v___x_3957_ = crate::leanh::lean_box(0);
                                v_isShared_3958_ = v_isSharedCheck_3962_;
                                state = 15;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3887_);
                        crate::leanh::lean_dec_ref_known(v___x_3883_, 3);
                        crate::leanh::lean_dec_ref(v___y_3873_);
                        crate::leanh::lean_dec(v___y_3872_);
                        crate::leanh::lean_dec_ref(v___y_3863_);
                        crate::leanh::lean_dec(v___y_3859_);
                        crate::leanh::lean_dec_ref(v_type_3852_);
                        crate::leanh::lean_dec(v_levelParams_3851_);
                        crate::leanh::lean_dec(v_name_3850_);
                        v_a_3963_ = crate::leanh::lean_ctor_get(v___x_3888_, 0);
                        v_isSharedCheck_3970_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3888_)) as u8;
                        if v_isSharedCheck_3970_ == 0 {
                            v___x_3965_ = v___x_3888_;
                            v_isShared_3966_ = v_isSharedCheck_3970_;
                            state = 17;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3963_);
                            crate::leanh::lean_dec(v___x_3888_);
                            v___x_3965_ = crate::leanh::lean_box(0);
                            v_isShared_3966_ = v_isSharedCheck_3970_;
                            state = 17;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3883_, 3);
                    crate::leanh::lean_dec_ref(v___y_3873_);
                    crate::leanh::lean_dec(v___y_3872_);
                    crate::leanh::lean_dec_ref(v___y_3863_);
                    crate::leanh::lean_dec(v___y_3859_);
                    crate::leanh::lean_dec_ref(v_params_3853_);
                    crate::leanh::lean_dec_ref(v_type_3852_);
                    crate::leanh::lean_dec(v_levelParams_3851_);
                    crate::leanh::lean_dec(v_name_3850_);
                    v_a_3971_ = crate::leanh::lean_ctor_get(v___x_3884_, 0);
                    v_isSharedCheck_3978_ = (!crate::leanh::lean_is_exclusive(v___x_3884_)) as u8;
                    if v_isSharedCheck_3978_ == 0 {
                        v___x_3973_ = v___x_3884_;
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 19;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3971_);
                        crate::leanh::lean_dec(v___x_3884_);
                        v___x_3973_ = crate::leanh::lean_box(0);
                        v_isShared_3974_ = v_isSharedCheck_3978_;
                        state = 19;
                        continue;
                    }
                }
            }
            5 => {
                v___x_3901_ = crate::leanh::lean_alloc_ctor(3, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3901_, 0, v___y_3859_);
                crate::leanh::lean_ctor_set(v___x_3901_, 1, v___x_3880_);
                crate::leanh::lean_ctor_set(v___x_3901_, 2, v_fst_3897_);
                v___x_3902_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__2;
                v___x_3903_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
                    v___y_3869_,
                    v___x_3901_,
                    v___x_3902_,
                    v___y_3865_,
                    v___y_3862_,
                    v___y_3860_,
                    v___y_3870_,
                );
                if crate::leanh::lean_obj_tag(v___x_3903_) == 0 {
                    v_a_3904_ = crate::leanh::lean_ctor_get(v___x_3903_, 0);
                    crate::leanh::lean_inc(v_a_3904_);
                    crate::leanh::lean_dec_ref_known(v___x_3903_, 1);
                    v_fvarId_3905_ = crate::leanh::lean_ctor_get(v_a_3904_, 0);
                    crate::leanh::lean_inc(v_fvarId_3905_);
                    v___x_3906_ = crate::leanh::lean_alloc_ctor(5, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3906_, 0, v_fvarId_3905_);
                    if v_isShared_3900_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3899_, 1, v___x_3906_);
                        crate::leanh::lean_ctor_set(v___x_3899_, 0, v_a_3904_);
                        v___x_3908_ = v___x_3899_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3944_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 0, v_a_3904_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3944_, 1, v___x_3906_);
                        v___x_3908_ = v_reuseFailAlloc_3944_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3899_);
                    crate::leanh::lean_dec(v_a_3889_);
                    crate::leanh::lean_dec(v___x_3887_);
                    crate::leanh::lean_dec_ref_known(v___x_3883_, 3);
                    crate::leanh::lean_dec_ref(v___y_3873_);
                    crate::leanh::lean_dec_ref(v_type_3852_);
                    crate::leanh::lean_dec(v_levelParams_3851_);
                    crate::leanh::lean_dec(v_name_3850_);
                    v_a_3945_ = crate::leanh::lean_ctor_get(v___x_3903_, 0);
                    v_isSharedCheck_3952_ = (!crate::leanh::lean_is_exclusive(v___x_3903_)) as u8;
                    if v_isSharedCheck_3952_ == 0 {
                        v___x_3947_ = v___x_3903_;
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 13;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3945_);
                        crate::leanh::lean_dec(v___x_3903_);
                        v___x_3947_ = crate::leanh::lean_box(0);
                        v_isShared_3948_ = v_isSharedCheck_3952_;
                        state = 13;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3909_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3909_, 0, v___x_3908_);
                v___x_3910_ = crate::leanh::lean_alloc_ctor(0, 4, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3910_, 0, v_name_3850_);
                crate::leanh::lean_ctor_set(v___x_3910_, 1, v_levelParams_3851_);
                crate::leanh::lean_ctor_set(v___x_3910_, 2, v_type_3852_);
                crate::leanh::lean_ctor_set(v___x_3910_, 3, v_a_3889_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3910_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 4) as u32,
                    v_safe_3854_,
                );
                v___x_3911_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__3;
                v___x_3912_ = crate::leanh::lean_alloc_ctor(0, 3, (1) as u32);
                crate::leanh::lean_ctor_set(v___x_3912_, 0, v___x_3910_);
                crate::leanh::lean_ctor_set(v___x_3912_, 1, v___x_3909_);
                crate::leanh::lean_ctor_set(v___x_3912_, 2, v___x_3911_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_3912_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 3) as u32,
                    v___y_3867_,
                );
                crate::leanh::lean_inc_ref(v___x_3912_);
                v___x_3913_ = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(v___x_3912_, v___y_3870_);
                if crate::leanh::lean_obj_tag(v___x_3913_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3913_, 1);
                    v___x_3914_ = lean_st_ref_get(v___x_3887_);
                    crate::leanh::lean_dec(v___x_3887_);
                    crate::leanh::lean_dec(v___x_3914_);
                    v___x_3915_ = l_Lean_Compiler_LCNF_eraseParams___redArg(
                        v___y_3869_,
                        v___y_3873_,
                        v___y_3862_,
                    );
                    crate::leanh::lean_dec_ref(v___y_3873_);
                    if crate::leanh::lean_obj_tag(v___x_3915_) == 0 {
                        v_isSharedCheck_3926_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3926_ == 0 {
                            v_unused_3927_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                            crate::leanh::lean_dec(v_unused_3927_);
                            v___x_3917_ = v___x_3915_;
                            v_isShared_3918_ = v_isSharedCheck_3926_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3915_);
                            v___x_3917_ = crate::leanh::lean_box(0);
                            v_isShared_3918_ = v_isSharedCheck_3926_;
                            state = 7;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v___x_3912_, 3);
                        crate::leanh::lean_dec_ref_known(v___x_3883_, 3);
                        v_a_3928_ = crate::leanh::lean_ctor_get(v___x_3915_, 0);
                        v_isSharedCheck_3935_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3915_)) as u8;
                        if v_isSharedCheck_3935_ == 0 {
                            v___x_3930_ = v___x_3915_;
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3928_);
                            crate::leanh::lean_dec(v___x_3915_);
                            v___x_3930_ = crate::leanh::lean_box(0);
                            v_isShared_3931_ = v_isSharedCheck_3935_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_3912_, 3);
                    crate::leanh::lean_dec(v___x_3887_);
                    crate::leanh::lean_dec_ref_known(v___x_3883_, 3);
                    crate::leanh::lean_dec_ref(v___y_3873_);
                    v_a_3936_ = crate::leanh::lean_ctor_get(v___x_3913_, 0);
                    v_isSharedCheck_3943_ = (!crate::leanh::lean_is_exclusive(v___x_3913_)) as u8;
                    if v_isSharedCheck_3943_ == 0 {
                        v___x_3938_ = v___x_3913_;
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3936_);
                        crate::leanh::lean_dec(v___x_3913_);
                        v___x_3938_ = crate::leanh::lean_box(0);
                        v_isShared_3939_ = v_isSharedCheck_3943_;
                        state = 11;
                        continue;
                    }
                }
            }
            7 => {
                v___x_3919_ = crate::leanh::lean_unsigned_to_nat(2);
                v___x_3920_ = lean_mk_empty_array_with_capacity(v___x_3919_);
                v___x_3921_ = lean_array_push(v___x_3920_, v___x_3883_);
                v___x_3922_ = lean_array_push(v___x_3921_, v___x_3912_);
                if v_isShared_3918_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3917_, 0, v___x_3922_);
                    v___x_3924_ = v___x_3917_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3925_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3925_, 0, v___x_3922_);
                    v___x_3924_ = v_reuseFailAlloc_3925_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3924_;
            }
            9 => {
                if v_isShared_3931_ == 0 {
                    v___x_3933_ = v___x_3930_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3934_, 0, v_a_3928_);
                    v___x_3933_ = v_reuseFailAlloc_3934_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3933_;
            }
            11 => {
                if v_isShared_3939_ == 0 {
                    v___x_3941_ = v___x_3938_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3942_, 0, v_a_3936_);
                    v___x_3941_ = v_reuseFailAlloc_3942_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3941_;
            }
            13 => {
                if v_isShared_3948_ == 0 {
                    v___x_3950_ = v___x_3947_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3951_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
                    v___x_3950_ = v_reuseFailAlloc_3951_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3950_;
            }
            15 => {
                if v_isShared_3958_ == 0 {
                    v___x_3960_ = v___x_3957_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3961_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3961_, 0, v_a_3955_);
                    v___x_3960_ = v_reuseFailAlloc_3961_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3960_;
            }
            17 => {
                if v_isShared_3966_ == 0 {
                    v___x_3968_ = v___x_3965_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
                    v___x_3968_ = v_reuseFailAlloc_3969_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3968_;
            }
            19 => {
                if v_isShared_3974_ == 0 {
                    v___x_3976_ = v___x_3973_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3977_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3977_, 0, v_a_3971_);
                    v___x_3976_ = v_reuseFailAlloc_3977_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3976_;
            }
            21 => {
                if v_isShared_3983_ == 0 {
                    v___x_3985_ = v___x_3982_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3986_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
                    v___x_3985_ = v_reuseFailAlloc_3986_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3985_;
            }
            23 => {
                if v_isShared_3991_ == 0 {
                    v___x_3993_ = v___x_3990_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3994_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3994_, 0, v_a_3988_);
                    v___x_3993_ = v_reuseFailAlloc_3994_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3993_;
            }
            25 => {
                if v_isShared_3999_ == 0 {
                    v___x_4001_ = v___x_3998_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_4002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4002_, 0, v_a_3996_);
                    v___x_4001_ = v_reuseFailAlloc_4002_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_4001_;
            }
            27 => {
                v___x_4017_ = 0;
                v___x_4018_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__4;
                crate::leanh::lean_inc_ref(v___y_4007_);
                crate::leanh::lean_inc(v___y_4006_);
                crate::leanh::lean_inc(v_name_3850_);
                v___x_4019_ = crate::leanh::lean_alloc_ctor(0, 3, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4019_, 0, v_name_3850_);
                crate::leanh::lean_ctor_set(v___x_4019_, 1, v___y_4006_);
                crate::leanh::lean_ctor_set(v___x_4019_, 2, v___y_4007_);
                v___x_4020_ = lean_mk_empty_array_with_capacity(v___y_4015_);
                v___x_4021_ = lean_nat_dec_lt(v___y_4015_, v___x_4004_);
                if v___x_4021_ == 0 {
                    crate::leanh::lean_dec(v_a_3844_);
                    v___y_3859_ = v___y_4006_;
                    v___y_3860_ = v___y_4008_;
                    v___y_3861_ = v___y_4016_;
                    v___y_3862_ = v___y_4014_;
                    v___y_3863_ = v___y_4007_;
                    v___y_3864_ = v___x_4018_;
                    v___y_3865_ = v___y_4009_;
                    v___y_3866_ = v___y_4010_;
                    v___y_3867_ = v___y_4011_;
                    v___y_3868_ = v___x_4019_;
                    v___y_3869_ = v___x_4017_;
                    v___y_3870_ = v___y_4013_;
                    v___y_3871_ = v___y_4012_;
                    v___y_3872_ = v___y_4015_;
                    v___y_3873_ = v___x_4020_;
                    state = 3;
                    continue;
                } else {
                    v___x_4022_ = lean_nat_dec_le(v___x_4004_, v___x_4004_);
                    if v___x_4022_ == 0 {
                        if v___x_4021_ == 0 {
                            crate::leanh::lean_dec(v_a_3844_);
                            v___y_3859_ = v___y_4006_;
                            v___y_3860_ = v___y_4008_;
                            v___y_3861_ = v___y_4016_;
                            v___y_3862_ = v___y_4014_;
                            v___y_3863_ = v___y_4007_;
                            v___y_3864_ = v___x_4018_;
                            v___y_3865_ = v___y_4009_;
                            v___y_3866_ = v___y_4010_;
                            v___y_3867_ = v___y_4011_;
                            v___y_3868_ = v___x_4019_;
                            v___y_3869_ = v___x_4017_;
                            v___y_3870_ = v___y_4013_;
                            v___y_3871_ = v___y_4012_;
                            v___y_3872_ = v___y_4015_;
                            v___y_3873_ = v___x_4020_;
                            state = 3;
                            continue;
                        } else {
                            v___x_4023_ = lean_usize_of_nat(v___x_4004_);
                            v___x_4024_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_3844_, v_params_3853_, v___y_4012_, v___x_4023_, v___x_4020_);
                            crate::leanh::lean_dec(v_a_3844_);
                            v___y_3859_ = v___y_4006_;
                            v___y_3860_ = v___y_4008_;
                            v___y_3861_ = v___y_4016_;
                            v___y_3862_ = v___y_4014_;
                            v___y_3863_ = v___y_4007_;
                            v___y_3864_ = v___x_4018_;
                            v___y_3865_ = v___y_4009_;
                            v___y_3866_ = v___y_4010_;
                            v___y_3867_ = v___y_4011_;
                            v___y_3868_ = v___x_4019_;
                            v___y_3869_ = v___x_4017_;
                            v___y_3870_ = v___y_4013_;
                            v___y_3871_ = v___y_4012_;
                            v___y_3872_ = v___y_4015_;
                            v___y_3873_ = v___x_4024_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4025_ = lean_usize_of_nat(v___x_4004_);
                        v___x_4026_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__5(v_a_3844_, v_params_3853_, v___y_4012_, v___x_4025_, v___x_4020_);
                        crate::leanh::lean_dec(v_a_3844_);
                        v___y_3859_ = v___y_4006_;
                        v___y_3860_ = v___y_4008_;
                        v___y_3861_ = v___y_4016_;
                        v___y_3862_ = v___y_4014_;
                        v___y_3863_ = v___y_4007_;
                        v___y_3864_ = v___x_4018_;
                        v___y_3865_ = v___y_4009_;
                        v___y_3866_ = v___y_4010_;
                        v___y_3867_ = v___y_4011_;
                        v___y_3868_ = v___x_4019_;
                        v___y_3869_ = v___x_4017_;
                        v___y_3870_ = v___y_4013_;
                        v___y_3871_ = v___y_4012_;
                        v___y_3872_ = v___y_4015_;
                        v___y_3873_ = v___x_4026_;
                        state = 3;
                        continue;
                    }
                }
            }
            28 => {
                v_sz_4033_ = lean_array_size(v_params_3853_);
                v___x_4034_ = 0usize;
                crate::leanh::lean_inc_ref(v_params_3853_);
                v___x_4035_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__1(v_a_3844_, v_sz_4033_, v___x_4034_, v_params_3853_);
                v___x_4036_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__6;
                crate::leanh::lean_inc(v_name_3850_);
                v___x_4037_ = l_Lean_Name_append(v_name_3850_, v___x_4036_);
                v___x_4038_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4039_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__7;
                v___x_4040_ = lean_nat_dec_lt(v___x_4038_, v___x_4004_);
                if v___x_4040_ == 0 {
                    v___y_4006_ = v___x_4037_;
                    v___y_4007_ = v___x_4035_;
                    v___y_4008_ = v___y_4031_;
                    v___y_4009_ = v___y_4029_;
                    v___y_4010_ = v_sz_4033_;
                    v___y_4011_ = v___y_4028_;
                    v___y_4012_ = v___x_4034_;
                    v___y_4013_ = v___y_4032_;
                    v___y_4014_ = v___y_4030_;
                    v___y_4015_ = v___x_4038_;
                    v___y_4016_ = v___x_4039_;
                    state = 27;
                    continue;
                } else {
                    v___x_4041_ = lean_nat_dec_le(v___x_4004_, v___x_4004_);
                    if v___x_4041_ == 0 {
                        if v___x_4040_ == 0 {
                            v___y_4006_ = v___x_4037_;
                            v___y_4007_ = v___x_4035_;
                            v___y_4008_ = v___y_4031_;
                            v___y_4009_ = v___y_4029_;
                            v___y_4010_ = v_sz_4033_;
                            v___y_4011_ = v___y_4028_;
                            v___y_4012_ = v___x_4034_;
                            v___y_4013_ = v___y_4032_;
                            v___y_4014_ = v___y_4030_;
                            v___y_4015_ = v___x_4038_;
                            v___y_4016_ = v___x_4039_;
                            state = 27;
                            continue;
                        } else {
                            v___x_4042_ = lean_usize_of_nat(v___x_4004_);
                            v___x_4043_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_3844_, v_params_3853_, v___x_4034_, v___x_4042_, v___x_4039_);
                            v___y_4006_ = v___x_4037_;
                            v___y_4007_ = v___x_4035_;
                            v___y_4008_ = v___y_4031_;
                            v___y_4009_ = v___y_4029_;
                            v___y_4010_ = v_sz_4033_;
                            v___y_4011_ = v___y_4028_;
                            v___y_4012_ = v___x_4034_;
                            v___y_4013_ = v___y_4032_;
                            v___y_4014_ = v___y_4030_;
                            v___y_4015_ = v___x_4038_;
                            v___y_4016_ = v___x_4043_;
                            state = 27;
                            continue;
                        }
                    } else {
                        v___x_4044_ = lean_usize_of_nat(v___x_4004_);
                        v___x_4045_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__6(v_a_3844_, v_params_3853_, v___x_4034_, v___x_4044_, v___x_4039_);
                        v___y_4006_ = v___x_4037_;
                        v___y_4007_ = v___x_4035_;
                        v___y_4008_ = v___y_4031_;
                        v___y_4009_ = v___y_4029_;
                        v___y_4010_ = v_sz_4033_;
                        v___y_4011_ = v___y_4028_;
                        v___y_4012_ = v___x_4034_;
                        v___y_4013_ = v___y_4032_;
                        v___y_4014_ = v___y_4030_;
                        v___y_4015_ = v___x_4038_;
                        v___y_4016_ = v___x_4045_;
                        state = 27;
                        continue;
                    }
                }
            }
            29 => {
                v___x_4051_ = crate::leanh::lean_box(0);
                v___x_4052_ =
                    l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__7(
                        v___y_4050_,
                        v___x_4051_,
                    );
                v___x_4053_ =
                    l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__8(
                        v___x_4052_,
                        v___x_4051_,
                    );
                v___x_4054_ = l_Lean_MessageData_ofList(v___x_4053_);
                v___x_4055_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4055_, 0, v___y_4049_);
                crate::leanh::lean_ctor_set(v___x_4055_, 1, v___x_4054_);
                crate::leanh::lean_inc(v___y_4047_);
                v___x_4056_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__9(
                    v___y_4047_,
                    v___x_4055_,
                    v_a_3833_,
                    v_a_3834_,
                    v_a_3835_,
                    v_a_3836_,
                );
                if crate::leanh::lean_obj_tag(v___x_4056_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4056_, 1);
                    v___y_4028_ = v___y_4048_;
                    v___y_4029_ = v_a_3833_;
                    v___y_4030_ = v_a_3834_;
                    v___y_4031_ = v_a_3835_;
                    v___y_4032_ = v_a_3836_;
                    state = 28;
                    continue;
                } else {
                    crate::leanh::lean_del_object(v___x_3856_);
                    crate::leanh::lean_dec_ref(v_params_3853_);
                    crate::leanh::lean_dec_ref(v_type_3852_);
                    crate::leanh::lean_dec(v_levelParams_3851_);
                    crate::leanh::lean_dec(v_name_3850_);
                    crate::leanh::lean_dec(v_a_3844_);
                    crate::leanh::lean_dec_ref(v_code_3842_);
                    crate::leanh::lean_dec(v_inlineAttr_x3f_3841_);
                    crate::leanh::lean_dec_ref_known(v_value_3838_, 1);
                    v_a_4057_ = crate::leanh::lean_ctor_get(v___x_4056_, 0);
                    v_isSharedCheck_4064_ = (!crate::leanh::lean_is_exclusive(v___x_4056_)) as u8;
                    if v_isSharedCheck_4064_ == 0 {
                        v___x_4059_ = v___x_4056_;
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 30;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4057_);
                        crate::leanh::lean_dec(v___x_4056_);
                        v___x_4059_ = crate::leanh::lean_box(0);
                        v_isShared_4060_ = v_isSharedCheck_4064_;
                        state = 30;
                        continue;
                    }
                }
            }
            30 => {
                if v_isShared_4060_ == 0 {
                    v___x_4062_ = v___x_4059_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_4063_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4063_, 0, v_a_4057_);
                    v___x_4062_ = v_reuseFailAlloc_4063_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_4062_;
            }
            32 => {
                if v___y_4066_ == 0 {
                    crate::leanh::lean_inc(v_inlineAttr_x3f_3841_);
                    crate::leanh::lean_del_object(v___x_3846_);
                    crate::leanh::lean_dec_ref(v_decl_3832_);
                    v_options_4067_ = crate::leanh::lean_ctor_get(v_a_3835_, 2);
                    v_hasTrace_4068_ = crate::leanh::lean_ctor_get_uint8(
                        v_options_4067_,
                        (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4068_ == 0 {
                        v___y_4028_ = v___y_4066_;
                        v___y_4029_ = v_a_3833_;
                        v___y_4030_ = v_a_3834_;
                        v___y_4031_ = v_a_3835_;
                        v___y_4032_ = v_a_3836_;
                        state = 28;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4069_ = crate::leanh::lean_ctor_get(v_a_3835_, 13);
                        v___x_4070_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
                        v___x_4071_ = crate::leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__13,
                        );
                        v___x_4072_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4069_,
                            v_options_4067_,
                            v___x_4071_,
                        );
                        if v___x_4072_ == 0 {
                            v___y_4028_ = v___y_4066_;
                            v___y_4029_ = v_a_3833_;
                            v___y_4030_ = v_a_3834_;
                            v___y_4031_ = v_a_3835_;
                            v___y_4032_ = v_a_3836_;
                            state = 28;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_name_3850_);
                            v___x_4073_ = l_Lean_MessageData_ofName(v_name_3850_);
                            v___x_4074_ = crate::leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Decl_reduceArity___closed__15,
                            );
                            v___x_4075_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_4075_, 0, v___x_4073_);
                            crate::leanh::lean_ctor_set(v___x_4075_, 1, v___x_4074_);
                            v___x_4076_ = crate::leanh::lean_box(0);
                            v___x_4077_ = lean_array_get_size(v_buckets_3849_);
                            v___x_4078_ = crate::leanh::lean_unsigned_to_nat(0);
                            v___x_4079_ = lean_nat_dec_lt(v___x_4078_, v___x_4077_);
                            if v___x_4079_ == 0 {
                                v___y_4047_ = v___x_4070_;
                                v___y_4048_ = v___y_4066_;
                                v___y_4049_ = v___x_4075_;
                                v___y_4050_ = v___x_4076_;
                                state = 29;
                                continue;
                            } else {
                                v___x_4080_ = lean_usize_of_nat(v___x_4077_);
                                v___x_4081_ = 0usize;
                                v___x_4082_ = l___private_Init_Data_Array_Basic_0__Array_foldrMUnsafe_fold___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__11(v_buckets_3849_, v___x_4080_, v___x_4081_, v___x_4076_);
                                v___y_4047_ = v___x_4070_;
                                v___y_4048_ = v___y_4066_;
                                v___y_4049_ = v___x_4075_;
                                v___y_4050_ = v___x_4082_;
                                state = 29;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3856_);
                    crate::leanh::lean_dec_ref(v_params_3853_);
                    crate::leanh::lean_dec_ref(v_type_3852_);
                    crate::leanh::lean_dec(v_levelParams_3851_);
                    crate::leanh::lean_dec(v_name_3850_);
                    crate::leanh::lean_dec(v_a_3844_);
                    crate::leanh::lean_dec_ref(v_code_3842_);
                    crate::leanh::lean_dec_ref_known(v_value_3838_, 1);
                    v___x_4083_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4084_ = lean_mk_empty_array_with_capacity(v___x_4083_);
                    v___x_4085_ = lean_array_push(v___x_4084_, v_decl_3832_);
                    if v_isShared_3847_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_4085_);
                        v___x_4087_ = v___x_3846_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_4088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4088_, 0, v___x_4085_);
                        v___x_4087_ = v_reuseFailAlloc_4088_;
                        state = 33;
                        continue;
                    }
                }
            }
            33 => {
                return v___x_4087_;
            }
            34 => {
                if v_isShared_4097_ == 0 {
                    v___x_4099_ = v___x_4096_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_4100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4100_, 0, v_a_4094_);
                    v___x_4099_ = v_reuseFailAlloc_4100_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_4099_;
            }
            36 => {
                v___x_4105_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_4106_ = lean_mk_empty_array_with_capacity(v___x_4105_);
                v___x_4107_ = lean_array_push(v___x_4106_, v_decl_3832_);
                if v_isShared_4104_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4103_, 0);
                    crate::leanh::lean_ctor_set(v___x_4103_, 0, v___x_4107_);
                    v___x_4109_ = v___x_4103_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_4110_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
                    v___x_4109_ = v_reuseFailAlloc_4110_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_4109_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Decl_reduceArity___boxed(
    mut v_decl_4113_: *mut crate::leanh::LeanObject,
    mut v_a_4114_: *mut crate::leanh::LeanObject,
    mut v_a_4115_: *mut crate::leanh::LeanObject,
    mut v_a_4116_: *mut crate::leanh::LeanObject,
    mut v_a_4117_: *mut crate::leanh::LeanObject,
    mut v_a_4118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4119_ = l_Lean_Compiler_LCNF_Decl_reduceArity(
        v_decl_4113_,
        v_a_4114_,
        v_a_4115_,
        v_a_4116_,
        v_a_4117_,
    );
    crate::leanh::lean_dec(v_a_4117_);
    crate::leanh::lean_dec_ref(v_a_4116_);
    crate::leanh::lean_dec(v_a_4115_);
    crate::leanh::lean_dec_ref(v_a_4114_);
    return v_res_4119_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(
    mut v_00_u03b2_4120_: *mut crate::leanh::LeanObject,
    mut v_m_4121_: *mut crate::leanh::LeanObject,
    mut v_a_4122_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4123_: u8 = 0;
    v___x_4123_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___redArg(v_m_4121_, v_a_4122_);
    return v___x_4123_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(
    mut v_00_u03b2_4124_: *mut crate::leanh::LeanObject,
    mut v_m_4125_: *mut crate::leanh::LeanObject,
    mut v_a_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4127_: u8 = 0;
    let mut v_r_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4127_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__0(v_00_u03b2_4124_, v_m_4125_, v_a_4126_);
    crate::leanh::lean_dec(v_a_4126_);
    crate::leanh::lean_dec_ref(v_m_4125_);
    v_r_4128_ = crate::leanh::lean_box((v_res_4127_) as usize);
    return v_r_4128_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(
    mut v_as_4129_: *mut crate::leanh::LeanObject,
    mut v_sz_4130_: usize,
    mut v_i_4131_: usize,
    mut v_b_4132_: *mut crate::leanh::LeanObject,
    mut v___y_4133_: u8,
    mut v___y_4134_: *mut crate::leanh::LeanObject,
    mut v___y_4135_: *mut crate::leanh::LeanObject,
    mut v___y_4136_: *mut crate::leanh::LeanObject,
    mut v___y_4137_: *mut crate::leanh::LeanObject,
    mut v___y_4138_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4140_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___redArg(v_as_4129_, v_sz_4130_, v_i_4131_, v_b_4132_);
    return v___x_4140_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(
    mut v_as_4141_: *mut crate::leanh::LeanObject,
    mut v_sz_4142_: *mut crate::leanh::LeanObject,
    mut v_i_4143_: *mut crate::leanh::LeanObject,
    mut v_b_4144_: *mut crate::leanh::LeanObject,
    mut v___y_4145_: *mut crate::leanh::LeanObject,
    mut v___y_4146_: *mut crate::leanh::LeanObject,
    mut v___y_4147_: *mut crate::leanh::LeanObject,
    mut v___y_4148_: *mut crate::leanh::LeanObject,
    mut v___y_4149_: *mut crate::leanh::LeanObject,
    mut v___y_4150_: *mut crate::leanh::LeanObject,
    mut v___y_4151_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4152_: usize = 0;
    let mut v_i_boxed_4153_: usize = 0;
    let mut v___y_13288__boxed_4154_: u8 = 0;
    let mut v_res_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4152_ = crate::leanh::lean_unbox_usize(v_sz_4142_);
    crate::leanh::lean_dec(v_sz_4142_);
    v_i_boxed_4153_ = crate::leanh::lean_unbox_usize(v_i_4143_);
    crate::leanh::lean_dec(v_i_4143_);
    v___y_13288__boxed_4154_ = (crate::leanh::lean_unbox(v___y_4145_) as u8);
    v_res_4155_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Compiler_LCNF_Decl_reduceArity_spec__4(v_as_4141_, v_sz_boxed_4152_, v_i_boxed_4153_, v_b_4144_, v___y_13288__boxed_4154_, v___y_4146_, v___y_4147_, v___y_4148_, v___y_4149_, v___y_4150_);
    crate::leanh::lean_dec(v___y_4150_);
    crate::leanh::lean_dec_ref(v___y_4149_);
    crate::leanh::lean_dec(v___y_4148_);
    crate::leanh::lean_dec_ref(v___y_4147_);
    crate::leanh::lean_dec(v___y_4146_);
    crate::leanh::lean_dec_ref(v_as_4141_);
    return v_res_4155_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(
    mut v_as_4156_: *mut crate::leanh::LeanObject,
    mut v_i_4157_: usize,
    mut v_stop_4158_: usize,
    mut v_b_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
    mut v___y_4163_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4167_: usize = 0;
    let mut v___x_4168_: usize = 0;
    let mut v___x_4170_: u8 = 0;
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4170_ = lean_usize_dec_eq(v_i_4157_, v_stop_4158_);
                if v___x_4170_ == 0 {
                    v___x_4171_ = lean_array_uget_borrowed(v_as_4156_, v_i_4157_);
                    crate::leanh::lean_inc(v___x_4171_);
                    v___x_4172_ = l_Lean_Compiler_LCNF_Decl_reduceArity(
                        v___x_4171_,
                        v___y_4160_,
                        v___y_4161_,
                        v___y_4162_,
                        v___y_4163_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_4172_) == 0 {
                        v_a_4173_ = crate::leanh::lean_ctor_get(v___x_4172_, 0);
                        crate::leanh::lean_inc(v_a_4173_);
                        crate::leanh::lean_dec_ref_known(v___x_4172_, 1);
                        v___x_4174_ = l_Array_append___redArg(v_b_4159_, v_a_4173_);
                        crate::leanh::lean_dec(v_a_4173_);
                        v_a_4166_ = v___x_4174_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec_ref(v_b_4159_);
                        if crate::leanh::lean_obj_tag(v___x_4172_) == 0 {
                            v_a_4175_ = crate::leanh::lean_ctor_get(v___x_4172_, 0);
                            crate::leanh::lean_inc(v_a_4175_);
                            crate::leanh::lean_dec_ref_known(v___x_4172_, 1);
                            v_a_4166_ = v_a_4175_;
                            state = 1;
                            continue;
                        } else {
                            return v___x_4172_;
                        }
                    }
                } else {
                    v___x_4176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4176_, 0, v_b_4159_);
                    return v___x_4176_;
                }
            }
            1 => {
                v___x_4167_ = 1usize;
                v___x_4168_ = lean_usize_add(v_i_4157_, v___x_4167_);
                v_i_4157_ = v___x_4168_;
                v_b_4159_ = v_a_4166_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0___boxed(
    mut v_as_4177_: *mut crate::leanh::LeanObject,
    mut v_i_4178_: *mut crate::leanh::LeanObject,
    mut v_stop_4179_: *mut crate::leanh::LeanObject,
    mut v_b_4180_: *mut crate::leanh::LeanObject,
    mut v___y_4181_: *mut crate::leanh::LeanObject,
    mut v___y_4182_: *mut crate::leanh::LeanObject,
    mut v___y_4183_: *mut crate::leanh::LeanObject,
    mut v___y_4184_: *mut crate::leanh::LeanObject,
    mut v___y_4185_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_i_boxed_4186_: usize = 0;
    let mut v_stop_boxed_4187_: usize = 0;
    let mut v_res_4188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_4186_ = crate::leanh::lean_unbox_usize(v_i_4178_);
    crate::leanh::lean_dec(v_i_4178_);
    v_stop_boxed_4187_ = crate::leanh::lean_unbox_usize(v_stop_4179_);
    crate::leanh::lean_dec(v_stop_4179_);
    v_res_4188_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_as_4177_, v_i_boxed_4186_, v_stop_boxed_4187_, v_b_4180_, v___y_4181_, v___y_4182_, v___y_4183_, v___y_4184_);
    crate::leanh::lean_dec(v___y_4184_);
    crate::leanh::lean_dec_ref(v___y_4183_);
    crate::leanh::lean_dec(v___y_4182_);
    crate::leanh::lean_dec_ref(v___y_4181_);
    crate::leanh::lean_dec_ref(v_as_4177_);
    return v_res_4188_;
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceArity___lam__0(
    mut v___x_4189_: *mut crate::leanh::LeanObject,
    mut v_decls_4190_: *mut crate::leanh::LeanObject,
    mut v___y_4191_: *mut crate::leanh::LeanObject,
    mut v___y_4192_: *mut crate::leanh::LeanObject,
    mut v___y_4193_: *mut crate::leanh::LeanObject,
    mut v___y_4194_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4198_: u8 = 0;
    v___x_4196_ = lean_mk_empty_array_with_capacity(v___x_4189_);
    v___x_4197_ = lean_array_get_size(v_decls_4190_);
    v___x_4198_ = lean_nat_dec_lt(v___x_4189_, v___x_4197_);
    if v___x_4198_ == 0 {
        let mut v___x_4199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_4199_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_4199_, 0, v___x_4196_);
        return v___x_4199_;
    } else {
        let mut v___x_4200_: u8 = 0;
        v___x_4200_ = lean_nat_dec_le(v___x_4197_, v___x_4197_);
        if v___x_4200_ == 0 {
            if v___x_4198_ == 0 {
                let mut v___x_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4201_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4201_, 0, v___x_4196_);
                return v___x_4201_;
            } else {
                let mut v___x_4202_: usize = 0;
                let mut v___x_4203_: usize = 0;
                let mut v___x_4204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                v___x_4202_ = 0usize;
                v___x_4203_ = lean_usize_of_nat(v___x_4197_);
                v___x_4204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_4190_, v___x_4202_, v___x_4203_, v___x_4196_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
                return v___x_4204_;
            }
        } else {
            let mut v___x_4205_: usize = 0;
            let mut v___x_4206_: usize = 0;
            let mut v___x_4207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            v___x_4205_ = 0usize;
            v___x_4206_ = lean_usize_of_nat(v___x_4197_);
            v___x_4207_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Compiler_LCNF_reduceArity_spec__0(v_decls_4190_, v___x_4205_, v___x_4206_, v___x_4196_, v___y_4191_, v___y_4192_, v___y_4193_, v___y_4194_);
            return v___x_4207_;
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(
    mut v___x_4208_: *mut crate::leanh::LeanObject,
    mut v_decls_4209_: *mut crate::leanh::LeanObject,
    mut v___y_4210_: *mut crate::leanh::LeanObject,
    mut v___y_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
    mut v___y_4213_: *mut crate::leanh::LeanObject,
    mut v___y_4214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4215_ = l_Lean_Compiler_LCNF_reduceArity___lam__0(
        v___x_4208_,
        v_decls_4209_,
        v___y_4210_,
        v___y_4211_,
        v___y_4212_,
        v___y_4213_,
    );
    crate::leanh::lean_dec(v___y_4213_);
    crate::leanh::lean_dec_ref(v___y_4212_);
    crate::leanh::lean_dec(v___y_4211_);
    crate::leanh::lean_dec_ref(v___y_4210_);
    crate::leanh::lean_dec_ref(v_decls_4209_);
    crate::leanh::lean_dec(v___x_4208_);
    return v_res_4215_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4278_ = crate::leanh::lean_unsigned_to_nat(2803462840);
    v___x_4279_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
    v___x_4280_ = l_Lean_Name_num___override(v___x_4279_, v___x_4278_);
    return v___x_4280_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4282_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
    v___x_4283_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4284_ = l_Lean_Name_str___override(v___x_4283_, v___x_4282_);
    return v___x_4284_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4286_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_;
    v___x_4287_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4288_ = l_Lean_Name_str___override(v___x_4287_, v___x_4286_);
    return v___x_4288_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4289_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_4290_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4291_ = l_Lean_Name_num___override(v___x_4290_, v___x_4289_);
    return v___x_4291_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: u8 = 0;
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = l_Lean_Compiler_LCNF_Decl_reduceArity___closed__10;
    v___x_4294_ = 1;
    v___x_4295_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2__once), _init_l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_);
    v___x_4296_ = l_Lean_registerTraceClass(v___x_4293_, v___x_4294_, v___x_4295_);
    return v___x_4296_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2____boxed(
    mut v_a_4297_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4298_ = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
    return v_res_4298_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_ReduceArity(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = l___private_Lean_Compiler_LCNF_ReduceArity_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_ReduceArity_2803462840____hygCtx___hyg_2_();
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_ReduceArity(
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
pub unsafe fn initialize_Lean_Compiler_LCNF_ReduceArity(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_ReduceArity(builtin);
}
