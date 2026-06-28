// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.JpCases
// Imports: Lean.Compiler.LCNF.DependsOn Lean.Compiler.LCNF.Internalize Lean.Compiler.LCNF.Simp.DiscrM
use crate::r#gen::Init::Data::Array::Basic::{l_Array_append___redArg, l_Array_instInhabited};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_mkStr1, l_Lean_Name_mkStr3, l_Lean_Name_num___override,
    l_Lean_Name_str___override,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Compiler::LCNF::Basic::{
    l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg,
    l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg, l_Lean_Compiler_LCNF_attachCodeDecls,
    l_Lean_Compiler_LCNF_instInhabitedCases_default__1,
    l_Lean_Compiler_LCNF_instInhabitedParam_default,
};
use crate::r#gen::Lean::Compiler::LCNF::CompilerM::{
    l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg,
    l_Lean_Compiler_LCNF_eraseCode___redArg, l_Lean_Compiler_LCNF_getConfig___redArg,
    l_Lean_Compiler_LCNF_getPurity___redArg,
};
use crate::r#gen::Lean::Compiler::LCNF::DependsOn::{
    initialize_Lean_Compiler_LCNF_DependsOn, l_Lean_Compiler_LCNF_Code_dependsOn,
    l_Lean_Compiler_LCNF_CodeDecl_dependsOn, runtime_initialize_Lean_Compiler_LCNF_DependsOn,
};
use crate::r#gen::Lean::Compiler::LCNF::InferType::{
    l_Lean_Compiler_LCNF_mkAuxJpDecl, l_Lean_Compiler_LCNF_mkAuxLetDecl,
};
use crate::r#gen::Lean::Compiler::LCNF::Internalize::{
    initialize_Lean_Compiler_LCNF_Internalize, l_Lean_Compiler_LCNF_Internalize_internalizeCode,
    l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl,
    l_Lean_Compiler_LCNF_Internalize_internalizeParam,
    runtime_initialize_Lean_Compiler_LCNF_Internalize,
};
use crate::r#gen::Lean::Compiler::LCNF::LCtx::l_Lean_Compiler_LCNF_LCtx_toLocalContext;
use crate::r#gen::Lean::Compiler::LCNF::Simp::DiscrM::{
    initialize_Lean_Compiler_LCNF_Simp_DiscrM,
    l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx,
    l_Lean_Compiler_LCNF_Simp_CtorInfo_getName, l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg,
    l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg,
    runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM,
};
use crate::r#gen::Lean::Data::Name::l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl;
use crate::r#gen::Lean::Data::NameMap::Basic::{
    l_Lean_NameSet_contains, l_Lean_NameSet_empty, l_Lean_NameSet_insert,
    l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg,
};
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Data::PersistentHashMap::l_Lean_PersistentHashMap_mkEmptyEntriesArray;
use crate::r#gen::Lean::Expr::{
    l_Lean_instBEqFVarId_beq, l_Lean_instSingletonFVarIdFVarIdSet___lam__0, l_Lean_mkFVar,
    l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg,
};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofExpr, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList,
    l_Lean_MessageData_ofName, l_Lean_indentD, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_registerTraceClass,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_size, lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_sub, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Init::Util::lean_ptr_addr;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_ctor, lean_box, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_get_uint64, lean_ctor_set, lean_ctor_set_float, lean_ctor_set_tag,
    lean_ctor_set_uint8, lean_ctor_set_uint64, lean_dec, lean_dec_ref, lean_dec_ref_known,
    lean_del_object, lean_float_once, lean_inc, lean_inc_n, lean_inc_ref, lean_io_result_is_error,
    lean_io_result_mk_ok, lean_is_exclusive, lean_mark_persistent, lean_obj_once, lean_obj_tag,
    lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default: *mut LeanObject =
    core::ptr::null_mut();
pub static mut l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 1 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__0_value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2_value: LeanCtorObject<1> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*1 + 0) as u16, other: 1, tag: 0 }, m_objs: [core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__1_value) as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2_value) as *mut LeanObject;
pub static l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3: *mut LeanObject = core::ptr::addr_of!(l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3_value) as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1: *mut LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2: *mut LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0_value: LeanStringObject<32> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 32, m_capacity: 32, m_length: 31, m_data: [76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 74, 112, 67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1_value: LeanStringObject<85> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 85, m_capacity: 85, m_length: 84, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 74, 112, 67, 97, 115, 101, 115, 46, 48, 46, 76, 101, 97, 110, 46, 67, 111, 109, 112, 105, 108, 101, 114, 46, 76, 67, 78, 70, 46, 83, 105, 109, 112, 46, 101, 120, 116, 114, 97, 99, 116, 74, 112, 67, 97, 115, 101, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value: LeanStringObject<4> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [95, 106, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__2_value) as *mut LeanObject,12958253247387092313 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__1_value) as *mut LeanObject,7699194985028780469 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 1 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__0_value) as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1_value) as *mut LeanObject;
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2:
    *mut LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3:
    f64 = 0.0;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4_value: LeanStringObject<1> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4_value
) as *mut LeanObject;
pub static l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5:
    *mut LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5_value
) as *mut LeanObject;
pub static l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 3, m_data: [32, 226, 134, 166, 32, 0]};
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0_value) as *mut LeanObject;
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value: LeanStringObject<9> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value: LeanStringObject<5> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value: LeanStringObject<8> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 8,
        m_capacity: 8,
        m_length: 7,
        m_data: [106, 112, 67, 97, 115, 101, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value)
        as *mut LeanObject;
static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value)
                as *mut LeanObject,
            2042452093243897853 as *mut LeanObject,
        ],
    };
static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_0)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__1_value)
                as *mut LeanObject,
            11260351269579028997 as *mut LeanObject,
        ],
    };
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value_aux_1)
                as *mut LeanObject,
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__2_value)
                as *mut LeanObject,
            560254827231992844 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value: LeanStringObject<6> =
    LeanStringObject {
        m_header: LeanObject {
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
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value: LeanCtorObject<3> =
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
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__4_value)
                as *mut LeanObject,
            14231257465488249300 as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7_value: LeanStringObject<11> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 11,
        m_capacity: 11,
        m_length: 10,
        m_data: [99, 97, 110, 100, 105, 100, 97, 116, 101, 115, 0],
    };
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7_value)
        as *mut LeanObject;
pub static l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8_value: LeanCtorObject<1> =
    LeanCtorObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (core::mem::size_of::<LeanObject>()
                + core::mem::size_of::<*mut LeanObject>() * 1
                + 0) as u16,
            other: 1,
            tag: 3,
        },
        m_objs: [
            core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__7_value)
                as *mut LeanObject,
        ],
    };
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8_value)
        as *mut LeanObject;
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__0_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,11079354408986465895 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__1_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,10352885018404983386 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__3_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value) as *mut LeanObject,1501781890156459336 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 67, 78, 70, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__4_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,4203849195465939425 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [83, 105, 109, 112, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__6_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,12083366481402619969 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [74, 112, 67, 97, 115, 101, 115, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__8_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,7896999158404270116 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__10_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject,7831352197456180485 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__11_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,17187288366457057872 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__12_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value) as *mut LeanObject,5953226175640132554 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__13_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,6083165972128552331 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<7> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__14_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__15_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,16151251433534021434 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<3> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__16_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__17_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,2362895922074051507 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__18_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__2_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,3579398845820999070 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__19_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__0_value) as *mut LeanObject,6348378076506317404 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__20_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__5_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,12195842648209257789 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__21_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__7_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,3850634257535338549 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__22_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__9_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,15261025455405039712 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__23_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,((( 862626027 as usize) << 1) | 1) as *mut LeanObject,15832392317084714319 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<8> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__24_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__25_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,13025816319652243716 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__26_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__27_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,2204248240144664208 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub static l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__28_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject,((( 2 as usize) << 1) | 1) as *mut LeanObject,18202736977431220481 as *mut LeanObject] };
static mut l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2__value) as *mut LeanObject;
pub unsafe fn l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0(
    mut v_cases_2204_: *mut LeanObject,
    mut v_as_2205_: *mut LeanObject,
    mut v_j_2206_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: u8 = 0;
    let mut v___x_2209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_2210_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2213_: u8 = 0;
    let mut v___x_2214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2215_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2217_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2207_ = lean_array_get_size(v_as_2205_);
                v___x_2208_ = lean_nat_dec_lt(v_j_2206_, v___x_2207_);
                if v___x_2208_ == 0 {
                    lean_dec(v_j_2206_);
                    v___x_2209_ = lean_box(0);
                    return v___x_2209_;
                } else {
                    v_discr_2210_ = lean_ctor_get(v_cases_2204_, 2);
                    v___x_2211_ = lean_array_fget_borrowed(v_as_2205_, v_j_2206_);
                    v_fvarId_2212_ = lean_ctor_get(v___x_2211_, 0);
                    v___x_2213_ = l_Lean_instBEqFVarId_beq(v_discr_2210_, v_fvarId_2212_);
                    if v___x_2213_ == 0 {
                        v___x_2214_ = lean_unsigned_to_nat(1);
                        v___x_2215_ = lean_nat_add(v_j_2206_, v___x_2214_);
                        lean_dec(v_j_2206_);
                        v_j_2206_ = v___x_2215_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2217_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2217_, 0, v_j_2206_);
                        return v___x_2217_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0___boxed(
    mut v_cases_2218_: *mut LeanObject,
    mut v_as_2219_: *mut LeanObject,
    mut v_j_2220_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2221_: *mut LeanObject = core::ptr::null_mut();
    v_res_2221_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0(v_cases_2218_, v_as_2219_, v_j_2220_);
    lean_dec_ref(v_as_2219_);
    lean_dec_ref(v_cases_2218_);
    return v_res_2221_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(
    mut v_decl_2222_: *mut LeanObject,
    mut v_small_2223_: *mut LeanObject,
    mut v_code_2224_: *mut LeanObject,
    mut v_prefixSize_2225_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2226_: u8 = 0;
    let mut v_k_2227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2228_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_2231_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2235_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2226_ = lean_nat_dec_lt(v_small_2223_, v_prefixSize_2225_);
                if v___x_2226_ == 0 {
                    match lean_obj_tag(v_code_2224_) {
                        0 => {
                            v_k_2227_ = lean_ctor_get(v_code_2224_, 1);
                            v___x_2228_ = lean_unsigned_to_nat(1);
                            v___x_2229_ = lean_nat_add(v_prefixSize_2225_, v___x_2228_);
                            lean_dec(v_prefixSize_2225_);
                            v_code_2224_ = v_k_2227_;
                            v_prefixSize_2225_ = v___x_2229_;
                            state = 0;
                            continue;
                        }
                        4 => {
                            lean_dec(v_prefixSize_2225_);
                            v_cases_2231_ = lean_ctor_get(v_code_2224_, 0);
                            v_params_2232_ = lean_ctor_get(v_decl_2222_, 2);
                            v___x_2233_ = lean_unsigned_to_nat(0);
                            v___x_2234_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go_spec__0(v_cases_2231_, v_params_2232_, v___x_2233_);
                            return v___x_2234_;
                        }
                        _ => {
                            lean_dec(v_prefixSize_2225_);
                            v___x_2235_ = lean_box(0);
                            return v___x_2235_;
                        }
                    }
                } else {
                    lean_dec(v_prefixSize_2225_);
                    v___x_2236_ = lean_box(0);
                    return v___x_2236_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go___boxed(
    mut v_decl_2237_: *mut LeanObject,
    mut v_small_2238_: *mut LeanObject,
    mut v_code_2239_: *mut LeanObject,
    mut v_prefixSize_2240_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2241_: *mut LeanObject = core::ptr::null_mut();
    v_res_2241_ =
        l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(
            v_decl_2237_,
            v_small_2238_,
            v_code_2239_,
            v_prefixSize_2240_,
        );
    lean_dec_ref(v_code_2239_);
    lean_dec(v_small_2238_);
    lean_dec_ref(v_decl_2237_);
    return v_res_2241_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(
    mut v_decl_2242_: *mut LeanObject,
    mut v_a_2243_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_params_2245_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2249_: u8 = 0;
    let mut v___x_2250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2251_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2254_: u8 = 0;
    let mut v_smallThreshold_2255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2256_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2258_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2260_: u8 = 0;
    let mut v_a_2261_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2264_: u8 = 0;
    let mut v___x_2266_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2268_: u8 = 0;
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_params_2245_ = lean_ctor_get(v_decl_2242_, 2);
                v_value_2246_ = lean_ctor_get(v_decl_2242_, 4);
                v___x_2247_ = lean_array_get_size(v_params_2245_);
                v___x_2248_ = lean_unsigned_to_nat(0);
                v___x_2249_ = lean_nat_dec_eq(v___x_2247_, v___x_2248_);
                if v___x_2249_ == 0 {
                    v___x_2250_ = l_Lean_Compiler_LCNF_getConfig___redArg(v_a_2243_);
                    if lean_obj_tag(v___x_2250_) == 0 {
                        v_a_2251_ = lean_ctor_get(v___x_2250_, 0);
                        v_isSharedCheck_2260_ = (!lean_is_exclusive(v___x_2250_)) as u8;
                        if v_isSharedCheck_2260_ == 0 {
                            v___x_2253_ = v___x_2250_;
                            v_isShared_2254_ = v_isSharedCheck_2260_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2251_);
                            lean_dec(v___x_2250_);
                            v___x_2253_ = lean_box(0);
                            v_isShared_2254_ = v_isSharedCheck_2260_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2261_ = lean_ctor_get(v___x_2250_, 0);
                        v_isSharedCheck_2268_ = (!lean_is_exclusive(v___x_2250_)) as u8;
                        if v_isSharedCheck_2268_ == 0 {
                            v___x_2263_ = v___x_2250_;
                            v_isShared_2264_ = v_isSharedCheck_2268_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2261_);
                            lean_dec(v___x_2250_);
                            v___x_2263_ = lean_box(0);
                            v_isShared_2264_ = v_isSharedCheck_2268_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v___x_2269_ = lean_box(0);
                    v___x_2270_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2270_, 0, v___x_2269_);
                    return v___x_2270_;
                }
            }
            1 => {
                v_smallThreshold_2255_ = lean_ctor_get(v_a_2251_, 0);
                lean_inc(v_smallThreshold_2255_);
                lean_dec(v_a_2251_);
                v___x_2256_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_isJpCases_x3f_go(v_decl_2242_, v_smallThreshold_2255_, v_value_2246_, v___x_2248_);
                lean_dec(v_smallThreshold_2255_);
                if v_isShared_2254_ == 0 {
                    lean_ctor_set(v___x_2253_, 0, v___x_2256_);
                    v___x_2258_ = v___x_2253_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2259_, 0, v___x_2256_);
                    v___x_2258_ = v_reuseFailAlloc_2259_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2258_;
            }
            3 => {
                if v_isShared_2264_ == 0 {
                    v___x_2266_ = v___x_2263_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
                    v___x_2266_ = v_reuseFailAlloc_2267_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2266_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg___boxed(
    mut v_decl_2271_: *mut LeanObject,
    mut v_a_2272_: *mut LeanObject,
    mut v_a_2273_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2274_: *mut LeanObject = core::ptr::null_mut();
    v_res_2274_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_2271_, v_a_2272_);
    lean_dec_ref(v_a_2272_);
    lean_dec_ref(v_decl_2271_);
    return v_res_2274_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(
    mut v_decl_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_a_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2281_: *mut LeanObject = core::ptr::null_mut();
    v___x_2281_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_2275_, v_a_2276_);
    return v___x_2281_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___boxed(
    mut v_decl_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
    mut v_a_2286_: *mut LeanObject,
    mut v_a_2287_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2288_: *mut LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Lean_Compiler_LCNF_Simp_isJpCases_x3f(
        v_decl_2282_,
        v_a_2283_,
        v_a_2284_,
        v_a_2285_,
        v_a_2286_,
    );
    lean_dec(v_a_2286_);
    lean_dec_ref(v_a_2285_);
    lean_dec(v_a_2284_);
    lean_dec_ref(v_a_2283_);
    lean_dec_ref(v_decl_2282_);
    return v_res_2288_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0()
-> *mut LeanObject {
    let mut v___x_2289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2291_: *mut LeanObject = core::ptr::null_mut();
    v___x_2289_ = l_Lean_NameSet_empty;
    v___x_2290_ = lean_unsigned_to_nat(0);
    v___x_2291_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2291_, 0, v___x_2290_);
    lean_ctor_set(v___x_2291_, 1, v___x_2289_);
    return v___x_2291_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default() -> *mut LeanObject
{
    let mut v___x_2292_: *mut LeanObject = core::ptr::null_mut();
    v___x_2292_ = lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0_once
        ),
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default___closed__0,
    );
    return v___x_2292_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo() -> *mut LeanObject {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    v___x_2293_ = l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default;
    return v___x_2293_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(
    mut v_init_2305_: *mut LeanObject,
    mut v_x_2306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_2307_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorNames_2311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2306_) == 0 {
                    v_v_2307_ = lean_ctor_get(v_x_2306_, 2);
                    v_l_2308_ = lean_ctor_get(v_x_2306_, 3);
                    v_r_2309_ = lean_ctor_get(v_x_2306_, 4);
                    v___x_2310_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_2305_, v_l_2308_);
                    if lean_obj_tag(v___x_2310_) == 0 {
                        return v___x_2310_;
                    } else {
                        lean_dec_ref_known(v___x_2310_, 1);
                        v_ctorNames_2311_ = lean_ctor_get(v_v_2307_, 1);
                        if lean_obj_tag(v_ctorNames_2311_) == 0 {
                            v___x_2312_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2;
                            return v___x_2312_;
                        } else {
                            v___x_2313_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3;
                            v_init_2305_ = v___x_2313_;
                            v_x_2306_ = v_r_2309_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2315_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2315_, 0, v_init_2305_);
                    return v___x_2315_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___boxed(
    mut v_init_2316_: *mut LeanObject,
    mut v_x_2317_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2318_: *mut LeanObject = core::ptr::null_mut();
    v_res_2318_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v_init_2316_, v_x_2317_);
    lean_dec(v_x_2317_);
    return v_res_2318_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(
    mut v_info_2319_: *mut LeanObject,
) -> u8 {
    let mut v___y_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_2322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: u8 = 0;
    let mut v_val_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2325_: u8 = 0;
    let mut v___x_2326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2328_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2326_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3;
                v___x_2327_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0(v___x_2326_, v_info_2319_);
                v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
                lean_inc(v_a_2328_);
                lean_dec_ref(v___x_2327_);
                v___y_2321_ = v_a_2328_;
                state = 1;
                continue;
            }
            1 => {
                v_fst_2322_ = lean_ctor_get(v___y_2321_, 0);
                lean_inc(v_fst_2322_);
                lean_dec_ref(v___y_2321_);
                if lean_obj_tag(v_fst_2322_) == 0 {
                    v___x_2323_ = 0;
                    return v___x_2323_;
                } else {
                    v_val_2324_ = lean_ctor_get(v_fst_2322_, 0);
                    lean_inc(v_val_2324_);
                    lean_dec_ref_known(v_fst_2322_, 1);
                    v___x_2325_ = (lean_unbox(v_val_2324_) as u8);
                    lean_dec(v_val_2324_);
                    return v___x_2325_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate___boxed(
    mut v_info_2329_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2330_: u8 = 0;
    let mut v_r_2331_: *mut LeanObject = core::ptr::null_mut();
    v_res_2330_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_info_2329_);
    lean_dec(v_info_2329_);
    v_r_2331_ = lean_box((v_res_2330_) as usize);
    return v_r_2331_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(
    mut v_t_2332_: *mut LeanObject,
    mut v_k_2333_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2338_: u8 = 0;
    let mut v___x_2340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2342_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_2332_) == 0 {
                    v_k_2334_ = lean_ctor_get(v_t_2332_, 1);
                    v_v_2335_ = lean_ctor_get(v_t_2332_, 2);
                    v_l_2336_ = lean_ctor_get(v_t_2332_, 3);
                    v_r_2337_ = lean_ctor_get(v_t_2332_, 4);
                    v___x_2338_ =
                        l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_2333_, v_k_2334_);
                    match v___x_2338_ {
                        0 => {
                            v_t_2332_ = v_l_2336_;
                            state = 0;
                            continue;
                        }
                        1 => {
                            lean_inc(v_v_2335_);
                            v___x_2340_ = lean_alloc_ctor(1, 1, (0) as u32);
                            lean_ctor_set(v___x_2340_, 0, v_v_2335_);
                            return v___x_2340_;
                        }
                        _ => {
                            v_t_2332_ = v_r_2337_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_2342_ = lean_box(0);
                    return v___x_2342_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg___boxed(
    mut v_t_2343_: *mut LeanObject,
    mut v_k_2344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2345_: *mut LeanObject = core::ptr::null_mut();
    v_res_2345_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_2343_, v_k_2344_);
    lean_dec(v_k_2344_);
    lean_dec(v_t_2343_);
    return v_res_2345_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(
    mut v_code_2346_: *mut LeanObject,
    mut v_a_2347_: *mut LeanObject,
    mut v_a_2348_: *mut LeanObject,
    mut v_a_2349_: *mut LeanObject,
    mut v_a_2350_: *mut LeanObject,
    mut v_a_2351_: *mut LeanObject,
    mut v_a_2352_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2365_: u8 = 0;
    let mut v___y_2367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2371_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_2373_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2377_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2384_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2390_: u8 = 0;
    let mut v___x_2392_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2394_: u8 = 0;
    let mut v_isSharedCheck_2395_: u8 = 0;
    let mut v_fvarId_2396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_2397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2400_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2402_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2403_: u8 = 0;
    let mut v_paramIdx_2404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorNames_2405_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2408_: u8 = 0;
    let mut v___x_2409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2410_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2415_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2416_: u8 = 0;
    let mut v_val_2417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2422_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2433_: u8 = 0;
    let mut v_a_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2437_: u8 = 0;
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2441_: u8 = 0;
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2446_: u8 = 0;
    let mut v_isSharedCheck_2447_: u8 = 0;
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_2450_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2453_: u8 = 0;
    let mut v_discr_2454_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: u8 = 0;
    let mut v___x_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: u8 = 0;
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2467_: usize = 0;
    let mut v___x_2468_: usize = 0;
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2470_: usize = 0;
    let mut v___x_2471_: usize = 0;
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2473_: u8 = 0;
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2476_: u8 = 0;
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2481_: u8 = 0;
    let mut v_unused_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_2346_) {
                0 => {
                    v_k_2354_ = lean_ctor_get(v_code_2346_, 1);
                    lean_inc_ref(v_k_2354_);
                    lean_dec_ref_known(v_code_2346_, 2);
                    v_code_2346_ = v_k_2354_;
                    state = 0;
                    continue;
                }
                1 => {
                    v_decl_2356_ = lean_ctor_get(v_code_2346_, 0);
                    lean_inc_ref(v_decl_2356_);
                    v_k_2357_ = lean_ctor_get(v_code_2346_, 1);
                    lean_inc_ref(v_k_2357_);
                    lean_dec_ref_known(v_code_2346_, 2);
                    v_value_2358_ = lean_ctor_get(v_decl_2356_, 4);
                    lean_inc_ref(v_value_2358_);
                    lean_dec_ref(v_decl_2356_);
                    v___x_2359_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_2358_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
                    if lean_obj_tag(v___x_2359_) == 0 {
                        lean_dec_ref_known(v___x_2359_, 1);
                        v_code_2346_ = v_k_2357_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_k_2357_);
                        return v___x_2359_;
                    }
                }
                2 => {
                    v_decl_2361_ = lean_ctor_get(v_code_2346_, 0);
                    v_k_2362_ = lean_ctor_get(v_code_2346_, 1);
                    v_isSharedCheck_2395_ = (!lean_is_exclusive(v_code_2346_)) as u8;
                    if v_isSharedCheck_2395_ == 0 {
                        v___x_2364_ = v_code_2346_;
                        v_isShared_2365_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_k_2362_);
                        lean_inc(v_decl_2361_);
                        lean_dec(v_code_2346_);
                        v___x_2364_ = lean_box(0);
                        v_isShared_2365_ = v_isSharedCheck_2395_;
                        state = 1;
                        continue;
                    }
                }
                3 => {
                    v_fvarId_2396_ = lean_ctor_get(v_code_2346_, 0);
                    lean_inc(v_fvarId_2396_);
                    v_args_2397_ = lean_ctor_get(v_code_2346_, 1);
                    lean_inc_ref(v_args_2397_);
                    lean_dec_ref_known(v_code_2346_, 2);
                    v___x_2398_ = lean_st_ref_get(v_a_2347_);
                    v___x_2399_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_2398_, v_fvarId_2396_);
                    lean_dec(v___x_2398_);
                    if lean_obj_tag(v___x_2399_) == 1 {
                        v_val_2400_ = lean_ctor_get(v___x_2399_, 0);
                        v_isSharedCheck_2447_ = (!lean_is_exclusive(v___x_2399_)) as u8;
                        if v_isSharedCheck_2447_ == 0 {
                            v___x_2402_ = v___x_2399_;
                            v_isShared_2403_ = v_isSharedCheck_2447_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_val_2400_);
                            lean_dec(v___x_2399_);
                            v___x_2402_ = lean_box(0);
                            v_isShared_2403_ = v_isSharedCheck_2447_;
                            state = 6;
                            continue;
                        }
                    } else {
                        lean_dec(v___x_2399_);
                        lean_dec_ref(v_args_2397_);
                        lean_dec(v_fvarId_2396_);
                        v___x_2448_ = lean_box(0);
                        v___x_2449_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_2449_, 0, v___x_2448_);
                        return v___x_2449_;
                    }
                }
                4 => {
                    v_cases_2450_ = lean_ctor_get(v_code_2346_, 0);
                    v_isSharedCheck_2473_ = (!lean_is_exclusive(v_code_2346_)) as u8;
                    if v_isSharedCheck_2473_ == 0 {
                        v___x_2452_ = v_code_2346_;
                        v_isShared_2453_ = v_isSharedCheck_2473_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_cases_2450_);
                        lean_dec(v_code_2346_);
                        v___x_2452_ = lean_box(0);
                        v_isShared_2453_ = v_isSharedCheck_2473_;
                        state = 15;
                        continue;
                    }
                }
                _ => {
                    v_isSharedCheck_2481_ = (!lean_is_exclusive(v_code_2346_)) as u8;
                    if v_isSharedCheck_2481_ == 0 {
                        v_unused_2482_ = lean_ctor_get(v_code_2346_, 0);
                        lean_dec(v_unused_2482_);
                        v___x_2475_ = v_code_2346_;
                        v_isShared_2476_ = v_isSharedCheck_2481_;
                        state = 18;
                        continue;
                    } else {
                        lean_dec(v_code_2346_);
                        v___x_2475_ = lean_box(0);
                        v_isShared_2476_ = v_isSharedCheck_2481_;
                        state = 18;
                        continue;
                    }
                }
            },
            1 => {
                v___x_2376_ =
                    l_Lean_Compiler_LCNF_Simp_isJpCases_x3f___redArg(v_decl_2361_, v_a_2349_);
                if lean_obj_tag(v___x_2376_) == 0 {
                    v_a_2377_ = lean_ctor_get(v___x_2376_, 0);
                    lean_inc(v_a_2377_);
                    lean_dec_ref_known(v___x_2376_, 1);
                    if lean_obj_tag(v_a_2377_) == 1 {
                        v_val_2378_ = lean_ctor_get(v_a_2377_, 0);
                        lean_inc(v_val_2378_);
                        lean_dec_ref_known(v_a_2377_, 1);
                        v___x_2379_ = lean_st_ref_take(v_a_2347_);
                        v_fvarId_2380_ = lean_ctor_get(v_decl_2361_, 0);
                        v___x_2381_ = l_Lean_NameSet_empty;
                        if v_isShared_2365_ == 0 {
                            lean_ctor_set_tag(v___x_2364_, 0);
                            lean_ctor_set(v___x_2364_, 1, v___x_2381_);
                            lean_ctor_set(v___x_2364_, 0, v_val_2378_);
                            v___x_2383_ = v___x_2364_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2386_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_val_2378_);
                            lean_ctor_set(v_reuseFailAlloc_2386_, 1, v___x_2381_);
                            v___x_2383_ = v_reuseFailAlloc_2386_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2377_);
                        lean_del_object(v___x_2364_);
                        v___y_2367_ = v_a_2347_;
                        v___y_2368_ = v_a_2348_;
                        v___y_2369_ = v_a_2349_;
                        v___y_2370_ = v_a_2350_;
                        v___y_2371_ = v_a_2351_;
                        v___y_2372_ = v_a_2352_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2364_);
                    lean_dec_ref(v_k_2362_);
                    lean_dec_ref(v_decl_2361_);
                    v_a_2387_ = lean_ctor_get(v___x_2376_, 0);
                    v_isSharedCheck_2394_ = (!lean_is_exclusive(v___x_2376_)) as u8;
                    if v_isSharedCheck_2394_ == 0 {
                        v___x_2389_ = v___x_2376_;
                        v_isShared_2390_ = v_isSharedCheck_2394_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2387_);
                        lean_dec(v___x_2376_);
                        v___x_2389_ = lean_box(0);
                        v_isShared_2390_ = v_isSharedCheck_2394_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v_value_2373_ = lean_ctor_get(v_decl_2361_, 4);
                lean_inc_ref(v_value_2373_);
                lean_dec_ref(v_decl_2361_);
                v___x_2374_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_value_2373_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_, v___y_2371_, v___y_2372_);
                if lean_obj_tag(v___x_2374_) == 0 {
                    lean_dec_ref_known(v___x_2374_, 1);
                    v_code_2346_ = v_k_2362_;
                    v_a_2347_ = v___y_2367_;
                    v_a_2348_ = v___y_2368_;
                    v_a_2349_ = v___y_2369_;
                    v_a_2350_ = v___y_2370_;
                    v_a_2351_ = v___y_2371_;
                    v_a_2352_ = v___y_2372_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_k_2362_);
                    return v___x_2374_;
                }
            }
            3 => {
                lean_inc(v_fvarId_2380_);
                v___x_2384_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_2380_, v___x_2383_, v___x_2379_);
                v___x_2385_ = lean_st_ref_set(v_a_2347_, v___x_2384_);
                v___y_2367_ = v_a_2347_;
                v___y_2368_ = v_a_2348_;
                v___y_2369_ = v_a_2349_;
                v___y_2370_ = v_a_2350_;
                v___y_2371_ = v_a_2351_;
                v___y_2372_ = v_a_2352_;
                state = 2;
                continue;
            }
            4 => {
                if v_isShared_2390_ == 0 {
                    v___x_2392_ = v___x_2389_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2393_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2393_, 0, v_a_2387_);
                    v___x_2392_ = v_reuseFailAlloc_2393_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2392_;
            }
            6 => {
                v_paramIdx_2404_ = lean_ctor_get(v_val_2400_, 0);
                v_ctorNames_2405_ = lean_ctor_get(v_val_2400_, 1);
                v_isSharedCheck_2446_ = (!lean_is_exclusive(v_val_2400_)) as u8;
                if v_isSharedCheck_2446_ == 0 {
                    v___x_2407_ = v_val_2400_;
                    v_isShared_2408_ = v_isSharedCheck_2446_;
                    state = 7;
                    continue;
                } else {
                    lean_inc(v_ctorNames_2405_);
                    lean_inc(v_paramIdx_2404_);
                    lean_dec(v_val_2400_);
                    v___x_2407_ = lean_box(0);
                    v_isShared_2408_ = v_isSharedCheck_2446_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_2409_ = lean_box(0);
                v___x_2410_ = lean_array_get(v___x_2409_, v_args_2397_, v_paramIdx_2404_);
                lean_dec_ref(v_args_2397_);
                if lean_obj_tag(v___x_2410_) == 1 {
                    lean_del_object(v___x_2402_);
                    v_fvarId_2411_ = lean_ctor_get(v___x_2410_, 0);
                    lean_inc(v_fvarId_2411_);
                    lean_dec_ref_known(v___x_2410_, 1);
                    v___x_2412_ = l_Lean_Compiler_LCNF_Simp_findCtorName_x3f___redArg(
                        v_fvarId_2411_,
                        v_a_2348_,
                        v_a_2350_,
                        v_a_2352_,
                    );
                    lean_dec(v_fvarId_2411_);
                    if lean_obj_tag(v___x_2412_) == 0 {
                        v_a_2413_ = lean_ctor_get(v___x_2412_, 0);
                        v_isSharedCheck_2433_ = (!lean_is_exclusive(v___x_2412_)) as u8;
                        if v_isSharedCheck_2433_ == 0 {
                            v___x_2415_ = v___x_2412_;
                            v_isShared_2416_ = v_isSharedCheck_2433_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2413_);
                            lean_dec(v___x_2412_);
                            v___x_2415_ = lean_box(0);
                            v_isShared_2416_ = v_isSharedCheck_2433_;
                            state = 8;
                            continue;
                        }
                    } else {
                        lean_del_object(v___x_2407_);
                        lean_dec(v_ctorNames_2405_);
                        lean_dec(v_paramIdx_2404_);
                        lean_dec(v_fvarId_2396_);
                        v_a_2434_ = lean_ctor_get(v___x_2412_, 0);
                        v_isSharedCheck_2441_ = (!lean_is_exclusive(v___x_2412_)) as u8;
                        if v_isSharedCheck_2441_ == 0 {
                            v___x_2436_ = v___x_2412_;
                            v_isShared_2437_ = v_isSharedCheck_2441_;
                            state = 12;
                            continue;
                        } else {
                            lean_inc(v_a_2434_);
                            lean_dec(v___x_2412_);
                            v___x_2436_ = lean_box(0);
                            v_isShared_2437_ = v_isSharedCheck_2441_;
                            state = 12;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_2410_);
                    lean_del_object(v___x_2407_);
                    lean_dec(v_ctorNames_2405_);
                    lean_dec(v_paramIdx_2404_);
                    lean_dec(v_fvarId_2396_);
                    v___x_2442_ = lean_box(0);
                    if v_isShared_2403_ == 0 {
                        lean_ctor_set_tag(v___x_2402_, 0);
                        lean_ctor_set(v___x_2402_, 0, v___x_2442_);
                        v___x_2444_ = v___x_2402_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_2445_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2445_, 0, v___x_2442_);
                        v___x_2444_ = v_reuseFailAlloc_2445_;
                        state = 14;
                        continue;
                    }
                }
            }
            8 => {
                if lean_obj_tag(v_a_2413_) == 1 {
                    v_val_2417_ = lean_ctor_get(v_a_2413_, 0);
                    lean_inc(v_val_2417_);
                    lean_dec_ref_known(v_a_2413_, 1);
                    v___x_2418_ = lean_st_ref_take(v_a_2347_);
                    v___x_2419_ = l_Lean_NameSet_insert(v_ctorNames_2405_, v_val_2417_);
                    if v_isShared_2408_ == 0 {
                        lean_ctor_set(v___x_2407_, 1, v___x_2419_);
                        v___x_2421_ = v___x_2407_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_paramIdx_2404_);
                        lean_ctor_set(v_reuseFailAlloc_2428_, 1, v___x_2419_);
                        v___x_2421_ = v_reuseFailAlloc_2428_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2413_);
                    lean_del_object(v___x_2407_);
                    lean_dec(v_ctorNames_2405_);
                    lean_dec(v_paramIdx_2404_);
                    lean_dec(v_fvarId_2396_);
                    v___x_2429_ = lean_box(0);
                    if v_isShared_2416_ == 0 {
                        lean_ctor_set(v___x_2415_, 0, v___x_2429_);
                        v___x_2431_ = v___x_2415_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_2432_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2432_, 0, v___x_2429_);
                        v___x_2431_ = v_reuseFailAlloc_2432_;
                        state = 11;
                        continue;
                    }
                }
            }
            9 => {
                v___x_2422_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_2396_, v___x_2421_, v___x_2418_);
                v___x_2423_ = lean_st_ref_set(v_a_2347_, v___x_2422_);
                v___x_2424_ = lean_box(0);
                if v_isShared_2416_ == 0 {
                    lean_ctor_set(v___x_2415_, 0, v___x_2424_);
                    v___x_2426_ = v___x_2415_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2427_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
                    v___x_2426_ = v_reuseFailAlloc_2427_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2426_;
            }
            11 => {
                return v___x_2431_;
            }
            12 => {
                if v_isShared_2437_ == 0 {
                    v___x_2439_ = v___x_2436_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_2440_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2440_, 0, v_a_2434_);
                    v___x_2439_ = v_reuseFailAlloc_2440_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_2439_;
            }
            14 => {
                return v___x_2444_;
            }
            15 => {
                v_discr_2454_ = lean_ctor_get(v_cases_2450_, 2);
                lean_inc(v_discr_2454_);
                v_alts_2455_ = lean_ctor_get(v_cases_2450_, 3);
                lean_inc_ref(v_alts_2455_);
                lean_dec_ref(v_cases_2450_);
                v___x_2456_ = lean_unsigned_to_nat(0);
                v___x_2457_ = lean_array_get_size(v_alts_2455_);
                v___x_2458_ = lean_box(0);
                v___x_2459_ = lean_nat_dec_lt(v___x_2456_, v___x_2457_);
                if v___x_2459_ == 0 {
                    lean_dec_ref(v_alts_2455_);
                    lean_dec(v_discr_2454_);
                    if v_isShared_2453_ == 0 {
                        lean_ctor_set_tag(v___x_2452_, 0);
                        lean_ctor_set(v___x_2452_, 0, v___x_2458_);
                        v___x_2461_ = v___x_2452_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2458_);
                        v___x_2461_ = v_reuseFailAlloc_2462_;
                        state = 16;
                        continue;
                    }
                } else {
                    v___x_2463_ = lean_nat_dec_le(v___x_2457_, v___x_2457_);
                    if v___x_2463_ == 0 {
                        if v___x_2459_ == 0 {
                            lean_dec_ref(v_alts_2455_);
                            lean_dec(v_discr_2454_);
                            if v_isShared_2453_ == 0 {
                                lean_ctor_set_tag(v___x_2452_, 0);
                                lean_ctor_set(v___x_2452_, 0, v___x_2458_);
                                v___x_2465_ = v___x_2452_;
                                state = 17;
                                continue;
                            } else {
                                v_reuseFailAlloc_2466_ = lean_alloc_ctor(0, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_2466_, 0, v___x_2458_);
                                v___x_2465_ = v_reuseFailAlloc_2466_;
                                state = 17;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_2452_);
                            v___x_2467_ = 0usize;
                            v___x_2468_ = lean_usize_of_nat(v___x_2457_);
                            v___x_2469_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_2454_, v_alts_2455_, v___x_2467_, v___x_2468_, v___x_2458_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
                            lean_dec_ref(v_alts_2455_);
                            return v___x_2469_;
                        }
                    } else {
                        lean_del_object(v___x_2452_);
                        v___x_2470_ = 0usize;
                        v___x_2471_ = lean_usize_of_nat(v___x_2457_);
                        v___x_2472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_2454_, v_alts_2455_, v___x_2470_, v___x_2471_, v___x_2458_, v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
                        lean_dec_ref(v_alts_2455_);
                        return v___x_2472_;
                    }
                }
            }
            16 => {
                return v___x_2461_;
            }
            17 => {
                return v___x_2465_;
            }
            18 => {
                v___x_2477_ = lean_box(0);
                if v_isShared_2476_ == 0 {
                    lean_ctor_set_tag(v___x_2475_, 0);
                    lean_ctor_set(v___x_2475_, 0, v___x_2477_);
                    v___x_2479_ = v___x_2475_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_2480_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2480_, 0, v___x_2477_);
                    v___x_2479_ = v_reuseFailAlloc_2480_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_2479_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(
    mut v_discr_2483_: *mut LeanObject,
    mut v_as_2484_: *mut LeanObject,
    mut v_i_2485_: usize,
    mut v_stop_2486_: usize,
    mut v_b_2487_: *mut LeanObject,
    mut v___y_2488_: *mut LeanObject,
    mut v___y_2489_: *mut LeanObject,
    mut v___y_2490_: *mut LeanObject,
    mut v___y_2491_: *mut LeanObject,
    mut v___y_2492_: *mut LeanObject,
    mut v___y_2493_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_2496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2498_: usize = 0;
    let mut v___x_2499_: usize = 0;
    let mut v___x_2501_: u8 = 0;
    let mut v___x_2502_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_2503_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_2504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_2505_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2512_: u8 = 0;
    let mut v___x_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2516_: u8 = 0;
    let mut v_code_2517_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2501_ = lean_usize_dec_eq(v_i_2485_, v_stop_2486_);
                if v___x_2501_ == 0 {
                    v___x_2502_ = lean_array_uget_borrowed(v_as_2484_, v_i_2485_);
                    if lean_obj_tag(v___x_2502_) == 0 {
                        v_ctorName_2503_ = lean_ctor_get(v___x_2502_, 0);
                        v_params_2504_ = lean_ctor_get(v___x_2502_, 1);
                        v_code_2505_ = lean_ctor_get(v___x_2502_, 2);
                        lean_inc_ref(v_params_2504_);
                        lean_inc(v_ctorName_2503_);
                        lean_inc(v_discr_2483_);
                        v___x_2506_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_2483_, v_ctorName_2503_, v_params_2504_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
                        if lean_obj_tag(v___x_2506_) == 0 {
                            v_a_2507_ = lean_ctor_get(v___x_2506_, 0);
                            lean_inc(v_a_2507_);
                            lean_dec_ref_known(v___x_2506_, 1);
                            lean_inc_ref(v_code_2505_);
                            v___x_2508_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_2505_, v___y_2488_, v_a_2507_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
                            lean_dec(v_a_2507_);
                            v___y_2496_ = v___x_2508_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_discr_2483_);
                            v_a_2509_ = lean_ctor_get(v___x_2506_, 0);
                            v_isSharedCheck_2516_ = (!lean_is_exclusive(v___x_2506_)) as u8;
                            if v_isSharedCheck_2516_ == 0 {
                                v___x_2511_ = v___x_2506_;
                                v_isShared_2512_ = v_isSharedCheck_2516_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_2509_);
                                lean_dec(v___x_2506_);
                                v___x_2511_ = lean_box(0);
                                v_isShared_2512_ = v_isSharedCheck_2516_;
                                state = 2;
                                continue;
                            }
                        }
                    } else {
                        v_code_2517_ = lean_ctor_get(v___x_2502_, 0);
                        lean_inc_ref(v_code_2517_);
                        v___x_2518_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_2517_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_, v___y_2492_, v___y_2493_);
                        v___y_2496_ = v___x_2518_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v_discr_2483_);
                    v___x_2519_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2519_, 0, v_b_2487_);
                    return v___x_2519_;
                }
            }
            1 => {
                if lean_obj_tag(v___y_2496_) == 0 {
                    v_a_2497_ = lean_ctor_get(v___y_2496_, 0);
                    lean_inc(v_a_2497_);
                    lean_dec_ref_known(v___y_2496_, 1);
                    v___x_2498_ = 1usize;
                    v___x_2499_ = lean_usize_add(v_i_2485_, v___x_2498_);
                    v_i_2485_ = v___x_2499_;
                    v_b_2487_ = v_a_2497_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_discr_2483_);
                    return v___y_2496_;
                }
            }
            2 => {
                if v_isShared_2512_ == 0 {
                    v___x_2514_ = v___x_2511_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2515_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2515_, 0, v_a_2509_);
                    v___x_2514_ = v_reuseFailAlloc_2515_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2514_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1___boxed(
    mut v_discr_2520_: *mut LeanObject,
    mut v_as_2521_: *mut LeanObject,
    mut v_i_2522_: *mut LeanObject,
    mut v_stop_2523_: *mut LeanObject,
    mut v_b_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2532_: usize = 0;
    let mut v_stop_boxed_2533_: usize = 0;
    let mut v_res_2534_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2532_ = lean_unbox_usize(v_i_2522_);
    lean_dec(v_i_2522_);
    v_stop_boxed_2533_ = lean_unbox_usize(v_stop_2523_);
    lean_dec(v_stop_2523_);
    v_res_2534_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__1(v_discr_2520_, v_as_2521_, v_i_boxed_2532_, v_stop_boxed_2533_, v_b_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
    lean_dec(v___y_2530_);
    lean_dec_ref(v___y_2529_);
    lean_dec(v___y_2528_);
    lean_dec_ref(v___y_2527_);
    lean_dec_ref(v___y_2526_);
    lean_dec(v___y_2525_);
    lean_dec_ref(v_as_2521_);
    return v_res_2534_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go___boxed(
    mut v_code_2535_: *mut LeanObject,
    mut v_a_2536_: *mut LeanObject,
    mut v_a_2537_: *mut LeanObject,
    mut v_a_2538_: *mut LeanObject,
    mut v_a_2539_: *mut LeanObject,
    mut v_a_2540_: *mut LeanObject,
    mut v_a_2541_: *mut LeanObject,
    mut v_a_2542_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2543_: *mut LeanObject = core::ptr::null_mut();
    v_res_2543_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_2535_, v_a_2536_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
    lean_dec(v_a_2541_);
    lean_dec_ref(v_a_2540_);
    lean_dec(v_a_2539_);
    lean_dec_ref(v_a_2538_);
    lean_dec_ref(v_a_2537_);
    lean_dec(v_a_2536_);
    return v_res_2543_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(
    mut v_00_u03b4_2544_: *mut LeanObject,
    mut v_t_2545_: *mut LeanObject,
    mut v_k_2546_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2547_: *mut LeanObject = core::ptr::null_mut();
    v___x_2547_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_t_2545_, v_k_2546_);
    return v___x_2547_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___boxed(
    mut v_00_u03b4_2548_: *mut LeanObject,
    mut v_t_2549_: *mut LeanObject,
    mut v_k_2550_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2551_: *mut LeanObject = core::ptr::null_mut();
    v_res_2551_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0(v_00_u03b4_2548_, v_t_2549_, v_k_2550_);
    lean_dec(v_k_2550_);
    lean_dec(v_t_2549_);
    return v_res_2551_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0() -> *mut LeanObject {
    let mut v___x_2552_: *mut LeanObject = core::ptr::null_mut();
    v___x_2552_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_2552_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1() -> *mut LeanObject {
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut LeanObject = core::ptr::null_mut();
    v___x_2553_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0_once),
        _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__0,
    );
    v___x_2554_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2554_, 0, v___x_2553_);
    return v___x_2554_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2() -> *mut LeanObject {
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2556_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    v___x_2555_ = lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1_once),
        _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__1,
    );
    v___x_2556_ = lean_box(1);
    v___x_2557_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2557_, 0, v___x_2556_);
    lean_ctor_set(v___x_2557_, 1, v___x_2555_);
    return v___x_2557_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(
    mut v_code_2558_: *mut LeanObject,
    mut v_a_2559_: *mut LeanObject,
    mut v_a_2560_: *mut LeanObject,
    mut v_a_2561_: *mut LeanObject,
    mut v_a_2562_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2570_: u8 = 0;
    let mut v___x_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2575_: u8 = 0;
    let mut v_unused_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2584_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2564_ = lean_box(1);
                v___x_2565_ = lean_st_mk_ref(v___x_2564_);
                v___x_2566_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2,
                );
                v___x_2567_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go(v_code_2558_, v___x_2565_, v___x_2566_, v_a_2559_, v_a_2560_, v_a_2561_, v_a_2562_);
                if lean_obj_tag(v___x_2567_) == 0 {
                    v_isSharedCheck_2575_ = (!lean_is_exclusive(v___x_2567_)) as u8;
                    if v_isSharedCheck_2575_ == 0 {
                        v_unused_2576_ = lean_ctor_get(v___x_2567_, 0);
                        lean_dec(v_unused_2576_);
                        v___x_2569_ = v___x_2567_;
                        v_isShared_2570_ = v_isSharedCheck_2575_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_2567_);
                        v___x_2569_ = lean_box(0);
                        v_isShared_2570_ = v_isSharedCheck_2575_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_2565_);
                    v_a_2577_ = lean_ctor_get(v___x_2567_, 0);
                    v_isSharedCheck_2584_ = (!lean_is_exclusive(v___x_2567_)) as u8;
                    if v_isSharedCheck_2584_ == 0 {
                        v___x_2579_ = v___x_2567_;
                        v_isShared_2580_ = v_isSharedCheck_2584_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2577_);
                        lean_dec(v___x_2567_);
                        v___x_2579_ = lean_box(0);
                        v_isShared_2580_ = v_isSharedCheck_2584_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2571_ = lean_st_ref_get(v___x_2565_);
                lean_dec(v___x_2565_);
                if v_isShared_2570_ == 0 {
                    lean_ctor_set(v___x_2569_, 0, v___x_2571_);
                    v___x_2573_ = v___x_2569_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2574_, 0, v___x_2571_);
                    v___x_2573_ = v_reuseFailAlloc_2574_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2573_;
            }
            3 => {
                if v_isShared_2580_ == 0 {
                    v___x_2582_ = v___x_2579_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2583_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_a_2577_);
                    v___x_2582_ = v_reuseFailAlloc_2583_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2582_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___boxed(
    mut v_code_2585_: *mut LeanObject,
    mut v_a_2586_: *mut LeanObject,
    mut v_a_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2591_: *mut LeanObject = core::ptr::null_mut();
    v_res_2591_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(
        v_code_2585_,
        v_a_2586_,
        v_a_2587_,
        v_a_2588_,
        v_a_2589_,
    );
    lean_dec(v_a_2589_);
    lean_dec_ref(v_a_2588_);
    lean_dec(v_a_2587_);
    lean_dec_ref(v_a_2586_);
    return v_res_2591_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_2592_: *mut LeanObject = core::ptr::null_mut();
    v___x_2592_ = l_Array_instInhabited(lean_box(0));
    return v___x_2592_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1()
-> *mut LeanObject {
    let mut v___x_2593_: u8 = 0;
    let mut v___x_2594_: *mut LeanObject = core::ptr::null_mut();
    v___x_2593_ = 0;
    v___x_2594_ = l_Lean_Compiler_LCNF_instInhabitedCases_default__1(v___x_2593_);
    return v___x_2594_;
}
pub unsafe fn l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(
    mut v_msg_2595_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    v___x_2596_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__0);
    v___x_2597_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1_once), _init_l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0___closed__1);
    v___x_2598_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_2598_, 0, v___x_2596_);
    lean_ctor_set(v___x_2598_, 1, v___x_2597_);
    v___x_2599_ = lean_panic_fn_borrowed(v___x_2598_, v_msg_2595_);
    lean_dec_ref_known(v___x_2598_, 2);
    return v___x_2599_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3()
-> *mut LeanObject {
    let mut v___x_2603_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2606_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    v___x_2603_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__2;
    v___x_2604_ = lean_unsigned_to_nat(11);
    v___x_2605_ = lean_unsigned_to_nat(100);
    v___x_2606_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__1;
    v___x_2607_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__0;
    v___x_2608_ = l_mkPanicMessageWithDecl(
        v___x_2607_,
        v___x_2606_,
        v___x_2605_,
        v___x_2604_,
        v___x_2603_,
    );
    return v___x_2608_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(
    mut v_code_2609_: *mut LeanObject,
    mut v_decls_2610_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_2611_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2614_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cases_2616_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2617_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2618_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_2609_) {
                0 => {
                    v_decl_2611_ = lean_ctor_get(v_code_2609_, 0);
                    v_k_2612_ = lean_ctor_get(v_code_2609_, 1);
                    lean_inc_ref(v_decl_2611_);
                    v___x_2613_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2613_, 0, v_decl_2611_);
                    v___x_2614_ = lean_array_push(v_decls_2610_, v___x_2613_);
                    v_code_2609_ = v_k_2612_;
                    v_decls_2610_ = v___x_2614_;
                    state = 0;
                    continue;
                }
                4 => {
                    v_cases_2616_ = lean_ctor_get(v_code_2609_, 0);
                    lean_inc_ref(v_cases_2616_);
                    v___x_2617_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2617_, 0, v_decls_2610_);
                    lean_ctor_set(v___x_2617_, 1, v_cases_2616_);
                    return v___x_2617_;
                }
                _ => {
                    lean_dec_ref(v_decls_2610_);
                    v___x_2618_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3_once), _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___closed__3);
                    v___x_2619_ = l_panic___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go_spec__0(v___x_2618_);
                    return v___x_2619_;
                }
            },
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go___boxed(
    mut v_code_2620_: *mut LeanObject,
    mut v_decls_2621_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2622_: *mut LeanObject = core::ptr::null_mut();
    v_res_2622_ =
        l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(
            v_code_2620_,
            v_decls_2621_,
        );
    lean_dec_ref(v_code_2620_);
    return v_res_2622_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(
    mut v_code_2625_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut LeanObject = core::ptr::null_mut();
    v___x_2626_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___closed__0;
    v___x_2627_ =
        l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases_go(
            v_code_2625_,
            v___x_2626_,
        );
    return v___x_2627_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases___boxed(
    mut v_code_2628_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2629_: *mut LeanObject = core::ptr::null_mut();
    v_res_2629_ =
        l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(
            v_code_2628_,
        );
    lean_dec_ref(v_code_2628_);
    return v_res_2629_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(
    mut v_singleton_2630_: *mut LeanObject,
    mut v_as_2631_: *mut LeanObject,
    mut v_i_2632_: usize,
    mut v_stop_2633_: usize,
) -> u8 {
    let mut v___x_2634_: u8 = 0;
    let mut v___x_2635_: u8 = 0;
    let mut v___x_2636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: u8 = 0;
    let mut v___x_2638_: usize = 0;
    let mut v___x_2639_: usize = 0;
    let mut v___x_2641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2634_ = lean_usize_dec_eq(v_i_2632_, v_stop_2633_);
                if v___x_2634_ == 0 {
                    v___x_2635_ = 0;
                    v___x_2636_ = lean_array_uget_borrowed(v_as_2631_, v_i_2632_);
                    v___x_2637_ = l_Lean_Compiler_LCNF_CodeDecl_dependsOn(
                        v___x_2635_,
                        v___x_2636_,
                        v_singleton_2630_,
                    );
                    if v___x_2637_ == 0 {
                        v___x_2638_ = 1usize;
                        v___x_2639_ = lean_usize_add(v_i_2632_, v___x_2638_);
                        v_i_2632_ = v___x_2639_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2637_;
                    }
                } else {
                    v___x_2641_ = 0;
                    return v___x_2641_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3___boxed(
    mut v_singleton_2642_: *mut LeanObject,
    mut v_as_2643_: *mut LeanObject,
    mut v_i_2644_: *mut LeanObject,
    mut v_stop_2645_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_i_boxed_2646_: usize = 0;
    let mut v_stop_boxed_2647_: usize = 0;
    let mut v_res_2648_: u8 = 0;
    let mut v_r_2649_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2646_ = lean_unbox_usize(v_i_2644_);
    lean_dec(v_i_2644_);
    v_stop_boxed_2647_ = lean_unbox_usize(v_stop_2645_);
    lean_dec(v_stop_2645_);
    v_res_2648_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_2642_, v_as_2643_, v_i_boxed_2646_, v_stop_boxed_2647_);
    lean_dec_ref(v_as_2643_);
    lean_dec(v_singleton_2642_);
    v_r_2649_ = lean_box((v_res_2648_) as usize);
    return v_r_2649_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(
    mut v_sz_2650_: usize,
    mut v_i_2651_: usize,
    mut v_bs_2652_: *mut LeanObject,
    mut v___y_2653_: u8,
    mut v___y_2654_: *mut LeanObject,
    mut v___y_2655_: *mut LeanObject,
    mut v___y_2656_: *mut LeanObject,
    mut v___y_2657_: *mut LeanObject,
    mut v___y_2658_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2660_: u8 = 0;
    let mut v___x_2661_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: u8 = 0;
    let mut v_v_2663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2665_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2668_: usize = 0;
    let mut v___x_2669_: usize = 0;
    let mut v___x_2670_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2675_: u8 = 0;
    let mut v___x_2677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2660_ = lean_usize_dec_lt(v_i_2651_, v_sz_2650_);
                if v___x_2660_ == 0 {
                    v___x_2661_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2661_, 0, v_bs_2652_);
                    return v___x_2661_;
                } else {
                    v___x_2662_ = 0;
                    v_v_2663_ = lean_array_uget_borrowed(v_bs_2652_, v_i_2651_);
                    lean_inc(v_v_2663_);
                    v___x_2664_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
                        v___x_2662_,
                        v_v_2663_,
                        v___y_2653_,
                        v___y_2654_,
                        v___y_2655_,
                        v___y_2656_,
                        v___y_2657_,
                        v___y_2658_,
                    );
                    if lean_obj_tag(v___x_2664_) == 0 {
                        v_a_2665_ = lean_ctor_get(v___x_2664_, 0);
                        lean_inc(v_a_2665_);
                        lean_dec_ref_known(v___x_2664_, 1);
                        v___x_2666_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2667_ = lean_array_uset(v_bs_2652_, v_i_2651_, v___x_2666_);
                        v___x_2668_ = 1usize;
                        v___x_2669_ = lean_usize_add(v_i_2651_, v___x_2668_);
                        v___x_2670_ = lean_array_uset(v_bs_x27_2667_, v_i_2651_, v_a_2665_);
                        v_i_2651_ = v___x_2669_;
                        v_bs_2652_ = v___x_2670_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2652_);
                        v_a_2672_ = lean_ctor_get(v___x_2664_, 0);
                        v_isSharedCheck_2679_ = (!lean_is_exclusive(v___x_2664_)) as u8;
                        if v_isSharedCheck_2679_ == 0 {
                            v___x_2674_ = v___x_2664_;
                            v_isShared_2675_ = v_isSharedCheck_2679_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2672_);
                            lean_dec(v___x_2664_);
                            v___x_2674_ = lean_box(0);
                            v_isShared_2675_ = v_isSharedCheck_2679_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2675_ == 0 {
                    v___x_2677_ = v___x_2674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
                    v___x_2677_ = v_reuseFailAlloc_2678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0___boxed(
    mut v_sz_2680_: *mut LeanObject,
    mut v_i_2681_: *mut LeanObject,
    mut v_bs_2682_: *mut LeanObject,
    mut v___y_2683_: *mut LeanObject,
    mut v___y_2684_: *mut LeanObject,
    mut v___y_2685_: *mut LeanObject,
    mut v___y_2686_: *mut LeanObject,
    mut v___y_2687_: *mut LeanObject,
    mut v___y_2688_: *mut LeanObject,
    mut v___y_2689_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2690_: usize = 0;
    let mut v_i_boxed_2691_: usize = 0;
    let mut v___y_5526__boxed_2692_: u8 = 0;
    let mut v_res_2693_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2690_ = lean_unbox_usize(v_sz_2680_);
    lean_dec(v_sz_2680_);
    v_i_boxed_2691_ = lean_unbox_usize(v_i_2681_);
    lean_dec(v_i_2681_);
    v___y_5526__boxed_2692_ = (lean_unbox(v___y_2683_) as u8);
    v_res_2693_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_boxed_2690_, v_i_boxed_2691_, v_bs_2682_, v___y_5526__boxed_2692_, v___y_2684_, v___y_2685_, v___y_2686_, v___y_2687_, v___y_2688_);
    lean_dec(v___y_2688_);
    lean_dec_ref(v___y_2687_);
    lean_dec(v___y_2686_);
    lean_dec_ref(v___y_2685_);
    lean_dec(v___y_2684_);
    return v_res_2693_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(
    mut v_fields_2694_: *mut LeanObject,
    mut v_____r_2695_: *mut LeanObject,
    mut v_paramsNew_2696_: *mut LeanObject,
    mut v___y_2697_: u8,
    mut v___y_2698_: *mut LeanObject,
    mut v___y_2699_: *mut LeanObject,
    mut v___y_2700_: *mut LeanObject,
    mut v___y_2701_: *mut LeanObject,
    mut v___y_2702_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_2704_: usize = 0;
    let mut v___x_2705_: usize = 0;
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2710_: u8 = 0;
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2716_: u8 = 0;
    let mut v_a_2717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2720_: u8 = 0;
    let mut v___x_2722_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2723_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_sz_2704_ = lean_array_size(v_fields_2694_);
                v___x_2705_ = 0usize;
                v___x_2706_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__0(v_sz_2704_, v___x_2705_, v_fields_2694_, v___y_2697_, v___y_2698_, v___y_2699_, v___y_2700_, v___y_2701_, v___y_2702_);
                if lean_obj_tag(v___x_2706_) == 0 {
                    v_a_2707_ = lean_ctor_get(v___x_2706_, 0);
                    v_isSharedCheck_2716_ = (!lean_is_exclusive(v___x_2706_)) as u8;
                    if v_isSharedCheck_2716_ == 0 {
                        v___x_2709_ = v___x_2706_;
                        v_isShared_2710_ = v_isSharedCheck_2716_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2707_);
                        lean_dec(v___x_2706_);
                        v___x_2709_ = lean_box(0);
                        v_isShared_2710_ = v_isSharedCheck_2716_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_paramsNew_2696_);
                    v_a_2717_ = lean_ctor_get(v___x_2706_, 0);
                    v_isSharedCheck_2724_ = (!lean_is_exclusive(v___x_2706_)) as u8;
                    if v_isSharedCheck_2724_ == 0 {
                        v___x_2719_ = v___x_2706_;
                        v_isShared_2720_ = v_isSharedCheck_2724_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2717_);
                        lean_dec(v___x_2706_);
                        v___x_2719_ = lean_box(0);
                        v_isShared_2720_ = v_isSharedCheck_2724_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2711_ = l_Array_append___redArg(v_paramsNew_2696_, v_a_2707_);
                lean_dec(v_a_2707_);
                v___x_2712_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_2712_, 0, v___x_2711_);
                if v_isShared_2710_ == 0 {
                    lean_ctor_set(v___x_2709_, 0, v___x_2712_);
                    v___x_2714_ = v___x_2709_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2715_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
                    v___x_2714_ = v_reuseFailAlloc_2715_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2714_;
            }
            3 => {
                if v_isShared_2720_ == 0 {
                    v___x_2722_ = v___x_2719_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2723_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2723_, 0, v_a_2717_);
                    v___x_2722_ = v_reuseFailAlloc_2723_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2722_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0___boxed(
    mut v_fields_2725_: *mut LeanObject,
    mut v_____r_2726_: *mut LeanObject,
    mut v_paramsNew_2727_: *mut LeanObject,
    mut v___y_2728_: *mut LeanObject,
    mut v___y_2729_: *mut LeanObject,
    mut v___y_2730_: *mut LeanObject,
    mut v___y_2731_: *mut LeanObject,
    mut v___y_2732_: *mut LeanObject,
    mut v___y_2733_: *mut LeanObject,
    mut v___y_2734_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5584__boxed_2735_: u8 = 0;
    let mut v_res_2736_: *mut LeanObject = core::ptr::null_mut();
    v___y_5584__boxed_2735_ = (lean_unbox(v___y_2728_) as u8);
    v_res_2736_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_2725_, v_____r_2726_, v_paramsNew_2727_, v___y_5584__boxed_2735_, v___y_2729_, v___y_2730_, v___y_2731_, v___y_2732_, v___y_2733_);
    lean_dec(v___y_2733_);
    lean_dec_ref(v___y_2732_);
    lean_dec(v___y_2731_);
    lean_dec_ref(v___y_2730_);
    lean_dec(v___y_2729_);
    return v_res_2736_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(
    mut v_upperBound_2737_: *mut LeanObject,
    mut v_params_2738_: *mut LeanObject,
    mut v_targetParamIdx_2739_: *mut LeanObject,
    mut v___y_2740_: u8,
    mut v_fields_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
    mut v_b_2743_: *mut LeanObject,
    mut v___y_2744_: u8,
    mut v___y_2745_: *mut LeanObject,
    mut v___y_2746_: *mut LeanObject,
    mut v___y_2747_: *mut LeanObject,
    mut v___y_2748_: *mut LeanObject,
    mut v___y_2749_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2761_: u8 = 0;
    let mut v_a_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2765_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2766_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2767_: u8 = 0;
    let mut v_a_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2771_: u8 = 0;
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2775_: u8 = 0;
    let mut v___x_2776_: u8 = 0;
    let mut v___x_2777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2778_: u8 = 0;
    let mut v___x_2779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2780_: u8 = 0;
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2784_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2787_: u8 = 0;
    let mut v___x_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2791_: u8 = 0;
    let mut v___x_2792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2802_: u8 = 0;
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2806_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2776_ = lean_nat_dec_lt(v_a_2742_, v_upperBound_2737_);
                if v___x_2776_ == 0 {
                    lean_dec(v_a_2742_);
                    lean_dec_ref(v_fields_2741_);
                    v___x_2777_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2777_, 0, v_b_2743_);
                    return v___x_2777_;
                } else {
                    v___x_2778_ = 0;
                    v___x_2779_ = lean_array_fget_borrowed(v_params_2738_, v_a_2742_);
                    v___x_2780_ = lean_nat_dec_eq(v_targetParamIdx_2739_, v_a_2742_);
                    if v___x_2780_ == 0 {
                        lean_inc(v___x_2779_);
                        v___x_2781_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
                            v___x_2778_,
                            v___x_2779_,
                            v___y_2744_,
                            v___y_2745_,
                            v___y_2746_,
                            v___y_2747_,
                            v___y_2748_,
                            v___y_2749_,
                        );
                        if lean_obj_tag(v___x_2781_) == 0 {
                            v_a_2782_ = lean_ctor_get(v___x_2781_, 0);
                            lean_inc(v_a_2782_);
                            lean_dec_ref_known(v___x_2781_, 1);
                            v___x_2783_ = lean_array_push(v_b_2743_, v_a_2782_);
                            v_a_2752_ = v___x_2783_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_b_2743_);
                            lean_dec(v_a_2742_);
                            lean_dec_ref(v_fields_2741_);
                            v_a_2784_ = lean_ctor_get(v___x_2781_, 0);
                            v_isSharedCheck_2791_ = (!lean_is_exclusive(v___x_2781_)) as u8;
                            if v_isSharedCheck_2791_ == 0 {
                                v___x_2786_ = v___x_2781_;
                                v_isShared_2787_ = v_isSharedCheck_2791_;
                                state = 7;
                                continue;
                            } else {
                                lean_inc(v_a_2784_);
                                lean_dec(v___x_2781_);
                                v___x_2786_ = lean_box(0);
                                v_isShared_2787_ = v_isSharedCheck_2791_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        if v___y_2740_ == 0 {
                            v___x_2792_ = lean_box(0);
                            lean_inc_ref(v_fields_2741_);
                            v___x_2793_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_2741_, v___x_2792_, v_b_2743_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
                            v___y_2757_ = v___x_2793_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v___x_2779_);
                            v___x_2794_ = l_Lean_Compiler_LCNF_Internalize_internalizeParam(
                                v___x_2778_,
                                v___x_2779_,
                                v___y_2744_,
                                v___y_2745_,
                                v___y_2746_,
                                v___y_2747_,
                                v___y_2748_,
                                v___y_2749_,
                            );
                            if lean_obj_tag(v___x_2794_) == 0 {
                                v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
                                lean_inc(v_a_2795_);
                                lean_dec_ref_known(v___x_2794_, 1);
                                v___x_2796_ = lean_array_push(v_b_2743_, v_a_2795_);
                                v___x_2797_ = lean_box(0);
                                lean_inc_ref(v_fields_2741_);
                                v___x_2798_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___lam__0(v_fields_2741_, v___x_2797_, v___x_2796_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_, v___y_2748_, v___y_2749_);
                                v___y_2757_ = v___x_2798_;
                                state = 2;
                                continue;
                            } else {
                                lean_dec_ref(v_b_2743_);
                                lean_dec(v_a_2742_);
                                lean_dec_ref(v_fields_2741_);
                                v_a_2799_ = lean_ctor_get(v___x_2794_, 0);
                                v_isSharedCheck_2806_ = (!lean_is_exclusive(v___x_2794_)) as u8;
                                if v_isSharedCheck_2806_ == 0 {
                                    v___x_2801_ = v___x_2794_;
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_2799_);
                                    lean_dec(v___x_2794_);
                                    v___x_2801_ = lean_box(0);
                                    v_isShared_2802_ = v_isSharedCheck_2806_;
                                    state = 9;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2753_ = lean_unsigned_to_nat(1);
                v___x_2754_ = lean_nat_add(v_a_2742_, v___x_2753_);
                lean_dec(v_a_2742_);
                v_a_2742_ = v___x_2754_;
                v_b_2743_ = v_a_2752_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_2757_) == 0 {
                    v_a_2758_ = lean_ctor_get(v___y_2757_, 0);
                    v_isSharedCheck_2767_ = (!lean_is_exclusive(v___y_2757_)) as u8;
                    if v_isSharedCheck_2767_ == 0 {
                        v___x_2760_ = v___y_2757_;
                        v_isShared_2761_ = v_isSharedCheck_2767_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2758_);
                        lean_dec(v___y_2757_);
                        v___x_2760_ = lean_box(0);
                        v_isShared_2761_ = v_isSharedCheck_2767_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_2742_);
                    lean_dec_ref(v_fields_2741_);
                    v_a_2768_ = lean_ctor_get(v___y_2757_, 0);
                    v_isSharedCheck_2775_ = (!lean_is_exclusive(v___y_2757_)) as u8;
                    if v_isSharedCheck_2775_ == 0 {
                        v___x_2770_ = v___y_2757_;
                        v_isShared_2771_ = v_isSharedCheck_2775_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2768_);
                        lean_dec(v___y_2757_);
                        v___x_2770_ = lean_box(0);
                        v_isShared_2771_ = v_isSharedCheck_2775_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if lean_obj_tag(v_a_2758_) == 0 {
                    lean_dec(v_a_2742_);
                    lean_dec_ref(v_fields_2741_);
                    v_a_2762_ = lean_ctor_get(v_a_2758_, 0);
                    lean_inc(v_a_2762_);
                    lean_dec_ref_known(v_a_2758_, 1);
                    if v_isShared_2761_ == 0 {
                        lean_ctor_set(v___x_2760_, 0, v_a_2762_);
                        v___x_2764_ = v___x_2760_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2765_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2765_, 0, v_a_2762_);
                        v___x_2764_ = v_reuseFailAlloc_2765_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2760_);
                    v_a_2766_ = lean_ctor_get(v_a_2758_, 0);
                    lean_inc(v_a_2766_);
                    lean_dec_ref_known(v_a_2758_, 1);
                    v_a_2752_ = v_a_2766_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_2764_;
            }
            5 => {
                if v_isShared_2771_ == 0 {
                    v___x_2773_ = v___x_2770_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2774_, 0, v_a_2768_);
                    v___x_2773_ = v_reuseFailAlloc_2774_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2773_;
            }
            7 => {
                if v_isShared_2787_ == 0 {
                    v___x_2789_ = v___x_2786_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2790_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2790_, 0, v_a_2784_);
                    v___x_2789_ = v_reuseFailAlloc_2790_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2789_;
            }
            9 => {
                if v_isShared_2802_ == 0 {
                    v___x_2804_ = v___x_2801_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2805_, 0, v_a_2799_);
                    v___x_2804_ = v_reuseFailAlloc_2805_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg___boxed(
    mut v_upperBound_2807_: *mut LeanObject,
    mut v_params_2808_: *mut LeanObject,
    mut v_targetParamIdx_2809_: *mut LeanObject,
    mut v___y_2810_: *mut LeanObject,
    mut v_fields_2811_: *mut LeanObject,
    mut v_a_2812_: *mut LeanObject,
    mut v_b_2813_: *mut LeanObject,
    mut v___y_2814_: *mut LeanObject,
    mut v___y_2815_: *mut LeanObject,
    mut v___y_2816_: *mut LeanObject,
    mut v___y_2817_: *mut LeanObject,
    mut v___y_2818_: *mut LeanObject,
    mut v___y_2819_: *mut LeanObject,
    mut v___y_2820_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_5648__boxed_2821_: u8 = 0;
    let mut v___y_5649__boxed_2822_: u8 = 0;
    let mut v_res_2823_: *mut LeanObject = core::ptr::null_mut();
    v___y_5648__boxed_2821_ = (lean_unbox(v___y_2810_) as u8);
    v___y_5649__boxed_2822_ = (lean_unbox(v___y_2814_) as u8);
    v_res_2823_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_2807_, v_params_2808_, v_targetParamIdx_2809_, v___y_5648__boxed_2821_, v_fields_2811_, v_a_2812_, v_b_2813_, v___y_5649__boxed_2822_, v___y_2815_, v___y_2816_, v___y_2817_, v___y_2818_, v___y_2819_);
    lean_dec(v___y_2819_);
    lean_dec_ref(v___y_2818_);
    lean_dec(v___y_2817_);
    lean_dec_ref(v___y_2816_);
    lean_dec(v___y_2815_);
    lean_dec(v_targetParamIdx_2809_);
    lean_dec_ref(v_params_2808_);
    lean_dec(v_upperBound_2807_);
    return v_res_2823_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(
    mut v_sz_2824_: usize,
    mut v_i_2825_: usize,
    mut v_bs_2826_: *mut LeanObject,
    mut v___y_2827_: u8,
    mut v___y_2828_: *mut LeanObject,
    mut v___y_2829_: *mut LeanObject,
    mut v___y_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2834_: u8 = 0;
    let mut v___x_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2836_: u8 = 0;
    let mut v_v_2837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2839_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2842_: usize = 0;
    let mut v___x_2843_: usize = 0;
    let mut v___x_2844_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2849_: u8 = 0;
    let mut v___x_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2853_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2834_ = lean_usize_dec_lt(v_i_2825_, v_sz_2824_);
                if v___x_2834_ == 0 {
                    v___x_2835_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2835_, 0, v_bs_2826_);
                    return v___x_2835_;
                } else {
                    v___x_2836_ = 0;
                    v_v_2837_ = lean_array_uget_borrowed(v_bs_2826_, v_i_2825_);
                    lean_inc(v_v_2837_);
                    v___x_2838_ = l_Lean_Compiler_LCNF_Internalize_internalizeCodeDecl(
                        v___x_2836_,
                        v_v_2837_,
                        v___y_2827_,
                        v___y_2828_,
                        v___y_2829_,
                        v___y_2830_,
                        v___y_2831_,
                        v___y_2832_,
                    );
                    if lean_obj_tag(v___x_2838_) == 0 {
                        v_a_2839_ = lean_ctor_get(v___x_2838_, 0);
                        lean_inc(v_a_2839_);
                        lean_dec_ref_known(v___x_2838_, 1);
                        v___x_2840_ = lean_unsigned_to_nat(0);
                        v_bs_x27_2841_ = lean_array_uset(v_bs_2826_, v_i_2825_, v___x_2840_);
                        v___x_2842_ = 1usize;
                        v___x_2843_ = lean_usize_add(v_i_2825_, v___x_2842_);
                        v___x_2844_ = lean_array_uset(v_bs_x27_2841_, v_i_2825_, v_a_2839_);
                        v_i_2825_ = v___x_2843_;
                        v_bs_2826_ = v___x_2844_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec_ref(v_bs_2826_);
                        v_a_2846_ = lean_ctor_get(v___x_2838_, 0);
                        v_isSharedCheck_2853_ = (!lean_is_exclusive(v___x_2838_)) as u8;
                        if v_isSharedCheck_2853_ == 0 {
                            v___x_2848_ = v___x_2838_;
                            v_isShared_2849_ = v_isSharedCheck_2853_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2846_);
                            lean_dec(v___x_2838_);
                            v___x_2848_ = lean_box(0);
                            v_isShared_2849_ = v_isSharedCheck_2853_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2849_ == 0 {
                    v___x_2851_ = v___x_2848_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2852_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2852_, 0, v_a_2846_);
                    v___x_2851_ = v_reuseFailAlloc_2852_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2851_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1___boxed(
    mut v_sz_2854_: *mut LeanObject,
    mut v_i_2855_: *mut LeanObject,
    mut v_bs_2856_: *mut LeanObject,
    mut v___y_2857_: *mut LeanObject,
    mut v___y_2858_: *mut LeanObject,
    mut v___y_2859_: *mut LeanObject,
    mut v___y_2860_: *mut LeanObject,
    mut v___y_2861_: *mut LeanObject,
    mut v___y_2862_: *mut LeanObject,
    mut v___y_2863_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2864_: usize = 0;
    let mut v_i_boxed_2865_: usize = 0;
    let mut v___y_5786__boxed_2866_: u8 = 0;
    let mut v_res_2867_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2864_ = lean_unbox_usize(v_sz_2854_);
    lean_dec(v_sz_2854_);
    v_i_boxed_2865_ = lean_unbox_usize(v_i_2855_);
    lean_dec(v_i_2855_);
    v___y_5786__boxed_2866_ = (lean_unbox(v___y_2857_) as u8);
    v_res_2867_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_boxed_2864_, v_i_boxed_2865_, v_bs_2856_, v___y_5786__boxed_2866_, v___y_2858_, v___y_2859_, v___y_2860_, v___y_2861_, v___y_2862_);
    lean_dec(v___y_2862_);
    lean_dec_ref(v___y_2861_);
    lean_dec(v___y_2860_);
    lean_dec_ref(v___y_2859_);
    lean_dec(v___y_2858_);
    return v_res_2867_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0()
-> *mut LeanObject {
    let mut v___x_2868_: u8 = 0;
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    v___x_2868_ = 0;
    v___x_2869_ = l_Lean_Compiler_LCNF_instInhabitedParam_default(v___x_2868_);
    return v___x_2869_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(
    mut v_decls_2875_: *mut LeanObject,
    mut v_params_2876_: *mut LeanObject,
    mut v_targetParamIdx_2877_: *mut LeanObject,
    mut v_fields_2878_: *mut LeanObject,
    mut v_k_2879_: *mut LeanObject,
    mut v_default_2880_: u8,
    mut v_a_2881_: u8,
    mut v_a_2882_: *mut LeanObject,
    mut v_a_2883_: *mut LeanObject,
    mut v_a_2884_: *mut LeanObject,
    mut v_a_2885_: *mut LeanObject,
    mut v_a_2886_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2888_: u8 = 0;
    let mut v___x_2889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramsNew_2893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2895_: u8 = 0;
    let mut v___x_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2897_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2899_: usize = 0;
    let mut v___x_2900_: usize = 0;
    let mut v___x_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2911_: u8 = 0;
    let mut v___x_2912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2916_: u8 = 0;
    let mut v_a_2917_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2920_: u8 = 0;
    let mut v___x_2922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2924_: u8 = 0;
    let mut v_a_2925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2928_: u8 = 0;
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2931_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2932_: u8 = 0;
    let mut v_a_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2936_: u8 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2940_: u8 = 0;
    let mut v_a_2941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2944_: u8 = 0;
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2948_: u8 = 0;
    let mut v_singleton_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2950_: u8 = 0;
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2952_: u8 = 0;
    let mut v___x_2953_: usize = 0;
    let mut v___x_2954_: usize = 0;
    let mut v___x_2955_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2888_ = 0;
                v___x_2889_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__0);
                v___x_2890_ =
                    lean_array_get_borrowed(v___x_2889_, v_params_2876_, v_targetParamIdx_2877_);
                v_fvarId_2891_ = lean_ctor_get(v___x_2890_, 0);
                v___x_2892_ = lean_unsigned_to_nat(0);
                v_paramsNew_2893_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1;
                lean_inc(v_fvarId_2891_);
                v_singleton_2949_ = l_Lean_instSingletonFVarIdFVarIdSet___lam__0(v_fvarId_2891_);
                v___x_2950_ =
                    l_Lean_Compiler_LCNF_Code_dependsOn(v___x_2888_, v_k_2879_, v_singleton_2949_);
                if v___x_2950_ == 0 {
                    v___x_2951_ = lean_array_get_size(v_decls_2875_);
                    v___x_2952_ = lean_nat_dec_lt(v___x_2892_, v___x_2951_);
                    if v___x_2952_ == 0 {
                        lean_dec(v_singleton_2949_);
                        v___y_2895_ = v___x_2950_;
                        state = 1;
                        continue;
                    } else {
                        if v___x_2952_ == 0 {
                            lean_dec(v_singleton_2949_);
                            v___y_2895_ = v___x_2950_;
                            state = 1;
                            continue;
                        } else {
                            v___x_2953_ = 0usize;
                            v___x_2954_ = lean_usize_of_nat(v___x_2951_);
                            v___x_2955_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__3(v_singleton_2949_, v_decls_2875_, v___x_2953_, v___x_2954_);
                            lean_dec(v_singleton_2949_);
                            v___y_2895_ = v___x_2955_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_singleton_2949_);
                    v___y_2895_ = v___x_2950_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2896_ = lean_array_get_size(v_params_2876_);
                v___x_2897_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v___x_2896_, v_params_2876_, v_targetParamIdx_2877_, v___y_2895_, v_fields_2878_, v___x_2892_, v_paramsNew_2893_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
                if lean_obj_tag(v___x_2897_) == 0 {
                    v_a_2898_ = lean_ctor_get(v___x_2897_, 0);
                    lean_inc(v_a_2898_);
                    lean_dec_ref_known(v___x_2897_, 1);
                    v_sz_2899_ = lean_array_size(v_decls_2875_);
                    v___x_2900_ = 0usize;
                    v___x_2901_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__1(v_sz_2899_, v___x_2900_, v_decls_2875_, v_a_2881_, v_a_2882_, v_a_2883_, v_a_2884_, v_a_2885_, v_a_2886_);
                    if lean_obj_tag(v___x_2901_) == 0 {
                        v_a_2902_ = lean_ctor_get(v___x_2901_, 0);
                        lean_inc(v_a_2902_);
                        lean_dec_ref_known(v___x_2901_, 1);
                        v___x_2903_ = l_Lean_Compiler_LCNF_Internalize_internalizeCode(
                            v___x_2888_,
                            v_k_2879_,
                            v_a_2881_,
                            v_a_2882_,
                            v_a_2883_,
                            v_a_2884_,
                            v_a_2885_,
                            v_a_2886_,
                        );
                        if lean_obj_tag(v___x_2903_) == 0 {
                            v_a_2904_ = lean_ctor_get(v___x_2903_, 0);
                            lean_inc(v_a_2904_);
                            lean_dec_ref_known(v___x_2903_, 1);
                            v___x_2905_ = l_Lean_Compiler_LCNF_attachCodeDecls(
                                v___x_2888_,
                                v_a_2902_,
                                v_a_2904_,
                            );
                            lean_dec(v_a_2902_);
                            v___x_2906_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__3;
                            v___x_2907_ = l_Lean_Compiler_LCNF_mkAuxJpDecl(
                                v___x_2888_,
                                v_a_2898_,
                                v___x_2905_,
                                v___x_2906_,
                                v_a_2883_,
                                v_a_2884_,
                                v_a_2885_,
                                v_a_2886_,
                            );
                            if lean_obj_tag(v___x_2907_) == 0 {
                                v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
                                v_isSharedCheck_2916_ = (!lean_is_exclusive(v___x_2907_)) as u8;
                                if v_isSharedCheck_2916_ == 0 {
                                    v___x_2910_ = v___x_2907_;
                                    v_isShared_2911_ = v_isSharedCheck_2916_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_2908_);
                                    lean_dec(v___x_2907_);
                                    v___x_2910_ = lean_box(0);
                                    v_isShared_2911_ = v_isSharedCheck_2916_;
                                    state = 2;
                                    continue;
                                }
                            } else {
                                v_a_2917_ = lean_ctor_get(v___x_2907_, 0);
                                v_isSharedCheck_2924_ = (!lean_is_exclusive(v___x_2907_)) as u8;
                                if v_isSharedCheck_2924_ == 0 {
                                    v___x_2919_ = v___x_2907_;
                                    v_isShared_2920_ = v_isSharedCheck_2924_;
                                    state = 4;
                                    continue;
                                } else {
                                    lean_inc(v_a_2917_);
                                    lean_dec(v___x_2907_);
                                    v___x_2919_ = lean_box(0);
                                    v_isShared_2920_ = v_isSharedCheck_2924_;
                                    state = 4;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec(v_a_2902_);
                            lean_dec(v_a_2898_);
                            v_a_2925_ = lean_ctor_get(v___x_2903_, 0);
                            v_isSharedCheck_2932_ = (!lean_is_exclusive(v___x_2903_)) as u8;
                            if v_isSharedCheck_2932_ == 0 {
                                v___x_2927_ = v___x_2903_;
                                v_isShared_2928_ = v_isSharedCheck_2932_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_2925_);
                                lean_dec(v___x_2903_);
                                v___x_2927_ = lean_box(0);
                                v_isShared_2928_ = v_isSharedCheck_2932_;
                                state = 6;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_2898_);
                        lean_dec_ref(v_k_2879_);
                        v_a_2933_ = lean_ctor_get(v___x_2901_, 0);
                        v_isSharedCheck_2940_ = (!lean_is_exclusive(v___x_2901_)) as u8;
                        if v_isSharedCheck_2940_ == 0 {
                            v___x_2935_ = v___x_2901_;
                            v_isShared_2936_ = v_isSharedCheck_2940_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_a_2933_);
                            lean_dec(v___x_2901_);
                            v___x_2935_ = lean_box(0);
                            v_isShared_2936_ = v_isSharedCheck_2940_;
                            state = 8;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_k_2879_);
                    lean_dec_ref(v_decls_2875_);
                    v_a_2941_ = lean_ctor_get(v___x_2897_, 0);
                    v_isSharedCheck_2948_ = (!lean_is_exclusive(v___x_2897_)) as u8;
                    if v_isSharedCheck_2948_ == 0 {
                        v___x_2943_ = v___x_2897_;
                        v_isShared_2944_ = v_isSharedCheck_2948_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_2941_);
                        lean_dec(v___x_2897_);
                        v___x_2943_ = lean_box(0);
                        v_isShared_2944_ = v_isSharedCheck_2948_;
                        state = 10;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2912_ = lean_alloc_ctor(0, 1, (2) as u32);
                lean_ctor_set(v___x_2912_, 0, v_a_2908_);
                lean_ctor_set_uint8(
                    v___x_2912_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    v_default_2880_,
                );
                lean_ctor_set_uint8(
                    v___x_2912_,
                    (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    v___y_2895_,
                );
                if v_isShared_2911_ == 0 {
                    lean_ctor_set(v___x_2910_, 0, v___x_2912_);
                    v___x_2914_ = v___x_2910_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2915_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2915_, 0, v___x_2912_);
                    v___x_2914_ = v_reuseFailAlloc_2915_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2914_;
            }
            4 => {
                if v_isShared_2920_ == 0 {
                    v___x_2922_ = v___x_2919_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2923_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_a_2917_);
                    v___x_2922_ = v_reuseFailAlloc_2923_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2922_;
            }
            6 => {
                if v_isShared_2928_ == 0 {
                    v___x_2930_ = v___x_2927_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2931_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2931_, 0, v_a_2925_);
                    v___x_2930_ = v_reuseFailAlloc_2931_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2930_;
            }
            8 => {
                if v_isShared_2936_ == 0 {
                    v___x_2938_ = v___x_2935_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2939_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2939_, 0, v_a_2933_);
                    v___x_2938_ = v_reuseFailAlloc_2939_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2938_;
            }
            10 => {
                if v_isShared_2944_ == 0 {
                    v___x_2946_ = v___x_2943_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2947_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2947_, 0, v_a_2941_);
                    v___x_2946_ = v_reuseFailAlloc_2947_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2946_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___boxed(
    mut v_decls_2956_: *mut LeanObject,
    mut v_params_2957_: *mut LeanObject,
    mut v_targetParamIdx_2958_: *mut LeanObject,
    mut v_fields_2959_: *mut LeanObject,
    mut v_k_2960_: *mut LeanObject,
    mut v_default_2961_: *mut LeanObject,
    mut v_a_2962_: *mut LeanObject,
    mut v_a_2963_: *mut LeanObject,
    mut v_a_2964_: *mut LeanObject,
    mut v_a_2965_: *mut LeanObject,
    mut v_a_2966_: *mut LeanObject,
    mut v_a_2967_: *mut LeanObject,
    mut v_a_2968_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_default_boxed_2969_: u8 = 0;
    let mut v_a_boxed_2970_: u8 = 0;
    let mut v_res_2971_: *mut LeanObject = core::ptr::null_mut();
    v_default_boxed_2969_ = (lean_unbox(v_default_2961_) as u8);
    v_a_boxed_2970_ = (lean_unbox(v_a_2962_) as u8);
    v_res_2971_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(
        v_decls_2956_,
        v_params_2957_,
        v_targetParamIdx_2958_,
        v_fields_2959_,
        v_k_2960_,
        v_default_boxed_2969_,
        v_a_boxed_2970_,
        v_a_2963_,
        v_a_2964_,
        v_a_2965_,
        v_a_2966_,
        v_a_2967_,
    );
    lean_dec(v_a_2967_);
    lean_dec_ref(v_a_2966_);
    lean_dec(v_a_2965_);
    lean_dec_ref(v_a_2964_);
    lean_dec(v_a_2963_);
    lean_dec(v_targetParamIdx_2958_);
    lean_dec_ref(v_params_2957_);
    return v_res_2971_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(
    mut v_upperBound_2972_: *mut LeanObject,
    mut v_params_2973_: *mut LeanObject,
    mut v_targetParamIdx_2974_: *mut LeanObject,
    mut v___y_2975_: u8,
    mut v_fields_2976_: *mut LeanObject,
    mut v_inst_2977_: *mut LeanObject,
    mut v_R_2978_: *mut LeanObject,
    mut v_a_2979_: *mut LeanObject,
    mut v_b_2980_: *mut LeanObject,
    mut v_c_2981_: *mut LeanObject,
    mut v___y_2982_: u8,
    mut v___y_2983_: *mut LeanObject,
    mut v___y_2984_: *mut LeanObject,
    mut v___y_2985_: *mut LeanObject,
    mut v___y_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2989_: *mut LeanObject = core::ptr::null_mut();
    v___x_2989_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___redArg(v_upperBound_2972_, v_params_2973_, v_targetParamIdx_2974_, v___y_2975_, v_fields_2976_, v_a_2979_, v_b_2980_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
    return v___x_2989_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_2990_: *mut LeanObject = *_args.add(0);
    let mut v_params_2991_: *mut LeanObject = *_args.add(1);
    let mut v_targetParamIdx_2992_: *mut LeanObject = *_args.add(2);
    let mut v___y_2993_: *mut LeanObject = *_args.add(3);
    let mut v_fields_2994_: *mut LeanObject = *_args.add(4);
    let mut v_inst_2995_: *mut LeanObject = *_args.add(5);
    let mut v_R_2996_: *mut LeanObject = *_args.add(6);
    let mut v_a_2997_: *mut LeanObject = *_args.add(7);
    let mut v_b_2998_: *mut LeanObject = *_args.add(8);
    let mut v_c_2999_: *mut LeanObject = *_args.add(9);
    let mut v___y_3000_: *mut LeanObject = *_args.add(10);
    let mut v___y_3001_: *mut LeanObject = *_args.add(11);
    let mut v___y_3002_: *mut LeanObject = *_args.add(12);
    let mut v___y_3003_: *mut LeanObject = *_args.add(13);
    let mut v___y_3004_: *mut LeanObject = *_args.add(14);
    let mut v___y_3005_: *mut LeanObject = *_args.add(15);
    let mut v___y_3006_: *mut LeanObject = *_args.add(16);
    let mut v___y_5993__boxed_3007_: u8 = 0;
    let mut v___y_5995__boxed_3008_: u8 = 0;
    let mut v_res_3009_: *mut LeanObject = core::ptr::null_mut();
    v___y_5993__boxed_3007_ = (lean_unbox(v___y_2993_) as u8);
    v___y_5995__boxed_3008_ = (lean_unbox(v___y_3000_) as u8);
    v_res_3009_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(v_upperBound_2990_, v_params_2991_, v_targetParamIdx_2992_, v___y_5993__boxed_3007_, v_fields_2994_, v_inst_2995_, v_R_2996_, v_a_2997_, v_b_2998_, v_c_2999_, v___y_5995__boxed_3008_, v___y_3001_, v___y_3002_, v___y_3003_, v___y_3004_, v___y_3005_);
    lean_dec(v___y_3005_);
    lean_dec_ref(v___y_3004_);
    lean_dec(v___y_3003_);
    lean_dec_ref(v___y_3002_);
    lean_dec(v___y_3001_);
    lean_dec(v_targetParamIdx_2992_);
    lean_dec_ref(v_params_2991_);
    lean_dec(v_upperBound_2990_);
    return v_res_3009_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0()
-> *mut LeanObject {
    let mut v___x_3010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3012_: *mut LeanObject = core::ptr::null_mut();
    v___x_3010_ = lean_box(0);
    v___x_3011_ = lean_unsigned_to_nat(16);
    v___x_3012_ = lean_mk_array(v___x_3011_, v___x_3010_);
    return v___x_3012_;
}
pub unsafe fn _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1()
-> *mut LeanObject {
    let mut v___x_3013_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3015_: *mut LeanObject = core::ptr::null_mut();
    v___x_3013_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0_once), _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__0);
    v___x_3014_ = lean_unsigned_to_nat(0);
    v___x_3015_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3015_, 0, v___x_3014_);
    lean_ctor_set(v___x_3015_, 1, v___x_3013_);
    return v___x_3015_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(
    mut v_decls_3016_: *mut LeanObject,
    mut v_params_3017_: *mut LeanObject,
    mut v_targetParamIdx_3018_: *mut LeanObject,
    mut v_fields_3019_: *mut LeanObject,
    mut v_k_3020_: *mut LeanObject,
    mut v_default_3021_: u8,
    mut v_a_3022_: *mut LeanObject,
    mut v_a_3023_: *mut LeanObject,
    mut v_a_3024_: *mut LeanObject,
    mut v_a_3025_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: u8 = 0;
    let mut v___x_3030_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3033_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3034_: u8 = 0;
    let mut v___x_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3038_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3039_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3027_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1_once), _init_l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___closed__1);
                v___x_3028_ = lean_st_mk_ref(v___x_3027_);
                v___x_3029_ = 0;
                v___x_3030_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go(v_decls_3016_, v_params_3017_, v_targetParamIdx_3018_, v_fields_3019_, v_k_3020_, v_default_3021_, v___x_3029_, v___x_3028_, v_a_3022_, v_a_3023_, v_a_3024_, v_a_3025_);
                if lean_obj_tag(v___x_3030_) == 0 {
                    v_a_3031_ = lean_ctor_get(v___x_3030_, 0);
                    v_isSharedCheck_3039_ = (!lean_is_exclusive(v___x_3030_)) as u8;
                    if v_isSharedCheck_3039_ == 0 {
                        v___x_3033_ = v___x_3030_;
                        v_isShared_3034_ = v_isSharedCheck_3039_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3031_);
                        lean_dec(v___x_3030_);
                        v___x_3033_ = lean_box(0);
                        v_isShared_3034_ = v_isSharedCheck_3039_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3028_);
                    return v___x_3030_;
                }
            }
            1 => {
                v___x_3035_ = lean_st_ref_get(v___x_3028_);
                lean_dec(v___x_3028_);
                lean_dec(v___x_3035_);
                if v_isShared_3034_ == 0 {
                    v___x_3037_ = v___x_3033_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_a_3031_);
                    v___x_3037_ = v_reuseFailAlloc_3038_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3037_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt___boxed(
    mut v_decls_3040_: *mut LeanObject,
    mut v_params_3041_: *mut LeanObject,
    mut v_targetParamIdx_3042_: *mut LeanObject,
    mut v_fields_3043_: *mut LeanObject,
    mut v_k_3044_: *mut LeanObject,
    mut v_default_3045_: *mut LeanObject,
    mut v_a_3046_: *mut LeanObject,
    mut v_a_3047_: *mut LeanObject,
    mut v_a_3048_: *mut LeanObject,
    mut v_a_3049_: *mut LeanObject,
    mut v_a_3050_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_default_boxed_3051_: u8 = 0;
    let mut v_res_3052_: *mut LeanObject = core::ptr::null_mut();
    v_default_boxed_3051_ = (lean_unbox(v_default_3045_) as u8);
    v_res_3052_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(
        v_decls_3040_,
        v_params_3041_,
        v_targetParamIdx_3042_,
        v_fields_3043_,
        v_k_3044_,
        v_default_boxed_3051_,
        v_a_3046_,
        v_a_3047_,
        v_a_3048_,
        v_a_3049_,
    );
    lean_dec(v_a_3049_);
    lean_dec_ref(v_a_3048_);
    lean_dec(v_a_3047_);
    lean_dec_ref(v_a_3046_);
    lean_dec(v_targetParamIdx_3042_);
    lean_dec_ref(v_params_3041_);
    return v_res_3052_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(
    mut v_args_3053_: *mut LeanObject,
    mut v_targetParamIdx_3054_: *mut LeanObject,
    mut v_fields_3055_: *mut LeanObject,
    mut v_dependsOnTarget_3056_: u8,
) -> *mut LeanObject {
    let mut v___x_3057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3059_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: u8 = 0;
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if v_dependsOnTarget_3056_ == 0 {
                    v___x_3057_ = lean_unsigned_to_nat(0);
                    lean_inc(v_targetParamIdx_3054_);
                    lean_inc_ref(v_args_3053_);
                    v___x_3058_ = l_Array_toSubarray___redArg(
                        v_args_3053_,
                        v___x_3057_,
                        v_targetParamIdx_3054_,
                    );
                    v___x_3059_ = l_Subarray_copy___redArg(v___x_3058_);
                    v___x_3060_ = l_Array_append___redArg(v___x_3059_, v_fields_3055_);
                    v___x_3067_ = lean_array_get_size(v_args_3053_);
                    v___x_3068_ = lean_unsigned_to_nat(1);
                    v___x_3069_ = lean_nat_add(v_targetParamIdx_3054_, v___x_3068_);
                    lean_dec(v_targetParamIdx_3054_);
                    v___x_3070_ = lean_nat_dec_le(v___x_3069_, v___x_3057_);
                    if v___x_3070_ == 0 {
                        v_lower_3062_ = v___x_3069_;
                        v_upper_3063_ = v___x_3067_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_3069_);
                        v_lower_3062_ = v___x_3057_;
                        v_upper_3063_ = v___x_3067_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_3071_ = lean_unsigned_to_nat(0);
                    v___x_3072_ = lean_unsigned_to_nat(1);
                    v___x_3073_ = lean_nat_add(v_targetParamIdx_3054_, v___x_3072_);
                    lean_dec(v_targetParamIdx_3054_);
                    lean_inc(v___x_3073_);
                    lean_inc_ref(v_args_3053_);
                    v___x_3074_ =
                        l_Array_toSubarray___redArg(v_args_3053_, v___x_3071_, v___x_3073_);
                    v___x_3075_ = l_Subarray_copy___redArg(v___x_3074_);
                    v___x_3076_ = l_Array_append___redArg(v___x_3075_, v_fields_3055_);
                    v___x_3083_ = lean_array_get_size(v_args_3053_);
                    v___x_3084_ = lean_nat_dec_le(v___x_3073_, v___x_3071_);
                    if v___x_3084_ == 0 {
                        v_lower_3078_ = v___x_3073_;
                        v_upper_3079_ = v___x_3083_;
                        state = 2;
                        continue;
                    } else {
                        lean_dec(v___x_3073_);
                        v_lower_3078_ = v___x_3071_;
                        v_upper_3079_ = v___x_3083_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3064_ =
                    l_Array_toSubarray___redArg(v_args_3053_, v_lower_3062_, v_upper_3063_);
                v___x_3065_ = l_Subarray_copy___redArg(v___x_3064_);
                v___x_3066_ = l_Array_append___redArg(v___x_3060_, v___x_3065_);
                lean_dec_ref(v___x_3065_);
                return v___x_3066_;
            }
            2 => {
                v___x_3080_ =
                    l_Array_toSubarray___redArg(v_args_3053_, v_lower_3078_, v_upper_3079_);
                v___x_3081_ = l_Subarray_copy___redArg(v___x_3080_);
                v___x_3082_ = l_Array_append___redArg(v___x_3076_, v___x_3081_);
                lean_dec_ref(v___x_3081_);
                return v___x_3082_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs___boxed(
    mut v_args_3085_: *mut LeanObject,
    mut v_targetParamIdx_3086_: *mut LeanObject,
    mut v_fields_3087_: *mut LeanObject,
    mut v_dependsOnTarget_3088_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dependsOnTarget_boxed_3089_: u8 = 0;
    let mut v_res_3090_: *mut LeanObject = core::ptr::null_mut();
    v_dependsOnTarget_boxed_3089_ = (lean_unbox(v_dependsOnTarget_3088_) as u8);
    v_res_3090_ =
        l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(
            v_args_3085_,
            v_targetParamIdx_3086_,
            v_fields_3087_,
            v_dependsOnTarget_boxed_3089_,
        );
    lean_dec_ref(v_fields_3087_);
    return v_res_3090_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(
    mut v_sz_3091_: usize,
    mut v_i_3092_: usize,
    mut v_bs_3093_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3094_: u8 = 0;
    let mut v_v_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_3098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: usize = 0;
    let mut v___x_3101_: usize = 0;
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3094_ = lean_usize_dec_lt(v_i_3092_, v_sz_3091_);
                if v___x_3094_ == 0 {
                    return v_bs_3093_;
                } else {
                    v_v_3095_ = lean_array_uget_borrowed(v_bs_3093_, v_i_3092_);
                    v_fvarId_3096_ = lean_ctor_get(v_v_3095_, 0);
                    lean_inc(v_fvarId_3096_);
                    v___x_3097_ = lean_unsigned_to_nat(0);
                    v_bs_x27_3098_ = lean_array_uset(v_bs_3093_, v_i_3092_, v___x_3097_);
                    v___x_3099_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3099_, 0, v_fvarId_3096_);
                    v___x_3100_ = 1usize;
                    v___x_3101_ = lean_usize_add(v_i_3092_, v___x_3100_);
                    v___x_3102_ = lean_array_uset(v_bs_x27_3098_, v_i_3092_, v___x_3099_);
                    v_i_3092_ = v___x_3101_;
                    v_bs_3093_ = v___x_3102_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0___boxed(
    mut v_sz_3104_: *mut LeanObject,
    mut v_i_3105_: *mut LeanObject,
    mut v_bs_3106_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3107_: usize = 0;
    let mut v_i_boxed_3108_: usize = 0;
    let mut v_res_3109_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3107_ = lean_unbox_usize(v_sz_3104_);
    lean_dec(v_sz_3104_);
    v_i_boxed_3108_ = lean_unbox_usize(v_i_3105_);
    lean_dec(v_i_3105_);
    v_res_3109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_boxed_3107_, v_i_boxed_3108_, v_bs_3106_);
    return v_res_3109_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(
    mut v_sz_3110_: usize,
    mut v_i_3111_: usize,
    mut v_bs_3112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3113_: u8 = 0;
    v___x_3113_ = lean_usize_dec_lt(v_i_3111_, v_sz_3110_);
    if v___x_3113_ == 0 {
        return v_bs_3112_;
    } else {
        let mut v_v_3114_: *mut LeanObject = core::ptr::null_mut();
        let mut v_fvarId_3115_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3116_: *mut LeanObject = core::ptr::null_mut();
        let mut v_bs_x27_3117_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3118_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3119_: usize = 0;
        let mut v___x_3120_: usize = 0;
        let mut v___x_3121_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3122_: *mut LeanObject = core::ptr::null_mut();
        v_v_3114_ = lean_array_uget_borrowed(v_bs_3112_, v_i_3111_);
        v_fvarId_3115_ = lean_ctor_get(v_v_3114_, 0);
        lean_inc(v_fvarId_3115_);
        v___x_3116_ = lean_unsigned_to_nat(0);
        v_bs_x27_3117_ = lean_array_uset(v_bs_3112_, v_i_3111_, v___x_3116_);
        v___x_3118_ = lean_alloc_ctor(1, 1, (0) as u32);
        lean_ctor_set(v___x_3118_, 0, v_fvarId_3115_);
        v___x_3119_ = 1usize;
        v___x_3120_ = lean_usize_add(v_i_3111_, v___x_3119_);
        v___x_3121_ = lean_array_uset(v_bs_x27_3117_, v_i_3111_, v___x_3118_);
        v___x_3122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0_spec__0(v_sz_3110_, v___x_3120_, v___x_3121_);
        return v___x_3122_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0___boxed(
    mut v_sz_3123_: *mut LeanObject,
    mut v_i_3124_: *mut LeanObject,
    mut v_bs_3125_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3126_: usize = 0;
    let mut v_i_boxed_3127_: usize = 0;
    let mut v_res_3128_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3126_ = lean_unbox_usize(v_sz_3123_);
    lean_dec(v_sz_3123_);
    v_i_boxed_3127_ = lean_unbox_usize(v_i_3124_);
    lean_dec(v_i_3124_);
    v_res_3128_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_boxed_3126_, v_i_boxed_3127_, v_bs_3125_);
    return v_res_3128_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(
    mut v_params_3129_: *mut LeanObject,
    mut v_targetParamIdx_3130_: *mut LeanObject,
    mut v_fields_3131_: *mut LeanObject,
    mut v_dependsOnTarget_3132_: u8,
) -> *mut LeanObject {
    let mut v_sz_3133_: usize = 0;
    let mut v___x_3134_: usize = 0;
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3136_: usize = 0;
    let mut v___x_3137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3138_: *mut LeanObject = core::ptr::null_mut();
    v_sz_3133_ = lean_array_size(v_params_3129_);
    v___x_3134_ = 0usize;
    v___x_3135_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_3133_, v___x_3134_, v_params_3129_);
    v_sz_3136_ = lean_array_size(v_fields_3131_);
    v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp_spec__0(v_sz_3136_, v___x_3134_, v_fields_3131_);
    v___x_3138_ =
        l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(
            v___x_3135_,
            v_targetParamIdx_3130_,
            v___x_3137_,
            v_dependsOnTarget_3132_,
        );
    lean_dec_ref(v___x_3137_);
    return v___x_3138_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp___boxed(
    mut v_params_3139_: *mut LeanObject,
    mut v_targetParamIdx_3140_: *mut LeanObject,
    mut v_fields_3141_: *mut LeanObject,
    mut v_dependsOnTarget_3142_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_dependsOnTarget_boxed_3143_: u8 = 0;
    let mut v_res_3144_: *mut LeanObject = core::ptr::null_mut();
    v_dependsOnTarget_boxed_3143_ = (lean_unbox(v_dependsOnTarget_3142_) as u8);
    v_res_3144_ =
        l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(
            v_params_3139_,
            v_targetParamIdx_3140_,
            v_fields_3141_,
            v_dependsOnTarget_boxed_3143_,
        );
    return v_res_3144_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(
    mut v_fvarId_3150_: *mut LeanObject,
    mut v_args_3151_: *mut LeanObject,
    mut v_a_3152_: *mut LeanObject,
    mut v_a_3153_: *mut LeanObject,
    mut v_a_3154_: *mut LeanObject,
    mut v_a_3155_: *mut LeanObject,
    mut v_a_3156_: *mut LeanObject,
    mut v_a_3157_: *mut LeanObject,
    mut v_a_3158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3161_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3165_: u8 = 0;
    let mut v___x_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3167_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3170_: u8 = 0;
    let mut v_paramIdx_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3174_: u8 = 0;
    let mut v___x_3175_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3180_: u8 = 0;
    let mut v___x_3181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v_val_3186_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3189_: u8 = 0;
    let mut v___x_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3195_: u8 = 0;
    let mut v_default_3196_: u8 = 0;
    let mut v_decl_3197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dependsOnDiscr_3198_: u8 = 0;
    let mut v_val_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3203_: u8 = 0;
    let mut v___y_3205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3206_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lower_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_upper_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3211_: u8 = 0;
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3218_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3220_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3221_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3222_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3223_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3224_: u8 = 0;
    let mut v_numParams_3225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3228_: u8 = 0;
    let mut v___x_3230_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3235_: u8 = 0;
    let mut v_decl_3236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dependsOnDiscr_3237_: u8 = 0;
    let mut v_n_3238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3241_: u8 = 0;
    let mut v_zero_3242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isZero_3243_: u8 = 0;
    let mut v_fvarId_3244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3254_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3255_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3256_: u8 = 0;
    let mut v_one_3257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_n_3258_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v_fvarId_3269_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3277_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_a_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut v_reuseFailAlloc_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3298_: u8 = 0;
    let mut v_decl_3299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dependsOnDiscr_3300_: u8 = 0;
    let mut v_fvarId_3301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3302_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3307_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3313_: u8 = 0;
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3318_: u8 = 0;
    let mut v___x_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3322_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3323_: u8 = 0;
    let mut v_a_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3327_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3331_: u8 = 0;
    let mut v_isSharedCheck_3332_: u8 = 0;
    let mut v___x_3333_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3337_: u8 = 0;
    let mut v_unused_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v___x_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3344_: u8 = 0;
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3160_ = lean_st_ref_get(v_a_3153_);
                v___x_3161_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v___x_3160_, v_fvarId_3150_);
                lean_dec(v___x_3160_);
                if lean_obj_tag(v___x_3161_) == 1 {
                    v_val_3162_ = lean_ctor_get(v___x_3161_, 0);
                    v_isSharedCheck_3344_ = (!lean_is_exclusive(v___x_3161_)) as u8;
                    if v_isSharedCheck_3344_ == 0 {
                        v___x_3164_ = v___x_3161_;
                        v_isShared_3165_ = v_isSharedCheck_3344_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3162_);
                        lean_dec(v___x_3161_);
                        v___x_3164_ = lean_box(0);
                        v_isShared_3165_ = v_isSharedCheck_3344_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3161_);
                    lean_dec_ref(v_args_3151_);
                    v___x_3345_ = lean_box(0);
                    v___x_3346_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3346_, 0, v___x_3345_);
                    return v___x_3346_;
                }
            }
            1 => {
                v___x_3166_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_3152_, v_fvarId_3150_);
                if lean_obj_tag(v___x_3166_) == 1 {
                    lean_del_object(v___x_3164_);
                    v_val_3167_ = lean_ctor_get(v___x_3166_, 0);
                    v_isSharedCheck_3339_ = (!lean_is_exclusive(v___x_3166_)) as u8;
                    if v_isSharedCheck_3339_ == 0 {
                        v___x_3169_ = v___x_3166_;
                        v_isShared_3170_ = v_isSharedCheck_3339_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_val_3167_);
                        lean_dec(v___x_3166_);
                        v___x_3169_ = lean_box(0);
                        v_isShared_3170_ = v_isSharedCheck_3339_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3166_);
                    lean_dec(v_val_3162_);
                    lean_dec_ref(v_args_3151_);
                    v___x_3340_ = lean_box(0);
                    if v_isShared_3165_ == 0 {
                        lean_ctor_set_tag(v___x_3164_, 0);
                        lean_ctor_set(v___x_3164_, 0, v___x_3340_);
                        v___x_3342_ = v___x_3164_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_3343_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3343_, 0, v___x_3340_);
                        v___x_3342_ = v_reuseFailAlloc_3343_;
                        state = 37;
                        continue;
                    }
                }
            }
            2 => {
                v_paramIdx_3171_ = lean_ctor_get(v_val_3167_, 0);
                v_isSharedCheck_3337_ = (!lean_is_exclusive(v_val_3167_)) as u8;
                if v_isSharedCheck_3337_ == 0 {
                    v_unused_3338_ = lean_ctor_get(v_val_3167_, 1);
                    lean_dec(v_unused_3338_);
                    v___x_3173_ = v_val_3167_;
                    v_isShared_3174_ = v_isSharedCheck_3337_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_paramIdx_3171_);
                    lean_dec(v_val_3167_);
                    v___x_3173_ = lean_box(0);
                    v_isShared_3174_ = v_isSharedCheck_3337_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3175_ = lean_box(0);
                v___x_3176_ = lean_array_get(v___x_3175_, v_args_3151_, v_paramIdx_3171_);
                if lean_obj_tag(v___x_3176_) == 1 {
                    lean_del_object(v___x_3169_);
                    v_fvarId_3177_ = lean_ctor_get(v___x_3176_, 0);
                    v_isSharedCheck_3332_ = (!lean_is_exclusive(v___x_3176_)) as u8;
                    if v_isSharedCheck_3332_ == 0 {
                        v___x_3179_ = v___x_3176_;
                        v_isShared_3180_ = v_isSharedCheck_3332_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_fvarId_3177_);
                        lean_dec(v___x_3176_);
                        v___x_3179_ = lean_box(0);
                        v_isShared_3180_ = v_isSharedCheck_3332_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3176_);
                    lean_del_object(v___x_3173_);
                    lean_dec(v_paramIdx_3171_);
                    lean_dec(v_val_3162_);
                    lean_dec_ref(v_args_3151_);
                    v___x_3333_ = lean_box(0);
                    if v_isShared_3170_ == 0 {
                        lean_ctor_set_tag(v___x_3169_, 0);
                        lean_ctor_set(v___x_3169_, 0, v___x_3333_);
                        v___x_3335_ = v___x_3169_;
                        state = 36;
                        continue;
                    } else {
                        v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
                        v___x_3335_ = v_reuseFailAlloc_3336_;
                        state = 36;
                        continue;
                    }
                }
            }
            4 => {
                v___x_3181_ = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(
                    v_fvarId_3177_,
                    v_a_3154_,
                    v_a_3156_,
                    v_a_3158_,
                );
                lean_dec(v_fvarId_3177_);
                if lean_obj_tag(v___x_3181_) == 0 {
                    v_a_3182_ = lean_ctor_get(v___x_3181_, 0);
                    v_isSharedCheck_3323_ = (!lean_is_exclusive(v___x_3181_)) as u8;
                    if v_isSharedCheck_3323_ == 0 {
                        v___x_3184_ = v___x_3181_;
                        v_isShared_3185_ = v_isSharedCheck_3323_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_3182_);
                        lean_dec(v___x_3181_);
                        v___x_3184_ = lean_box(0);
                        v_isShared_3185_ = v_isSharedCheck_3323_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3179_);
                    lean_del_object(v___x_3173_);
                    lean_dec(v_paramIdx_3171_);
                    lean_dec(v_val_3162_);
                    lean_dec_ref(v_args_3151_);
                    v_a_3324_ = lean_ctor_get(v___x_3181_, 0);
                    v_isSharedCheck_3331_ = (!lean_is_exclusive(v___x_3181_)) as u8;
                    if v_isSharedCheck_3331_ == 0 {
                        v___x_3326_ = v___x_3181_;
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 34;
                        continue;
                    } else {
                        lean_inc(v_a_3324_);
                        lean_dec(v___x_3181_);
                        v___x_3326_ = lean_box(0);
                        v_isShared_3327_ = v_isSharedCheck_3331_;
                        state = 34;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_3182_) == 1 {
                    v_val_3186_ = lean_ctor_get(v_a_3182_, 0);
                    v_isSharedCheck_3318_ = (!lean_is_exclusive(v_a_3182_)) as u8;
                    if v_isSharedCheck_3318_ == 0 {
                        v___x_3188_ = v_a_3182_;
                        v_isShared_3189_ = v_isSharedCheck_3318_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_val_3186_);
                        lean_dec(v_a_3182_);
                        v___x_3188_ = lean_box(0);
                        v_isShared_3189_ = v_isSharedCheck_3318_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3182_);
                    lean_del_object(v___x_3179_);
                    lean_del_object(v___x_3173_);
                    lean_dec(v_paramIdx_3171_);
                    lean_dec(v_val_3162_);
                    lean_dec_ref(v_args_3151_);
                    v___x_3319_ = lean_box(0);
                    if v_isShared_3185_ == 0 {
                        lean_ctor_set(v___x_3184_, 0, v___x_3319_);
                        v___x_3321_ = v___x_3184_;
                        state = 33;
                        continue;
                    } else {
                        v_reuseFailAlloc_3322_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3319_);
                        v___x_3321_ = v_reuseFailAlloc_3322_;
                        state = 33;
                        continue;
                    }
                }
            }
            6 => {
                v___x_3190_ = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(v_val_3186_);
                v___x_3191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_val_3162_, v___x_3190_);
                lean_dec(v___x_3190_);
                lean_dec(v_val_3162_);
                if lean_obj_tag(v___x_3191_) == 1 {
                    v_val_3192_ = lean_ctor_get(v___x_3191_, 0);
                    v_isSharedCheck_3313_ = (!lean_is_exclusive(v___x_3191_)) as u8;
                    if v_isSharedCheck_3313_ == 0 {
                        v___x_3194_ = v___x_3191_;
                        v_isShared_3195_ = v_isSharedCheck_3313_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_val_3192_);
                        lean_dec(v___x_3191_);
                        v___x_3194_ = lean_box(0);
                        v_isShared_3195_ = v_isSharedCheck_3313_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3191_);
                    lean_del_object(v___x_3188_);
                    lean_dec(v_val_3186_);
                    lean_del_object(v___x_3179_);
                    lean_del_object(v___x_3173_);
                    lean_dec(v_paramIdx_3171_);
                    lean_dec_ref(v_args_3151_);
                    v___x_3314_ = lean_box(0);
                    if v_isShared_3185_ == 0 {
                        lean_ctor_set(v___x_3184_, 0, v___x_3314_);
                        v___x_3316_ = v___x_3184_;
                        state = 32;
                        continue;
                    } else {
                        v_reuseFailAlloc_3317_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3317_, 0, v___x_3314_);
                        v___x_3316_ = v_reuseFailAlloc_3317_;
                        state = 32;
                        continue;
                    }
                }
            }
            7 => {
                v_default_3196_ = lean_ctor_get_uint8(
                    v_val_3192_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                if v_default_3196_ == 0 {
                    if lean_obj_tag(v_val_3186_) == 0 {
                        lean_del_object(v___x_3188_);
                        lean_del_object(v___x_3179_);
                        lean_del_object(v___x_3173_);
                        v_decl_3197_ = lean_ctor_get(v_val_3192_, 0);
                        lean_inc_ref(v_decl_3197_);
                        v_dependsOnDiscr_3198_ = lean_ctor_get_uint8(
                            v_val_3192_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        );
                        lean_dec(v_val_3192_);
                        v_val_3199_ = lean_ctor_get(v_val_3186_, 0);
                        v_args_3200_ = lean_ctor_get(v_val_3186_, 1);
                        v_isSharedCheck_3235_ = (!lean_is_exclusive(v_val_3186_)) as u8;
                        if v_isSharedCheck_3235_ == 0 {
                            v___x_3202_ = v_val_3186_;
                            v_isShared_3203_ = v_isSharedCheck_3235_;
                            state = 8;
                            continue;
                        } else {
                            lean_inc(v_args_3200_);
                            lean_inc(v_val_3199_);
                            lean_dec(v_val_3186_);
                            v___x_3202_ = lean_box(0);
                            v_isShared_3203_ = v_isSharedCheck_3235_;
                            state = 8;
                            continue;
                        }
                    } else {
                        v_decl_3236_ = lean_ctor_get(v_val_3192_, 0);
                        lean_inc_ref(v_decl_3236_);
                        v_dependsOnDiscr_3237_ = lean_ctor_get_uint8(
                            v_val_3192_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        );
                        lean_dec(v_val_3192_);
                        v_n_3238_ = lean_ctor_get(v_val_3186_, 0);
                        v_isSharedCheck_3298_ = (!lean_is_exclusive(v_val_3186_)) as u8;
                        if v_isSharedCheck_3298_ == 0 {
                            v___x_3240_ = v_val_3186_;
                            v_isShared_3241_ = v_isSharedCheck_3298_;
                            state = 16;
                            continue;
                        } else {
                            lean_inc(v_n_3238_);
                            lean_dec(v_val_3186_);
                            v___x_3240_ = lean_box(0);
                            v_isShared_3241_ = v_isSharedCheck_3298_;
                            state = 16;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3188_);
                    lean_dec(v_val_3186_);
                    lean_del_object(v___x_3179_);
                    v_decl_3299_ = lean_ctor_get(v_val_3192_, 0);
                    lean_inc_ref(v_decl_3299_);
                    v_dependsOnDiscr_3300_ = lean_ctor_get_uint8(
                        v_val_3192_,
                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                    );
                    lean_dec(v_val_3192_);
                    v_fvarId_3301_ = lean_ctor_get(v_decl_3299_, 0);
                    lean_inc(v_fvarId_3301_);
                    lean_dec_ref(v_decl_3299_);
                    v___x_3302_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
                    v___x_3303_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_3151_, v_paramIdx_3171_, v___x_3302_, v_dependsOnDiscr_3300_);
                    if v_isShared_3174_ == 0 {
                        lean_ctor_set_tag(v___x_3173_, 3);
                        lean_ctor_set(v___x_3173_, 1, v___x_3303_);
                        lean_ctor_set(v___x_3173_, 0, v_fvarId_3301_);
                        v___x_3305_ = v___x_3173_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_3312_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_fvarId_3301_);
                        lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3303_);
                        v___x_3305_ = v_reuseFailAlloc_3312_;
                        state = 29;
                        continue;
                    }
                }
            }
            8 => {
                v_numParams_3225_ = lean_ctor_get(v_val_3199_, 3);
                lean_inc(v_numParams_3225_);
                lean_dec_ref(v_val_3199_);
                v___x_3226_ = lean_unsigned_to_nat(0);
                v___x_3227_ = lean_array_get_size(v_args_3200_);
                v___x_3228_ = lean_nat_dec_le(v_numParams_3225_, v___x_3226_);
                if v___x_3228_ == 0 {
                    if v_isShared_3203_ == 0 {
                        lean_ctor_set(v___x_3202_, 1, v___x_3227_);
                        lean_ctor_set(v___x_3202_, 0, v_numParams_3225_);
                        v___x_3230_ = v___x_3202_;
                        state = 14;
                        continue;
                    } else {
                        v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_numParams_3225_);
                        lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3227_);
                        v___x_3230_ = v_reuseFailAlloc_3231_;
                        state = 14;
                        continue;
                    }
                } else {
                    lean_dec(v_numParams_3225_);
                    if v_isShared_3203_ == 0 {
                        lean_ctor_set(v___x_3202_, 1, v___x_3227_);
                        lean_ctor_set(v___x_3202_, 0, v___x_3226_);
                        v___x_3233_ = v___x_3202_;
                        state = 15;
                        continue;
                    } else {
                        v_reuseFailAlloc_3234_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3234_, 0, v___x_3226_);
                        lean_ctor_set(v_reuseFailAlloc_3234_, 1, v___x_3227_);
                        v___x_3233_ = v_reuseFailAlloc_3234_;
                        state = 15;
                        continue;
                    }
                }
            }
            9 => {
                v_fvarId_3206_ = lean_ctor_get(v_decl_3197_, 0);
                lean_inc(v_fvarId_3206_);
                lean_dec_ref(v_decl_3197_);
                v_lower_3207_ = lean_ctor_get(v___y_3205_, 0);
                v_upper_3208_ = lean_ctor_get(v___y_3205_, 1);
                v_isSharedCheck_3224_ = (!lean_is_exclusive(v___y_3205_)) as u8;
                if v_isSharedCheck_3224_ == 0 {
                    v___x_3210_ = v___y_3205_;
                    v_isShared_3211_ = v_isSharedCheck_3224_;
                    state = 10;
                    continue;
                } else {
                    lean_inc(v_upper_3208_);
                    lean_inc(v_lower_3207_);
                    lean_dec(v___y_3205_);
                    v___x_3210_ = lean_box(0);
                    v_isShared_3211_ = v_isSharedCheck_3224_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_3212_ =
                    l_Array_toSubarray___redArg(v_args_3200_, v_lower_3207_, v_upper_3208_);
                v___x_3213_ = l_Subarray_copy___redArg(v___x_3212_);
                v___x_3214_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_3151_, v_paramIdx_3171_, v___x_3213_, v_dependsOnDiscr_3198_);
                lean_dec_ref(v___x_3213_);
                if v_isShared_3211_ == 0 {
                    lean_ctor_set_tag(v___x_3210_, 3);
                    lean_ctor_set(v___x_3210_, 1, v___x_3214_);
                    lean_ctor_set(v___x_3210_, 0, v_fvarId_3206_);
                    v___x_3216_ = v___x_3210_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3223_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3223_, 0, v_fvarId_3206_);
                    lean_ctor_set(v_reuseFailAlloc_3223_, 1, v___x_3214_);
                    v___x_3216_ = v_reuseFailAlloc_3223_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_3195_ == 0 {
                    lean_ctor_set(v___x_3194_, 0, v___x_3216_);
                    v___x_3218_ = v___x_3194_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3222_, 0, v___x_3216_);
                    v___x_3218_ = v_reuseFailAlloc_3222_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_3185_ == 0 {
                    lean_ctor_set(v___x_3184_, 0, v___x_3218_);
                    v___x_3220_ = v___x_3184_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3221_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
                    v___x_3220_ = v_reuseFailAlloc_3221_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3220_;
            }
            14 => {
                v___y_3205_ = v___x_3230_;
                state = 9;
                continue;
            }
            15 => {
                v___y_3205_ = v___x_3233_;
                state = 9;
                continue;
            }
            16 => {
                v_zero_3242_ = lean_unsigned_to_nat(0);
                v_isZero_3243_ = lean_nat_dec_eq(v_n_3238_, v_zero_3242_);
                if v_isZero_3243_ == 1 {
                    lean_del_object(v___x_3240_);
                    lean_dec(v_n_3238_);
                    lean_del_object(v___x_3188_);
                    lean_del_object(v___x_3179_);
                    v_fvarId_3244_ = lean_ctor_get(v_decl_3236_, 0);
                    lean_inc(v_fvarId_3244_);
                    lean_dec_ref(v_decl_3236_);
                    v___x_3245_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__0;
                    v___x_3246_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_3151_, v_paramIdx_3171_, v___x_3245_, v_dependsOnDiscr_3237_);
                    if v_isShared_3174_ == 0 {
                        lean_ctor_set_tag(v___x_3173_, 3);
                        lean_ctor_set(v___x_3173_, 1, v___x_3246_);
                        lean_ctor_set(v___x_3173_, 0, v_fvarId_3244_);
                        v___x_3248_ = v___x_3173_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_3255_ = lean_alloc_ctor(3, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3255_, 0, v_fvarId_3244_);
                        lean_ctor_set(v_reuseFailAlloc_3255_, 1, v___x_3246_);
                        v___x_3248_ = v_reuseFailAlloc_3255_;
                        state = 17;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3184_);
                    v___x_3256_ = 0;
                    v_one_3257_ = lean_unsigned_to_nat(1);
                    v_n_3258_ = lean_nat_sub(v_n_3238_, v_one_3257_);
                    lean_dec(v_n_3238_);
                    if v_isShared_3241_ == 0 {
                        lean_ctor_set_tag(v___x_3240_, 0);
                        lean_ctor_set(v___x_3240_, 0, v_n_3258_);
                        v___x_3260_ = v___x_3240_;
                        state = 20;
                        continue;
                    } else {
                        v_reuseFailAlloc_3297_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_n_3258_);
                        v___x_3260_ = v_reuseFailAlloc_3297_;
                        state = 20;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_3195_ == 0 {
                    lean_ctor_set(v___x_3194_, 0, v___x_3248_);
                    v___x_3250_ = v___x_3194_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3254_, 0, v___x_3248_);
                    v___x_3250_ = v_reuseFailAlloc_3254_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_3185_ == 0 {
                    lean_ctor_set(v___x_3184_, 0, v___x_3250_);
                    v___x_3252_ = v___x_3184_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3253_, 0, v___x_3250_);
                    v___x_3252_ = v_reuseFailAlloc_3253_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_3252_;
            }
            20 => {
                if v_isShared_3189_ == 0 {
                    lean_ctor_set_tag(v___x_3188_, 0);
                    lean_ctor_set(v___x_3188_, 0, v___x_3260_);
                    v___x_3262_ = v___x_3188_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3296_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3296_, 0, v___x_3260_);
                    v___x_3262_ = v_reuseFailAlloc_3296_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                v___x_3263_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___closed__2;
                v___x_3264_ = l_Lean_Compiler_LCNF_mkAuxLetDecl(
                    v___x_3256_,
                    v___x_3262_,
                    v___x_3263_,
                    v_a_3155_,
                    v_a_3156_,
                    v_a_3157_,
                    v_a_3158_,
                );
                if lean_obj_tag(v___x_3264_) == 0 {
                    v_a_3265_ = lean_ctor_get(v___x_3264_, 0);
                    v_isSharedCheck_3287_ = (!lean_is_exclusive(v___x_3264_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3267_ = v___x_3264_;
                        v_isShared_3268_ = v_isSharedCheck_3287_;
                        state = 22;
                        continue;
                    } else {
                        lean_inc(v_a_3265_);
                        lean_dec(v___x_3264_);
                        v___x_3267_ = lean_box(0);
                        v_isShared_3268_ = v_isSharedCheck_3287_;
                        state = 22;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_decl_3236_);
                    lean_del_object(v___x_3194_);
                    lean_del_object(v___x_3179_);
                    lean_del_object(v___x_3173_);
                    lean_dec(v_paramIdx_3171_);
                    lean_dec_ref(v_args_3151_);
                    v_a_3288_ = lean_ctor_get(v___x_3264_, 0);
                    v_isSharedCheck_3295_ = (!lean_is_exclusive(v___x_3264_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3290_ = v___x_3264_;
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 27;
                        continue;
                    } else {
                        lean_inc(v_a_3288_);
                        lean_dec(v___x_3264_);
                        v___x_3290_ = lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 27;
                        continue;
                    }
                }
            }
            22 => {
                v_fvarId_3269_ = lean_ctor_get(v_decl_3236_, 0);
                lean_inc(v_fvarId_3269_);
                lean_dec_ref(v_decl_3236_);
                v_fvarId_3270_ = lean_ctor_get(v_a_3265_, 0);
                lean_inc(v_fvarId_3270_);
                if v_isShared_3180_ == 0 {
                    lean_ctor_set(v___x_3179_, 0, v_fvarId_3270_);
                    v___x_3272_ = v___x_3179_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_3286_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_fvarId_3270_);
                    v___x_3272_ = v_reuseFailAlloc_3286_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_3273_ = lean_mk_empty_array_with_capacity(v_one_3257_);
                v___x_3274_ = lean_array_push(v___x_3273_, v___x_3272_);
                v___x_3275_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpNewArgs(v_args_3151_, v_paramIdx_3171_, v___x_3274_, v_dependsOnDiscr_3237_);
                lean_dec_ref(v___x_3274_);
                if v_isShared_3174_ == 0 {
                    lean_ctor_set_tag(v___x_3173_, 3);
                    lean_ctor_set(v___x_3173_, 1, v___x_3275_);
                    lean_ctor_set(v___x_3173_, 0, v_fvarId_3269_);
                    v___x_3277_ = v___x_3173_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_fvarId_3269_);
                    lean_ctor_set(v_reuseFailAlloc_3285_, 1, v___x_3275_);
                    v___x_3277_ = v_reuseFailAlloc_3285_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                v___x_3278_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3278_, 0, v_a_3265_);
                lean_ctor_set(v___x_3278_, 1, v___x_3277_);
                if v_isShared_3195_ == 0 {
                    lean_ctor_set(v___x_3194_, 0, v___x_3278_);
                    v___x_3280_ = v___x_3194_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3278_);
                    v___x_3280_ = v_reuseFailAlloc_3284_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_3268_ == 0 {
                    lean_ctor_set(v___x_3267_, 0, v___x_3280_);
                    v___x_3282_ = v___x_3267_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3283_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3283_, 0, v___x_3280_);
                    v___x_3282_ = v_reuseFailAlloc_3283_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3282_;
            }
            27 => {
                if v_isShared_3291_ == 0 {
                    v___x_3293_ = v___x_3290_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_3294_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
                    v___x_3293_ = v_reuseFailAlloc_3294_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                return v___x_3293_;
            }
            29 => {
                if v_isShared_3195_ == 0 {
                    lean_ctor_set(v___x_3194_, 0, v___x_3305_);
                    v___x_3307_ = v___x_3194_;
                    state = 30;
                    continue;
                } else {
                    v_reuseFailAlloc_3311_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3311_, 0, v___x_3305_);
                    v___x_3307_ = v_reuseFailAlloc_3311_;
                    state = 30;
                    continue;
                }
            }
            30 => {
                if v_isShared_3185_ == 0 {
                    lean_ctor_set(v___x_3184_, 0, v___x_3307_);
                    v___x_3309_ = v___x_3184_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
                    v___x_3309_ = v_reuseFailAlloc_3310_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3309_;
            }
            32 => {
                return v___x_3316_;
            }
            33 => {
                return v___x_3321_;
            }
            34 => {
                if v_isShared_3327_ == 0 {
                    v___x_3329_ = v___x_3326_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3330_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3330_, 0, v_a_3324_);
                    v___x_3329_ = v_reuseFailAlloc_3330_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_3329_;
            }
            36 => {
                return v___x_3335_;
            }
            37 => {
                return v___x_3342_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f___boxed(
    mut v_fvarId_3347_: *mut LeanObject,
    mut v_args_3348_: *mut LeanObject,
    mut v_a_3349_: *mut LeanObject,
    mut v_a_3350_: *mut LeanObject,
    mut v_a_3351_: *mut LeanObject,
    mut v_a_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3357_: *mut LeanObject = core::ptr::null_mut();
    v_res_3357_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_3347_, v_args_3348_, v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_);
    lean_dec(v_a_3355_);
    lean_dec_ref(v_a_3354_);
    lean_dec(v_a_3353_);
    lean_dec_ref(v_a_3352_);
    lean_dec_ref(v_a_3351_);
    lean_dec(v_a_3350_);
    lean_dec(v_a_3349_);
    lean_dec(v_fvarId_3347_);
    return v_res_3357_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(
    mut v___x_3358_: *mut LeanObject,
    mut v_init_3359_: *mut LeanObject,
    mut v_x_3360_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3365_: u8 = 0;
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3367_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3360_) == 0 {
                    v_k_3361_ = lean_ctor_get(v_x_3360_, 1);
                    v_l_3362_ = lean_ctor_get(v_x_3360_, 3);
                    v_r_3363_ = lean_ctor_get(v_x_3360_, 4);
                    v___x_3364_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_3358_, v_init_3359_, v_l_3362_);
                    if lean_obj_tag(v___x_3364_) == 0 {
                        return v___x_3364_;
                    } else {
                        lean_dec_ref_known(v___x_3364_, 1);
                        v___x_3365_ = l_Lean_NameSet_contains(v___x_3358_, v_k_3361_);
                        if v___x_3365_ == 0 {
                            v___x_3366_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__2;
                            return v___x_3366_;
                        } else {
                            v___x_3367_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3;
                            v_init_3359_ = v___x_3367_;
                            v_x_3360_ = v_r_3363_;
                            state = 0;
                            continue;
                        }
                    }
                } else {
                    v___x_3369_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3369_, 0, v_init_3359_);
                    return v___x_3369_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3___boxed(
    mut v___x_3370_: *mut LeanObject,
    mut v_init_3371_: *mut LeanObject,
    mut v_x_3372_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3373_: *mut LeanObject = core::ptr::null_mut();
    v_res_3373_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_3370_, v_init_3371_, v_x_3372_);
    lean_dec(v_x_3372_);
    lean_dec(v___x_3370_);
    return v_res_3373_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(
    mut v___x_3374_: *mut LeanObject,
    mut v_a_3375_: *mut LeanObject,
    mut v_init_3376_: *mut LeanObject,
    mut v_x_3377_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_d_3380_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3384_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3390_: u8 = 0;
    let mut v___x_3391_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3393_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3394_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3377_) == 0 {
                    v_k_3383_ = lean_ctor_get(v_x_3377_, 1);
                    lean_inc(v_k_3383_);
                    v_l_3384_ = lean_ctor_get(v_x_3377_, 3);
                    lean_inc(v_l_3384_);
                    v_r_3385_ = lean_ctor_get(v_x_3377_, 4);
                    lean_inc(v_r_3385_);
                    lean_dec_ref_known(v_x_3377_, 5);
                    lean_inc_ref(v_a_3375_);
                    v___x_3386_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_3374_, v_a_3375_, v_init_3376_, v_l_3384_);
                    v_a_3387_ = lean_ctor_get(v___x_3386_, 0);
                    lean_inc(v_a_3387_);
                    if lean_obj_tag(v_a_3387_) == 0 {
                        lean_dec_ref(v___x_3386_);
                        lean_dec(v_r_3385_);
                        lean_dec(v_k_3383_);
                        lean_dec_ref(v_a_3375_);
                        v_a_3388_ = lean_ctor_get(v_a_3387_, 0);
                        lean_inc(v_a_3388_);
                        lean_dec_ref_known(v_a_3387_, 1);
                        v_d_3380_ = v_a_3388_;
                        state = 1;
                        continue;
                    } else {
                        v_a_3389_ = lean_ctor_get(v_a_3387_, 0);
                        lean_inc(v_a_3389_);
                        lean_dec_ref_known(v_a_3387_, 1);
                        v___x_3390_ = l_Lean_NameSet_contains(v___x_3374_, v_k_3383_);
                        if v___x_3390_ == 0 {
                            lean_dec_ref(v___x_3386_);
                            lean_inc_ref(v_a_3375_);
                            v___x_3391_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_3383_, v_a_3375_, v_a_3389_);
                            v_init_3376_ = v___x_3391_;
                            v_x_3377_ = v_r_3385_;
                            state = 0;
                            continue;
                        } else {
                            lean_dec(v_a_3389_);
                            lean_dec(v_k_3383_);
                            v_a_3393_ = lean_ctor_get(v___x_3386_, 0);
                            lean_inc(v_a_3393_);
                            lean_dec_ref(v___x_3386_);
                            if lean_obj_tag(v_a_3393_) == 0 {
                                lean_dec(v_r_3385_);
                                lean_dec_ref(v_a_3375_);
                                v_a_3394_ = lean_ctor_get(v_a_3393_, 0);
                                lean_inc(v_a_3394_);
                                lean_dec_ref_known(v_a_3393_, 1);
                                v_d_3380_ = v_a_3394_;
                                state = 1;
                                continue;
                            } else {
                                v_a_3395_ = lean_ctor_get(v_a_3393_, 0);
                                lean_inc(v_a_3395_);
                                lean_dec_ref_known(v_a_3393_, 1);
                                v_init_3376_ = v_a_3395_;
                                v_x_3377_ = v_r_3385_;
                                state = 0;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_dec_ref(v_a_3375_);
                    v___x_3397_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_3397_, 0, v_init_3376_);
                    v___x_3398_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3398_, 0, v___x_3397_);
                    return v___x_3398_;
                }
            }
            1 => {
                v___x_3381_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3381_, 0, v_d_3380_);
                v___x_3382_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3382_, 0, v___x_3381_);
                return v___x_3382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg___boxed(
    mut v___x_3399_: *mut LeanObject,
    mut v_a_3400_: *mut LeanObject,
    mut v_init_3401_: *mut LeanObject,
    mut v_x_3402_: *mut LeanObject,
    mut v___y_3403_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3404_: *mut LeanObject = core::ptr::null_mut();
    v_res_3404_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_3399_, v_a_3400_, v_init_3401_, v_x_3402_);
    lean_dec(v___x_3399_);
    return v_res_3404_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(
    mut v_discr_3410_: *mut LeanObject,
    mut v___x_3411_: *mut LeanObject,
    mut v_val_3412_: *mut LeanObject,
    mut v_fst_3413_: *mut LeanObject,
    mut v_params_3414_: *mut LeanObject,
    mut v_snd_3415_: *mut LeanObject,
    mut v_as_3416_: *mut LeanObject,
    mut v_sz_3417_: usize,
    mut v_i_3418_: usize,
    mut v_b_3419_: *mut LeanObject,
    mut v___y_3420_: *mut LeanObject,
    mut v___y_3421_: *mut LeanObject,
    mut v___y_3422_: *mut LeanObject,
    mut v___y_3423_: *mut LeanObject,
    mut v___y_3424_: *mut LeanObject,
    mut v___y_3425_: *mut LeanObject,
    mut v___y_3426_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3430_: usize = 0;
    let mut v___x_3431_: usize = 0;
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3439_: u8 = 0;
    let mut v_fst_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3444_: u8 = 0;
    let mut v___x_3445_: u8 = 0;
    let mut v_a_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3449_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3450_: u8 = 0;
    let mut v___y_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3454_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3469_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: u8 = 0;
    let mut v___x_3473_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_paramIdx_3477_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3478_: u8 = 0;
    let mut v___x_3479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dependsOnDiscr_3482_: u8 = 0;
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fvarId_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3485_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3487_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3489_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3490_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3497_: u8 = 0;
    let mut v___x_3499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3500_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3501_: u8 = 0;
    let mut v_a_3502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3504_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3505_: u8 = 0;
    let mut v___x_3507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3509_: u8 = 0;
    let mut v_a_3510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3513_: u8 = 0;
    let mut v___x_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3517_: u8 = 0;
    let mut v_a_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3521_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3524_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3525_: u8 = 0;
    let mut v_code_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3541_: u8 = 0;
    let mut v___x_3542_: u8 = 0;
    let mut v_paramIdx_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_decl_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_dependsOnDiscr_3548_: u8 = 0;
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3560_: u8 = 0;
    let mut v___x_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3564_: u8 = 0;
    let mut v_a_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3568_: u8 = 0;
    let mut v___x_3570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3572_: u8 = 0;
    let mut v_a_3573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3576_: u8 = 0;
    let mut v___x_3578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3579_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3580_: u8 = 0;
    let mut v_isSharedCheck_3581_: u8 = 0;
    let mut v___x_3582_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v___x_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3592_: u8 = 0;
    let mut v_isSharedCheck_3593_: u8 = 0;
    let mut v_isSharedCheck_3594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3433_ = lean_usize_dec_lt(v_i_3418_, v_sz_3417_);
                if v___x_3433_ == 0 {
                    lean_dec_ref(v_params_3414_);
                    lean_dec_ref(v_fst_3413_);
                    lean_dec_ref(v_val_3412_);
                    lean_dec(v___x_3411_);
                    lean_dec(v_discr_3410_);
                    v___x_3434_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3434_, 0, v_b_3419_);
                    return v___x_3434_;
                } else {
                    v_snd_3435_ = lean_ctor_get(v_b_3419_, 1);
                    v_fst_3436_ = lean_ctor_get(v_b_3419_, 0);
                    v_isSharedCheck_3594_ = (!lean_is_exclusive(v_b_3419_)) as u8;
                    if v_isSharedCheck_3594_ == 0 {
                        v___x_3438_ = v_b_3419_;
                        v_isShared_3439_ = v_isSharedCheck_3594_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_snd_3435_);
                        lean_inc(v_fst_3436_);
                        lean_dec(v_b_3419_);
                        v___x_3438_ = lean_box(0);
                        v_isShared_3439_ = v_isSharedCheck_3594_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3430_ = 1usize;
                v___x_3431_ = lean_usize_add(v_i_3418_, v___x_3430_);
                v_i_3418_ = v___x_3431_;
                v_b_3419_ = v_a_3429_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_3440_ = lean_ctor_get(v_snd_3435_, 0);
                v_snd_3441_ = lean_ctor_get(v_snd_3435_, 1);
                v_isSharedCheck_3593_ = (!lean_is_exclusive(v_snd_3435_)) as u8;
                if v_isSharedCheck_3593_ == 0 {
                    v___x_3443_ = v_snd_3435_;
                    v_isShared_3444_ = v_isSharedCheck_3593_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snd_3441_);
                    lean_inc(v_fst_3440_);
                    lean_dec(v_snd_3435_);
                    v___x_3443_ = lean_box(0);
                    v_isShared_3444_ = v_isSharedCheck_3593_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3445_ = 0;
                v_a_3446_ = lean_array_uget_borrowed(v_as_3416_, v_i_3418_);
                if lean_obj_tag(v_a_3446_) == 0 {
                    lean_del_object(v___x_3443_);
                    lean_del_object(v___x_3438_);
                    v_ctorName_3465_ = lean_ctor_get(v_a_3446_, 0);
                    v_params_3466_ = lean_ctor_get(v_a_3446_, 1);
                    v_code_3467_ = lean_ctor_get(v_a_3446_, 2);
                    lean_inc_ref(v_params_3466_);
                    lean_inc(v_ctorName_3465_);
                    lean_inc(v_discr_3410_);
                    v___x_3468_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_3410_, v_ctorName_3465_, v_params_3466_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
                    if lean_obj_tag(v___x_3468_) == 0 {
                        v_a_3469_ = lean_ctor_get(v___x_3468_, 0);
                        lean_inc(v_a_3469_);
                        lean_dec_ref_known(v___x_3468_, 1);
                        lean_inc_ref(v_code_3467_);
                        v___x_3470_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_3467_, v___y_3420_, v___y_3421_, v_a_3469_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
                        lean_dec(v_a_3469_);
                        if lean_obj_tag(v___x_3470_) == 0 {
                            v_a_3471_ = lean_ctor_get(v___x_3470_, 0);
                            lean_inc(v_a_3471_);
                            lean_dec_ref_known(v___x_3470_, 1);
                            v___x_3472_ = l_Lean_NameSet_contains(v___x_3411_, v_ctorName_3465_);
                            if v___x_3472_ == 0 {
                                lean_inc_ref(v_a_3446_);
                                v___x_3473_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3446_, v_a_3471_);
                                v___x_3474_ = lean_array_push(v_snd_3441_, v___x_3473_);
                                v___x_3475_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3475_, 0, v_fst_3440_);
                                lean_ctor_set(v___x_3475_, 1, v___x_3474_);
                                v___x_3476_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3476_, 0, v_fst_3436_);
                                lean_ctor_set(v___x_3476_, 1, v___x_3475_);
                                v_a_3429_ = v___x_3476_;
                                state = 1;
                                continue;
                            } else {
                                v_paramIdx_3477_ = lean_ctor_get(v_val_3412_, 0);
                                v___x_3478_ = 0;
                                lean_inc(v_a_3471_);
                                lean_inc_ref(v_params_3466_);
                                lean_inc_ref(v_fst_3413_);
                                v___x_3479_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_3413_, v_params_3414_, v_paramIdx_3477_, v_params_3466_, v_a_3471_, v___x_3478_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
                                if lean_obj_tag(v___x_3479_) == 0 {
                                    v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
                                    lean_inc(v_a_3480_);
                                    lean_dec_ref_known(v___x_3479_, 1);
                                    v_decl_3481_ = lean_ctor_get(v_a_3480_, 0);
                                    v_dependsOnDiscr_3482_ = lean_ctor_get_uint8(
                                        v_a_3480_,
                                        (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                                    );
                                    v___x_3483_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                                        v___x_3445_,
                                        v_a_3471_,
                                        v___y_3424_,
                                    );
                                    lean_dec(v_a_3471_);
                                    if lean_obj_tag(v___x_3483_) == 0 {
                                        lean_dec_ref_known(v___x_3483_, 1);
                                        v_fvarId_3484_ = lean_ctor_get(v_decl_3481_, 0);
                                        lean_inc(v_fvarId_3484_);
                                        lean_inc_ref(v_decl_3481_);
                                        v___x_3485_ = lean_alloc_ctor(2, 1, (0) as u32);
                                        lean_ctor_set(v___x_3485_, 0, v_decl_3481_);
                                        v___x_3486_ = lean_array_push(v_fst_3440_, v___x_3485_);
                                        lean_inc(v_ctorName_3465_);
                                        v___x_3487_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_ctorName_3465_, v_a_3480_, v_fst_3436_);
                                        lean_inc_ref(v_params_3466_);
                                        lean_inc(v_paramIdx_3477_);
                                        lean_inc_ref(v_params_3414_);
                                        v___x_3488_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_3414_, v_paramIdx_3477_, v_params_3466_, v_dependsOnDiscr_3482_);
                                        v___x_3489_ = lean_alloc_ctor(3, 2, (0) as u32);
                                        lean_ctor_set(v___x_3489_, 0, v_fvarId_3484_);
                                        lean_ctor_set(v___x_3489_, 1, v___x_3488_);
                                        lean_inc_ref(v_a_3446_);
                                        v___x_3490_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3446_, v___x_3489_);
                                        v___x_3491_ = lean_array_push(v_snd_3441_, v___x_3490_);
                                        v___x_3492_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_3492_, 0, v___x_3486_);
                                        lean_ctor_set(v___x_3492_, 1, v___x_3491_);
                                        v___x_3493_ = lean_alloc_ctor(0, 2, (0) as u32);
                                        lean_ctor_set(v___x_3493_, 0, v___x_3487_);
                                        lean_ctor_set(v___x_3493_, 1, v___x_3492_);
                                        v_a_3429_ = v___x_3493_;
                                        state = 1;
                                        continue;
                                    } else {
                                        lean_dec(v_a_3480_);
                                        lean_dec(v_snd_3441_);
                                        lean_dec(v_fst_3440_);
                                        lean_dec(v_fst_3436_);
                                        lean_dec_ref(v_params_3414_);
                                        lean_dec_ref(v_fst_3413_);
                                        lean_dec_ref(v_val_3412_);
                                        lean_dec(v___x_3411_);
                                        lean_dec(v_discr_3410_);
                                        v_a_3494_ = lean_ctor_get(v___x_3483_, 0);
                                        v_isSharedCheck_3501_ =
                                            (!lean_is_exclusive(v___x_3483_)) as u8;
                                        if v_isSharedCheck_3501_ == 0 {
                                            v___x_3496_ = v___x_3483_;
                                            v_isShared_3497_ = v_isSharedCheck_3501_;
                                            state = 7;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3494_);
                                            lean_dec(v___x_3483_);
                                            v___x_3496_ = lean_box(0);
                                            v_isShared_3497_ = v_isSharedCheck_3501_;
                                            state = 7;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec(v_a_3471_);
                                    lean_dec(v_snd_3441_);
                                    lean_dec(v_fst_3440_);
                                    lean_dec(v_fst_3436_);
                                    lean_dec_ref(v_params_3414_);
                                    lean_dec_ref(v_fst_3413_);
                                    lean_dec_ref(v_val_3412_);
                                    lean_dec(v___x_3411_);
                                    lean_dec(v_discr_3410_);
                                    v_a_3502_ = lean_ctor_get(v___x_3479_, 0);
                                    v_isSharedCheck_3509_ = (!lean_is_exclusive(v___x_3479_)) as u8;
                                    if v_isSharedCheck_3509_ == 0 {
                                        v___x_3504_ = v___x_3479_;
                                        v_isShared_3505_ = v_isSharedCheck_3509_;
                                        state = 9;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3502_);
                                        lean_dec(v___x_3479_);
                                        v___x_3504_ = lean_box(0);
                                        v_isShared_3505_ = v_isSharedCheck_3509_;
                                        state = 9;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            lean_dec(v_snd_3441_);
                            lean_dec(v_fst_3440_);
                            lean_dec(v_fst_3436_);
                            lean_dec_ref(v_params_3414_);
                            lean_dec_ref(v_fst_3413_);
                            lean_dec_ref(v_val_3412_);
                            lean_dec(v___x_3411_);
                            lean_dec(v_discr_3410_);
                            v_a_3510_ = lean_ctor_get(v___x_3470_, 0);
                            v_isSharedCheck_3517_ = (!lean_is_exclusive(v___x_3470_)) as u8;
                            if v_isSharedCheck_3517_ == 0 {
                                v___x_3512_ = v___x_3470_;
                                v_isShared_3513_ = v_isSharedCheck_3517_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_3510_);
                                lean_dec(v___x_3470_);
                                v___x_3512_ = lean_box(0);
                                v_isShared_3513_ = v_isSharedCheck_3517_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_snd_3441_);
                        lean_dec(v_fst_3440_);
                        lean_dec(v_fst_3436_);
                        lean_dec_ref(v_params_3414_);
                        lean_dec_ref(v_fst_3413_);
                        lean_dec_ref(v_val_3412_);
                        lean_dec(v___x_3411_);
                        lean_dec(v_discr_3410_);
                        v_a_3518_ = lean_ctor_get(v___x_3468_, 0);
                        v_isSharedCheck_3525_ = (!lean_is_exclusive(v___x_3468_)) as u8;
                        if v_isSharedCheck_3525_ == 0 {
                            v___x_3520_ = v___x_3468_;
                            v_isShared_3521_ = v_isSharedCheck_3525_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3518_);
                            lean_dec(v___x_3468_);
                            v___x_3520_ = lean_box(0);
                            v_isShared_3521_ = v_isSharedCheck_3525_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    v_code_3526_ = lean_ctor_get(v_a_3446_, 0);
                    lean_inc_ref(v_code_3526_);
                    v___x_3527_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_3526_, v___y_3420_, v___y_3421_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
                    if lean_obj_tag(v___x_3527_) == 0 {
                        v_a_3528_ = lean_ctor_get(v___x_3527_, 0);
                        lean_inc(v_a_3528_);
                        lean_dec_ref_known(v___x_3527_, 1);
                        v___x_3534_ = l_Lean_Compiler_LCNF_Cases_getCtorNames___redArg(v_snd_3415_);
                        v___x_3582_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate_spec__0___closed__3;
                        v___x_3583_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__3(v___x_3534_, v___x_3582_, v___x_3411_);
                        v_a_3584_ = lean_ctor_get(v___x_3583_, 0);
                        lean_inc(v_a_3584_);
                        lean_dec_ref(v___x_3583_);
                        v___y_3536_ = v_a_3584_;
                        state = 16;
                        continue;
                    } else {
                        lean_del_object(v___x_3443_);
                        lean_dec(v_snd_3441_);
                        lean_dec(v_fst_3440_);
                        lean_del_object(v___x_3438_);
                        lean_dec(v_fst_3436_);
                        lean_dec_ref(v_params_3414_);
                        lean_dec_ref(v_fst_3413_);
                        lean_dec_ref(v_val_3412_);
                        lean_dec(v___x_3411_);
                        lean_dec(v_discr_3410_);
                        v_a_3585_ = lean_ctor_get(v___x_3527_, 0);
                        v_isSharedCheck_3592_ = (!lean_is_exclusive(v___x_3527_)) as u8;
                        if v_isSharedCheck_3592_ == 0 {
                            v___x_3587_ = v___x_3527_;
                            v_isShared_3588_ = v_isSharedCheck_3592_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_3585_);
                            lean_dec(v___x_3527_);
                            v___x_3587_ = lean_box(0);
                            v_isShared_3588_ = v_isSharedCheck_3592_;
                            state = 25;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v_fvarId_3454_ = lean_ctor_get(v___y_3448_, 0);
                lean_inc(v_fvarId_3454_);
                lean_dec_ref(v___y_3448_);
                lean_inc_ref(v_params_3414_);
                v___x_3455_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJmpArgsAtJp(v_params_3414_, v___y_3452_, v___y_3449_, v___y_3450_);
                v___x_3456_ = lean_alloc_ctor(3, 2, (0) as u32);
                lean_ctor_set(v___x_3456_, 0, v_fvarId_3454_);
                lean_ctor_set(v___x_3456_, 1, v___x_3455_);
                lean_inc(v_a_3446_);
                v___x_3457_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3446_, v___x_3456_);
                v___x_3458_ = lean_array_push(v_snd_3441_, v___x_3457_);
                if v_isShared_3444_ == 0 {
                    lean_ctor_set(v___x_3443_, 1, v___x_3458_);
                    lean_ctor_set(v___x_3443_, 0, v___y_3451_);
                    v___x_3460_ = v___x_3443_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___y_3451_);
                    lean_ctor_set(v_reuseFailAlloc_3464_, 1, v___x_3458_);
                    v___x_3460_ = v_reuseFailAlloc_3464_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3439_ == 0 {
                    lean_ctor_set(v___x_3438_, 1, v___x_3460_);
                    lean_ctor_set(v___x_3438_, 0, v_a_3453_);
                    v___x_3462_ = v___x_3438_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3453_);
                    lean_ctor_set(v_reuseFailAlloc_3463_, 1, v___x_3460_);
                    v___x_3462_ = v_reuseFailAlloc_3463_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_a_3429_ = v___x_3462_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_3497_ == 0 {
                    v___x_3499_ = v___x_3496_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3500_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3500_, 0, v_a_3494_);
                    v___x_3499_ = v_reuseFailAlloc_3500_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3499_;
            }
            9 => {
                if v_isShared_3505_ == 0 {
                    v___x_3507_ = v___x_3504_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3508_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3508_, 0, v_a_3502_);
                    v___x_3507_ = v_reuseFailAlloc_3508_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3507_;
            }
            11 => {
                if v_isShared_3513_ == 0 {
                    v___x_3515_ = v___x_3512_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3516_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3516_, 0, v_a_3510_);
                    v___x_3515_ = v_reuseFailAlloc_3516_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3515_;
            }
            13 => {
                if v_isShared_3521_ == 0 {
                    v___x_3523_ = v___x_3520_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3524_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3524_, 0, v_a_3518_);
                    v___x_3523_ = v_reuseFailAlloc_3524_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3523_;
            }
            15 => {
                lean_inc_ref(v_a_3446_);
                v___x_3530_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3446_, v_a_3528_);
                v___x_3531_ = lean_array_push(v_snd_3441_, v___x_3530_);
                v___x_3532_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3532_, 0, v_fst_3440_);
                lean_ctor_set(v___x_3532_, 1, v___x_3531_);
                v___x_3533_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_3533_, 0, v_fst_3436_);
                lean_ctor_set(v___x_3533_, 1, v___x_3532_);
                v_a_3429_ = v___x_3533_;
                state = 1;
                continue;
            }
            16 => {
                v_fst_3537_ = lean_ctor_get(v___y_3536_, 0);
                lean_inc(v_fst_3537_);
                lean_dec_ref(v___y_3536_);
                if lean_obj_tag(v_fst_3537_) == 0 {
                    lean_dec(v___x_3534_);
                    lean_del_object(v___x_3443_);
                    lean_del_object(v___x_3438_);
                    state = 15;
                    continue;
                } else {
                    v_val_3538_ = lean_ctor_get(v_fst_3537_, 0);
                    v_isSharedCheck_3581_ = (!lean_is_exclusive(v_fst_3537_)) as u8;
                    if v_isSharedCheck_3581_ == 0 {
                        v___x_3540_ = v_fst_3537_;
                        v_isShared_3541_ = v_isSharedCheck_3581_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_val_3538_);
                        lean_dec(v_fst_3537_);
                        v___x_3540_ = lean_box(0);
                        v_isShared_3541_ = v_isSharedCheck_3581_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                v___x_3542_ = (lean_unbox(v_val_3538_) as u8);
                lean_dec(v_val_3538_);
                if v___x_3542_ == 0 {
                    lean_del_object(v___x_3540_);
                    lean_dec(v___x_3534_);
                    lean_del_object(v___x_3443_);
                    lean_del_object(v___x_3438_);
                    state = 15;
                    continue;
                } else {
                    v_paramIdx_3543_ = lean_ctor_get(v_val_3412_, 0);
                    v___x_3544_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go___closed__1;
                    lean_inc(v_a_3528_);
                    lean_inc_ref(v_fst_3413_);
                    v___x_3545_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt(v_fst_3413_, v_params_3414_, v_paramIdx_3543_, v___x_3544_, v_a_3528_, v___x_3433_, v___y_3423_, v___y_3424_, v___y_3425_, v___y_3426_);
                    if lean_obj_tag(v___x_3545_) == 0 {
                        v_a_3546_ = lean_ctor_get(v___x_3545_, 0);
                        lean_inc(v_a_3546_);
                        lean_dec_ref_known(v___x_3545_, 1);
                        v_decl_3547_ = lean_ctor_get(v_a_3546_, 0);
                        lean_inc_ref(v_decl_3547_);
                        v_dependsOnDiscr_3548_ = lean_ctor_get_uint8(
                            v_a_3546_,
                            (core::mem::size_of::<*mut LeanObject>() * 1 + 1) as u32,
                        );
                        v___x_3549_ = l_Lean_Compiler_LCNF_eraseCode___redArg(
                            v___x_3445_,
                            v_a_3528_,
                            v___y_3424_,
                        );
                        lean_dec(v_a_3528_);
                        if lean_obj_tag(v___x_3549_) == 0 {
                            lean_dec_ref_known(v___x_3549_, 1);
                            lean_inc(v___x_3411_);
                            v___x_3550_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_3534_, v_a_3546_, v_fst_3436_, v___x_3411_);
                            lean_dec(v___x_3534_);
                            if lean_obj_tag(v___x_3550_) == 0 {
                                v_a_3551_ = lean_ctor_get(v___x_3550_, 0);
                                lean_inc(v_a_3551_);
                                lean_dec_ref_known(v___x_3550_, 1);
                                lean_inc_ref(v_decl_3547_);
                                if v_isShared_3541_ == 0 {
                                    lean_ctor_set_tag(v___x_3540_, 2);
                                    lean_ctor_set(v___x_3540_, 0, v_decl_3547_);
                                    v___x_3553_ = v___x_3540_;
                                    state = 18;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3556_ = lean_alloc_ctor(2, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_decl_3547_);
                                    v___x_3553_ = v_reuseFailAlloc_3556_;
                                    state = 18;
                                    continue;
                                }
                            } else {
                                lean_dec_ref(v_decl_3547_);
                                lean_del_object(v___x_3540_);
                                lean_del_object(v___x_3443_);
                                lean_dec(v_snd_3441_);
                                lean_dec(v_fst_3440_);
                                lean_del_object(v___x_3438_);
                                lean_dec_ref(v_params_3414_);
                                lean_dec_ref(v_fst_3413_);
                                lean_dec_ref(v_val_3412_);
                                lean_dec(v___x_3411_);
                                lean_dec(v_discr_3410_);
                                v_a_3557_ = lean_ctor_get(v___x_3550_, 0);
                                v_isSharedCheck_3564_ = (!lean_is_exclusive(v___x_3550_)) as u8;
                                if v_isSharedCheck_3564_ == 0 {
                                    v___x_3559_ = v___x_3550_;
                                    v_isShared_3560_ = v_isSharedCheck_3564_;
                                    state = 19;
                                    continue;
                                } else {
                                    lean_inc(v_a_3557_);
                                    lean_dec(v___x_3550_);
                                    v___x_3559_ = lean_box(0);
                                    v_isShared_3560_ = v_isSharedCheck_3564_;
                                    state = 19;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_decl_3547_);
                            lean_dec(v_a_3546_);
                            lean_del_object(v___x_3540_);
                            lean_dec(v___x_3534_);
                            lean_del_object(v___x_3443_);
                            lean_dec(v_snd_3441_);
                            lean_dec(v_fst_3440_);
                            lean_del_object(v___x_3438_);
                            lean_dec(v_fst_3436_);
                            lean_dec_ref(v_params_3414_);
                            lean_dec_ref(v_fst_3413_);
                            lean_dec_ref(v_val_3412_);
                            lean_dec(v___x_3411_);
                            lean_dec(v_discr_3410_);
                            v_a_3565_ = lean_ctor_get(v___x_3549_, 0);
                            v_isSharedCheck_3572_ = (!lean_is_exclusive(v___x_3549_)) as u8;
                            if v_isSharedCheck_3572_ == 0 {
                                v___x_3567_ = v___x_3549_;
                                v_isShared_3568_ = v_isSharedCheck_3572_;
                                state = 21;
                                continue;
                            } else {
                                lean_inc(v_a_3565_);
                                lean_dec(v___x_3549_);
                                v___x_3567_ = lean_box(0);
                                v_isShared_3568_ = v_isSharedCheck_3572_;
                                state = 21;
                                continue;
                            }
                        }
                    } else {
                        lean_del_object(v___x_3540_);
                        lean_dec(v___x_3534_);
                        lean_dec(v_a_3528_);
                        lean_del_object(v___x_3443_);
                        lean_dec(v_snd_3441_);
                        lean_dec(v_fst_3440_);
                        lean_del_object(v___x_3438_);
                        lean_dec(v_fst_3436_);
                        lean_dec_ref(v_params_3414_);
                        lean_dec_ref(v_fst_3413_);
                        lean_dec_ref(v_val_3412_);
                        lean_dec(v___x_3411_);
                        lean_dec(v_discr_3410_);
                        v_a_3573_ = lean_ctor_get(v___x_3545_, 0);
                        v_isSharedCheck_3580_ = (!lean_is_exclusive(v___x_3545_)) as u8;
                        if v_isSharedCheck_3580_ == 0 {
                            v___x_3575_ = v___x_3545_;
                            v_isShared_3576_ = v_isSharedCheck_3580_;
                            state = 23;
                            continue;
                        } else {
                            lean_inc(v_a_3573_);
                            lean_dec(v___x_3545_);
                            v___x_3575_ = lean_box(0);
                            v_isShared_3576_ = v_isSharedCheck_3580_;
                            state = 23;
                            continue;
                        }
                    }
                }
            }
            18 => {
                v___x_3554_ = lean_array_push(v_fst_3440_, v___x_3553_);
                v_a_3555_ = lean_ctor_get(v_a_3551_, 0);
                lean_inc(v_a_3555_);
                lean_dec(v_a_3551_);
                lean_inc(v_paramIdx_3543_);
                v___y_3448_ = v_decl_3547_;
                v___y_3449_ = v___x_3544_;
                v___y_3450_ = v_dependsOnDiscr_3548_;
                v___y_3451_ = v___x_3554_;
                v___y_3452_ = v_paramIdx_3543_;
                v_a_3453_ = v_a_3555_;
                state = 4;
                continue;
            }
            19 => {
                if v_isShared_3560_ == 0 {
                    v___x_3562_ = v___x_3559_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3563_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3563_, 0, v_a_3557_);
                    v___x_3562_ = v_reuseFailAlloc_3563_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3562_;
            }
            21 => {
                if v_isShared_3568_ == 0 {
                    v___x_3570_ = v___x_3567_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3571_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3571_, 0, v_a_3565_);
                    v___x_3570_ = v_reuseFailAlloc_3571_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3570_;
            }
            23 => {
                if v_isShared_3576_ == 0 {
                    v___x_3578_ = v___x_3575_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3579_, 0, v_a_3573_);
                    v___x_3578_ = v_reuseFailAlloc_3579_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3578_;
            }
            25 => {
                if v_isShared_3588_ == 0 {
                    v___x_3590_ = v___x_3587_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3591_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3591_, 0, v_a_3585_);
                    v___x_3590_ = v_reuseFailAlloc_3591_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3590_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(
    mut v_decl_3595_: *mut LeanObject,
    mut v_k_3596_: *mut LeanObject,
    mut v_a_3597_: *mut LeanObject,
    mut v_a_3598_: *mut LeanObject,
    mut v_a_3599_: *mut LeanObject,
    mut v_a_3600_: *mut LeanObject,
    mut v_a_3601_: *mut LeanObject,
    mut v_a_3602_: *mut LeanObject,
    mut v_a_3603_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_fvarId_3605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3608_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3610_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3613_: u8 = 0;
    let mut v_ctorNames_3614_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3616_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_3618_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_3619_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3622_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3623_: usize = 0;
    let mut v___x_3624_: usize = 0;
    let mut v___x_3625_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3636_: u8 = 0;
    let mut v___x_3637_: u8 = 0;
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3647_: u8 = 0;
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3655_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3658_: u8 = 0;
    let mut v_a_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3662_: u8 = 0;
    let mut v___x_3664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3666_: u8 = 0;
    let mut v_a_3667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3670_: u8 = 0;
    let mut v___x_3672_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3674_: u8 = 0;
    let mut v_isSharedCheck_3675_: u8 = 0;
    let mut v_a_3676_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3679_: u8 = 0;
    let mut v___x_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3683_: u8 = 0;
    let mut v___x_3684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3686_: u8 = 0;
    let mut v___x_3687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3688_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fvarId_3605_ = lean_ctor_get(v_decl_3595_, 0);
                v_params_3606_ = lean_ctor_get(v_decl_3595_, 2);
                lean_inc_ref(v_params_3606_);
                v_type_3607_ = lean_ctor_get(v_decl_3595_, 3);
                lean_inc_ref(v_type_3607_);
                v_value_3608_ = lean_ctor_get(v_decl_3595_, 4);
                v___x_3609_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_collectJpCasesInfo_go_spec__0___redArg(v_a_3597_, v_fvarId_3605_);
                if lean_obj_tag(v___x_3609_) == 1 {
                    v_val_3610_ = lean_ctor_get(v___x_3609_, 0);
                    v_isSharedCheck_3686_ = (!lean_is_exclusive(v___x_3609_)) as u8;
                    if v_isSharedCheck_3686_ == 0 {
                        v___x_3612_ = v___x_3609_;
                        v_isShared_3613_ = v_isSharedCheck_3686_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3610_);
                        lean_dec(v___x_3609_);
                        v___x_3612_ = lean_box(0);
                        v_isShared_3613_ = v_isSharedCheck_3686_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3609_);
                    lean_dec_ref(v_type_3607_);
                    lean_dec_ref(v_params_3606_);
                    lean_dec_ref(v_k_3596_);
                    lean_dec_ref(v_decl_3595_);
                    v___x_3687_ = lean_box(0);
                    v___x_3688_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3688_, 0, v___x_3687_);
                    return v___x_3688_;
                }
            }
            1 => {
                v_ctorNames_3614_ = lean_ctor_get(v_val_3610_, 1);
                lean_inc(v_ctorNames_3614_);
                if lean_obj_tag(v_ctorNames_3614_) == 0 {
                    v___x_3615_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_extractJpCases(v_value_3608_);
                    v_snd_3616_ = lean_ctor_get(v___x_3615_, 1);
                    lean_inc(v_snd_3616_);
                    v_fst_3617_ = lean_ctor_get(v___x_3615_, 0);
                    lean_inc_n(v_fst_3617_, 2);
                    lean_dec_ref(v___x_3615_);
                    v_typeName_3618_ = lean_ctor_get(v_snd_3616_, 0);
                    lean_inc(v_typeName_3618_);
                    v_resultType_3619_ = lean_ctor_get(v_snd_3616_, 1);
                    lean_inc_ref(v_resultType_3619_);
                    v_discr_3620_ = lean_ctor_get(v_snd_3616_, 2);
                    lean_inc_n(v_discr_3620_, 2);
                    v_alts_3621_ = lean_ctor_get(v_snd_3616_, 3);
                    lean_inc_ref(v_alts_3621_);
                    v___x_3622_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___closed__1;
                    v_sz_3623_ = lean_array_size(v_alts_3621_);
                    v___x_3624_ = 0usize;
                    lean_inc_ref(v_params_3606_);
                    v___x_3625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_3620_, v_ctorNames_3614_, v_val_3610_, v_fst_3617_, v_params_3606_, v_snd_3616_, v_alts_3621_, v_sz_3623_, v___x_3624_, v___x_3622_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
                    lean_dec_ref(v_alts_3621_);
                    lean_dec(v_snd_3616_);
                    if lean_obj_tag(v___x_3625_) == 0 {
                        v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
                        lean_inc(v_a_3626_);
                        lean_dec_ref_known(v___x_3625_, 1);
                        v___x_3627_ = lean_st_ref_take(v_a_3598_);
                        v_fst_3628_ = lean_ctor_get(v_a_3626_, 0);
                        lean_inc(v_fst_3628_);
                        v_snd_3629_ = lean_ctor_get(v_a_3626_, 1);
                        lean_inc(v_snd_3629_);
                        lean_dec(v_a_3626_);
                        lean_inc(v_fvarId_3605_);
                        v___x_3630_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fvarId_3605_, v_fst_3628_, v___x_3627_);
                        v___x_3631_ = lean_st_ref_set(v_a_3598_, v___x_3630_);
                        v_fst_3632_ = lean_ctor_get(v_snd_3629_, 0);
                        v_snd_3633_ = lean_ctor_get(v_snd_3629_, 1);
                        v_isSharedCheck_3675_ = (!lean_is_exclusive(v_snd_3629_)) as u8;
                        if v_isSharedCheck_3675_ == 0 {
                            v___x_3635_ = v_snd_3629_;
                            v_isShared_3636_ = v_isSharedCheck_3675_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_snd_3633_);
                            lean_inc(v_fst_3632_);
                            lean_dec(v_snd_3629_);
                            v___x_3635_ = lean_box(0);
                            v_isShared_3636_ = v_isSharedCheck_3675_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec(v_discr_3620_);
                        lean_dec_ref(v_resultType_3619_);
                        lean_dec(v_typeName_3618_);
                        lean_dec(v_fst_3617_);
                        lean_del_object(v___x_3612_);
                        lean_dec_ref(v_type_3607_);
                        lean_dec_ref(v_params_3606_);
                        lean_dec_ref(v_k_3596_);
                        lean_dec_ref(v_decl_3595_);
                        v_a_3676_ = lean_ctor_get(v___x_3625_, 0);
                        v_isSharedCheck_3683_ = (!lean_is_exclusive(v___x_3625_)) as u8;
                        if v_isSharedCheck_3683_ == 0 {
                            v___x_3678_ = v___x_3625_;
                            v_isShared_3679_ = v_isSharedCheck_3683_;
                            state = 11;
                            continue;
                        } else {
                            lean_inc(v_a_3676_);
                            lean_dec(v___x_3625_);
                            v___x_3678_ = lean_box(0);
                            v_isShared_3679_ = v_isSharedCheck_3683_;
                            state = 11;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3612_);
                    lean_dec(v_val_3610_);
                    lean_dec_ref(v_type_3607_);
                    lean_dec_ref(v_params_3606_);
                    lean_dec_ref(v_k_3596_);
                    lean_dec_ref(v_decl_3595_);
                    v___x_3684_ = lean_box(0);
                    v___x_3685_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3685_, 0, v___x_3684_);
                    return v___x_3685_;
                }
            }
            2 => {
                v___x_3637_ = 0;
                v___x_3638_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_3638_, 0, v_typeName_3618_);
                lean_ctor_set(v___x_3638_, 1, v_resultType_3619_);
                lean_ctor_set(v___x_3638_, 2, v_discr_3620_);
                lean_ctor_set(v___x_3638_, 3, v_snd_3633_);
                v___x_3639_ = lean_alloc_ctor(4, 1, (0) as u32);
                lean_ctor_set(v___x_3639_, 0, v___x_3638_);
                v___x_3640_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3637_, v_fst_3617_, v___x_3639_);
                lean_dec(v_fst_3617_);
                v___x_3641_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3637_, v_decl_3595_, v_type_3607_, v_params_3606_, v___x_3640_, v_a_3601_);
                if lean_obj_tag(v___x_3641_) == 0 {
                    v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
                    lean_inc(v_a_3642_);
                    lean_dec_ref_known(v___x_3641_, 1);
                    v___x_3643_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_3596_, v_a_3597_, v_a_3598_, v_a_3599_, v_a_3600_, v_a_3601_, v_a_3602_, v_a_3603_);
                    if lean_obj_tag(v___x_3643_) == 0 {
                        v_a_3644_ = lean_ctor_get(v___x_3643_, 0);
                        v_isSharedCheck_3658_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                        if v_isSharedCheck_3658_ == 0 {
                            v___x_3646_ = v___x_3643_;
                            v_isShared_3647_ = v_isSharedCheck_3658_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3644_);
                            lean_dec(v___x_3643_);
                            v___x_3646_ = lean_box(0);
                            v_isShared_3647_ = v_isSharedCheck_3658_;
                            state = 3;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_3642_);
                        lean_del_object(v___x_3635_);
                        lean_dec(v_fst_3632_);
                        lean_del_object(v___x_3612_);
                        v_a_3659_ = lean_ctor_get(v___x_3643_, 0);
                        v_isSharedCheck_3666_ = (!lean_is_exclusive(v___x_3643_)) as u8;
                        if v_isSharedCheck_3666_ == 0 {
                            v___x_3661_ = v___x_3643_;
                            v_isShared_3662_ = v_isSharedCheck_3666_;
                            state = 7;
                            continue;
                        } else {
                            lean_inc(v_a_3659_);
                            lean_dec(v___x_3643_);
                            v___x_3661_ = lean_box(0);
                            v_isShared_3662_ = v_isSharedCheck_3666_;
                            state = 7;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3635_);
                    lean_dec(v_fst_3632_);
                    lean_del_object(v___x_3612_);
                    lean_dec_ref(v_k_3596_);
                    v_a_3667_ = lean_ctor_get(v___x_3641_, 0);
                    v_isSharedCheck_3674_ = (!lean_is_exclusive(v___x_3641_)) as u8;
                    if v_isSharedCheck_3674_ == 0 {
                        v___x_3669_ = v___x_3641_;
                        v_isShared_3670_ = v_isSharedCheck_3674_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_3667_);
                        lean_dec(v___x_3641_);
                        v___x_3669_ = lean_box(0);
                        v_isShared_3670_ = v_isSharedCheck_3674_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3636_ == 0 {
                    lean_ctor_set_tag(v___x_3635_, 2);
                    lean_ctor_set(v___x_3635_, 1, v_a_3644_);
                    lean_ctor_set(v___x_3635_, 0, v_a_3642_);
                    v___x_3649_ = v___x_3635_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3657_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3642_);
                    lean_ctor_set(v_reuseFailAlloc_3657_, 1, v_a_3644_);
                    v___x_3649_ = v_reuseFailAlloc_3657_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3650_ =
                    l_Lean_Compiler_LCNF_attachCodeDecls(v___x_3637_, v_fst_3632_, v___x_3649_);
                lean_dec(v_fst_3632_);
                if v_isShared_3613_ == 0 {
                    lean_ctor_set(v___x_3612_, 0, v___x_3650_);
                    v___x_3652_ = v___x_3612_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3650_);
                    v___x_3652_ = v_reuseFailAlloc_3656_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_3647_ == 0 {
                    lean_ctor_set(v___x_3646_, 0, v___x_3652_);
                    v___x_3654_ = v___x_3646_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
                    v___x_3654_ = v_reuseFailAlloc_3655_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3654_;
            }
            7 => {
                if v_isShared_3662_ == 0 {
                    v___x_3664_ = v___x_3661_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
                    v___x_3664_ = v_reuseFailAlloc_3665_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3664_;
            }
            9 => {
                if v_isShared_3670_ == 0 {
                    v___x_3672_ = v___x_3669_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
                    v___x_3672_ = v_reuseFailAlloc_3673_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3672_;
            }
            11 => {
                if v_isShared_3679_ == 0 {
                    v___x_3681_ = v___x_3678_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3682_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_a_3676_);
                    v___x_3681_ = v_reuseFailAlloc_3682_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3681_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(
    mut v_code_3689_: *mut LeanObject,
    mut v_a_3690_: *mut LeanObject,
    mut v_a_3691_: *mut LeanObject,
    mut v_a_3692_: *mut LeanObject,
    mut v_a_3693_: *mut LeanObject,
    mut v_a_3694_: *mut LeanObject,
    mut v_a_3695_: *mut LeanObject,
    mut v_a_3696_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_decl_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3704_: u8 = 0;
    let mut v___y_3706_: u8 = 0;
    let mut v___x_3708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3709_: u8 = 0;
    let mut v___x_3711_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3713_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3716_: u8 = 0;
    let mut v_unused_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3722_: usize = 0;
    let mut v___x_3723_: usize = 0;
    let mut v___x_3724_: u8 = 0;
    let mut v___x_3725_: usize = 0;
    let mut v___x_3726_: u8 = 0;
    let mut v_isSharedCheck_3727_: u8 = 0;
    let mut v_decl_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3730_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3732_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3733_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: u8 = 0;
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3742_: u8 = 0;
    let mut v___y_3744_: u8 = 0;
    let mut v___x_3746_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3747_: u8 = 0;
    let mut v___x_3749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3753_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3754_: u8 = 0;
    let mut v_unused_3755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: usize = 0;
    let mut v___x_3761_: usize = 0;
    let mut v___x_3762_: u8 = 0;
    let mut v___x_3763_: usize = 0;
    let mut v___x_3764_: usize = 0;
    let mut v___x_3765_: u8 = 0;
    let mut v_isSharedCheck_3766_: u8 = 0;
    let mut v_a_3767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3770_: u8 = 0;
    let mut v___x_3772_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3773_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3774_: u8 = 0;
    let mut v_decl_3775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_3776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3777_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3780_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3781_: u8 = 0;
    let mut v_val_3782_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3784_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3786_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3787_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3791_: u8 = 0;
    let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3798_: u8 = 0;
    let mut v___y_3800_: u8 = 0;
    let mut v___x_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3803_: u8 = 0;
    let mut v___x_3805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3810_: u8 = 0;
    let mut v_unused_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3816_: usize = 0;
    let mut v___x_3817_: usize = 0;
    let mut v___x_3818_: u8 = 0;
    let mut v___x_3819_: usize = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___x_3821_: u8 = 0;
    let mut v_isSharedCheck_3822_: u8 = 0;
    let mut v_a_3823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3826_: u8 = 0;
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3830_: u8 = 0;
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut v_a_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3835_: u8 = 0;
    let mut v___x_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3839_: u8 = 0;
    let mut v_fvarId_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v_args_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3846_: u8 = 0;
    let mut v_val_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3852_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3854_: u8 = 0;
    let mut v_a_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3858_: u8 = 0;
    let mut v___x_3860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3862_: u8 = 0;
    let mut v_cases_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeName_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_resultType_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_discr_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_alts_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3876_: u8 = 0;
    let mut v___x_3877_: usize = 0;
    let mut v___x_3878_: usize = 0;
    let mut v___x_3879_: u8 = 0;
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3882_: u8 = 0;
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3892_: u8 = 0;
    let mut v_unused_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_a_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3900_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3901_: u8 = 0;
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3905_: u8 = 0;
    let mut v_isSharedCheck_3906_: u8 = 0;
    let mut v___x_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match lean_obj_tag(v_code_3689_) {
                0 => {
                    v_decl_3698_ = lean_ctor_get(v_code_3689_, 0);
                    v_k_3699_ = lean_ctor_get(v_code_3689_, 1);
                    lean_inc_ref(v_k_3699_);
                    v___x_3700_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_3699_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                    if lean_obj_tag(v___x_3700_) == 0 {
                        v_a_3701_ = lean_ctor_get(v___x_3700_, 0);
                        v_isSharedCheck_3727_ = (!lean_is_exclusive(v___x_3700_)) as u8;
                        if v_isSharedCheck_3727_ == 0 {
                            v___x_3703_ = v___x_3700_;
                            v_isShared_3704_ = v_isSharedCheck_3727_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3701_);
                            lean_dec(v___x_3700_);
                            v___x_3703_ = lean_box(0);
                            v_isShared_3704_ = v_isSharedCheck_3727_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_3689_, 2);
                        return v___x_3700_;
                    }
                }
                1 => {
                    v_decl_3728_ = lean_ctor_get(v_code_3689_, 0);
                    v_k_3729_ = lean_ctor_get(v_code_3689_, 1);
                    v_params_3730_ = lean_ctor_get(v_decl_3728_, 2);
                    v_type_3731_ = lean_ctor_get(v_decl_3728_, 3);
                    v_value_3732_ = lean_ctor_get(v_decl_3728_, 4);
                    lean_inc_ref(v_value_3732_);
                    v___x_3733_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_3732_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                    if lean_obj_tag(v___x_3733_) == 0 {
                        v_a_3734_ = lean_ctor_get(v___x_3733_, 0);
                        lean_inc(v_a_3734_);
                        lean_dec_ref_known(v___x_3733_, 1);
                        v___x_3735_ = 0;
                        lean_inc_ref(v_params_3730_);
                        lean_inc_ref(v_type_3731_);
                        lean_inc_ref(v_decl_3728_);
                        v___x_3736_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3735_, v_decl_3728_, v_type_3731_, v_params_3730_, v_a_3734_, v_a_3694_);
                        if lean_obj_tag(v___x_3736_) == 0 {
                            v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
                            lean_inc(v_a_3737_);
                            lean_dec_ref_known(v___x_3736_, 1);
                            lean_inc_ref(v_k_3729_);
                            v___x_3738_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_3729_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                            if lean_obj_tag(v___x_3738_) == 0 {
                                v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
                                v_isSharedCheck_3766_ = (!lean_is_exclusive(v___x_3738_)) as u8;
                                if v_isSharedCheck_3766_ == 0 {
                                    v___x_3741_ = v___x_3738_;
                                    v_isShared_3742_ = v_isSharedCheck_3766_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_3739_);
                                    lean_dec(v___x_3738_);
                                    v___x_3741_ = lean_box(0);
                                    v_isShared_3742_ = v_isSharedCheck_3766_;
                                    state = 7;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3737_);
                                lean_dec_ref_known(v_code_3689_, 2);
                                return v___x_3738_;
                            }
                        } else {
                            lean_dec_ref_known(v_code_3689_, 2);
                            v_a_3767_ = lean_ctor_get(v___x_3736_, 0);
                            v_isSharedCheck_3774_ = (!lean_is_exclusive(v___x_3736_)) as u8;
                            if v_isSharedCheck_3774_ == 0 {
                                v___x_3769_ = v___x_3736_;
                                v_isShared_3770_ = v_isSharedCheck_3774_;
                                state = 13;
                                continue;
                            } else {
                                lean_inc(v_a_3767_);
                                lean_dec(v___x_3736_);
                                v___x_3769_ = lean_box(0);
                                v_isShared_3770_ = v_isSharedCheck_3774_;
                                state = 13;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_3689_, 2);
                        return v___x_3733_;
                    }
                }
                2 => {
                    v_decl_3775_ = lean_ctor_get(v_code_3689_, 0);
                    v_k_3776_ = lean_ctor_get(v_code_3689_, 1);
                    lean_inc_ref(v_k_3776_);
                    lean_inc_ref(v_decl_3775_);
                    v___x_3777_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_3775_, v_k_3776_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                    if lean_obj_tag(v___x_3777_) == 0 {
                        v_a_3778_ = lean_ctor_get(v___x_3777_, 0);
                        v_isSharedCheck_3831_ = (!lean_is_exclusive(v___x_3777_)) as u8;
                        if v_isSharedCheck_3831_ == 0 {
                            v___x_3780_ = v___x_3777_;
                            v_isShared_3781_ = v_isSharedCheck_3831_;
                            state = 15;
                            continue;
                        } else {
                            lean_inc(v_a_3778_);
                            lean_dec(v___x_3777_);
                            v___x_3780_ = lean_box(0);
                            v_isShared_3781_ = v_isSharedCheck_3831_;
                            state = 15;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_3689_, 2);
                        v_a_3832_ = lean_ctor_get(v___x_3777_, 0);
                        v_isSharedCheck_3839_ = (!lean_is_exclusive(v___x_3777_)) as u8;
                        if v_isSharedCheck_3839_ == 0 {
                            v___x_3834_ = v___x_3777_;
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 25;
                            continue;
                        } else {
                            lean_inc(v_a_3832_);
                            lean_dec(v___x_3777_);
                            v___x_3834_ = lean_box(0);
                            v_isShared_3835_ = v_isSharedCheck_3839_;
                            state = 25;
                            continue;
                        }
                    }
                }
                3 => {
                    v_fvarId_3840_ = lean_ctor_get(v_code_3689_, 0);
                    v_args_3841_ = lean_ctor_get(v_code_3689_, 1);
                    lean_inc_ref(v_args_3841_);
                    v___x_3842_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJmp_x3f(v_fvarId_3840_, v_args_3841_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                    if lean_obj_tag(v___x_3842_) == 0 {
                        v_a_3843_ = lean_ctor_get(v___x_3842_, 0);
                        v_isSharedCheck_3854_ = (!lean_is_exclusive(v___x_3842_)) as u8;
                        if v_isSharedCheck_3854_ == 0 {
                            v___x_3845_ = v___x_3842_;
                            v_isShared_3846_ = v_isSharedCheck_3854_;
                            state = 27;
                            continue;
                        } else {
                            lean_inc(v_a_3843_);
                            lean_dec(v___x_3842_);
                            v___x_3845_ = lean_box(0);
                            v_isShared_3846_ = v_isSharedCheck_3854_;
                            state = 27;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_code_3689_, 2);
                        v_a_3855_ = lean_ctor_get(v___x_3842_, 0);
                        v_isSharedCheck_3862_ = (!lean_is_exclusive(v___x_3842_)) as u8;
                        if v_isSharedCheck_3862_ == 0 {
                            v___x_3857_ = v___x_3842_;
                            v_isShared_3858_ = v_isSharedCheck_3862_;
                            state = 30;
                            continue;
                        } else {
                            lean_inc(v_a_3855_);
                            lean_dec(v___x_3842_);
                            v___x_3857_ = lean_box(0);
                            v_isShared_3858_ = v_isSharedCheck_3862_;
                            state = 30;
                            continue;
                        }
                    }
                }
                4 => {
                    v_cases_3863_ = lean_ctor_get(v_code_3689_, 0);
                    lean_inc_ref(v_cases_3863_);
                    v_typeName_3864_ = lean_ctor_get(v_cases_3863_, 0);
                    v_resultType_3865_ = lean_ctor_get(v_cases_3863_, 1);
                    v_discr_3866_ = lean_ctor_get(v_cases_3863_, 2);
                    v_alts_3867_ = lean_ctor_get(v_cases_3863_, 3);
                    v_isSharedCheck_3906_ = (!lean_is_exclusive(v_cases_3863_)) as u8;
                    if v_isSharedCheck_3906_ == 0 {
                        v___x_3869_ = v_cases_3863_;
                        v_isShared_3870_ = v_isSharedCheck_3906_;
                        state = 32;
                        continue;
                    } else {
                        lean_inc(v_alts_3867_);
                        lean_inc(v_discr_3866_);
                        lean_inc(v_resultType_3865_);
                        lean_inc(v_typeName_3864_);
                        lean_dec(v_cases_3863_);
                        v___x_3869_ = lean_box(0);
                        v_isShared_3870_ = v_isSharedCheck_3906_;
                        state = 32;
                        continue;
                    }
                }
                _ => {
                    v___x_3907_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3907_, 0, v_code_3689_);
                    return v___x_3907_;
                }
            },
            1 => {
                v___x_3722_ = lean_ptr_addr(v_k_3699_);
                v___x_3723_ = lean_ptr_addr(v_a_3701_);
                v___x_3724_ = lean_usize_dec_eq(v___x_3722_, v___x_3723_);
                if v___x_3724_ == 0 {
                    v___y_3706_ = v___x_3724_;
                    state = 2;
                    continue;
                } else {
                    v___x_3725_ = lean_ptr_addr(v_decl_3698_);
                    v___x_3726_ = lean_usize_dec_eq(v___x_3725_, v___x_3725_);
                    v___y_3706_ = v___x_3726_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v___y_3706_ == 0 {
                    lean_inc_ref(v_decl_3698_);
                    v_isSharedCheck_3716_ = (!lean_is_exclusive(v_code_3689_)) as u8;
                    if v_isSharedCheck_3716_ == 0 {
                        v_unused_3717_ = lean_ctor_get(v_code_3689_, 1);
                        lean_dec(v_unused_3717_);
                        v_unused_3718_ = lean_ctor_get(v_code_3689_, 0);
                        lean_dec(v_unused_3718_);
                        v___x_3708_ = v_code_3689_;
                        v_isShared_3709_ = v_isSharedCheck_3716_;
                        state = 3;
                        continue;
                    } else {
                        lean_dec(v_code_3689_);
                        v___x_3708_ = lean_box(0);
                        v_isShared_3709_ = v_isSharedCheck_3716_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3701_);
                    if v_isShared_3704_ == 0 {
                        lean_ctor_set(v___x_3703_, 0, v_code_3689_);
                        v___x_3720_ = v___x_3703_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_3721_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3721_, 0, v_code_3689_);
                        v___x_3720_ = v_reuseFailAlloc_3721_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3709_ == 0 {
                    lean_ctor_set(v___x_3708_, 1, v_a_3701_);
                    v___x_3711_ = v___x_3708_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3715_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 0, v_decl_3698_);
                    lean_ctor_set(v_reuseFailAlloc_3715_, 1, v_a_3701_);
                    v___x_3711_ = v_reuseFailAlloc_3715_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_3704_ == 0 {
                    lean_ctor_set(v___x_3703_, 0, v___x_3711_);
                    v___x_3713_ = v___x_3703_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3714_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3714_, 0, v___x_3711_);
                    v___x_3713_ = v_reuseFailAlloc_3714_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3713_;
            }
            6 => {
                return v___x_3720_;
            }
            7 => {
                v___x_3760_ = lean_ptr_addr(v_k_3729_);
                v___x_3761_ = lean_ptr_addr(v_a_3739_);
                v___x_3762_ = lean_usize_dec_eq(v___x_3760_, v___x_3761_);
                if v___x_3762_ == 0 {
                    v___y_3744_ = v___x_3762_;
                    state = 8;
                    continue;
                } else {
                    v___x_3763_ = lean_ptr_addr(v_decl_3728_);
                    v___x_3764_ = lean_ptr_addr(v_a_3737_);
                    v___x_3765_ = lean_usize_dec_eq(v___x_3763_, v___x_3764_);
                    v___y_3744_ = v___x_3765_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v___y_3744_ == 0 {
                    v_isSharedCheck_3754_ = (!lean_is_exclusive(v_code_3689_)) as u8;
                    if v_isSharedCheck_3754_ == 0 {
                        v_unused_3755_ = lean_ctor_get(v_code_3689_, 1);
                        lean_dec(v_unused_3755_);
                        v_unused_3756_ = lean_ctor_get(v_code_3689_, 0);
                        lean_dec(v_unused_3756_);
                        v___x_3746_ = v_code_3689_;
                        v_isShared_3747_ = v_isSharedCheck_3754_;
                        state = 9;
                        continue;
                    } else {
                        lean_dec(v_code_3689_);
                        v___x_3746_ = lean_box(0);
                        v_isShared_3747_ = v_isSharedCheck_3754_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3739_);
                    lean_dec(v_a_3737_);
                    if v_isShared_3742_ == 0 {
                        lean_ctor_set(v___x_3741_, 0, v_code_3689_);
                        v___x_3758_ = v___x_3741_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_3759_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3759_, 0, v_code_3689_);
                        v___x_3758_ = v_reuseFailAlloc_3759_;
                        state = 12;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_3747_ == 0 {
                    lean_ctor_set(v___x_3746_, 1, v_a_3739_);
                    lean_ctor_set(v___x_3746_, 0, v_a_3737_);
                    v___x_3749_ = v___x_3746_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3753_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 0, v_a_3737_);
                    lean_ctor_set(v_reuseFailAlloc_3753_, 1, v_a_3739_);
                    v___x_3749_ = v_reuseFailAlloc_3753_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3742_ == 0 {
                    lean_ctor_set(v___x_3741_, 0, v___x_3749_);
                    v___x_3751_ = v___x_3741_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3752_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3752_, 0, v___x_3749_);
                    v___x_3751_ = v_reuseFailAlloc_3752_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3751_;
            }
            12 => {
                return v___x_3758_;
            }
            13 => {
                if v_isShared_3770_ == 0 {
                    v___x_3772_ = v___x_3769_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3773_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3773_, 0, v_a_3767_);
                    v___x_3772_ = v_reuseFailAlloc_3773_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3772_;
            }
            15 => {
                if lean_obj_tag(v_a_3778_) == 1 {
                    lean_dec_ref_known(v_code_3689_, 2);
                    v_val_3782_ = lean_ctor_get(v_a_3778_, 0);
                    lean_inc(v_val_3782_);
                    lean_dec_ref_known(v_a_3778_, 1);
                    if v_isShared_3781_ == 0 {
                        lean_ctor_set(v___x_3780_, 0, v_val_3782_);
                        v___x_3784_ = v___x_3780_;
                        state = 16;
                        continue;
                    } else {
                        v_reuseFailAlloc_3785_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3785_, 0, v_val_3782_);
                        v___x_3784_ = v_reuseFailAlloc_3785_;
                        state = 16;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3780_);
                    lean_dec(v_a_3778_);
                    v_params_3786_ = lean_ctor_get(v_decl_3775_, 2);
                    v_type_3787_ = lean_ctor_get(v_decl_3775_, 3);
                    v_value_3788_ = lean_ctor_get(v_decl_3775_, 4);
                    lean_inc_ref(v_value_3788_);
                    v___x_3789_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_value_3788_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                    if lean_obj_tag(v___x_3789_) == 0 {
                        v_a_3790_ = lean_ctor_get(v___x_3789_, 0);
                        lean_inc(v_a_3790_);
                        lean_dec_ref_known(v___x_3789_, 1);
                        v___x_3791_ = 0;
                        lean_inc_ref(v_params_3786_);
                        lean_inc_ref(v_type_3787_);
                        lean_inc_ref(v_decl_3775_);
                        v___x_3792_ = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(v___x_3791_, v_decl_3775_, v_type_3787_, v_params_3786_, v_a_3790_, v_a_3694_);
                        if lean_obj_tag(v___x_3792_) == 0 {
                            v_a_3793_ = lean_ctor_get(v___x_3792_, 0);
                            lean_inc(v_a_3793_);
                            lean_dec_ref_known(v___x_3792_, 1);
                            lean_inc_ref(v_k_3776_);
                            v___x_3794_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_k_3776_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                            if lean_obj_tag(v___x_3794_) == 0 {
                                v_a_3795_ = lean_ctor_get(v___x_3794_, 0);
                                v_isSharedCheck_3822_ = (!lean_is_exclusive(v___x_3794_)) as u8;
                                if v_isSharedCheck_3822_ == 0 {
                                    v___x_3797_ = v___x_3794_;
                                    v_isShared_3798_ = v_isSharedCheck_3822_;
                                    state = 17;
                                    continue;
                                } else {
                                    lean_inc(v_a_3795_);
                                    lean_dec(v___x_3794_);
                                    v___x_3797_ = lean_box(0);
                                    v_isShared_3798_ = v_isSharedCheck_3822_;
                                    state = 17;
                                    continue;
                                }
                            } else {
                                lean_dec(v_a_3793_);
                                lean_dec_ref_known(v_code_3689_, 2);
                                return v___x_3794_;
                            }
                        } else {
                            lean_dec_ref_known(v_code_3689_, 2);
                            v_a_3823_ = lean_ctor_get(v___x_3792_, 0);
                            v_isSharedCheck_3830_ = (!lean_is_exclusive(v___x_3792_)) as u8;
                            if v_isSharedCheck_3830_ == 0 {
                                v___x_3825_ = v___x_3792_;
                                v_isShared_3826_ = v_isSharedCheck_3830_;
                                state = 23;
                                continue;
                            } else {
                                lean_inc(v_a_3823_);
                                lean_dec(v___x_3792_);
                                v___x_3825_ = lean_box(0);
                                v_isShared_3826_ = v_isSharedCheck_3830_;
                                state = 23;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref_known(v_code_3689_, 2);
                        return v___x_3789_;
                    }
                }
            }
            16 => {
                return v___x_3784_;
            }
            17 => {
                v___x_3816_ = lean_ptr_addr(v_k_3776_);
                v___x_3817_ = lean_ptr_addr(v_a_3795_);
                v___x_3818_ = lean_usize_dec_eq(v___x_3816_, v___x_3817_);
                if v___x_3818_ == 0 {
                    v___y_3800_ = v___x_3818_;
                    state = 18;
                    continue;
                } else {
                    v___x_3819_ = lean_ptr_addr(v_decl_3775_);
                    v___x_3820_ = lean_ptr_addr(v_a_3793_);
                    v___x_3821_ = lean_usize_dec_eq(v___x_3819_, v___x_3820_);
                    v___y_3800_ = v___x_3821_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v___y_3800_ == 0 {
                    v_isSharedCheck_3810_ = (!lean_is_exclusive(v_code_3689_)) as u8;
                    if v_isSharedCheck_3810_ == 0 {
                        v_unused_3811_ = lean_ctor_get(v_code_3689_, 1);
                        lean_dec(v_unused_3811_);
                        v_unused_3812_ = lean_ctor_get(v_code_3689_, 0);
                        lean_dec(v_unused_3812_);
                        v___x_3802_ = v_code_3689_;
                        v_isShared_3803_ = v_isSharedCheck_3810_;
                        state = 19;
                        continue;
                    } else {
                        lean_dec(v_code_3689_);
                        v___x_3802_ = lean_box(0);
                        v_isShared_3803_ = v_isSharedCheck_3810_;
                        state = 19;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3795_);
                    lean_dec(v_a_3793_);
                    if v_isShared_3798_ == 0 {
                        lean_ctor_set(v___x_3797_, 0, v_code_3689_);
                        v___x_3814_ = v___x_3797_;
                        state = 22;
                        continue;
                    } else {
                        v_reuseFailAlloc_3815_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3815_, 0, v_code_3689_);
                        v___x_3814_ = v_reuseFailAlloc_3815_;
                        state = 22;
                        continue;
                    }
                }
            }
            19 => {
                if v_isShared_3803_ == 0 {
                    lean_ctor_set(v___x_3802_, 1, v_a_3795_);
                    lean_ctor_set(v___x_3802_, 0, v_a_3793_);
                    v___x_3805_ = v___x_3802_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3809_ = lean_alloc_ctor(2, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3809_, 0, v_a_3793_);
                    lean_ctor_set(v_reuseFailAlloc_3809_, 1, v_a_3795_);
                    v___x_3805_ = v_reuseFailAlloc_3809_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_3798_ == 0 {
                    lean_ctor_set(v___x_3797_, 0, v___x_3805_);
                    v___x_3807_ = v___x_3797_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_3808_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3808_, 0, v___x_3805_);
                    v___x_3807_ = v_reuseFailAlloc_3808_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_3807_;
            }
            22 => {
                return v___x_3814_;
            }
            23 => {
                if v_isShared_3826_ == 0 {
                    v___x_3828_ = v___x_3825_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
                    v___x_3828_ = v_reuseFailAlloc_3829_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_3828_;
            }
            25 => {
                if v_isShared_3835_ == 0 {
                    v___x_3837_ = v___x_3834_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_3838_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3838_, 0, v_a_3832_);
                    v___x_3837_ = v_reuseFailAlloc_3838_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                return v___x_3837_;
            }
            27 => {
                if lean_obj_tag(v_a_3843_) == 1 {
                    lean_dec_ref_known(v_code_3689_, 2);
                    v_val_3847_ = lean_ctor_get(v_a_3843_, 0);
                    lean_inc(v_val_3847_);
                    lean_dec_ref_known(v_a_3843_, 1);
                    if v_isShared_3846_ == 0 {
                        lean_ctor_set(v___x_3845_, 0, v_val_3847_);
                        v___x_3849_ = v___x_3845_;
                        state = 28;
                        continue;
                    } else {
                        v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_val_3847_);
                        v___x_3849_ = v_reuseFailAlloc_3850_;
                        state = 28;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3843_);
                    if v_isShared_3846_ == 0 {
                        lean_ctor_set(v___x_3845_, 0, v_code_3689_);
                        v___x_3852_ = v___x_3845_;
                        state = 29;
                        continue;
                    } else {
                        v_reuseFailAlloc_3853_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3853_, 0, v_code_3689_);
                        v___x_3852_ = v_reuseFailAlloc_3853_;
                        state = 29;
                        continue;
                    }
                }
            }
            28 => {
                return v___x_3849_;
            }
            29 => {
                return v___x_3852_;
            }
            30 => {
                if v_isShared_3858_ == 0 {
                    v___x_3860_ = v___x_3857_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_3861_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3861_, 0, v_a_3855_);
                    v___x_3860_ = v_reuseFailAlloc_3861_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_3860_;
            }
            32 => {
                v___x_3871_ = lean_unsigned_to_nat(0);
                lean_inc_ref(v_alts_3867_);
                lean_inc(v_discr_3866_);
                v___x_3872_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_3866_, v___x_3871_, v_alts_3867_, v_a_3690_, v_a_3691_, v_a_3692_, v_a_3693_, v_a_3694_, v_a_3695_, v_a_3696_);
                if lean_obj_tag(v___x_3872_) == 0 {
                    v_a_3873_ = lean_ctor_get(v___x_3872_, 0);
                    v_isSharedCheck_3897_ = (!lean_is_exclusive(v___x_3872_)) as u8;
                    if v_isSharedCheck_3897_ == 0 {
                        v___x_3875_ = v___x_3872_;
                        v_isShared_3876_ = v_isSharedCheck_3897_;
                        state = 33;
                        continue;
                    } else {
                        lean_inc(v_a_3873_);
                        lean_dec(v___x_3872_);
                        v___x_3875_ = lean_box(0);
                        v_isShared_3876_ = v_isSharedCheck_3897_;
                        state = 33;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3869_);
                    lean_dec_ref(v_alts_3867_);
                    lean_dec(v_discr_3866_);
                    lean_dec_ref(v_resultType_3865_);
                    lean_dec(v_typeName_3864_);
                    lean_dec_ref_known(v_code_3689_, 1);
                    v_a_3898_ = lean_ctor_get(v___x_3872_, 0);
                    v_isSharedCheck_3905_ = (!lean_is_exclusive(v___x_3872_)) as u8;
                    if v_isSharedCheck_3905_ == 0 {
                        v___x_3900_ = v___x_3872_;
                        v_isShared_3901_ = v_isSharedCheck_3905_;
                        state = 39;
                        continue;
                    } else {
                        lean_inc(v_a_3898_);
                        lean_dec(v___x_3872_);
                        v___x_3900_ = lean_box(0);
                        v_isShared_3901_ = v_isSharedCheck_3905_;
                        state = 39;
                        continue;
                    }
                }
            }
            33 => {
                v___x_3877_ = lean_ptr_addr(v_alts_3867_);
                lean_dec_ref(v_alts_3867_);
                v___x_3878_ = lean_ptr_addr(v_a_3873_);
                v___x_3879_ = lean_usize_dec_eq(v___x_3877_, v___x_3878_);
                if v___x_3879_ == 0 {
                    v_isSharedCheck_3892_ = (!lean_is_exclusive(v_code_3689_)) as u8;
                    if v_isSharedCheck_3892_ == 0 {
                        v_unused_3893_ = lean_ctor_get(v_code_3689_, 0);
                        lean_dec(v_unused_3893_);
                        v___x_3881_ = v_code_3689_;
                        v_isShared_3882_ = v_isSharedCheck_3892_;
                        state = 34;
                        continue;
                    } else {
                        lean_dec(v_code_3689_);
                        v___x_3881_ = lean_box(0);
                        v_isShared_3882_ = v_isSharedCheck_3892_;
                        state = 34;
                        continue;
                    }
                } else {
                    lean_dec(v_a_3873_);
                    lean_del_object(v___x_3869_);
                    lean_dec(v_discr_3866_);
                    lean_dec_ref(v_resultType_3865_);
                    lean_dec(v_typeName_3864_);
                    if v_isShared_3876_ == 0 {
                        lean_ctor_set(v___x_3875_, 0, v_code_3689_);
                        v___x_3895_ = v___x_3875_;
                        state = 38;
                        continue;
                    } else {
                        v_reuseFailAlloc_3896_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3896_, 0, v_code_3689_);
                        v___x_3895_ = v_reuseFailAlloc_3896_;
                        state = 38;
                        continue;
                    }
                }
            }
            34 => {
                if v_isShared_3870_ == 0 {
                    lean_ctor_set(v___x_3869_, 3, v_a_3873_);
                    v___x_3884_ = v___x_3869_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_3891_ = lean_alloc_ctor(0, 4, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3891_, 0, v_typeName_3864_);
                    lean_ctor_set(v_reuseFailAlloc_3891_, 1, v_resultType_3865_);
                    lean_ctor_set(v_reuseFailAlloc_3891_, 2, v_discr_3866_);
                    lean_ctor_set(v_reuseFailAlloc_3891_, 3, v_a_3873_);
                    v___x_3884_ = v_reuseFailAlloc_3891_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                if v_isShared_3882_ == 0 {
                    lean_ctor_set(v___x_3881_, 0, v___x_3884_);
                    v___x_3886_ = v___x_3881_;
                    state = 36;
                    continue;
                } else {
                    v_reuseFailAlloc_3890_ = lean_alloc_ctor(4, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3890_, 0, v___x_3884_);
                    v___x_3886_ = v_reuseFailAlloc_3890_;
                    state = 36;
                    continue;
                }
            }
            36 => {
                if v_isShared_3876_ == 0 {
                    lean_ctor_set(v___x_3875_, 0, v___x_3886_);
                    v___x_3888_ = v___x_3875_;
                    state = 37;
                    continue;
                } else {
                    v_reuseFailAlloc_3889_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3889_, 0, v___x_3886_);
                    v___x_3888_ = v_reuseFailAlloc_3889_;
                    state = 37;
                    continue;
                }
            }
            37 => {
                return v___x_3888_;
            }
            38 => {
                return v___x_3895_;
            }
            39 => {
                if v_isShared_3901_ == 0 {
                    v___x_3903_ = v___x_3900_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_3904_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3904_, 0, v_a_3898_);
                    v___x_3903_ = v_reuseFailAlloc_3904_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_3903_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(
    mut v_discr_3908_: *mut LeanObject,
    mut v_i_3909_: *mut LeanObject,
    mut v_as_3910_: *mut LeanObject,
    mut v___y_3911_: *mut LeanObject,
    mut v___y_3912_: *mut LeanObject,
    mut v___y_3913_: *mut LeanObject,
    mut v___y_3914_: *mut LeanObject,
    mut v___y_3915_: *mut LeanObject,
    mut v___y_3916_: *mut LeanObject,
    mut v___y_3917_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: u8 = 0;
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3925_: usize = 0;
    let mut v___x_3926_: usize = 0;
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorName_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_params_3936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_code_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3945_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3946_: u8 = 0;
    let mut v___x_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3950_: u8 = 0;
    let mut v_a_3951_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3954_: u8 = 0;
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v_code_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3970_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3919_ = lean_array_get_size(v_as_3910_);
                v___x_3920_ = lean_nat_dec_lt(v_i_3909_, v___x_3919_);
                if v___x_3920_ == 0 {
                    lean_dec(v_i_3909_);
                    lean_dec(v_discr_3908_);
                    v___x_3921_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3921_, 0, v_as_3910_);
                    return v___x_3921_;
                } else {
                    v_a_3922_ = lean_array_fget_borrowed(v_as_3910_, v_i_3909_);
                    if lean_obj_tag(v_a_3922_) == 0 {
                        v_ctorName_3935_ = lean_ctor_get(v_a_3922_, 0);
                        v_params_3936_ = lean_ctor_get(v_a_3922_, 1);
                        v_code_3937_ = lean_ctor_get(v_a_3922_, 2);
                        lean_inc_ref(v_params_3936_);
                        lean_inc(v_ctorName_3935_);
                        lean_inc(v_discr_3908_);
                        v___x_3938_ = l___private_Lean_Compiler_LCNF_Simp_DiscrM_0__Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(v_discr_3908_, v_ctorName_3935_, v_params_3936_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
                        if lean_obj_tag(v___x_3938_) == 0 {
                            v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
                            lean_inc(v_a_3939_);
                            lean_dec_ref_known(v___x_3938_, 1);
                            lean_inc_ref(v_code_3937_);
                            v___x_3940_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_3937_, v___y_3911_, v___y_3912_, v_a_3939_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
                            lean_dec(v_a_3939_);
                            if lean_obj_tag(v___x_3940_) == 0 {
                                v_a_3941_ = lean_ctor_get(v___x_3940_, 0);
                                lean_inc(v_a_3941_);
                                lean_dec_ref_known(v___x_3940_, 1);
                                lean_inc_ref(v_a_3922_);
                                v___x_3942_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3922_, v_a_3941_);
                                v_a_3924_ = v___x_3942_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec_ref(v_as_3910_);
                                lean_dec(v_i_3909_);
                                lean_dec(v_discr_3908_);
                                v_a_3943_ = lean_ctor_get(v___x_3940_, 0);
                                v_isSharedCheck_3950_ = (!lean_is_exclusive(v___x_3940_)) as u8;
                                if v_isSharedCheck_3950_ == 0 {
                                    v___x_3945_ = v___x_3940_;
                                    v_isShared_3946_ = v_isSharedCheck_3950_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_3943_);
                                    lean_dec(v___x_3940_);
                                    v___x_3945_ = lean_box(0);
                                    v_isShared_3946_ = v_isSharedCheck_3950_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_as_3910_);
                            lean_dec(v_i_3909_);
                            lean_dec(v_discr_3908_);
                            v_a_3951_ = lean_ctor_get(v___x_3938_, 0);
                            v_isSharedCheck_3958_ = (!lean_is_exclusive(v___x_3938_)) as u8;
                            if v_isSharedCheck_3958_ == 0 {
                                v___x_3953_ = v___x_3938_;
                                v_isShared_3954_ = v_isSharedCheck_3958_;
                                state = 4;
                                continue;
                            } else {
                                lean_inc(v_a_3951_);
                                lean_dec(v___x_3938_);
                                v___x_3953_ = lean_box(0);
                                v_isShared_3954_ = v_isSharedCheck_3958_;
                                state = 4;
                                continue;
                            }
                        }
                    } else {
                        v_code_3959_ = lean_ctor_get(v_a_3922_, 0);
                        lean_inc_ref(v_code_3959_);
                        v___x_3960_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_3959_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_, v___y_3917_);
                        if lean_obj_tag(v___x_3960_) == 0 {
                            v_a_3961_ = lean_ctor_get(v___x_3960_, 0);
                            lean_inc(v_a_3961_);
                            lean_dec_ref_known(v___x_3960_, 1);
                            lean_inc_ref(v_a_3922_);
                            v___x_3962_ = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(v_a_3922_, v_a_3961_);
                            v_a_3924_ = v___x_3962_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec_ref(v_as_3910_);
                            lean_dec(v_i_3909_);
                            lean_dec(v_discr_3908_);
                            v_a_3963_ = lean_ctor_get(v___x_3960_, 0);
                            v_isSharedCheck_3970_ = (!lean_is_exclusive(v___x_3960_)) as u8;
                            if v_isSharedCheck_3970_ == 0 {
                                v___x_3965_ = v___x_3960_;
                                v_isShared_3966_ = v_isSharedCheck_3970_;
                                state = 6;
                                continue;
                            } else {
                                lean_inc(v_a_3963_);
                                lean_dec(v___x_3960_);
                                v___x_3965_ = lean_box(0);
                                v_isShared_3966_ = v_isSharedCheck_3970_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_3925_ = lean_ptr_addr(v_a_3922_);
                v___x_3926_ = lean_ptr_addr(v_a_3924_);
                v___x_3927_ = lean_usize_dec_eq(v___x_3925_, v___x_3926_);
                if v___x_3927_ == 0 {
                    v___x_3928_ = lean_unsigned_to_nat(1);
                    v___x_3929_ = lean_nat_add(v_i_3909_, v___x_3928_);
                    v___x_3930_ = lean_array_fset(v_as_3910_, v_i_3909_, v_a_3924_);
                    lean_dec(v_i_3909_);
                    v_i_3909_ = v___x_3929_;
                    v_as_3910_ = v___x_3930_;
                    state = 0;
                    continue;
                } else {
                    lean_dec_ref(v_a_3924_);
                    v___x_3932_ = lean_unsigned_to_nat(1);
                    v___x_3933_ = lean_nat_add(v_i_3909_, v___x_3932_);
                    lean_dec(v_i_3909_);
                    v_i_3909_ = v___x_3933_;
                    state = 0;
                    continue;
                }
            }
            2 => {
                if v_isShared_3946_ == 0 {
                    v___x_3948_ = v___x_3945_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3949_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3949_, 0, v_a_3943_);
                    v___x_3948_ = v_reuseFailAlloc_3949_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3948_;
            }
            4 => {
                if v_isShared_3954_ == 0 {
                    v___x_3956_ = v___x_3953_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_a_3951_);
                    v___x_3956_ = v_reuseFailAlloc_3957_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3956_;
            }
            6 => {
                if v_isShared_3966_ == 0 {
                    v___x_3968_ = v___x_3965_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3969_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3969_, 0, v_a_3963_);
                    v___x_3968_ = v_reuseFailAlloc_3969_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3968_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0___boxed(
    mut v_discr_3971_: *mut LeanObject,
    mut v_i_3972_: *mut LeanObject,
    mut v_as_3973_: *mut LeanObject,
    mut v___y_3974_: *mut LeanObject,
    mut v___y_3975_: *mut LeanObject,
    mut v___y_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3982_: *mut LeanObject = core::ptr::null_mut();
    v_res_3982_ = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit_spec__0(v_discr_3971_, v_i_3972_, v_as_3973_, v___y_3974_, v___y_3975_, v___y_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_);
    lean_dec(v___y_3980_);
    lean_dec_ref(v___y_3979_);
    lean_dec(v___y_3978_);
    lean_dec_ref(v___y_3977_);
    lean_dec_ref(v___y_3976_);
    lean_dec(v___y_3975_);
    lean_dec(v___y_3974_);
    return v_res_3982_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f___boxed(
    mut v_decl_3983_: *mut LeanObject,
    mut v_k_3984_: *mut LeanObject,
    mut v_a_3985_: *mut LeanObject,
    mut v_a_3986_: *mut LeanObject,
    mut v_a_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
    mut v_a_3989_: *mut LeanObject,
    mut v_a_3990_: *mut LeanObject,
    mut v_a_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3993_: *mut LeanObject = core::ptr::null_mut();
    v_res_3993_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f(v_decl_3983_, v_k_3984_, v_a_3985_, v_a_3986_, v_a_3987_, v_a_3988_, v_a_3989_, v_a_3990_, v_a_3991_);
    lean_dec(v_a_3991_);
    lean_dec_ref(v_a_3990_);
    lean_dec(v_a_3989_);
    lean_dec_ref(v_a_3988_);
    lean_dec_ref(v_a_3987_);
    lean_dec(v_a_3986_);
    lean_dec(v_a_3985_);
    return v_res_3993_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_discr_3994_: *mut LeanObject = *_args.add(0);
    let mut v___x_3995_: *mut LeanObject = *_args.add(1);
    let mut v_val_3996_: *mut LeanObject = *_args.add(2);
    let mut v_fst_3997_: *mut LeanObject = *_args.add(3);
    let mut v_params_3998_: *mut LeanObject = *_args.add(4);
    let mut v_snd_3999_: *mut LeanObject = *_args.add(5);
    let mut v_as_4000_: *mut LeanObject = *_args.add(6);
    let mut v_sz_4001_: *mut LeanObject = *_args.add(7);
    let mut v_i_4002_: *mut LeanObject = *_args.add(8);
    let mut v_b_4003_: *mut LeanObject = *_args.add(9);
    let mut v___y_4004_: *mut LeanObject = *_args.add(10);
    let mut v___y_4005_: *mut LeanObject = *_args.add(11);
    let mut v___y_4006_: *mut LeanObject = *_args.add(12);
    let mut v___y_4007_: *mut LeanObject = *_args.add(13);
    let mut v___y_4008_: *mut LeanObject = *_args.add(14);
    let mut v___y_4009_: *mut LeanObject = *_args.add(15);
    let mut v___y_4010_: *mut LeanObject = *_args.add(16);
    let mut v___y_4011_: *mut LeanObject = *_args.add(17);
    let mut v_sz_boxed_4012_: usize = 0;
    let mut v_i_boxed_4013_: usize = 0;
    let mut v_res_4014_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_4012_ = lean_unbox_usize(v_sz_4001_);
    lean_dec(v_sz_4001_);
    v_i_boxed_4013_ = lean_unbox_usize(v_i_4002_);
    lean_dec(v_i_4002_);
    v_res_4014_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__4(v_discr_3994_, v___x_3995_, v_val_3996_, v_fst_3997_, v_params_3998_, v_snd_3999_, v_as_4000_, v_sz_boxed_4012_, v_i_boxed_4013_, v_b_4003_, v___y_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
    lean_dec(v___y_4010_);
    lean_dec_ref(v___y_4009_);
    lean_dec(v___y_4008_);
    lean_dec_ref(v___y_4007_);
    lean_dec_ref(v___y_4006_);
    lean_dec(v___y_4005_);
    lean_dec(v___y_4004_);
    lean_dec_ref(v_as_4000_);
    lean_dec_ref(v_snd_3999_);
    return v_res_4014_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit___boxed(
    mut v_code_4015_: *mut LeanObject,
    mut v_a_4016_: *mut LeanObject,
    mut v_a_4017_: *mut LeanObject,
    mut v_a_4018_: *mut LeanObject,
    mut v_a_4019_: *mut LeanObject,
    mut v_a_4020_: *mut LeanObject,
    mut v_a_4021_: *mut LeanObject,
    mut v_a_4022_: *mut LeanObject,
    mut v_a_4023_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4024_: *mut LeanObject = core::ptr::null_mut();
    v_res_4024_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_4015_, v_a_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_, v_a_4021_, v_a_4022_);
    lean_dec(v_a_4022_);
    lean_dec_ref(v_a_4021_);
    lean_dec(v_a_4020_);
    lean_dec_ref(v_a_4019_);
    lean_dec_ref(v_a_4018_);
    lean_dec(v_a_4017_);
    lean_dec(v_a_4016_);
    return v_res_4024_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(
    mut v___x_4025_: *mut LeanObject,
    mut v_a_4026_: *mut LeanObject,
    mut v_init_4027_: *mut LeanObject,
    mut v_x_4028_: *mut LeanObject,
    mut v___y_4029_: *mut LeanObject,
    mut v___y_4030_: *mut LeanObject,
    mut v___y_4031_: *mut LeanObject,
    mut v___y_4032_: *mut LeanObject,
    mut v___y_4033_: *mut LeanObject,
    mut v___y_4034_: *mut LeanObject,
    mut v___y_4035_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4037_: *mut LeanObject = core::ptr::null_mut();
    v___x_4037_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___redArg(v___x_4025_, v_a_4026_, v_init_4027_, v_x_4028_);
    return v___x_4037_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2___boxed(
    mut v___x_4038_: *mut LeanObject,
    mut v_a_4039_: *mut LeanObject,
    mut v_init_4040_: *mut LeanObject,
    mut v_x_4041_: *mut LeanObject,
    mut v___y_4042_: *mut LeanObject,
    mut v___y_4043_: *mut LeanObject,
    mut v___y_4044_: *mut LeanObject,
    mut v___y_4045_: *mut LeanObject,
    mut v___y_4046_: *mut LeanObject,
    mut v___y_4047_: *mut LeanObject,
    mut v___y_4048_: *mut LeanObject,
    mut v___y_4049_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4050_: *mut LeanObject = core::ptr::null_mut();
    v_res_4050_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visitJp_x3f_spec__2(v___x_4038_, v_a_4039_, v_init_4040_, v_x_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_, v___y_4047_, v___y_4048_);
    lean_dec(v___y_4048_);
    lean_dec_ref(v___y_4047_);
    lean_dec(v___y_4046_);
    lean_dec_ref(v___y_4045_);
    lean_dec_ref(v___y_4044_);
    lean_dec(v___y_4043_);
    lean_dec(v___y_4042_);
    lean_dec(v___x_4038_);
    return v_res_4050_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0()
-> *mut LeanObject {
    let mut v___x_4051_: *mut LeanObject = core::ptr::null_mut();
    v___x_4051_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
    return v___x_4051_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1()
-> *mut LeanObject {
    let mut v___x_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    v___x_4052_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__0);
    v___x_4053_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_4053_, 0, v___x_4052_);
    return v___x_4053_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2()
-> *mut LeanObject {
    let mut v___x_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4055_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    v___x_4054_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__1);
    v___x_4055_ = lean_unsigned_to_nat(0);
    v___x_4056_ = lean_alloc_ctor(0, 10, (0) as u32);
    lean_ctor_set(v___x_4056_, 0, v___x_4055_);
    lean_ctor_set(v___x_4056_, 1, v___x_4055_);
    lean_ctor_set(v___x_4056_, 2, v___x_4055_);
    lean_ctor_set(v___x_4056_, 3, v___x_4055_);
    lean_ctor_set(v___x_4056_, 4, v___x_4054_);
    lean_ctor_set(v___x_4056_, 5, v___x_4054_);
    lean_ctor_set(v___x_4056_, 6, v___x_4054_);
    lean_ctor_set(v___x_4056_, 7, v___x_4054_);
    lean_ctor_set(v___x_4056_, 8, v___x_4054_);
    lean_ctor_set(v___x_4056_, 9, v___x_4054_);
    return v___x_4056_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3()
-> f64 {
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4058_: f64 = 0.0;
    v___x_4057_ = lean_unsigned_to_nat(0);
    v___x_4058_ = lean_float_of_nat(v___x_4057_);
    return v___x_4058_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(
    mut v_cls_4062_: *mut LeanObject,
    mut v_msg_4063_: *mut LeanObject,
    mut v___y_4064_: *mut LeanObject,
    mut v___y_4065_: *mut LeanObject,
    mut v___y_4066_: *mut LeanObject,
    mut v___y_4067_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_options_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ref_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4071_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4077_: u8 = 0;
    let mut v_env_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4082_: u8 = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_traceState_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ngen_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_4089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_cache_4090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_messages_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_infoState_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4096_: u8 = 0;
    let mut v_tid_4097_: u64 = 0;
    let mut v_traces_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4101_: u8 = 0;
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: f64 = 0.0;
    let mut v___x_4109_: u8 = 0;
    let mut v___x_4110_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4120_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4124_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4128_: u8 = 0;
    let mut v_isSharedCheck_4129_: u8 = 0;
    let mut v_isSharedCheck_4130_: u8 = 0;
    let mut v_unused_4131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4132_: u8 = 0;
    let mut v_a_4133_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4136_: u8 = 0;
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4140_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_options_4069_ = lean_ctor_get(v___y_4066_, 2);
                v_ref_4070_ = lean_ctor_get(v___y_4066_, 5);
                v___x_4071_ = lean_st_ref_get(v___y_4067_);
                v___x_4072_ = lean_st_ref_get(v___y_4065_);
                v___x_4073_ = l_Lean_Compiler_LCNF_getPurity___redArg(v___y_4064_);
                if lean_obj_tag(v___x_4073_) == 0 {
                    v_a_4074_ = lean_ctor_get(v___x_4073_, 0);
                    v_isSharedCheck_4132_ = (!lean_is_exclusive(v___x_4073_)) as u8;
                    if v_isSharedCheck_4132_ == 0 {
                        v___x_4076_ = v___x_4073_;
                        v_isShared_4077_ = v_isSharedCheck_4132_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4074_);
                        lean_dec(v___x_4073_);
                        v___x_4076_ = lean_box(0);
                        v_isShared_4077_ = v_isSharedCheck_4132_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4072_);
                    lean_dec(v___x_4071_);
                    lean_dec_ref(v_msg_4063_);
                    lean_dec(v_cls_4062_);
                    v_a_4133_ = lean_ctor_get(v___x_4073_, 0);
                    v_isSharedCheck_4140_ = (!lean_is_exclusive(v___x_4073_)) as u8;
                    if v_isSharedCheck_4140_ == 0 {
                        v___x_4135_ = v___x_4073_;
                        v_isShared_4136_ = v_isSharedCheck_4140_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4133_);
                        lean_dec(v___x_4073_);
                        v___x_4135_ = lean_box(0);
                        v_isShared_4136_ = v_isSharedCheck_4140_;
                        state = 9;
                        continue;
                    }
                }
            }
            1 => {
                v_env_4078_ = lean_ctor_get(v___x_4071_, 0);
                lean_inc_ref(v_env_4078_);
                lean_dec(v___x_4071_);
                v_lctx_4079_ = lean_ctor_get(v___x_4072_, 0);
                v_isSharedCheck_4130_ = (!lean_is_exclusive(v___x_4072_)) as u8;
                if v_isSharedCheck_4130_ == 0 {
                    v_unused_4131_ = lean_ctor_get(v___x_4072_, 1);
                    lean_dec(v_unused_4131_);
                    v___x_4081_ = v___x_4072_;
                    v_isShared_4082_ = v_isSharedCheck_4130_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_lctx_4079_);
                    lean_dec(v___x_4072_);
                    v___x_4081_ = lean_box(0);
                    v_isShared_4082_ = v_isSharedCheck_4130_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4083_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__2);
                v___x_4084_ = lean_st_ref_take(v___y_4067_);
                v_traceState_4085_ = lean_ctor_get(v___x_4084_, 4);
                v_env_4086_ = lean_ctor_get(v___x_4084_, 0);
                v_nextMacroScope_4087_ = lean_ctor_get(v___x_4084_, 1);
                v_ngen_4088_ = lean_ctor_get(v___x_4084_, 2);
                v_auxDeclNGen_4089_ = lean_ctor_get(v___x_4084_, 3);
                v_cache_4090_ = lean_ctor_get(v___x_4084_, 5);
                v_messages_4091_ = lean_ctor_get(v___x_4084_, 6);
                v_infoState_4092_ = lean_ctor_get(v___x_4084_, 7);
                v_snapshotTasks_4093_ = lean_ctor_get(v___x_4084_, 8);
                v_isSharedCheck_4129_ = (!lean_is_exclusive(v___x_4084_)) as u8;
                if v_isSharedCheck_4129_ == 0 {
                    v___x_4095_ = v___x_4084_;
                    v_isShared_4096_ = v_isSharedCheck_4129_;
                    state = 3;
                    continue;
                } else {
                    lean_inc(v_snapshotTasks_4093_);
                    lean_inc(v_infoState_4092_);
                    lean_inc(v_messages_4091_);
                    lean_inc(v_cache_4090_);
                    lean_inc(v_traceState_4085_);
                    lean_inc(v_auxDeclNGen_4089_);
                    lean_inc(v_ngen_4088_);
                    lean_inc(v_nextMacroScope_4087_);
                    lean_inc(v_env_4086_);
                    lean_dec(v___x_4084_);
                    v___x_4095_ = lean_box(0);
                    v_isShared_4096_ = v_isSharedCheck_4129_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_tid_4097_ = lean_ctor_get_uint64(
                    v_traceState_4085_,
                    (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                );
                v_traces_4098_ = lean_ctor_get(v_traceState_4085_, 0);
                v_isSharedCheck_4128_ = (!lean_is_exclusive(v_traceState_4085_)) as u8;
                if v_isSharedCheck_4128_ == 0 {
                    v___x_4100_ = v_traceState_4085_;
                    v_isShared_4101_ = v_isSharedCheck_4128_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_traces_4098_);
                    lean_dec(v_traceState_4085_);
                    v___x_4100_ = lean_box(0);
                    v_isShared_4101_ = v_isSharedCheck_4128_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4102_ = (lean_unbox(v_a_4074_) as u8);
                lean_dec(v_a_4074_);
                v___x_4103_ = l_Lean_Compiler_LCNF_LCtx_toLocalContext(v_lctx_4079_, v___x_4102_);
                lean_dec_ref(v_lctx_4079_);
                lean_inc_ref(v_options_4069_);
                v___x_4104_ = lean_alloc_ctor(0, 4, (0) as u32);
                lean_ctor_set(v___x_4104_, 0, v_env_4078_);
                lean_ctor_set(v___x_4104_, 1, v___x_4083_);
                lean_ctor_set(v___x_4104_, 2, v___x_4103_);
                lean_ctor_set(v___x_4104_, 3, v_options_4069_);
                if v_isShared_4082_ == 0 {
                    lean_ctor_set_tag(v___x_4081_, 3);
                    lean_ctor_set(v___x_4081_, 1, v_msg_4063_);
                    lean_ctor_set(v___x_4081_, 0, v___x_4104_);
                    v___x_4106_ = v___x_4081_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4127_ = lean_alloc_ctor(3, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4127_, 0, v___x_4104_);
                    lean_ctor_set(v_reuseFailAlloc_4127_, 1, v_msg_4063_);
                    v___x_4106_ = v_reuseFailAlloc_4127_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_4107_ = lean_box(0);
                v___x_4108_ = lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3_once), _init_l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__3);
                v___x_4109_ = 0;
                v___x_4110_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__4;
                v___x_4111_ = lean_alloc_ctor(0, 3, (17) as u32);
                lean_ctor_set(v___x_4111_, 0, v_cls_4062_);
                lean_ctor_set(v___x_4111_, 1, v___x_4107_);
                lean_ctor_set(v___x_4111_, 2, v___x_4110_);
                lean_ctor_set_float(
                    v___x_4111_,
                    (core::mem::size_of::<*mut LeanObject>() * 3) as u32,
                    v___x_4108_,
                );
                lean_ctor_set_float(
                    v___x_4111_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 8) as u32,
                    v___x_4108_,
                );
                lean_ctor_set_uint8(
                    v___x_4111_,
                    (core::mem::size_of::<*mut LeanObject>() * 3 + 16) as u32,
                    v___x_4109_,
                );
                v___x_4112_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___closed__5;
                v___x_4113_ = lean_alloc_ctor(9, 3, (0) as u32);
                lean_ctor_set(v___x_4113_, 0, v___x_4111_);
                lean_ctor_set(v___x_4113_, 1, v___x_4106_);
                lean_ctor_set(v___x_4113_, 2, v___x_4112_);
                lean_inc(v_ref_4070_);
                v___x_4114_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4114_, 0, v_ref_4070_);
                lean_ctor_set(v___x_4114_, 1, v___x_4113_);
                v___x_4115_ = l_Lean_PersistentArray_push___redArg(v_traces_4098_, v___x_4114_);
                if v_isShared_4101_ == 0 {
                    lean_ctor_set(v___x_4100_, 0, v___x_4115_);
                    v___x_4117_ = v___x_4100_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4126_ = lean_alloc_ctor(0, 1, (8) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4126_, 0, v___x_4115_);
                    lean_ctor_set_uint64(
                        v_reuseFailAlloc_4126_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v_tid_4097_,
                    );
                    v___x_4117_ = v_reuseFailAlloc_4126_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_4096_ == 0 {
                    lean_ctor_set(v___x_4095_, 4, v___x_4117_);
                    v___x_4119_ = v___x_4095_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4125_ = lean_alloc_ctor(0, 9, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 0, v_env_4086_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 1, v_nextMacroScope_4087_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 2, v_ngen_4088_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 3, v_auxDeclNGen_4089_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 4, v___x_4117_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 5, v_cache_4090_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 6, v_messages_4091_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 7, v_infoState_4092_);
                    lean_ctor_set(v_reuseFailAlloc_4125_, 8, v_snapshotTasks_4093_);
                    v___x_4119_ = v_reuseFailAlloc_4125_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4120_ = lean_st_ref_set(v___y_4067_, v___x_4119_);
                v___x_4121_ = lean_box(0);
                if v_isShared_4077_ == 0 {
                    lean_ctor_set(v___x_4076_, 0, v___x_4121_);
                    v___x_4123_ = v___x_4076_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4124_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4124_, 0, v___x_4121_);
                    v___x_4123_ = v_reuseFailAlloc_4124_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4123_;
            }
            9 => {
                if v_isShared_4136_ == 0 {
                    v___x_4138_ = v___x_4135_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4139_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4139_, 0, v_a_4133_);
                    v___x_4138_ = v_reuseFailAlloc_4139_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4138_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4___boxed(
    mut v_cls_4141_: *mut LeanObject,
    mut v_msg_4142_: *mut LeanObject,
    mut v___y_4143_: *mut LeanObject,
    mut v___y_4144_: *mut LeanObject,
    mut v___y_4145_: *mut LeanObject,
    mut v___y_4146_: *mut LeanObject,
    mut v___y_4147_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4148_: *mut LeanObject = core::ptr::null_mut();
    v_res_4148_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(
        v_cls_4141_,
        v_msg_4142_,
        v___y_4143_,
        v___y_4144_,
        v___y_4145_,
        v___y_4146_,
    );
    lean_dec(v___y_4146_);
    lean_dec_ref(v___y_4145_);
    lean_dec(v___y_4144_);
    lean_dec_ref(v___y_4143_);
    return v_res_4148_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(
    mut v_init_4149_: *mut LeanObject,
    mut v_x_4150_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4153_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4150_) == 0 {
                    v_k_4151_ = lean_ctor_get(v_x_4150_, 1);
                    v_v_4152_ = lean_ctor_get(v_x_4150_, 2);
                    v_l_4153_ = lean_ctor_get(v_x_4150_, 3);
                    v_r_4154_ = lean_ctor_get(v_x_4150_, 4);
                    v___x_4155_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_4149_, v_r_4154_);
                    lean_inc(v_v_4152_);
                    lean_inc(v_k_4151_);
                    v___x_4156_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4156_, 0, v_k_4151_);
                    lean_ctor_set(v___x_4156_, 1, v_v_4152_);
                    v___x_4157_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4157_, 0, v___x_4156_);
                    lean_ctor_set(v___x_4157_, 1, v___x_4155_);
                    v_init_4149_ = v___x_4157_;
                    v_x_4150_ = v_l_4153_;
                    state = 0;
                    continue;
                } else {
                    return v_init_4149_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2___boxed(
    mut v_init_4159_: *mut LeanObject,
    mut v_x_4160_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4161_: *mut LeanObject = core::ptr::null_mut();
    v_res_4161_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v_init_4159_, v_x_4160_);
    lean_dec(v_x_4160_);
    return v_res_4161_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(
    mut v_a_4162_: *mut LeanObject,
    mut v_a_4163_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_4162_) == 0 {
                    v___x_4164_ = l_List_reverse___redArg(v_a_4163_);
                    return v___x_4164_;
                } else {
                    v_head_4165_ = lean_ctor_get(v_a_4162_, 0);
                    v_tail_4166_ = lean_ctor_get(v_a_4162_, 1);
                    v_isSharedCheck_4175_ = (!lean_is_exclusive(v_a_4162_)) as u8;
                    if v_isSharedCheck_4175_ == 0 {
                        v___x_4168_ = v_a_4162_;
                        v_isShared_4169_ = v_isSharedCheck_4175_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_4166_);
                        lean_inc(v_head_4165_);
                        lean_dec(v_a_4162_);
                        v___x_4168_ = lean_box(0);
                        v_isShared_4169_ = v_isSharedCheck_4175_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4170_ = l_Lean_MessageData_ofName(v_head_4165_);
                if v_isShared_4169_ == 0 {
                    lean_ctor_set(v___x_4168_, 1, v_a_4163_);
                    lean_ctor_set(v___x_4168_, 0, v___x_4170_);
                    v___x_4172_ = v___x_4168_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4174_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4170_);
                    lean_ctor_set(v_reuseFailAlloc_4174_, 1, v_a_4163_);
                    v___x_4172_ = v_reuseFailAlloc_4174_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_4162_ = v_tail_4166_;
                v_a_4163_ = v___x_4172_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(
    mut v_init_4176_: *mut LeanObject,
    mut v_x_4177_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_4179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_4180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_4177_) == 0 {
                    v_k_4178_ = lean_ctor_get(v_x_4177_, 1);
                    v_l_4179_ = lean_ctor_get(v_x_4177_, 3);
                    v_r_4180_ = lean_ctor_get(v_x_4177_, 4);
                    v___x_4181_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_4176_, v_r_4180_);
                    lean_inc(v_k_4178_);
                    v___x_4182_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4182_, 0, v_k_4178_);
                    lean_ctor_set(v___x_4182_, 1, v___x_4181_);
                    v_init_4176_ = v___x_4182_;
                    v_x_4177_ = v_l_4179_;
                    state = 0;
                    continue;
                } else {
                    return v_init_4176_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0___boxed(
    mut v_init_4184_: *mut LeanObject,
    mut v_x_4185_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4186_: *mut LeanObject = core::ptr::null_mut();
    v_res_4186_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v_init_4184_, v_x_4185_);
    lean_dec(v_x_4185_);
    return v_res_4186_;
}
pub unsafe fn _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_4188_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    v___x_4188_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__0;
    v___x_4189_ = l_Lean_stringToMessageData(v___x_4188_);
    return v___x_4189_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(
    mut v_as_x27_4190_: *mut LeanObject,
    mut v_b_4191_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_4194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_4197_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ctorNames_4198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4199_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4204_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4205_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4206_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4208_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4209_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_4190_) == 0 {
                    v___x_4193_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4193_, 0, v_b_4191_);
                    return v___x_4193_;
                } else {
                    v_head_4194_ = lean_ctor_get(v_as_x27_4190_, 0);
                    v_snd_4195_ = lean_ctor_get(v_head_4194_, 1);
                    v_tail_4196_ = lean_ctor_get(v_as_x27_4190_, 1);
                    v_fst_4197_ = lean_ctor_get(v_head_4194_, 0);
                    v_ctorNames_4198_ = lean_ctor_get(v_snd_4195_, 1);
                    lean_inc(v_fst_4197_);
                    v___x_4199_ = l_Lean_mkFVar(v_fst_4197_);
                    v___x_4200_ = l_Lean_MessageData_ofExpr(v___x_4199_);
                    v___x_4201_ = lean_obj_once(core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1), core::ptr::addr_of_mut!(l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1_once), _init_l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___closed__1);
                    v___x_4202_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4202_, 0, v___x_4200_);
                    lean_ctor_set(v___x_4202_, 1, v___x_4201_);
                    v___x_4203_ = lean_box(0);
                    v___x_4204_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__0(v___x_4203_, v_ctorNames_4198_);
                    v___x_4205_ =
                        l_List_mapTR_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__1(
                            v___x_4204_,
                            v___x_4203_,
                        );
                    v___x_4206_ = l_Lean_MessageData_ofList(v___x_4205_);
                    v___x_4207_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4207_, 0, v___x_4202_);
                    lean_ctor_set(v___x_4207_, 1, v___x_4206_);
                    v___x_4208_ = l_Lean_indentD(v___x_4207_);
                    v___x_4209_ = lean_alloc_ctor(7, 2, (0) as u32);
                    lean_ctor_set(v___x_4209_, 0, v_b_4191_);
                    lean_ctor_set(v___x_4209_, 1, v___x_4208_);
                    v_as_x27_4190_ = v_tail_4196_;
                    v_b_4191_ = v___x_4209_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg___boxed(
    mut v_as_x27_4211_: *mut LeanObject,
    mut v_b_4212_: *mut LeanObject,
    mut v___y_4213_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4214_: *mut LeanObject = core::ptr::null_mut();
    v_res_4214_ =
        l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(
            v_as_x27_4211_,
            v_b_4212_,
        );
    lean_dec(v_as_x27_4211_);
    return v_res_4214_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6() -> *mut LeanObject {
    let mut v___x_4225_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4227_: *mut LeanObject = core::ptr::null_mut();
    v___x_4225_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3;
    v___x_4226_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__5;
    v___x_4227_ = l_Lean_Name_append(v___x_4226_, v___x_4225_);
    return v___x_4227_;
}
pub unsafe fn _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9() -> *mut LeanObject {
    let mut v___x_4231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4232_: *mut LeanObject = core::ptr::null_mut();
    v___x_4231_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__8;
    v___x_4232_ = l_Lean_MessageData_ofFormat(v___x_4231_);
    return v___x_4232_;
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(
    mut v_code_4233_: *mut LeanObject,
    mut v_a_4234_: *mut LeanObject,
    mut v_a_4235_: *mut LeanObject,
    mut v_a_4236_: *mut LeanObject,
    mut v_a_4237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4243_: u8 = 0;
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4252_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4257_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4258_: u8 = 0;
    let mut v_a_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4261_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4262_: u8 = 0;
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4266_: u8 = 0;
    let mut v___x_4267_: u8 = 0;
    let mut v___x_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_4273_: u8 = 0;
    let mut v_inheritedTraceOptions_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4277_: u8 = 0;
    let mut v___x_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4279_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4282_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4286_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4287_: u8 = 0;
    let mut v___x_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4291_: u8 = 0;
    let mut v_isSharedCheck_4292_: u8 = 0;
    let mut v_a_4293_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4296_: u8 = 0;
    let mut v___x_4298_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                lean_inc_ref(v_code_4233_);
                v___x_4239_ = l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo(
                    v_code_4233_,
                    v_a_4234_,
                    v_a_4235_,
                    v_a_4236_,
                    v_a_4237_,
                );
                if lean_obj_tag(v___x_4239_) == 0 {
                    v_a_4240_ = lean_ctor_get(v___x_4239_, 0);
                    v_isSharedCheck_4292_ = (!lean_is_exclusive(v___x_4239_)) as u8;
                    if v_isSharedCheck_4292_ == 0 {
                        v___x_4242_ = v___x_4239_;
                        v_isShared_4243_ = v_isSharedCheck_4292_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4240_);
                        lean_dec(v___x_4239_);
                        v___x_4242_ = lean_box(0);
                        v_isShared_4243_ = v_isSharedCheck_4292_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_code_4233_);
                    v_a_4293_ = lean_ctor_get(v___x_4239_, 0);
                    v_isSharedCheck_4300_ = (!lean_is_exclusive(v___x_4239_)) as u8;
                    if v_isSharedCheck_4300_ == 0 {
                        v___x_4295_ = v___x_4239_;
                        v_isShared_4296_ = v_isSharedCheck_4300_;
                        state = 10;
                        continue;
                    } else {
                        lean_inc(v_a_4293_);
                        lean_dec(v___x_4239_);
                        v___x_4295_ = lean_box(0);
                        v_isShared_4296_ = v_isSharedCheck_4300_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4267_ = l_Lean_Compiler_LCNF_Simp_JpCasesInfoMap_isCandidate(v_a_4240_);
                if v___x_4267_ == 0 {
                    lean_dec(v_a_4240_);
                    lean_dec_ref(v_code_4233_);
                    v___x_4268_ = lean_box(0);
                    if v_isShared_4243_ == 0 {
                        lean_ctor_set(v___x_4242_, 0, v___x_4268_);
                        v___x_4270_ = v___x_4242_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4271_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4271_, 0, v___x_4268_);
                        v___x_4270_ = v_reuseFailAlloc_4271_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4242_);
                    v_options_4272_ = lean_ctor_get(v_a_4236_, 2);
                    v_hasTrace_4273_ = lean_ctor_get_uint8(
                        v_options_4272_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_4273_ == 0 {
                        state = 2;
                        continue;
                    } else {
                        v_inheritedTraceOptions_4274_ = lean_ctor_get(v_a_4236_, 13);
                        v___x_4275_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3;
                        v___x_4276_ = lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6_once
                            ),
                            _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__6,
                        );
                        v___x_4277_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_4274_,
                            v_options_4272_,
                            v___x_4276_,
                        );
                        if v___x_4277_ == 0 {
                            state = 2;
                            continue;
                        } else {
                            v___x_4278_ = lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9_once
                                ),
                                _init_l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__9,
                            );
                            v___x_4279_ = lean_box(0);
                            v___x_4280_ = l_Std_DTreeMap_Internal_Impl_foldrM___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__2(v___x_4279_, v_a_4240_);
                            v___x_4281_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(v___x_4280_, v___x_4278_);
                            lean_dec(v___x_4280_);
                            v_a_4282_ = lean_ctor_get(v___x_4281_, 0);
                            lean_inc(v_a_4282_);
                            lean_dec_ref(v___x_4281_);
                            v___x_4283_ = l_Lean_addTrace___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__4(v___x_4275_, v_a_4282_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_);
                            if lean_obj_tag(v___x_4283_) == 0 {
                                lean_dec_ref_known(v___x_4283_, 1);
                                state = 2;
                                continue;
                            } else {
                                lean_dec(v_a_4240_);
                                lean_dec_ref(v_code_4233_);
                                v_a_4284_ = lean_ctor_get(v___x_4283_, 0);
                                v_isSharedCheck_4291_ = (!lean_is_exclusive(v___x_4283_)) as u8;
                                if v_isSharedCheck_4291_ == 0 {
                                    v___x_4286_ = v___x_4283_;
                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                    state = 8;
                                    continue;
                                } else {
                                    lean_inc(v_a_4284_);
                                    lean_dec(v___x_4283_);
                                    v___x_4286_ = lean_box(0);
                                    v_isShared_4287_ = v_isSharedCheck_4291_;
                                    state = 8;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4245_ = lean_box(1);
                v___x_4246_ = lean_st_mk_ref(v___x_4245_);
                v___x_4247_ = lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2_once
                    ),
                    _init_l_Lean_Compiler_LCNF_Simp_collectJpCasesInfo___closed__2,
                );
                v___x_4248_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_simpJpCases_x3f_visit(v_code_4233_, v_a_4240_, v___x_4246_, v___x_4247_, v_a_4234_, v_a_4235_, v_a_4236_, v_a_4237_);
                lean_dec(v_a_4240_);
                if lean_obj_tag(v___x_4248_) == 0 {
                    v_a_4249_ = lean_ctor_get(v___x_4248_, 0);
                    v_isSharedCheck_4258_ = (!lean_is_exclusive(v___x_4248_)) as u8;
                    if v_isSharedCheck_4258_ == 0 {
                        v___x_4251_ = v___x_4248_;
                        v_isShared_4252_ = v_isSharedCheck_4258_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4249_);
                        lean_dec(v___x_4248_);
                        v___x_4251_ = lean_box(0);
                        v_isShared_4252_ = v_isSharedCheck_4258_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_dec(v___x_4246_);
                    v_a_4259_ = lean_ctor_get(v___x_4248_, 0);
                    v_isSharedCheck_4266_ = (!lean_is_exclusive(v___x_4248_)) as u8;
                    if v_isSharedCheck_4266_ == 0 {
                        v___x_4261_ = v___x_4248_;
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4259_);
                        lean_dec(v___x_4248_);
                        v___x_4261_ = lean_box(0);
                        v_isShared_4262_ = v_isSharedCheck_4266_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                v___x_4253_ = lean_st_ref_get(v___x_4246_);
                lean_dec(v___x_4246_);
                lean_dec(v___x_4253_);
                v___x_4254_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_4254_, 0, v_a_4249_);
                if v_isShared_4252_ == 0 {
                    lean_ctor_set(v___x_4251_, 0, v___x_4254_);
                    v___x_4256_ = v___x_4251_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4257_, 0, v___x_4254_);
                    v___x_4256_ = v_reuseFailAlloc_4257_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4256_;
            }
            5 => {
                if v_isShared_4262_ == 0 {
                    v___x_4264_ = v___x_4261_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4265_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4265_, 0, v_a_4259_);
                    v___x_4264_ = v_reuseFailAlloc_4265_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4264_;
            }
            7 => {
                return v___x_4270_;
            }
            8 => {
                if v_isShared_4287_ == 0 {
                    v___x_4289_ = v___x_4286_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4290_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4290_, 0, v_a_4284_);
                    v___x_4289_ = v_reuseFailAlloc_4290_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4289_;
            }
            10 => {
                if v_isShared_4296_ == 0 {
                    v___x_4298_ = v___x_4295_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4299_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4299_, 0, v_a_4293_);
                    v___x_4298_ = v_reuseFailAlloc_4299_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4298_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___boxed(
    mut v_code_4301_: *mut LeanObject,
    mut v_a_4302_: *mut LeanObject,
    mut v_a_4303_: *mut LeanObject,
    mut v_a_4304_: *mut LeanObject,
    mut v_a_4305_: *mut LeanObject,
    mut v_a_4306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4307_: *mut LeanObject = core::ptr::null_mut();
    v_res_4307_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f(
        v_code_4301_,
        v_a_4302_,
        v_a_4303_,
        v_a_4304_,
        v_a_4305_,
    );
    lean_dec(v_a_4305_);
    lean_dec_ref(v_a_4304_);
    lean_dec(v_a_4303_);
    lean_dec_ref(v_a_4302_);
    return v_res_4307_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(
    mut v_as_4308_: *mut LeanObject,
    mut v_as_x27_4309_: *mut LeanObject,
    mut v_b_4310_: *mut LeanObject,
    mut v_a_4311_: *mut LeanObject,
    mut v___y_4312_: *mut LeanObject,
    mut v___y_4313_: *mut LeanObject,
    mut v___y_4314_: *mut LeanObject,
    mut v___y_4315_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    v___x_4317_ =
        l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___redArg(
            v_as_x27_4309_,
            v_b_4310_,
        );
    return v___x_4317_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3___boxed(
    mut v_as_4318_: *mut LeanObject,
    mut v_as_x27_4319_: *mut LeanObject,
    mut v_b_4320_: *mut LeanObject,
    mut v_a_4321_: *mut LeanObject,
    mut v___y_4322_: *mut LeanObject,
    mut v___y_4323_: *mut LeanObject,
    mut v___y_4324_: *mut LeanObject,
    mut v___y_4325_: *mut LeanObject,
    mut v___y_4326_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4327_: *mut LeanObject = core::ptr::null_mut();
    v_res_4327_ = l_List_forIn_x27_loop___at___00Lean_Compiler_LCNF_Simp_simpJpCases_x3f_spec__3(
        v_as_4318_,
        v_as_x27_4319_,
        v_b_4320_,
        v_a_4321_,
        v___y_4322_,
        v___y_4323_,
        v___y_4324_,
        v___y_4325_,
    );
    lean_dec(v___y_4325_);
    lean_dec_ref(v___y_4324_);
    lean_dec(v___y_4323_);
    lean_dec_ref(v___y_4322_);
    lean_dec(v_as_x27_4319_);
    lean_dec(v_as_4318_);
    return v_res_4327_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_()
-> *mut LeanObject {
    let mut v___x_4401_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4402_: u8 = 0;
    let mut v___x_4403_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4404_: *mut LeanObject = core::ptr::null_mut();
    v___x_4401_ = l_Lean_Compiler_LCNF_Simp_simpJpCases_x3f___closed__3;
    v___x_4402_ = 0;
    v___x_4403_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn___closed__29_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_;
    v___x_4404_ = l_Lean_registerTraceClass(v___x_4401_, v___x_4402_, v___x_4403_);
    return v___x_4404_;
}
pub unsafe fn l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2____boxed(
    mut v_a_4405_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4406_: *mut LeanObject = core::ptr::null_mut();
    v_res_4406_ = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
    return v_res_4406_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default =
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default();
    lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo_default);
    l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo =
        _init_l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo();
    lean_mark_persistent(l_Lean_Compiler_LCNF_Simp_instInhabitedJpCasesInfo);
    res = l___private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_initFn_00___x40_Lean_Compiler_LCNF_Simp_JpCases_862626027____hygCtx___hyg_2_();
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_LCNF_DependsOn(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Internalize(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Compiler_LCNF_Simp_DiscrM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Compiler_LCNF_Simp_JpCases(builtin);
}
