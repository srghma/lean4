// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.FindRecArg
// Imports: Lean.Elab.PreDefinition.TerminationMeasure Lean.Elab.PreDefinition.Structural.Basic Lean.Elab.PreDefinition.Structural.RecArgInfo Init.Omega
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_mk, lean_array_push, lean_array_size,
    lean_array_to_list, lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_eqv,
    lean_infer_type, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq, lean_nat_add,
    lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul, lean_nat_sub,
    lean_panic_fn_borrowed, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_uint64_of_nat,
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_add,
    lean_usize_dec_eq, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_sub,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any,
    l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop, l_Array_append___redArg,
};
use crate::r#gen::Init::Data::Array::Subarray::l_Array_toSubarray___redArg;
use crate::r#gen::Init::Data::List::Basic::l_List_reverse___redArg;
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Nat_reprFast;
use crate::r#gen::Init::Data::Slice::Array::Iterator::l_Subarray_copy___redArg;
use crate::r#gen::Init::Omega::{initialize_Init_Omega, runtime_initialize_Init_Omega};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_hasMacroScopes, l_Lean_replaceRef,
};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::CoreM::l_Lean_Exception_isRuntime;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_push___redArg;
use crate::r#gen::Lean::Elab::PreDefinition::FixedParams::{
    l_Lean_Elab_FixedParamPerm_buildArgs___redArg, l_Lean_Elab_FixedParamPerm_isFixed,
    l_Lean_Elab_FixedParamPerm_pickVarying___redArg,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::Basic::{
    initialize_Lean_Elab_PreDefinition_Structural_Basic,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::IndGroupInfo::{
    l_Lean_Elab_Structural_IndGroupInfo_brecOnName, l_Lean_Elab_Structural_IndGroupInfo_numMotives,
    l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal,
    l_Lean_Elab_Structural_IndGroupInst_isDefEq,
    l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed,
    l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers,
    l_Lean_Elab_Structural_IndGroupInst_toMessageData,
};
use crate::r#gen::Lean::Elab::PreDefinition::Structural::RecArgInfo::{
    initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo,
    l_Lean_Elab_Structural_instInhabitedRecArgInfo_default,
    l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg,
    runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo,
};
use crate::r#gen::Lean::Elab::PreDefinition::TerminationMeasure::{
    initialize_Lean_Elab_PreDefinition_TerminationMeasure,
    l_Lean_Elab_TerminationMeasure_structuralArg,
    runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure,
};
use crate::r#gen::Lean::Environment::{l_Lean_Environment_contains, l_Lean_Environment_find_x3f};
use crate::r#gen::Lean::Exception::{l_Lean_Exception_isInterrupt, l_Lean_Exception_toMessageData};
use crate::r#gen::Lean::Expr::{
    l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux, l_Lean_Expr_fvarId_x21, l_Lean_Expr_getAppFn,
    l_Lean_Expr_getAppNumArgs, l_Lean_Expr_hasFVar, l_Lean_Expr_hasMVar, l_Lean_Expr_isFVar,
    l_Lean_Expr_sort___override, l_Lean_instBEqFVarId_beq, l_Lean_instInhabitedExpr,
};
use crate::r#gen::Lean::LocalContext::{l_Lean_LocalDecl_isLet, l_Lean_LocalDecl_type};
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_andList, l_Lean_MessageData_joinSep, l_Lean_MessageData_ofExpr,
    l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofList, l_Lean_MessageData_ofName,
    l_Lean_indentD, l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::Basic::{
    l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp,
    l_Lean_FVarId_getUserName___redArg, l_Lean_Meta_SavedState_restore___redArg,
    l_Lean_Meta_forallMetaTelescope, l_Lean_Meta_getFVarLocalDecl___redArg,
    l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, l_Lean_Meta_isExprDefEqGuarded,
    l_Lean_Meta_mapErrorImp___redArg, l_Lean_Meta_saveState___redArg, l_Lean_Meta_whnfD,
};
use crate::r#gen::Lean::MetavarContext::{
    l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit, l_Lean_instantiateMVarsCore,
};
use crate::r#gen::Lean::Util::Trace::l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go;
pub static l_Lean_Elab_Structural_prettyParam___closed__0_value: leanh::LeanStringObject<2> =
    leanh::LeanStringObject {
        m_header: leanh::LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 2,
        m_capacity: 2,
        m_length: 1,
        m_data: [35, 0],
    };
static mut l_Lean_Elab_Structural_prettyParam___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_prettyParam___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_prettyParam___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_prettyParam___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [32, 111, 102, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_prettyParameterSet___closed__0_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Structural_prettyParameterSet___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_prettyParameterSet___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_prettyParameterSet___closed__1_value:
    leanh::LeanStringObject<12> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 0],
};
static mut l_Lean_Elab_Structural_prettyParameterSet___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_prettyParameterSet___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_prettyParameterSet___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_prettyParameterSet___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_prettyParameterSet___closed__3_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 0],
};
static mut l_Lean_Elab_Structural_prettyParameterSet___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_prettyParameterSet___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_prettyParameterSet___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_prettyParameterSet___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0_value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_instInhabitedMetaM___lam__0___boxed as *const core::ffi::c_void,
    m_arity: 5,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0_value
) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0_value: leanh::LeanStringObject<46> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 46, m_capacity: 46, m_length: 45, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 80, 114, 101, 68, 101, 102, 105, 110, 105, 116, 105, 111, 110, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 70, 105, 110, 100, 82, 101, 99, 65, 114, 103, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 103, 101, 116, 82, 101, 99, 65, 114, 103, 73, 110, 102, 111, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__0_value: leanh::LeanStringObject<
    29,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 29,
    m_capacity: 29,
    m_length: 28,
    m_data: [
        105, 116, 115, 32, 116, 121, 112, 101, 32, 105, 115, 32, 110, 111, 116, 32, 97, 110, 32,
        105, 110, 100, 117, 99, 116, 105, 118, 101, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__2_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [105, 116, 115, 32, 116, 121, 112, 101, 32, 0],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__4_value: leanh::LeanStringObject<
    62,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 62,
    m_capacity: 62,
    m_length: 61,
    m_data: [
        32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 102, 97,
        109, 105, 108, 121, 32, 97, 110, 100, 32, 105, 110, 100, 105, 99, 101, 115, 32, 97, 114,
        101, 32, 110, 111, 116, 32, 112, 97, 105, 114, 119, 105, 115, 101, 32, 100, 105, 115, 116,
        105, 110, 99, 116, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__6_value: leanh::LeanStringObject<
    36,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 36,
    m_capacity: 36,
    m_length: 35,
    m_data: [
        123, 105, 110, 100, 73, 110, 102, 111, 46, 110, 97, 109, 101, 125, 32, 110, 111, 116, 32,
        105, 110, 32, 123, 105, 110, 100, 73, 110, 102, 111, 46, 97, 108, 108, 125, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__8_value: leanh::LeanStringObject<
    34,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 34,
    m_capacity: 34,
    m_length: 33,
    m_data: [
        105, 116, 115, 32, 116, 121, 112, 101, 32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 117,
        99, 116, 105, 118, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__8: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__8_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__9_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__9: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__10_value: leanh::LeanStringObject<
    28,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 28,
    m_capacity: 28,
    m_length: 27,
    m_data: [
        10, 97, 110, 100, 32, 116, 104, 101, 32, 100, 97, 116, 97, 116, 121, 112, 101, 32, 112, 97,
        114, 97, 109, 101, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__10: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__10_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__11_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__11: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__12_value: leanh::LeanStringObject<
    35,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 35,
    m_capacity: 35,
    m_length: 34,
    m_data: [
        10, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 116, 104, 101, 32, 102, 117, 110,
        99, 116, 105, 111, 110, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__12: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__12_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__13_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__13: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__14_value: leanh::LeanStringObject<
    21,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 21,
    m_capacity: 21,
    m_length: 20,
    m_data: [
        10, 119, 104, 105, 99, 104, 32, 105, 115, 32, 110, 111, 116, 32, 102, 105, 120, 101, 100,
        46, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__14: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__14_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__15_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__15: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__16_value: leanh::LeanStringObject<
    24,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 102, 97,
        109, 105, 108, 121, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__16: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__16_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__17_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__17: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__18_value: leanh::LeanStringObject<
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
    m_data: [10, 97, 110, 100, 32, 105, 110, 100, 101, 120, 0],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__18: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__18_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__19_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__19: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__20_value: leanh::LeanStringObject<
    26,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 26,
    m_capacity: 26,
    m_length: 25,
    m_data: [
        10, 100, 101, 112, 101, 110, 100, 115, 32, 111, 110, 32, 116, 104, 101, 32, 110, 111, 110,
        32, 105, 110, 100, 101, 120, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__20: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__20_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__21_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__21: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__22_value: leanh::LeanStringObject<
    54,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        32, 105, 115, 32, 97, 110, 32, 105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 102, 97,
        109, 105, 108, 121, 32, 97, 110, 100, 32, 105, 110, 100, 105, 99, 101, 115, 32, 97, 114,
        101, 32, 110, 111, 116, 32, 118, 97, 114, 105, 97, 98, 108, 101, 115, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__22: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__22_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__23_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__23: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__24_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__24: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__25_value: leanh::LeanStringObject<
    20,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 20,
    m_capacity: 20,
    m_length: 19,
    m_data: [
        105, 116, 32, 105, 115, 32, 97, 32, 108, 101, 116, 45, 98, 105, 110, 100, 105, 110, 103, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__25: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__25_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__26_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__26: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__27_value: leanh::LeanStringObject<
    54,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 54,
    m_capacity: 54,
    m_length: 53,
    m_data: [
        97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110,
        58, 32, 102, 105, 120, 101, 100, 80, 97, 114, 97, 109, 80, 101, 114, 109, 46, 115, 105,
        122, 101, 32, 61, 32, 120, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__27: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__27_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__28_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__28: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__29_value: leanh::LeanStringObject<
    12,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 12,
    m_capacity: 12,
    m_length: 11,
    m_data: [116, 104, 101, 32, 105, 110, 100, 101, 120, 32, 35, 0],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__29: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__29_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__30_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__30: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__31_value: leanh::LeanStringObject<
    10,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 10,
    m_capacity: 10,
    m_length: 9,
    m_data: [32, 101, 120, 99, 101, 101, 100, 115, 32, 0],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__31: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__31_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__32_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__32: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__33_value: leanh::LeanStringObject<
    27,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 27,
    m_capacity: 27,
    m_length: 26,
    m_data: [
        44, 32, 116, 104, 101, 32, 110, 117, 109, 98, 101, 114, 32, 111, 102, 32, 112, 97, 114, 97,
        109, 101, 116, 101, 114, 115, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__33: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__33_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__34_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__34: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfo___closed__35_value: leanh::LeanStringObject<
    39,
> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        105, 116, 32, 105, 115, 32, 117, 110, 99, 104, 97, 110, 103, 101, 100, 32, 105, 110, 32,
        116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 99, 97, 108, 108, 115,
        0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__35: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfo___closed__35_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__36_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_getRecArgInfo___closed__36: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0_value: leanh::LeanStringObject<27> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 27, m_capacity: 27, m_length: 26, m_data: [78, 111, 116, 32, 99, 111, 110, 115, 105, 100, 101, 114, 105, 110, 103, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [10, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5_value: leanh::LeanCtorObject<1> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*1 + 0) as u16, other: 1, tag: 3 }, m_objs: [core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4_value) as *mut leanh::LeanObject] };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0: f64 =
    0.0;
pub static l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0_value:
    leanh::LeanStringObject<55> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 55,
    m_capacity: 55,
    m_length: 54,
    m_data: [
        99, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 115, 112, 101, 99, 105, 102, 105, 101,
        100, 32, 109, 101, 97, 115, 117, 114, 101, 32, 102, 111, 114, 32, 115, 116, 114, 117, 99,
        116, 117, 114, 97, 108, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 58, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6_value:
    leanh::LeanStringObject<5> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 5,
    m_capacity: 5,
    m_length: 4,
    m_data: [69, 108, 97, 98, 0],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [100, 101, 102, 105, 110, 105, 116, 105, 111, 110, 0],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8_value:
    leanh::LeanStringObject<11> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 11,
    m_capacity: 11,
    m_length: 10,
    m_data: [115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 0],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8_value)
        as *mut leanh::LeanObject;
static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_0:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__6_value)
            as *mut leanh::LeanObject,
        12843180897352504333 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_1:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__7_value)
            as *mut leanh::LeanObject,
        6897119537390546559 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__8_value)
            as *mut leanh::LeanObject,
        14406337792964512117 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value:
    leanh::LeanStringObject<6> = leanh::LeanStringObject {
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
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
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
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__10_value)
            as *mut leanh::LeanObject,
        14231257465488249300 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13_value:
    leanh::LeanStringObject<24> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 24,
    m_capacity: 24,
    m_length: 23,
    m_data: [
        103, 101, 116, 82, 101, 99, 65, 114, 103, 73, 110, 102, 111, 115, 32, 114, 101, 112, 111,
        114, 116, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_nonIndicesFirst___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Elab_Structural_nonIndicesFirst___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_nonIndicesFirst___closed__2_value: leanh::LeanCtorObject<
    2,
> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_nonIndicesFirst___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_nonIndicesFirst___closed__2_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_inductiveGroups___closed__0_value:
    leanh::LeanClosureObject<0> = leanh::LeanClosureObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Elab_Structural_IndGroupInst_isDefEq___boxed as *const core::ffi::c_void,
    m_arity: 7,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Elab_Structural_inductiveGroups___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_inductiveGroups___closed__0_value)
        as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0_value: leanh::LeanStringObject<33> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 33, m_capacity: 33, m_length: 32, m_data: [76, 101, 97, 110, 46, 69, 108, 97, 98, 46, 83, 116, 114, 117, 99, 116, 117, 114, 97, 108, 46, 97, 114, 103, 115, 73, 110, 71, 114, 111, 117, 112, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Elab_Structural_maxCombinationSize: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1_value: leanh::LeanStringObject<28> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 28, m_capacity: 28, m_length: 27, m_data: [83, 107, 105, 112, 112, 105, 110, 103, 32, 97, 114, 103, 117, 109, 101, 110, 116, 115, 32, 111, 102, 32, 116, 121, 112, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [44, 32, 97, 115, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [32, 104, 97, 115, 32, 110, 111, 32, 99, 111, 109, 112, 97, 116, 105, 98, 108, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 46, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [84, 111, 111, 32, 109, 97, 110, 121, 32, 112, 111, 115, 115, 105, 98, 108, 101, 32, 99, 111, 109, 98, 105, 110, 97, 116, 105, 111, 110, 115, 32, 111, 102, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 111, 102, 32, 116, 121, 112, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [32, 40, 111, 114, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11_value: leanh::LeanStringObject<87> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 87, m_capacity: 87, m_length: 86, m_data: [112, 108, 101, 97, 115, 101, 32, 105, 110, 100, 105, 99, 97, 116, 101, 32, 116, 104, 101, 32, 114, 101, 99, 117, 114, 115, 105, 118, 101, 32, 97, 114, 103, 117, 109, 101, 110, 116, 32, 101, 120, 112, 108, 105, 99, 105, 116, 108, 121, 32, 117, 115, 105, 110, 103, 32, 96, 116, 101, 114, 109, 105, 110, 97, 116, 105, 111, 110, 95, 98, 121, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 96, 41, 46, 10, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value:
    leanh::LeanStringObject<48> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 48,
    m_capacity: 48,
    m_length: 47,
    m_data: [
        110, 111, 32, 112, 97, 114, 97, 109, 101, 116, 101, 114, 115, 32, 115, 117, 105, 116, 97,
        98, 108, 101, 32, 102, 111, 114, 32, 115, 116, 114, 117, 99, 116, 117, 114, 97, 108, 32,
        114, 101, 99, 117, 114, 115, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_findRecArgCandidates___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [
        core::ptr::addr_of!(l_Lean_Elab_Structural_findRecArgCandidates___closed__0_value)
            as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_findRecArgCandidates___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_findRecArgCandidates___closed__3_value:
    leanh::LeanStringObject<19> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 19,
    m_capacity: 19,
    m_length: 18,
    m_data: [
        105, 110, 100, 117, 99, 116, 105, 118, 101, 32, 103, 114, 111, 117, 112, 115, 58, 32, 0,
    ],
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_findRecArgCandidates___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Elab_Structural_findRecArgCandidates___closed__5_value:
    leanh::LeanArrayObject<0> = leanh::LeanArrayObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<usize>() * 2
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0) as u16,
        other: 0,
        tag: 246,
    },
    m_size: 0,
    m_capacity: 0,
    m_data: [],
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__5: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_findRecArgCandidates___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Elab_Structural_findRecArgCandidates___closed__6_value:
    leanh::LeanStringObject<13> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 13,
    m_capacity: 13,
    m_length: 12,
    m_data: [114, 101, 99, 65, 114, 103, 73, 110, 102, 111, 115, 58, 0],
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_findRecArgCandidates___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_findRecArgCandidates___closed__8: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0_value: leanh::LeanStringObject<10> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [116, 104, 101, 32, 116, 121, 112, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2_value: leanh::LeanStringObject<36> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 36, m_capacity: 36, m_length: 35, m_data: [32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 32, 96, 46, 98, 114, 101, 99, 79, 110, 96, 32, 114, 101, 99, 117, 114, 115, 111, 114, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [67, 97, 110, 110, 111, 116, 32, 117, 115, 101, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_tryCandidates___redArg___closed__0_value:
    leanh::LeanStringObject<39> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 39,
    m_capacity: 39,
    m_length: 38,
    m_data: [
        102, 97, 105, 108, 101, 100, 32, 116, 111, 32, 105, 110, 102, 101, 114, 32, 115, 116, 114,
        117, 99, 116, 117, 114, 97, 108, 32, 114, 101, 99, 117, 114, 115, 105, 111, 110, 58, 10, 0,
    ],
};
static mut l_Lean_Elab_Structural_tryCandidates___redArg___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_tryCandidates___redArg___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_tryCandidates___redArg___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Elab_Structural_tryCandidates___redArg___closed__2_value:
    leanh::LeanStringObject<16> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 16,
    m_capacity: 16,
    m_length: 15,
    m_data: [
        116, 114, 121, 67, 97, 110, 100, 105, 100, 97, 116, 101, 115, 58, 10, 0,
    ],
};
static mut l_Lean_Elab_Structural_tryCandidates___redArg___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Elab_Structural_tryCandidates___redArg___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Elab_Structural_tryCandidates___redArg___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(
    mut v_msgData_4599_: *mut leanh::LeanObject,
    mut v___y_4600_: *mut leanh::LeanObject,
    mut v___y_4601_: *mut leanh::LeanObject,
    mut v___y_4602_: *mut leanh::LeanObject,
    mut v___y_4603_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_4610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4605_ = lean_st_ref_get(v___y_4603_);
    v_env_4606_ = leanh::lean_ctor_get(v___x_4605_, 0);
    leanh::lean_inc_ref(v_env_4606_);
    leanh::lean_dec(v___x_4605_);
    v___x_4607_ = lean_st_ref_get(v___y_4601_);
    v_mctx_4608_ = leanh::lean_ctor_get(v___x_4607_, 0);
    leanh::lean_inc_ref(v_mctx_4608_);
    leanh::lean_dec(v___x_4607_);
    v_lctx_4609_ = leanh::lean_ctor_get(v___y_4600_, 2);
    v_options_4610_ = leanh::lean_ctor_get(v___y_4602_, 2);
    leanh::lean_inc_ref(v_options_4610_);
    leanh::lean_inc_ref(v_lctx_4609_);
    v___x_4611_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_4611_, 0, v_env_4606_);
    leanh::lean_ctor_set(v___x_4611_, 1, v_mctx_4608_);
    leanh::lean_ctor_set(v___x_4611_, 2, v_lctx_4609_);
    leanh::lean_ctor_set(v___x_4611_, 3, v_options_4610_);
    v___x_4612_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4612_, 0, v___x_4611_);
    leanh::lean_ctor_set(v___x_4612_, 1, v_msgData_4599_);
    v___x_4613_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4613_, 0, v___x_4612_);
    return v___x_4613_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0___boxed(
    mut v_msgData_4614_: *mut leanh::LeanObject,
    mut v___y_4615_: *mut leanh::LeanObject,
    mut v___y_4616_: *mut leanh::LeanObject,
    mut v___y_4617_: *mut leanh::LeanObject,
    mut v___y_4618_: *mut leanh::LeanObject,
    mut v___y_4619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4620_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(
        v_msgData_4614_,
        v___y_4615_,
        v___y_4616_,
        v___y_4617_,
        v___y_4618_,
    );
    leanh::lean_dec(v___y_4618_);
    leanh::lean_dec_ref(v___y_4617_);
    leanh::lean_dec(v___y_4616_);
    leanh::lean_dec_ref(v___y_4615_);
    return v_res_4620_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_prettyParam___closed__1() -> *mut leanh::LeanObject
{
    let mut v___x_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4622_ = l_Lean_Elab_Structural_prettyParam___closed__0;
    v___x_4623_ = l_Lean_stringToMessageData(v___x_4622_);
    return v___x_4623_;
}
pub unsafe fn l_Lean_Elab_Structural_prettyParam(
    mut v_xs_4624_: *mut leanh::LeanObject,
    mut v_i_4625_: *mut leanh::LeanObject,
    mut v_a_4626_: *mut leanh::LeanObject,
    mut v_a_4627_: *mut leanh::LeanObject,
    mut v_a_4628_: *mut leanh::LeanObject,
    mut v_a_4629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4636_: u8 = 0;
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4650_: u8 = 0;
    let mut v___x_4652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4654_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4631_ = l_Lean_instInhabitedExpr;
                v_x_4632_ = lean_array_get_borrowed(v___x_4631_, v_xs_4624_, v_i_4625_);
                v___x_4633_ = l_Lean_Expr_fvarId_x21(v_x_4632_);
                v___x_4634_ = l_Lean_FVarId_getUserName___redArg(
                    v___x_4633_,
                    v_a_4626_,
                    v_a_4628_,
                    v_a_4629_,
                );
                if leanh::lean_obj_tag(v___x_4634_) == 0 {
                    v_a_4635_ = leanh::lean_ctor_get(v___x_4634_, 0);
                    leanh::lean_inc(v_a_4635_);
                    leanh::lean_dec_ref_known(v___x_4634_, 1);
                    v___x_4636_ = l_Lean_Name_hasMacroScopes(v_a_4635_);
                    leanh::lean_dec(v_a_4635_);
                    if v___x_4636_ == 0 {
                        leanh::lean_inc(v_x_4632_);
                        v___x_4637_ = l_Lean_MessageData_ofExpr(v_x_4632_);
                        v___x_4638_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_4637_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
                        return v___x_4638_;
                    } else {
                        v___x_4639_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(l_Lean_Elab_Structural_prettyParam___closed__1),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_prettyParam___closed__1_once
                            ),
                            _init_l_Lean_Elab_Structural_prettyParam___closed__1,
                        );
                        v___x_4640_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4641_ = lean_nat_add(v_i_4625_, v___x_4640_);
                        v___x_4642_ = l_Nat_reprFast(v___x_4641_);
                        v___x_4643_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4643_, 0, v___x_4642_);
                        v___x_4644_ = l_Lean_MessageData_ofFormat(v___x_4643_);
                        v___x_4645_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4645_, 0, v___x_4639_);
                        leanh::lean_ctor_set(v___x_4645_, 1, v___x_4644_);
                        v___x_4646_ = l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(v___x_4645_, v_a_4626_, v_a_4627_, v_a_4628_, v_a_4629_);
                        return v___x_4646_;
                    }
                } else {
                    v_a_4647_ = leanh::lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4654_ = (!leanh::lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4654_ == 0 {
                        v___x_4649_ = v___x_4634_;
                        v_isShared_4650_ = v_isSharedCheck_4654_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4647_);
                        leanh::lean_dec(v___x_4634_);
                        v___x_4649_ = leanh::lean_box(0);
                        v_isShared_4650_ = v_isSharedCheck_4654_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4650_ == 0 {
                    v___x_4652_ = v___x_4649_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4653_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4653_, 0, v_a_4647_);
                    v___x_4652_ = v_reuseFailAlloc_4653_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_prettyParam___boxed(
    mut v_xs_4655_: *mut leanh::LeanObject,
    mut v_i_4656_: *mut leanh::LeanObject,
    mut v_a_4657_: *mut leanh::LeanObject,
    mut v_a_4658_: *mut leanh::LeanObject,
    mut v_a_4659_: *mut leanh::LeanObject,
    mut v_a_4660_: *mut leanh::LeanObject,
    mut v_a_4661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4662_ = l_Lean_Elab_Structural_prettyParam(
        v_xs_4655_, v_i_4656_, v_a_4657_, v_a_4658_, v_a_4659_, v_a_4660_,
    );
    leanh::lean_dec(v_a_4660_);
    leanh::lean_dec_ref(v_a_4659_);
    leanh::lean_dec(v_a_4658_);
    leanh::lean_dec_ref(v_a_4657_);
    leanh::lean_dec(v_i_4656_);
    leanh::lean_dec_ref(v_xs_4655_);
    return v_res_4662_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(
    mut v_k_4663_: *mut leanh::LeanObject,
    mut v_b_4664_: *mut leanh::LeanObject,
    mut v_c_4665_: *mut leanh::LeanObject,
    mut v___y_4666_: *mut leanh::LeanObject,
    mut v___y_4667_: *mut leanh::LeanObject,
    mut v___y_4668_: *mut leanh::LeanObject,
    mut v___y_4669_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4671_: *mut leanh::LeanObject = core::ptr::null_mut();
    leanh::lean_inc(v___y_4669_);
    leanh::lean_inc_ref(v___y_4668_);
    leanh::lean_inc(v___y_4667_);
    leanh::lean_inc_ref(v___y_4666_);
    v___x_4671_ = leanh::lean_apply_7(
        v_k_4663_,
        v_b_4664_,
        v_c_4665_,
        v___y_4666_,
        v___y_4667_,
        v___y_4668_,
        v___y_4669_,
        leanh::lean_box(0),
    );
    return v___x_4671_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed(
    mut v_k_4672_: *mut leanh::LeanObject,
    mut v_b_4673_: *mut leanh::LeanObject,
    mut v_c_4674_: *mut leanh::LeanObject,
    mut v___y_4675_: *mut leanh::LeanObject,
    mut v___y_4676_: *mut leanh::LeanObject,
    mut v___y_4677_: *mut leanh::LeanObject,
    mut v___y_4678_: *mut leanh::LeanObject,
    mut v___y_4679_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4680_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0(v_k_4672_, v_b_4673_, v_c_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
    leanh::lean_dec(v___y_4678_);
    leanh::lean_dec_ref(v___y_4677_);
    leanh::lean_dec(v___y_4676_);
    leanh::lean_dec_ref(v___y_4675_);
    return v_res_4680_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(
    mut v_e_4681_: *mut leanh::LeanObject,
    mut v_k_4682_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4683_: u8,
    mut v___y_4684_: *mut leanh::LeanObject,
    mut v___y_4685_: *mut leanh::LeanObject,
    mut v___y_4686_: *mut leanh::LeanObject,
    mut v___y_4687_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: u8 = 0;
    let mut v___x_4691_: u8 = 0;
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4697_: u8 = 0;
    let mut v___x_4699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4701_: u8 = 0;
    let mut v_a_4702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4705_: u8 = 0;
    let mut v___x_4707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4709_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_4689_ = leanh::lean_alloc_closure(l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___lam__0___boxed as *mut core::ffi::c_void, 8, 1);
                leanh::lean_closure_set(v___f_4689_, 0, v_k_4682_);
                v___x_4690_ = 1;
                v___x_4691_ = 0;
                v___x_4692_ = leanh::lean_box(0);
                v___x_4693_ = l___private_Lean_Meta_Basic_0__Lean_Meta_lambdaTelescopeImp(
                    leanh::lean_box(0),
                    v_e_4681_,
                    v___x_4690_,
                    v___x_4691_,
                    v___x_4690_,
                    v___x_4691_,
                    v___x_4692_,
                    v___f_4689_,
                    v_cleanupAnnotations_4683_,
                    v___y_4684_,
                    v___y_4685_,
                    v___y_4686_,
                    v___y_4687_,
                );
                if leanh::lean_obj_tag(v___x_4693_) == 0 {
                    v_a_4694_ = leanh::lean_ctor_get(v___x_4693_, 0);
                    v_isSharedCheck_4701_ = (!leanh::lean_is_exclusive(v___x_4693_)) as u8;
                    if v_isSharedCheck_4701_ == 0 {
                        v___x_4696_ = v___x_4693_;
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4694_);
                        leanh::lean_dec(v___x_4693_);
                        v___x_4696_ = leanh::lean_box(0);
                        v_isShared_4697_ = v_isSharedCheck_4701_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4702_ = leanh::lean_ctor_get(v___x_4693_, 0);
                    v_isSharedCheck_4709_ = (!leanh::lean_is_exclusive(v___x_4693_)) as u8;
                    if v_isSharedCheck_4709_ == 0 {
                        v___x_4704_ = v___x_4693_;
                        v_isShared_4705_ = v_isSharedCheck_4709_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4702_);
                        leanh::lean_dec(v___x_4693_);
                        v___x_4704_ = leanh::lean_box(0);
                        v_isShared_4705_ = v_isSharedCheck_4709_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4697_ == 0 {
                    v___x_4699_ = v___x_4696_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4700_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4700_, 0, v_a_4694_);
                    v___x_4699_ = v_reuseFailAlloc_4700_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4699_;
            }
            3 => {
                if v_isShared_4705_ == 0 {
                    v___x_4707_ = v___x_4704_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4708_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4708_, 0, v_a_4702_);
                    v___x_4707_ = v_reuseFailAlloc_4708_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4707_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg___boxed(
    mut v_e_4710_: *mut leanh::LeanObject,
    mut v_k_4711_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
    mut v___y_4714_: *mut leanh::LeanObject,
    mut v___y_4715_: *mut leanh::LeanObject,
    mut v___y_4716_: *mut leanh::LeanObject,
    mut v___y_4717_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4718_: u8 = 0;
    let mut v_res_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4718_ = (leanh::lean_unbox(v_cleanupAnnotations_4712_) as u8);
    v_res_4719_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(
            v_e_4710_,
            v_k_4711_,
            v_cleanupAnnotations_boxed_4718_,
            v___y_4713_,
            v___y_4714_,
            v___y_4715_,
            v___y_4716_,
        );
    leanh::lean_dec(v___y_4716_);
    leanh::lean_dec_ref(v___y_4715_);
    leanh::lean_dec(v___y_4714_);
    leanh::lean_dec_ref(v___y_4713_);
    return v_res_4719_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(
    mut v_00_u03b1_4720_: *mut leanh::LeanObject,
    mut v_e_4721_: *mut leanh::LeanObject,
    mut v_k_4722_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4723_: u8,
    mut v___y_4724_: *mut leanh::LeanObject,
    mut v___y_4725_: *mut leanh::LeanObject,
    mut v___y_4726_: *mut leanh::LeanObject,
    mut v___y_4727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4729_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(
            v_e_4721_,
            v_k_4722_,
            v_cleanupAnnotations_4723_,
            v___y_4724_,
            v___y_4725_,
            v___y_4726_,
            v___y_4727_,
        );
    return v___x_4729_;
}
pub unsafe fn l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___boxed(
    mut v_00_u03b1_4730_: *mut leanh::LeanObject,
    mut v_e_4731_: *mut leanh::LeanObject,
    mut v_k_4732_: *mut leanh::LeanObject,
    mut v_cleanupAnnotations_4733_: *mut leanh::LeanObject,
    mut v___y_4734_: *mut leanh::LeanObject,
    mut v___y_4735_: *mut leanh::LeanObject,
    mut v___y_4736_: *mut leanh::LeanObject,
    mut v___y_4737_: *mut leanh::LeanObject,
    mut v___y_4738_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cleanupAnnotations_boxed_4739_: u8 = 0;
    let mut v_res_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_cleanupAnnotations_boxed_4739_ = (leanh::lean_unbox(v_cleanupAnnotations_4733_) as u8);
    v_res_4740_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0(
        v_00_u03b1_4730_,
        v_e_4731_,
        v_k_4732_,
        v_cleanupAnnotations_boxed_4739_,
        v___y_4734_,
        v___y_4735_,
        v___y_4736_,
        v___y_4737_,
    );
    leanh::lean_dec(v___y_4737_);
    leanh::lean_dec_ref(v___y_4736_);
    leanh::lean_dec(v___y_4735_);
    leanh::lean_dec_ref(v___y_4734_);
    return v_res_4740_;
}
pub unsafe fn l_Lean_Elab_Structural_prettyRecArg___lam__0(
    mut v_recArgInfo_4741_: *mut leanh::LeanObject,
    mut v_xs_4742_: *mut leanh::LeanObject,
    mut v_ys_4743_: *mut leanh::LeanObject,
    mut v_x_4744_: *mut leanh::LeanObject,
    mut v___y_4745_: *mut leanh::LeanObject,
    mut v___y_4746_: *mut leanh::LeanObject,
    mut v___y_4747_: *mut leanh::LeanObject,
    mut v___y_4748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fixedParamPerm_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_4751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_fixedParamPerm_4750_ = leanh::lean_ctor_get(v_recArgInfo_4741_, 1);
    leanh::lean_inc_ref(v_fixedParamPerm_4750_);
    v_recArgPos_4751_ = leanh::lean_ctor_get(v_recArgInfo_4741_, 2);
    leanh::lean_inc(v_recArgPos_4751_);
    leanh::lean_dec_ref(v_recArgInfo_4741_);
    v___x_4752_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(
        v_fixedParamPerm_4750_,
        v_xs_4742_,
        v_ys_4743_,
    );
    v___x_4753_ = l_Lean_Elab_Structural_prettyParam(
        v___x_4752_,
        v_recArgPos_4751_,
        v___y_4745_,
        v___y_4746_,
        v___y_4747_,
        v___y_4748_,
    );
    leanh::lean_dec(v_recArgPos_4751_);
    leanh::lean_dec_ref(v___x_4752_);
    return v___x_4753_;
}
pub unsafe fn l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed(
    mut v_recArgInfo_4754_: *mut leanh::LeanObject,
    mut v_xs_4755_: *mut leanh::LeanObject,
    mut v_ys_4756_: *mut leanh::LeanObject,
    mut v_x_4757_: *mut leanh::LeanObject,
    mut v___y_4758_: *mut leanh::LeanObject,
    mut v___y_4759_: *mut leanh::LeanObject,
    mut v___y_4760_: *mut leanh::LeanObject,
    mut v___y_4761_: *mut leanh::LeanObject,
    mut v___y_4762_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4763_ = l_Lean_Elab_Structural_prettyRecArg___lam__0(
        v_recArgInfo_4754_,
        v_xs_4755_,
        v_ys_4756_,
        v_x_4757_,
        v___y_4758_,
        v___y_4759_,
        v___y_4760_,
        v___y_4761_,
    );
    leanh::lean_dec(v___y_4761_);
    leanh::lean_dec_ref(v___y_4760_);
    leanh::lean_dec(v___y_4759_);
    leanh::lean_dec_ref(v___y_4758_);
    leanh::lean_dec_ref(v_x_4757_);
    leanh::lean_dec_ref(v_xs_4755_);
    return v_res_4763_;
}
pub unsafe fn l_Lean_Elab_Structural_prettyRecArg(
    mut v_xs_4764_: *mut leanh::LeanObject,
    mut v_value_4765_: *mut leanh::LeanObject,
    mut v_recArgInfo_4766_: *mut leanh::LeanObject,
    mut v_a_4767_: *mut leanh::LeanObject,
    mut v_a_4768_: *mut leanh::LeanObject,
    mut v_a_4769_: *mut leanh::LeanObject,
    mut v_a_4770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_4772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4773_: u8 = 0;
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_4772_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Structural_prettyRecArg___lam__0___boxed as *mut core::ffi::c_void,
        9,
        2,
    );
    leanh::lean_closure_set(v___f_4772_, 0, v_recArgInfo_4766_);
    leanh::lean_closure_set(v___f_4772_, 1, v_xs_4764_);
    v___x_4773_ = 0;
    v___x_4774_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(
            v_value_4765_,
            v___f_4772_,
            v___x_4773_,
            v_a_4767_,
            v_a_4768_,
            v_a_4769_,
            v_a_4770_,
        );
    return v___x_4774_;
}
pub unsafe fn l_Lean_Elab_Structural_prettyRecArg___boxed(
    mut v_xs_4775_: *mut leanh::LeanObject,
    mut v_value_4776_: *mut leanh::LeanObject,
    mut v_recArgInfo_4777_: *mut leanh::LeanObject,
    mut v_a_4778_: *mut leanh::LeanObject,
    mut v_a_4779_: *mut leanh::LeanObject,
    mut v_a_4780_: *mut leanh::LeanObject,
    mut v_a_4781_: *mut leanh::LeanObject,
    mut v_a_4782_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4783_ = l_Lean_Elab_Structural_prettyRecArg(
        v_xs_4775_,
        v_value_4776_,
        v_recArgInfo_4777_,
        v_a_4778_,
        v_a_4779_,
        v_a_4780_,
        v_a_4781_,
    );
    leanh::lean_dec(v_a_4781_);
    leanh::lean_dec_ref(v_a_4780_);
    leanh::lean_dec(v_a_4779_);
    leanh::lean_dec_ref(v_a_4778_);
    return v_res_4783_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4786_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__0;
    v___x_4786_ = l_Lean_stringToMessageData(v___x_4785_);
    return v___x_4786_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(
    mut v_xs_4787_: *mut leanh::LeanObject,
    mut v_as_4788_: *mut leanh::LeanObject,
    mut v_sz_4789_: usize,
    mut v_i_4790_: usize,
    mut v_b_4791_: *mut leanh::LeanObject,
    mut v___y_4792_: *mut leanh::LeanObject,
    mut v___y_4793_: *mut leanh::LeanObject,
    mut v___y_4794_: *mut leanh::LeanObject,
    mut v___y_4795_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4797_: u8 = 0;
    let mut v___x_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4804_: u8 = 0;
    let mut v_fst_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4808_: u8 = 0;
    let mut v_array_4809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4812_: u8 = 0;
    let mut v___x_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4822_: u8 = 0;
    let mut v_array_4823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4831_: u8 = 0;
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4841_: u8 = 0;
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: usize = 0;
    let mut v___x_4859_: usize = 0;
    let mut v_reuseFailAlloc_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4867_: u8 = 0;
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4871_: u8 = 0;
    let mut v_isSharedCheck_4872_: u8 = 0;
    let mut v_unused_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4877_: u8 = 0;
    let mut v_unused_4878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4881_: u8 = 0;
    let mut v_unused_4882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4883_: u8 = 0;
    let mut v_unused_4884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4797_ = lean_usize_dec_lt(v_i_4790_, v_sz_4789_);
                if v___x_4797_ == 0 {
                    leanh::lean_dec_ref(v_xs_4787_);
                    v___x_4798_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4798_, 0, v_b_4791_);
                    return v___x_4798_;
                } else {
                    v_snd_4799_ = leanh::lean_ctor_get(v_b_4791_, 1);
                    leanh::lean_inc(v_snd_4799_);
                    v_snd_4800_ = leanh::lean_ctor_get(v_snd_4799_, 1);
                    leanh::lean_inc(v_snd_4800_);
                    v_fst_4801_ = leanh::lean_ctor_get(v_b_4791_, 0);
                    v_isSharedCheck_4883_ = (!leanh::lean_is_exclusive(v_b_4791_)) as u8;
                    if v_isSharedCheck_4883_ == 0 {
                        v_unused_4884_ = leanh::lean_ctor_get(v_b_4791_, 1);
                        leanh::lean_dec(v_unused_4884_);
                        v___x_4803_ = v_b_4791_;
                        v_isShared_4804_ = v_isSharedCheck_4883_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_4801_);
                        leanh::lean_dec(v_b_4791_);
                        v___x_4803_ = leanh::lean_box(0);
                        v_isShared_4804_ = v_isSharedCheck_4883_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_4805_ = leanh::lean_ctor_get(v_snd_4799_, 0);
                v_isSharedCheck_4881_ = (!leanh::lean_is_exclusive(v_snd_4799_)) as u8;
                if v_isSharedCheck_4881_ == 0 {
                    v_unused_4882_ = leanh::lean_ctor_get(v_snd_4799_, 1);
                    leanh::lean_dec(v_unused_4882_);
                    v___x_4807_ = v_snd_4799_;
                    v_isShared_4808_ = v_isSharedCheck_4881_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_4805_);
                    leanh::lean_dec(v_snd_4799_);
                    v___x_4807_ = leanh::lean_box(0);
                    v_isShared_4808_ = v_isSharedCheck_4881_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_array_4809_ = leanh::lean_ctor_get(v_snd_4800_, 0);
                v_start_4810_ = leanh::lean_ctor_get(v_snd_4800_, 1);
                v_stop_4811_ = leanh::lean_ctor_get(v_snd_4800_, 2);
                v___x_4812_ = lean_nat_dec_lt(v_start_4810_, v_stop_4811_);
                if v___x_4812_ == 0 {
                    leanh::lean_dec_ref(v_xs_4787_);
                    if v_isShared_4808_ == 0 {
                        v___x_4814_ = v___x_4807_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4819_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4819_, 0, v_fst_4805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4819_, 1, v_snd_4800_);
                        v___x_4814_ = v_reuseFailAlloc_4819_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_4811_);
                    leanh::lean_inc(v_start_4810_);
                    leanh::lean_inc_ref(v_array_4809_);
                    v_isSharedCheck_4877_ = (!leanh::lean_is_exclusive(v_snd_4800_)) as u8;
                    if v_isSharedCheck_4877_ == 0 {
                        v_unused_4878_ = leanh::lean_ctor_get(v_snd_4800_, 2);
                        leanh::lean_dec(v_unused_4878_);
                        v_unused_4879_ = leanh::lean_ctor_get(v_snd_4800_, 1);
                        leanh::lean_dec(v_unused_4879_);
                        v_unused_4880_ = leanh::lean_ctor_get(v_snd_4800_, 0);
                        leanh::lean_dec(v_unused_4880_);
                        v___x_4821_ = v_snd_4800_;
                        v_isShared_4822_ = v_isSharedCheck_4877_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_4800_);
                        v___x_4821_ = leanh::lean_box(0);
                        v_isShared_4822_ = v_isSharedCheck_4877_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4804_ == 0 {
                    leanh::lean_ctor_set(v___x_4803_, 1, v___x_4814_);
                    v___x_4816_ = v___x_4803_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4818_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 0, v_fst_4801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4818_, 1, v___x_4814_);
                    v___x_4816_ = v_reuseFailAlloc_4818_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_4817_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4817_, 0, v___x_4816_);
                return v___x_4817_;
            }
            5 => {
                v_array_4823_ = leanh::lean_ctor_get(v_fst_4805_, 0);
                v_start_4824_ = leanh::lean_ctor_get(v_fst_4805_, 1);
                v_stop_4825_ = leanh::lean_ctor_get(v_fst_4805_, 2);
                v___x_4826_ = lean_array_fget(v_array_4809_, v_start_4810_);
                v___x_4827_ = leanh::lean_unsigned_to_nat(1);
                v___x_4828_ = lean_nat_add(v_start_4810_, v___x_4827_);
                leanh::lean_dec(v_start_4810_);
                if v_isShared_4822_ == 0 {
                    leanh::lean_ctor_set(v___x_4821_, 1, v___x_4828_);
                    v___x_4830_ = v___x_4821_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4876_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4876_, 0, v_array_4809_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4876_, 1, v___x_4828_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4876_, 2, v_stop_4811_);
                    v___x_4830_ = v_reuseFailAlloc_4876_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v___x_4831_ = lean_nat_dec_lt(v_start_4824_, v_stop_4825_);
                if v___x_4831_ == 0 {
                    leanh::lean_dec(v___x_4826_);
                    leanh::lean_dec_ref(v_xs_4787_);
                    if v_isShared_4808_ == 0 {
                        leanh::lean_ctor_set(v___x_4807_, 1, v___x_4830_);
                        v___x_4833_ = v___x_4807_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4838_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 0, v_fst_4805_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4838_, 1, v___x_4830_);
                        v___x_4833_ = v_reuseFailAlloc_4838_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_4825_);
                    leanh::lean_inc(v_start_4824_);
                    leanh::lean_inc_ref(v_array_4823_);
                    v_isSharedCheck_4872_ = (!leanh::lean_is_exclusive(v_fst_4805_)) as u8;
                    if v_isSharedCheck_4872_ == 0 {
                        v_unused_4873_ = leanh::lean_ctor_get(v_fst_4805_, 2);
                        leanh::lean_dec(v_unused_4873_);
                        v_unused_4874_ = leanh::lean_ctor_get(v_fst_4805_, 1);
                        leanh::lean_dec(v_unused_4874_);
                        v_unused_4875_ = leanh::lean_ctor_get(v_fst_4805_, 0);
                        leanh::lean_dec(v_unused_4875_);
                        v___x_4840_ = v_fst_4805_;
                        v_isShared_4841_ = v_isSharedCheck_4872_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_4805_);
                        v___x_4840_ = leanh::lean_box(0);
                        v_isShared_4841_ = v_isSharedCheck_4872_;
                        state = 9;
                        continue;
                    }
                }
            }
            7 => {
                if v_isShared_4804_ == 0 {
                    leanh::lean_ctor_set(v___x_4803_, 1, v___x_4833_);
                    v___x_4835_ = v___x_4803_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4837_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 0, v_fst_4801_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4837_, 1, v___x_4833_);
                    v___x_4835_ = v_reuseFailAlloc_4837_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4836_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_4836_, 0, v___x_4835_);
                return v___x_4836_;
            }
            9 => {
                v___x_4842_ = lean_array_fget_borrowed(v_array_4823_, v_start_4824_);
                leanh::lean_inc(v___x_4842_);
                leanh::lean_inc_ref(v_xs_4787_);
                v___x_4843_ = l_Lean_Elab_Structural_prettyRecArg(
                    v_xs_4787_,
                    v___x_4842_,
                    v___x_4826_,
                    v___y_4792_,
                    v___y_4793_,
                    v___y_4794_,
                    v___y_4795_,
                );
                if leanh::lean_obj_tag(v___x_4843_) == 0 {
                    v_a_4844_ = leanh::lean_ctor_get(v___x_4843_, 0);
                    leanh::lean_inc(v_a_4844_);
                    leanh::lean_dec_ref_known(v___x_4843_, 1);
                    v_a_4845_ = lean_array_uget_borrowed(v_as_4788_, v_i_4790_);
                    v___x_4846_ = lean_nat_add(v_start_4824_, v___x_4827_);
                    leanh::lean_dec(v_start_4824_);
                    if v_isShared_4841_ == 0 {
                        leanh::lean_ctor_set(v___x_4840_, 1, v___x_4846_);
                        v___x_4848_ = v___x_4840_;
                        state = 10;
                        continue;
                    } else {
                        v_reuseFailAlloc_4863_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4863_, 0, v_array_4823_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4863_, 1, v___x_4846_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4863_, 2, v_stop_4825_);
                        v___x_4848_ = v_reuseFailAlloc_4863_;
                        state = 10;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4840_);
                    leanh::lean_dec_ref(v___x_4830_);
                    leanh::lean_dec(v_stop_4825_);
                    leanh::lean_dec(v_start_4824_);
                    leanh::lean_dec_ref(v_array_4823_);
                    leanh::lean_del_object(v___x_4807_);
                    leanh::lean_del_object(v___x_4803_);
                    leanh::lean_dec(v_fst_4801_);
                    leanh::lean_dec_ref(v_xs_4787_);
                    v_a_4864_ = leanh::lean_ctor_get(v___x_4843_, 0);
                    v_isSharedCheck_4871_ = (!leanh::lean_is_exclusive(v___x_4843_)) as u8;
                    if v_isSharedCheck_4871_ == 0 {
                        v___x_4866_ = v___x_4843_;
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 13;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4864_);
                        leanh::lean_dec(v___x_4843_);
                        v___x_4866_ = leanh::lean_box(0);
                        v_isShared_4867_ = v_isSharedCheck_4871_;
                        state = 13;
                        continue;
                    }
                }
            }
            10 => {
                v___x_4849_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
                v___x_4850_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4850_, 0, v_a_4844_);
                leanh::lean_ctor_set(v___x_4850_, 1, v___x_4849_);
                leanh::lean_inc(v_a_4845_);
                v___x_4851_ = l_Lean_MessageData_ofName(v_a_4845_);
                v___x_4852_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4852_, 0, v___x_4850_);
                leanh::lean_ctor_set(v___x_4852_, 1, v___x_4851_);
                v___x_4853_ = lean_array_push(v_fst_4801_, v___x_4852_);
                if v_isShared_4808_ == 0 {
                    leanh::lean_ctor_set(v___x_4807_, 1, v___x_4830_);
                    leanh::lean_ctor_set(v___x_4807_, 0, v___x_4848_);
                    v___x_4855_ = v___x_4807_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4862_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 0, v___x_4848_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4862_, 1, v___x_4830_);
                    v___x_4855_ = v_reuseFailAlloc_4862_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                if v_isShared_4804_ == 0 {
                    leanh::lean_ctor_set(v___x_4803_, 1, v___x_4855_);
                    leanh::lean_ctor_set(v___x_4803_, 0, v___x_4853_);
                    v___x_4857_ = v___x_4803_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4861_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4853_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 1, v___x_4855_);
                    v___x_4857_ = v_reuseFailAlloc_4861_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_4858_ = 1usize;
                v___x_4859_ = lean_usize_add(v_i_4790_, v___x_4858_);
                v_i_4790_ = v___x_4859_;
                v_b_4791_ = v___x_4857_;
                state = 0;
                continue;
            }
            13 => {
                if v_isShared_4867_ == 0 {
                    v___x_4869_ = v___x_4866_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
                    v___x_4869_ = v_reuseFailAlloc_4870_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4869_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___boxed(
    mut v_xs_4885_: *mut leanh::LeanObject,
    mut v_as_4886_: *mut leanh::LeanObject,
    mut v_sz_4887_: *mut leanh::LeanObject,
    mut v_i_4888_: *mut leanh::LeanObject,
    mut v_b_4889_: *mut leanh::LeanObject,
    mut v___y_4890_: *mut leanh::LeanObject,
    mut v___y_4891_: *mut leanh::LeanObject,
    mut v___y_4892_: *mut leanh::LeanObject,
    mut v___y_4893_: *mut leanh::LeanObject,
    mut v___y_4894_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_4895_: usize = 0;
    let mut v_i_boxed_4896_: usize = 0;
    let mut v_res_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4895_ = leanh::lean_unbox_usize(v_sz_4887_);
    leanh::lean_dec(v_sz_4887_);
    v_i_boxed_4896_ = leanh::lean_unbox_usize(v_i_4888_);
    leanh::lean_dec(v_i_4888_);
    v_res_4897_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_4885_, v_as_4886_, v_sz_boxed_4895_, v_i_boxed_4896_, v_b_4889_, v___y_4890_, v___y_4891_, v___y_4892_, v___y_4893_);
    leanh::lean_dec(v___y_4893_);
    leanh::lean_dec_ref(v___y_4892_);
    leanh::lean_dec(v___y_4891_);
    leanh::lean_dec_ref(v___y_4890_);
    leanh::lean_dec_ref(v_as_4886_);
    return v_res_4897_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4901_ = l_Lean_Elab_Structural_prettyParameterSet___closed__1;
    v___x_4902_ = l_Lean_stringToMessageData(v___x_4901_);
    return v___x_4902_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_4904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4904_ = l_Lean_Elab_Structural_prettyParameterSet___closed__3;
    v___x_4905_ = l_Lean_stringToMessageData(v___x_4904_);
    return v___x_4905_;
}
pub unsafe fn l_Lean_Elab_Structural_prettyParameterSet(
    mut v_fnNames_4906_: *mut leanh::LeanObject,
    mut v_xs_4907_: *mut leanh::LeanObject,
    mut v_values_4908_: *mut leanh::LeanObject,
    mut v_recArgInfos_4909_: *mut leanh::LeanObject,
    mut v_a_4910_: *mut leanh::LeanObject,
    mut v_a_4911_: *mut leanh::LeanObject,
    mut v_a_4912_: *mut leanh::LeanObject,
    mut v_a_4913_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4917_: u8 = 0;
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4926_: usize = 0;
    let mut v___x_4927_: usize = 0;
    let mut v___x_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4932_: u8 = 0;
    let mut v_fst_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4936_: u8 = 0;
    let mut v___x_4937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4946_: u8 = 0;
    let mut v_unused_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4948_: u8 = 0;
    let mut v_a_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4952_: u8 = 0;
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4956_: u8 = 0;
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4966_: u8 = 0;
    let mut v___x_4967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4972_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4915_ = lean_array_get_size(v_fnNames_4906_);
                v___x_4916_ = leanh::lean_unsigned_to_nat(1);
                v___x_4917_ = lean_nat_dec_eq(v___x_4915_, v___x_4916_);
                if v___x_4917_ == 0 {
                    v___x_4918_ = leanh::lean_unsigned_to_nat(0);
                    v_l_4919_ = l_Lean_Elab_Structural_prettyParameterSet___closed__0;
                    v___x_4920_ = lean_array_get_size(v_values_4908_);
                    v___x_4921_ =
                        l_Array_toSubarray___redArg(v_values_4908_, v___x_4918_, v___x_4920_);
                    v___x_4922_ = lean_array_get_size(v_recArgInfos_4909_);
                    v___x_4923_ =
                        l_Array_toSubarray___redArg(v_recArgInfos_4909_, v___x_4918_, v___x_4922_);
                    v___x_4924_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4924_, 0, v___x_4921_);
                    leanh::lean_ctor_set(v___x_4924_, 1, v___x_4923_);
                    v___x_4925_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4925_, 0, v_l_4919_);
                    leanh::lean_ctor_set(v___x_4925_, 1, v___x_4924_);
                    v_sz_4926_ = lean_array_size(v_fnNames_4906_);
                    v___x_4927_ = 0usize;
                    v___x_4928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0(v_xs_4907_, v_fnNames_4906_, v_sz_4926_, v___x_4927_, v___x_4925_, v_a_4910_, v_a_4911_, v_a_4912_, v_a_4913_);
                    if leanh::lean_obj_tag(v___x_4928_) == 0 {
                        v_a_4929_ = leanh::lean_ctor_get(v___x_4928_, 0);
                        v_isSharedCheck_4948_ =
                            (!leanh::lean_is_exclusive(v___x_4928_)) as u8;
                        if v_isSharedCheck_4948_ == 0 {
                            v___x_4931_ = v___x_4928_;
                            v_isShared_4932_ = v_isSharedCheck_4948_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4929_);
                            leanh::lean_dec(v___x_4928_);
                            v___x_4931_ = leanh::lean_box(0);
                            v_isShared_4932_ = v_isSharedCheck_4948_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4949_ = leanh::lean_ctor_get(v___x_4928_, 0);
                        v_isSharedCheck_4956_ =
                            (!leanh::lean_is_exclusive(v___x_4928_)) as u8;
                        if v_isSharedCheck_4956_ == 0 {
                            v___x_4951_ = v___x_4928_;
                            v_isShared_4952_ = v_isSharedCheck_4956_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4949_);
                            leanh::lean_dec(v___x_4928_);
                            v___x_4951_ = leanh::lean_box(0);
                            v_isShared_4952_ = v_isSharedCheck_4956_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v___x_4957_ = l_Lean_instInhabitedExpr;
                    v___x_4958_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4959_ = lean_array_get(v___x_4957_, v_values_4908_, v___x_4958_);
                    leanh::lean_dec_ref(v_values_4908_);
                    v___x_4960_ = l_Lean_Elab_Structural_instInhabitedRecArgInfo_default;
                    v___x_4961_ = lean_array_get(v___x_4960_, v_recArgInfos_4909_, v___x_4958_);
                    leanh::lean_dec_ref(v_recArgInfos_4909_);
                    v___x_4962_ = l_Lean_Elab_Structural_prettyRecArg(
                        v_xs_4907_,
                        v___x_4959_,
                        v___x_4961_,
                        v_a_4910_,
                        v_a_4911_,
                        v_a_4912_,
                        v_a_4913_,
                    );
                    if leanh::lean_obj_tag(v___x_4962_) == 0 {
                        v_a_4963_ = leanh::lean_ctor_get(v___x_4962_, 0);
                        v_isSharedCheck_4972_ =
                            (!leanh::lean_is_exclusive(v___x_4962_)) as u8;
                        if v_isSharedCheck_4972_ == 0 {
                            v___x_4965_ = v___x_4962_;
                            v_isShared_4966_ = v_isSharedCheck_4972_;
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4963_);
                            leanh::lean_dec(v___x_4962_);
                            v___x_4965_ = leanh::lean_box(0);
                            v_isShared_4966_ = v_isSharedCheck_4972_;
                            state = 7;
                            continue;
                        }
                    } else {
                        return v___x_4962_;
                    }
                }
            }
            1 => {
                v_fst_4933_ = leanh::lean_ctor_get(v_a_4929_, 0);
                v_isSharedCheck_4946_ = (!leanh::lean_is_exclusive(v_a_4929_)) as u8;
                if v_isSharedCheck_4946_ == 0 {
                    v_unused_4947_ = leanh::lean_ctor_get(v_a_4929_, 1);
                    leanh::lean_dec(v_unused_4947_);
                    v___x_4935_ = v_a_4929_;
                    v_isShared_4936_ = v_isSharedCheck_4946_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_4933_);
                    leanh::lean_dec(v_a_4929_);
                    v___x_4935_ = leanh::lean_box(0);
                    v_isShared_4936_ = v_isSharedCheck_4946_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4937_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_prettyParameterSet___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_prettyParameterSet___closed__2_once
                    ),
                    _init_l_Lean_Elab_Structural_prettyParameterSet___closed__2,
                );
                v___x_4938_ = lean_array_to_list(v_fst_4933_);
                v___x_4939_ = l_Lean_MessageData_andList(v___x_4938_);
                if v_isShared_4936_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4935_, 7);
                    leanh::lean_ctor_set(v___x_4935_, 1, v___x_4939_);
                    leanh::lean_ctor_set(v___x_4935_, 0, v___x_4937_);
                    v___x_4941_ = v___x_4935_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4945_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 0, v___x_4937_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4945_, 1, v___x_4939_);
                    v___x_4941_ = v_reuseFailAlloc_4945_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_4932_ == 0 {
                    leanh::lean_ctor_set(v___x_4931_, 0, v___x_4941_);
                    v___x_4943_ = v___x_4931_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4944_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4944_, 0, v___x_4941_);
                    v___x_4943_ = v_reuseFailAlloc_4944_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4943_;
            }
            5 => {
                if v_isShared_4952_ == 0 {
                    v___x_4954_ = v___x_4951_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4955_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4955_, 0, v_a_4949_);
                    v___x_4954_ = v_reuseFailAlloc_4955_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4954_;
            }
            7 => {
                v___x_4967_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_prettyParameterSet___closed__4),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_prettyParameterSet___closed__4_once
                    ),
                    _init_l_Lean_Elab_Structural_prettyParameterSet___closed__4,
                );
                v___x_4968_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4968_, 0, v___x_4967_);
                leanh::lean_ctor_set(v___x_4968_, 1, v_a_4963_);
                if v_isShared_4966_ == 0 {
                    leanh::lean_ctor_set(v___x_4965_, 0, v___x_4968_);
                    v___x_4970_ = v___x_4965_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4971_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4971_, 0, v___x_4968_);
                    v___x_4970_ = v_reuseFailAlloc_4971_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4970_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_prettyParameterSet___boxed(
    mut v_fnNames_4973_: *mut leanh::LeanObject,
    mut v_xs_4974_: *mut leanh::LeanObject,
    mut v_values_4975_: *mut leanh::LeanObject,
    mut v_recArgInfos_4976_: *mut leanh::LeanObject,
    mut v_a_4977_: *mut leanh::LeanObject,
    mut v_a_4978_: *mut leanh::LeanObject,
    mut v_a_4979_: *mut leanh::LeanObject,
    mut v_a_4980_: *mut leanh::LeanObject,
    mut v_a_4981_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4982_ = l_Lean_Elab_Structural_prettyParameterSet(
        v_fnNames_4973_,
        v_xs_4974_,
        v_values_4975_,
        v_recArgInfos_4976_,
        v_a_4977_,
        v_a_4978_,
        v_a_4979_,
        v_a_4980_,
    );
    leanh::lean_dec(v_a_4980_);
    leanh::lean_dec_ref(v_a_4979_);
    leanh::lean_dec(v_a_4978_);
    leanh::lean_dec_ref(v_a_4977_);
    leanh::lean_dec_ref(v_fnNames_4973_);
    return v_res_4982_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(
    mut v_xs_4983_: *mut leanh::LeanObject,
    mut v_v_4984_: *mut leanh::LeanObject,
    mut v_i_4985_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4987_: u8 = 0;
    let mut v___x_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4990_: u8 = 0;
    let mut v___x_4991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4986_ = lean_array_get_size(v_xs_4983_);
                v___x_4987_ = lean_nat_dec_lt(v_i_4985_, v___x_4986_);
                if v___x_4987_ == 0 {
                    leanh::lean_dec(v_i_4985_);
                    v___x_4988_ = leanh::lean_box(0);
                    return v___x_4988_;
                } else {
                    v___x_4989_ = lean_array_fget_borrowed(v_xs_4983_, v_i_4985_);
                    v___x_4990_ = lean_expr_eqv(v___x_4989_, v_v_4984_);
                    if v___x_4990_ == 0 {
                        v___x_4991_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4992_ = lean_nat_add(v_i_4985_, v___x_4991_);
                        leanh::lean_dec(v_i_4985_);
                        v_i_4985_ = v___x_4992_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4994_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4994_, 0, v_i_4985_);
                        return v___x_4994_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1___boxed(
    mut v_xs_4995_: *mut leanh::LeanObject,
    mut v_v_4996_: *mut leanh::LeanObject,
    mut v_i_4997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4998_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_4995_, v_v_4996_, v_i_4997_);
    leanh::lean_dec_ref(v_v_4996_);
    leanh::lean_dec_ref(v_xs_4995_);
    return v_res_4998_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(
    mut v_xs_4999_: *mut leanh::LeanObject,
    mut v_v_5000_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5002_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5001_ = leanh::lean_unsigned_to_nat(0);
    v___x_5002_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0_spec__1(v_xs_4999_, v_v_5000_, v___x_5001_);
    return v___x_5002_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0___boxed(
    mut v_xs_5003_: *mut leanh::LeanObject,
    mut v_v_5004_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5005_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_5003_, v_v_5004_);
    leanh::lean_dec_ref(v_v_5004_);
    leanh::lean_dec_ref(v_xs_5003_);
    return v_res_5005_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(
    mut v_xs_5006_: *mut leanh::LeanObject,
    mut v_v_5007_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5013_: u8 = 0;
    let mut v___x_5015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5017_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5008_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0_spec__0(v_xs_5006_, v_v_5007_);
                if leanh::lean_obj_tag(v___x_5008_) == 0 {
                    v___x_5009_ = leanh::lean_box(0);
                    return v___x_5009_;
                } else {
                    v_val_5010_ = leanh::lean_ctor_get(v___x_5008_, 0);
                    v_isSharedCheck_5017_ = (!leanh::lean_is_exclusive(v___x_5008_)) as u8;
                    if v_isSharedCheck_5017_ == 0 {
                        v___x_5012_ = v___x_5008_;
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5010_);
                        leanh::lean_dec(v___x_5008_);
                        v___x_5012_ = leanh::lean_box(0);
                        v_isShared_5013_ = v_isSharedCheck_5017_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5013_ == 0 {
                    v___x_5015_ = v___x_5012_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5016_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5016_, 0, v_val_5010_);
                    v___x_5015_ = v_reuseFailAlloc_5016_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5015_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0___boxed(
    mut v_xs_5018_: *mut leanh::LeanObject,
    mut v_v_5019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5020_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_5018_, v_v_5019_);
    leanh::lean_dec_ref(v_v_5019_);
    leanh::lean_dec_ref(v_xs_5018_);
    return v_res_5020_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(
    mut v_xs_5021_: *mut leanh::LeanObject,
    mut v_as_5022_: *mut leanh::LeanObject,
    mut v_sz_5023_: usize,
    mut v_i_5024_: usize,
    mut v_b_5025_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: usize = 0;
    let mut v___x_5029_: usize = 0;
    let mut v___x_5031_: u8 = 0;
    let mut v_a_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5031_ = lean_usize_dec_lt(v_i_5024_, v_sz_5023_);
                if v___x_5031_ == 0 {
                    return v_b_5025_;
                } else {
                    v_a_5032_ = lean_array_uget_borrowed(v_as_5022_, v_i_5024_);
                    v___x_5033_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_5021_, v_a_5032_);
                    if leanh::lean_obj_tag(v___x_5033_) == 1 {
                        v_val_5034_ = leanh::lean_ctor_get(v___x_5033_, 0);
                        leanh::lean_inc(v_val_5034_);
                        leanh::lean_dec_ref_known(v___x_5033_, 1);
                        v___x_5035_ = lean_nat_dec_lt(v_val_5034_, v_b_5025_);
                        if v___x_5035_ == 0 {
                            leanh::lean_dec(v_val_5034_);
                            v_a_5027_ = v_b_5025_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_b_5025_);
                            v_a_5027_ = v_val_5034_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_5033_);
                        v_a_5027_ = v_b_5025_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5028_ = 1usize;
                v___x_5029_ = lean_usize_add(v_i_5024_, v___x_5028_);
                v_i_5024_ = v___x_5029_;
                v_b_5025_ = v_a_5027_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1___boxed(
    mut v_xs_5036_: *mut leanh::LeanObject,
    mut v_as_5037_: *mut leanh::LeanObject,
    mut v_sz_5038_: *mut leanh::LeanObject,
    mut v_i_5039_: *mut leanh::LeanObject,
    mut v_b_5040_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5041_: usize = 0;
    let mut v_i_boxed_5042_: usize = 0;
    let mut v_res_5043_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5041_ = leanh::lean_unbox_usize(v_sz_5038_);
    leanh::lean_dec(v_sz_5038_);
    v_i_boxed_5042_ = leanh::lean_unbox_usize(v_i_5039_);
    leanh::lean_dec(v_i_5039_);
    v_res_5043_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_5036_, v_as_5037_, v_sz_boxed_5041_, v_i_boxed_5042_, v_b_5040_);
    leanh::lean_dec_ref(v_as_5037_);
    leanh::lean_dec_ref(v_xs_5036_);
    return v_res_5043_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(
    mut v_xs_5044_: *mut leanh::LeanObject,
    mut v_indices_5045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_minPos_5046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5047_: usize = 0;
    let mut v___x_5048_: usize = 0;
    let mut v___x_5049_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_minPos_5046_ = lean_array_get_size(v_xs_5044_);
    v_sz_5047_ = lean_array_size(v_indices_5045_);
    v___x_5048_ = 0usize;
    v___x_5049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__1(v_xs_5044_, v_indices_5045_, v_sz_5047_, v___x_5048_, v_minPos_5046_);
    return v___x_5049_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos___boxed(
    mut v_xs_5050_: *mut leanh::LeanObject,
    mut v_indices_5051_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5052_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos(v_xs_5050_, v_indices_5051_);
    leanh::lean_dec_ref(v_indices_5051_);
    leanh::lean_dec_ref(v_xs_5050_);
    return v_res_5052_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(
    mut v_x_5053_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5054_: u8 = 0;
    v___x_5054_ = 0;
    return v___x_5054_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0___boxed(
    mut v_x_5055_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5056_: u8 = 0;
    let mut v_r_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5056_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__0(v_x_5055_);
    leanh::lean_dec(v_x_5055_);
    v_r_5057_ = leanh::lean_box((v_res_5056_) as usize);
    return v_r_5057_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(
    mut v_fvarId_5058_: *mut leanh::LeanObject,
    mut v_x_5059_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5060_: u8 = 0;
    v___x_5060_ = l_Lean_instBEqFVarId_beq(v_fvarId_5058_, v_x_5059_);
    return v___x_5060_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed(
    mut v_fvarId_5061_: *mut leanh::LeanObject,
    mut v_x_5062_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5063_: u8 = 0;
    let mut v_r_5064_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5063_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1(v_fvarId_5061_, v_x_5062_);
    leanh::lean_dec(v_x_5062_);
    leanh::lean_dec(v_fvarId_5061_);
    v_r_5064_ = leanh::lean_box((v_res_5063_) as usize);
    return v_r_5064_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5066_ = leanh::lean_box(0);
    v___x_5067_ = leanh::lean_unsigned_to_nat(16);
    v___x_5068_ = lean_mk_array(v___x_5067_, v___x_5066_);
    return v___x_5068_;
}
pub unsafe fn _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5071_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5069_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1_once), _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__1);
    v___x_5070_ = leanh::lean_unsigned_to_nat(0);
    v___x_5071_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5071_, 0, v___x_5070_);
    leanh::lean_ctor_set(v___x_5071_, 1, v___x_5069_);
    return v___x_5071_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(
    mut v_e_5072_: *mut leanh::LeanObject,
    mut v_fvarId_5073_: *mut leanh::LeanObject,
    mut v___y_5074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5078_: u8 = 0;
    let mut v_mctx_5079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_5081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_5083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5087_: u8 = 0;
    let mut v___x_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5094_: u8 = 0;
    let mut v_unused_5095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5101_: u8 = 0;
    let mut v_mctx_5102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5107_: u8 = 0;
    let mut v___x_5108_: u8 = 0;
    let mut v___x_5109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5076_ = lean_st_ref_get(v___y_5074_);
                v_mctx_5102_ = leanh::lean_ctor_get(v___x_5076_, 0);
                leanh::lean_inc_ref_n(v_mctx_5102_, 2);
                leanh::lean_dec(v___x_5076_);
                v___f_5103_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__0;
                v___f_5104_ = leanh::lean_alloc_closure(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___lam__1___boxed as *mut core::ffi::c_void, 2, 1);
                leanh::lean_closure_set(v___f_5104_, 0, v_fvarId_5073_);
                v___x_5105_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2_once), _init_l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___closed__2);
                v___x_5106_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5106_, 0, v___x_5105_);
                leanh::lean_ctor_set(v___x_5106_, 1, v_mctx_5102_);
                v___x_5107_ = l_Lean_Expr_hasFVar(v_e_5072_);
                if v___x_5107_ == 0 {
                    v___x_5108_ = l_Lean_Expr_hasMVar(v_e_5072_);
                    if v___x_5108_ == 0 {
                        leanh::lean_dec_ref_known(v___x_5106_, 2);
                        leanh::lean_dec_ref(v___f_5104_);
                        leanh::lean_dec_ref(v_e_5072_);
                        v_fst_5078_ = v___x_5108_;
                        v_mctx_5079_ = v_mctx_5102_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_mctx_5102_);
                        v___x_5109_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                            v___f_5104_,
                            v___f_5103_,
                            v_e_5072_,
                            v___x_5106_,
                        );
                        v___y_5097_ = v___x_5109_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_mctx_5102_);
                    v___x_5110_ = l___private_Lean_MetavarContext_0__Lean_DependsOn_dep_visit(
                        v___f_5104_,
                        v___f_5103_,
                        v_e_5072_,
                        v___x_5106_,
                    );
                    v___y_5097_ = v___x_5110_;
                    state = 4;
                    continue;
                }
            }
            1 => {
                v___x_5080_ = lean_st_ref_take(v___y_5074_);
                v_cache_5081_ = leanh::lean_ctor_get(v___x_5080_, 1);
                v_zetaDeltaFVarIds_5082_ = leanh::lean_ctor_get(v___x_5080_, 2);
                v_postponed_5083_ = leanh::lean_ctor_get(v___x_5080_, 3);
                v_diag_5084_ = leanh::lean_ctor_get(v___x_5080_, 4);
                v_isSharedCheck_5094_ = (!leanh::lean_is_exclusive(v___x_5080_)) as u8;
                if v_isSharedCheck_5094_ == 0 {
                    v_unused_5095_ = leanh::lean_ctor_get(v___x_5080_, 0);
                    leanh::lean_dec(v_unused_5095_);
                    v___x_5086_ = v___x_5080_;
                    v_isShared_5087_ = v_isSharedCheck_5094_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_diag_5084_);
                    leanh::lean_inc(v_postponed_5083_);
                    leanh::lean_inc(v_zetaDeltaFVarIds_5082_);
                    leanh::lean_inc(v_cache_5081_);
                    leanh::lean_dec(v___x_5080_);
                    v___x_5086_ = leanh::lean_box(0);
                    v_isShared_5087_ = v_isSharedCheck_5094_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if v_isShared_5087_ == 0 {
                    leanh::lean_ctor_set(v___x_5086_, 0, v_mctx_5079_);
                    v___x_5089_ = v___x_5086_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5093_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 0, v_mctx_5079_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 1, v_cache_5081_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_5093_,
                        2,
                        v_zetaDeltaFVarIds_5082_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 3, v_postponed_5083_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5093_, 4, v_diag_5084_);
                    v___x_5089_ = v_reuseFailAlloc_5093_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5090_ = lean_st_ref_set(v___y_5074_, v___x_5089_);
                v___x_5091_ = leanh::lean_box((v_fst_5078_) as usize);
                v___x_5092_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5092_, 0, v___x_5091_);
                return v___x_5092_;
            }
            4 => {
                v_snd_5098_ = leanh::lean_ctor_get(v___y_5097_, 1);
                leanh::lean_inc(v_snd_5098_);
                v_fst_5099_ = leanh::lean_ctor_get(v___y_5097_, 0);
                leanh::lean_inc(v_fst_5099_);
                leanh::lean_dec_ref(v___y_5097_);
                v_mctx_5100_ = leanh::lean_ctor_get(v_snd_5098_, 1);
                leanh::lean_inc_ref(v_mctx_5100_);
                leanh::lean_dec(v_snd_5098_);
                v___x_5101_ = (leanh::lean_unbox(v_fst_5099_) as u8);
                leanh::lean_dec(v_fst_5099_);
                v_fst_5078_ = v___x_5101_;
                v_mctx_5079_ = v_mctx_5100_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg___boxed(
    mut v_e_5111_: *mut leanh::LeanObject,
    mut v_fvarId_5112_: *mut leanh::LeanObject,
    mut v___y_5113_: *mut leanh::LeanObject,
    mut v___y_5114_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5115_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5115_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_5111_, v_fvarId_5112_, v___y_5113_);
    leanh::lean_dec(v___y_5113_);
    return v_res_5115_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(
    mut v_e_5116_: *mut leanh::LeanObject,
    mut v_fvarId_5117_: *mut leanh::LeanObject,
    mut v___y_5118_: *mut leanh::LeanObject,
    mut v___y_5119_: *mut leanh::LeanObject,
    mut v___y_5120_: *mut leanh::LeanObject,
    mut v___y_5121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5123_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_e_5116_, v_fvarId_5117_, v___y_5119_);
    return v___x_5123_;
}
pub unsafe fn l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___boxed(
    mut v_e_5124_: *mut leanh::LeanObject,
    mut v_fvarId_5125_: *mut leanh::LeanObject,
    mut v___y_5126_: *mut leanh::LeanObject,
    mut v___y_5127_: *mut leanh::LeanObject,
    mut v___y_5128_: *mut leanh::LeanObject,
    mut v___y_5129_: *mut leanh::LeanObject,
    mut v___y_5130_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5131_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0(v_e_5124_, v_fvarId_5125_, v___y_5126_, v___y_5127_, v___y_5128_, v___y_5129_);
    leanh::lean_dec(v___y_5129_);
    leanh::lean_dec_ref(v___y_5128_);
    leanh::lean_dec(v___y_5127_);
    leanh::lean_dec_ref(v___y_5126_);
    return v_res_5131_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(
    mut v_a_5132_: *mut leanh::LeanObject,
    mut v_as_5133_: *mut leanh::LeanObject,
    mut v_i_5134_: usize,
    mut v_stop_5135_: usize,
) -> u8 {
    let mut v___x_5136_: u8 = 0;
    let mut v___x_5137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5138_: u8 = 0;
    let mut v___x_5139_: usize = 0;
    let mut v___x_5140_: usize = 0;
    let mut v___x_5142_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5136_ = lean_usize_dec_eq(v_i_5134_, v_stop_5135_);
                if v___x_5136_ == 0 {
                    v___x_5137_ = lean_array_uget_borrowed(v_as_5133_, v_i_5134_);
                    v___x_5138_ = lean_expr_eqv(v_a_5132_, v___x_5137_);
                    if v___x_5138_ == 0 {
                        v___x_5139_ = 1usize;
                        v___x_5140_ = lean_usize_add(v_i_5134_, v___x_5139_);
                        v_i_5134_ = v___x_5140_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5138_;
                    }
                } else {
                    v___x_5142_ = 0;
                    return v___x_5142_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1___boxed(
    mut v_a_5143_: *mut leanh::LeanObject,
    mut v_as_5144_: *mut leanh::LeanObject,
    mut v_i_5145_: *mut leanh::LeanObject,
    mut v_stop_5146_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5147_: usize = 0;
    let mut v_stop_boxed_5148_: usize = 0;
    let mut v_res_5149_: u8 = 0;
    let mut v_r_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5147_ = leanh::lean_unbox_usize(v_i_5145_);
    leanh::lean_dec(v_i_5145_);
    v_stop_boxed_5148_ = leanh::lean_unbox_usize(v_stop_5146_);
    leanh::lean_dec(v_stop_5146_);
    v_res_5149_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_5143_, v_as_5144_, v_i_boxed_5147_, v_stop_boxed_5148_);
    leanh::lean_dec_ref(v_as_5144_);
    leanh::lean_dec_ref(v_a_5143_);
    v_r_5150_ = leanh::lean_box((v_res_5149_) as usize);
    return v_r_5150_;
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(
    mut v_as_5151_: *mut leanh::LeanObject,
    mut v_a_5152_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5155_: u8 = 0;
    v___x_5153_ = leanh::lean_unsigned_to_nat(0);
    v___x_5154_ = lean_array_get_size(v_as_5151_);
    v___x_5155_ = lean_nat_dec_lt(v___x_5153_, v___x_5154_);
    if v___x_5155_ == 0 {
        return v___x_5155_;
    } else {
        if v___x_5155_ == 0 {
            return v___x_5155_;
        } else {
            let mut v___x_5156_: usize = 0;
            let mut v___x_5157_: usize = 0;
            let mut v___x_5158_: u8 = 0;
            v___x_5156_ = 0usize;
            v___x_5157_ = lean_usize_of_nat(v___x_5154_);
            v___x_5158_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1_spec__1(v_a_5152_, v_as_5151_, v___x_5156_, v___x_5157_);
            return v___x_5158_;
        }
    }
}
pub unsafe fn l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1___boxed(
    mut v_as_5159_: *mut leanh::LeanObject,
    mut v_a_5160_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5161_: u8 = 0;
    let mut v_r_5162_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5161_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_as_5159_, v_a_5160_);
    leanh::lean_dec_ref(v_a_5160_);
    leanh::lean_dec_ref(v_as_5159_);
    v_r_5162_ = leanh::lean_box((v_res_5161_) as usize);
    return v_r_5162_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(
    mut v_a_5166_: *mut leanh::LeanObject,
    mut v_indices_5167_: *mut leanh::LeanObject,
    mut v_a_5168_: *mut leanh::LeanObject,
    mut v_as_5169_: *mut leanh::LeanObject,
    mut v_sz_5170_: usize,
    mut v_i_5171_: usize,
    mut v_b_5172_: *mut leanh::LeanObject,
    mut v___y_5173_: *mut leanh::LeanObject,
    mut v___y_5174_: *mut leanh::LeanObject,
    mut v___y_5175_: *mut leanh::LeanObject,
    mut v___y_5176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5178_: u8 = 0;
    let mut v___x_5179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5186_: u8 = 0;
    let mut v_a_5188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: usize = 0;
    let mut v___x_5190_: usize = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5194_: u8 = 0;
    let mut v___x_5195_: u8 = 0;
    let mut v___x_5196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5199_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5203_: u8 = 0;
    let mut v_a_5204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5207_: u8 = 0;
    let mut v___x_5209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5211_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5178_ = lean_usize_dec_lt(v_i_5171_, v_sz_5170_);
                if v___x_5178_ == 0 {
                    leanh::lean_dec_ref(v_a_5168_);
                    leanh::lean_dec_ref(v_a_5166_);
                    v___x_5179_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5179_, 0, v_b_5172_);
                    return v___x_5179_;
                } else {
                    leanh::lean_dec_ref(v_b_5172_);
                    v_a_5180_ = lean_array_uget_borrowed(v_as_5169_, v_i_5171_);
                    v___x_5181_ = l_Lean_Expr_fvarId_x21(v_a_5180_);
                    leanh::lean_inc_ref(v_a_5166_);
                    v___x_5182_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_5166_, v___x_5181_, v___y_5174_);
                    if leanh::lean_obj_tag(v___x_5182_) == 0 {
                        v_a_5183_ = leanh::lean_ctor_get(v___x_5182_, 0);
                        v_isSharedCheck_5203_ =
                            (!leanh::lean_is_exclusive(v___x_5182_)) as u8;
                        if v_isSharedCheck_5203_ == 0 {
                            v___x_5185_ = v___x_5182_;
                            v_isShared_5186_ = v_isSharedCheck_5203_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5183_);
                            leanh::lean_dec(v___x_5182_);
                            v___x_5185_ = leanh::lean_box(0);
                            v_isShared_5186_ = v_isSharedCheck_5203_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_5168_);
                        leanh::lean_dec_ref(v_a_5166_);
                        v_a_5204_ = leanh::lean_ctor_get(v___x_5182_, 0);
                        v_isSharedCheck_5211_ =
                            (!leanh::lean_is_exclusive(v___x_5182_)) as u8;
                        if v_isSharedCheck_5211_ == 0 {
                            v___x_5206_ = v___x_5182_;
                            v_isShared_5207_ = v_isSharedCheck_5211_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5204_);
                            leanh::lean_dec(v___x_5182_);
                            v___x_5206_ = leanh::lean_box(0);
                            v_isShared_5207_ = v_isSharedCheck_5211_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5192_ = leanh::lean_box(0);
                v___x_5193_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0;
                v___x_5194_ = l_Array_contains___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__1(v_indices_5167_, v_a_5180_);
                if v___x_5194_ == 0 {
                    v___x_5195_ = (leanh::lean_unbox(v_a_5183_) as u8);
                    leanh::lean_dec(v_a_5183_);
                    if v___x_5195_ == 0 {
                        leanh::lean_del_object(v___x_5185_);
                        v_a_5188_ = v___x_5193_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_a_5166_);
                        leanh::lean_inc(v_a_5180_);
                        v___x_5196_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5196_, 0, v_a_5168_);
                        leanh::lean_ctor_set(v___x_5196_, 1, v_a_5180_);
                        v___x_5197_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5197_, 0, v___x_5196_);
                        v___x_5198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5198_, 0, v___x_5197_);
                        v___x_5199_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_5199_, 0, v___x_5198_);
                        leanh::lean_ctor_set(v___x_5199_, 1, v___x_5192_);
                        if v_isShared_5186_ == 0 {
                            leanh::lean_ctor_set(v___x_5185_, 0, v___x_5199_);
                            v___x_5201_ = v___x_5185_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5202_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5202_, 0, v___x_5199_);
                            v___x_5201_ = v_reuseFailAlloc_5202_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_5185_);
                    leanh::lean_dec(v_a_5183_);
                    v_a_5188_ = v___x_5193_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5189_ = 1usize;
                v___x_5190_ = lean_usize_add(v_i_5171_, v___x_5189_);
                leanh::lean_inc_ref(v_a_5188_);
                v_i_5171_ = v___x_5190_;
                v_b_5172_ = v_a_5188_;
                state = 0;
                continue;
            }
            3 => {
                return v___x_5201_;
            }
            4 => {
                if v_isShared_5207_ == 0 {
                    v___x_5209_ = v___x_5206_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5210_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5210_, 0, v_a_5204_);
                    v___x_5209_ = v_reuseFailAlloc_5210_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5209_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___boxed(
    mut v_a_5212_: *mut leanh::LeanObject,
    mut v_indices_5213_: *mut leanh::LeanObject,
    mut v_a_5214_: *mut leanh::LeanObject,
    mut v_as_5215_: *mut leanh::LeanObject,
    mut v_sz_5216_: *mut leanh::LeanObject,
    mut v_i_5217_: *mut leanh::LeanObject,
    mut v_b_5218_: *mut leanh::LeanObject,
    mut v___y_5219_: *mut leanh::LeanObject,
    mut v___y_5220_: *mut leanh::LeanObject,
    mut v___y_5221_: *mut leanh::LeanObject,
    mut v___y_5222_: *mut leanh::LeanObject,
    mut v___y_5223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5224_: usize = 0;
    let mut v_i_boxed_5225_: usize = 0;
    let mut v_res_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5224_ = leanh::lean_unbox_usize(v_sz_5216_);
    leanh::lean_dec(v_sz_5216_);
    v_i_boxed_5225_ = leanh::lean_unbox_usize(v_i_5217_);
    leanh::lean_dec(v_i_5217_);
    v_res_5226_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_5212_, v_indices_5213_, v_a_5214_, v_as_5215_, v_sz_boxed_5224_, v_i_boxed_5225_, v_b_5218_, v___y_5219_, v___y_5220_, v___y_5221_, v___y_5222_);
    leanh::lean_dec(v___y_5222_);
    leanh::lean_dec_ref(v___y_5221_);
    leanh::lean_dec(v___y_5220_);
    leanh::lean_dec_ref(v___y_5219_);
    leanh::lean_dec_ref(v_as_5215_);
    leanh::lean_dec_ref(v_indices_5213_);
    return v_res_5226_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(
    mut v_ys_5227_: *mut leanh::LeanObject,
    mut v_indices_5228_: *mut leanh::LeanObject,
    mut v_as_5229_: *mut leanh::LeanObject,
    mut v_sz_5230_: usize,
    mut v_i_5231_: usize,
    mut v_b_5232_: *mut leanh::LeanObject,
    mut v___y_5233_: *mut leanh::LeanObject,
    mut v___y_5234_: *mut leanh::LeanObject,
    mut v___y_5235_: *mut leanh::LeanObject,
    mut v___y_5236_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5238_: u8 = 0;
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5245_: usize = 0;
    let mut v___x_5246_: usize = 0;
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5251_: u8 = 0;
    let mut v_fst_5252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5255_: u8 = 0;
    let mut v___x_5256_: usize = 0;
    let mut v___x_5257_: usize = 0;
    let mut v___x_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5265_: u8 = 0;
    let mut v_unused_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5267_: u8 = 0;
    let mut v_a_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5271_: u8 = 0;
    let mut v___x_5273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5238_ = lean_usize_dec_lt(v_i_5231_, v_sz_5230_);
                if v___x_5238_ == 0 {
                    v___x_5239_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5239_, 0, v_b_5232_);
                    return v___x_5239_;
                } else {
                    leanh::lean_dec_ref(v_b_5232_);
                    v_a_5240_ = lean_array_uget_borrowed(v_as_5229_, v_i_5231_);
                    leanh::lean_inc(v___y_5236_);
                    leanh::lean_inc_ref(v___y_5235_);
                    leanh::lean_inc(v___y_5234_);
                    leanh::lean_inc_ref(v___y_5233_);
                    leanh::lean_inc(v_a_5240_);
                    v___x_5241_ = lean_infer_type(
                        v_a_5240_,
                        v___y_5233_,
                        v___y_5234_,
                        v___y_5235_,
                        v___y_5236_,
                    );
                    if leanh::lean_obj_tag(v___x_5241_) == 0 {
                        v_a_5242_ = leanh::lean_ctor_get(v___x_5241_, 0);
                        leanh::lean_inc(v_a_5242_);
                        leanh::lean_dec_ref_known(v___x_5241_, 1);
                        v___x_5243_ = leanh::lean_box(0);
                        v___x_5244_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0;
                        v_sz_5245_ = lean_array_size(v_ys_5227_);
                        v___x_5246_ = 0usize;
                        leanh::lean_inc(v_a_5240_);
                        v___x_5247_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_5242_, v_indices_5228_, v_a_5240_, v_ys_5227_, v_sz_5245_, v___x_5246_, v___x_5244_, v___y_5233_, v___y_5234_, v___y_5235_, v___y_5236_);
                        if leanh::lean_obj_tag(v___x_5247_) == 0 {
                            v_a_5248_ = leanh::lean_ctor_get(v___x_5247_, 0);
                            v_isSharedCheck_5267_ =
                                (!leanh::lean_is_exclusive(v___x_5247_)) as u8;
                            if v_isSharedCheck_5267_ == 0 {
                                v___x_5250_ = v___x_5247_;
                                v_isShared_5251_ = v_isSharedCheck_5267_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5248_);
                                leanh::lean_dec(v___x_5247_);
                                v___x_5250_ = leanh::lean_box(0);
                                v_isShared_5251_ = v_isSharedCheck_5267_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_5247_;
                        }
                    } else {
                        v_a_5268_ = leanh::lean_ctor_get(v___x_5241_, 0);
                        v_isSharedCheck_5275_ =
                            (!leanh::lean_is_exclusive(v___x_5241_)) as u8;
                        if v_isSharedCheck_5275_ == 0 {
                            v___x_5270_ = v___x_5241_;
                            v_isShared_5271_ = v_isSharedCheck_5275_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5268_);
                            leanh::lean_dec(v___x_5241_);
                            v___x_5270_ = leanh::lean_box(0);
                            v_isShared_5271_ = v_isSharedCheck_5275_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5252_ = leanh::lean_ctor_get(v_a_5248_, 0);
                v_isSharedCheck_5265_ = (!leanh::lean_is_exclusive(v_a_5248_)) as u8;
                if v_isSharedCheck_5265_ == 0 {
                    v_unused_5266_ = leanh::lean_ctor_get(v_a_5248_, 1);
                    leanh::lean_dec(v_unused_5266_);
                    v___x_5254_ = v_a_5248_;
                    v_isShared_5255_ = v_isSharedCheck_5265_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5252_);
                    leanh::lean_dec(v_a_5248_);
                    v___x_5254_ = leanh::lean_box(0);
                    v_isShared_5255_ = v_isSharedCheck_5265_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_5252_) == 0 {
                    leanh::lean_del_object(v___x_5254_);
                    leanh::lean_del_object(v___x_5250_);
                    v___x_5256_ = 1usize;
                    v___x_5257_ = lean_usize_add(v_i_5231_, v___x_5256_);
                    v_i_5231_ = v___x_5257_;
                    v_b_5232_ = v___x_5244_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5255_ == 0 {
                        leanh::lean_ctor_set(v___x_5254_, 1, v___x_5243_);
                        v___x_5260_ = v___x_5254_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5264_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5264_, 0, v_fst_5252_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5264_, 1, v___x_5243_);
                        v___x_5260_ = v_reuseFailAlloc_5264_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5251_ == 0 {
                    leanh::lean_ctor_set(v___x_5250_, 0, v___x_5260_);
                    v___x_5262_ = v___x_5250_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5263_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5263_, 0, v___x_5260_);
                    v___x_5262_ = v_reuseFailAlloc_5263_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5262_;
            }
            5 => {
                if v_isShared_5271_ == 0 {
                    v___x_5273_ = v___x_5270_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5274_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5274_, 0, v_a_5268_);
                    v___x_5273_ = v_reuseFailAlloc_5274_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4___boxed(
    mut v_ys_5276_: *mut leanh::LeanObject,
    mut v_indices_5277_: *mut leanh::LeanObject,
    mut v_as_5278_: *mut leanh::LeanObject,
    mut v_sz_5279_: *mut leanh::LeanObject,
    mut v_i_5280_: *mut leanh::LeanObject,
    mut v_b_5281_: *mut leanh::LeanObject,
    mut v___y_5282_: *mut leanh::LeanObject,
    mut v___y_5283_: *mut leanh::LeanObject,
    mut v___y_5284_: *mut leanh::LeanObject,
    mut v___y_5285_: *mut leanh::LeanObject,
    mut v___y_5286_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5287_: usize = 0;
    let mut v_i_boxed_5288_: usize = 0;
    let mut v_res_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5287_ = leanh::lean_unbox_usize(v_sz_5279_);
    leanh::lean_dec(v_sz_5279_);
    v_i_boxed_5288_ = leanh::lean_unbox_usize(v_i_5280_);
    leanh::lean_dec(v_i_5280_);
    v_res_5289_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_5276_, v_indices_5277_, v_as_5278_, v_sz_boxed_5287_, v_i_boxed_5288_, v_b_5281_, v___y_5282_, v___y_5283_, v___y_5284_, v___y_5285_);
    leanh::lean_dec(v___y_5285_);
    leanh::lean_dec_ref(v___y_5284_);
    leanh::lean_dec(v___y_5283_);
    leanh::lean_dec_ref(v___y_5282_);
    leanh::lean_dec_ref(v_as_5278_);
    leanh::lean_dec_ref(v_indices_5277_);
    leanh::lean_dec_ref(v_ys_5276_);
    return v_res_5289_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(
    mut v_indices_5290_: *mut leanh::LeanObject,
    mut v_ys_5291_: *mut leanh::LeanObject,
    mut v_as_5292_: *mut leanh::LeanObject,
    mut v_sz_5293_: usize,
    mut v_i_5294_: usize,
    mut v_b_5295_: *mut leanh::LeanObject,
    mut v___y_5296_: *mut leanh::LeanObject,
    mut v___y_5297_: *mut leanh::LeanObject,
    mut v___y_5298_: *mut leanh::LeanObject,
    mut v___y_5299_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5301_: u8 = 0;
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5304_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5308_: usize = 0;
    let mut v___x_5309_: usize = 0;
    let mut v___x_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5314_: u8 = 0;
    let mut v_fst_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5318_: u8 = 0;
    let mut v___x_5319_: usize = 0;
    let mut v___x_5320_: usize = 0;
    let mut v___x_5321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5328_: u8 = 0;
    let mut v_unused_5329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5330_: u8 = 0;
    let mut v_a_5331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5334_: u8 = 0;
    let mut v___x_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5301_ = lean_usize_dec_lt(v_i_5294_, v_sz_5293_);
                if v___x_5301_ == 0 {
                    v___x_5302_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5302_, 0, v_b_5295_);
                    return v___x_5302_;
                } else {
                    leanh::lean_dec_ref(v_b_5295_);
                    v_a_5303_ = lean_array_uget_borrowed(v_as_5292_, v_i_5294_);
                    leanh::lean_inc(v___y_5299_);
                    leanh::lean_inc_ref(v___y_5298_);
                    leanh::lean_inc(v___y_5297_);
                    leanh::lean_inc_ref(v___y_5296_);
                    leanh::lean_inc(v_a_5303_);
                    v___x_5304_ = lean_infer_type(
                        v_a_5303_,
                        v___y_5296_,
                        v___y_5297_,
                        v___y_5298_,
                        v___y_5299_,
                    );
                    if leanh::lean_obj_tag(v___x_5304_) == 0 {
                        v_a_5305_ = leanh::lean_ctor_get(v___x_5304_, 0);
                        leanh::lean_inc(v_a_5305_);
                        leanh::lean_dec_ref_known(v___x_5304_, 1);
                        v___x_5306_ = leanh::lean_box(0);
                        v___x_5307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0;
                        v_sz_5308_ = lean_array_size(v_ys_5291_);
                        v___x_5309_ = 0usize;
                        leanh::lean_inc(v_a_5303_);
                        v___x_5310_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2(v_a_5305_, v_indices_5290_, v_a_5303_, v_ys_5291_, v_sz_5308_, v___x_5309_, v___x_5307_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
                        if leanh::lean_obj_tag(v___x_5310_) == 0 {
                            v_a_5311_ = leanh::lean_ctor_get(v___x_5310_, 0);
                            v_isSharedCheck_5330_ =
                                (!leanh::lean_is_exclusive(v___x_5310_)) as u8;
                            if v_isSharedCheck_5330_ == 0 {
                                v___x_5313_ = v___x_5310_;
                                v_isShared_5314_ = v_isSharedCheck_5330_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_5311_);
                                leanh::lean_dec(v___x_5310_);
                                v___x_5313_ = leanh::lean_box(0);
                                v_isShared_5314_ = v_isSharedCheck_5330_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_5310_;
                        }
                    } else {
                        v_a_5331_ = leanh::lean_ctor_get(v___x_5304_, 0);
                        v_isSharedCheck_5338_ =
                            (!leanh::lean_is_exclusive(v___x_5304_)) as u8;
                        if v_isSharedCheck_5338_ == 0 {
                            v___x_5333_ = v___x_5304_;
                            v_isShared_5334_ = v_isSharedCheck_5338_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5331_);
                            leanh::lean_dec(v___x_5304_);
                            v___x_5333_ = leanh::lean_box(0);
                            v_isShared_5334_ = v_isSharedCheck_5338_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5315_ = leanh::lean_ctor_get(v_a_5311_, 0);
                v_isSharedCheck_5328_ = (!leanh::lean_is_exclusive(v_a_5311_)) as u8;
                if v_isSharedCheck_5328_ == 0 {
                    v_unused_5329_ = leanh::lean_ctor_get(v_a_5311_, 1);
                    leanh::lean_dec(v_unused_5329_);
                    v___x_5317_ = v_a_5311_;
                    v_isShared_5318_ = v_isSharedCheck_5328_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5315_);
                    leanh::lean_dec(v_a_5311_);
                    v___x_5317_ = leanh::lean_box(0);
                    v_isShared_5318_ = v_isSharedCheck_5328_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_5315_) == 0 {
                    leanh::lean_del_object(v___x_5317_);
                    leanh::lean_del_object(v___x_5313_);
                    v___x_5319_ = 1usize;
                    v___x_5320_ = lean_usize_add(v_i_5294_, v___x_5319_);
                    v___x_5321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3_spec__4(v_ys_5291_, v_indices_5290_, v_as_5292_, v_sz_5293_, v___x_5320_, v___x_5307_, v___y_5296_, v___y_5297_, v___y_5298_, v___y_5299_);
                    return v___x_5321_;
                } else {
                    if v_isShared_5318_ == 0 {
                        leanh::lean_ctor_set(v___x_5317_, 1, v___x_5306_);
                        v___x_5323_ = v___x_5317_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5327_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 0, v_fst_5315_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5327_, 1, v___x_5306_);
                        v___x_5323_ = v_reuseFailAlloc_5327_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5314_ == 0 {
                    leanh::lean_ctor_set(v___x_5313_, 0, v___x_5323_);
                    v___x_5325_ = v___x_5313_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5326_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5323_);
                    v___x_5325_ = v_reuseFailAlloc_5326_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5325_;
            }
            5 => {
                if v_isShared_5334_ == 0 {
                    v___x_5336_ = v___x_5333_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5337_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5337_, 0, v_a_5331_);
                    v___x_5336_ = v_reuseFailAlloc_5337_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5336_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3___boxed(
    mut v_indices_5339_: *mut leanh::LeanObject,
    mut v_ys_5340_: *mut leanh::LeanObject,
    mut v_as_5341_: *mut leanh::LeanObject,
    mut v_sz_5342_: *mut leanh::LeanObject,
    mut v_i_5343_: *mut leanh::LeanObject,
    mut v_b_5344_: *mut leanh::LeanObject,
    mut v___y_5345_: *mut leanh::LeanObject,
    mut v___y_5346_: *mut leanh::LeanObject,
    mut v___y_5347_: *mut leanh::LeanObject,
    mut v___y_5348_: *mut leanh::LeanObject,
    mut v___y_5349_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5350_: usize = 0;
    let mut v_i_boxed_5351_: usize = 0;
    let mut v_res_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5350_ = leanh::lean_unbox_usize(v_sz_5342_);
    leanh::lean_dec(v_sz_5342_);
    v_i_boxed_5351_ = leanh::lean_unbox_usize(v_i_5343_);
    leanh::lean_dec(v_i_5343_);
    v_res_5352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_5339_, v_ys_5340_, v_as_5341_, v_sz_boxed_5350_, v_i_boxed_5351_, v_b_5344_, v___y_5345_, v___y_5346_, v___y_5347_, v___y_5348_);
    leanh::lean_dec(v___y_5348_);
    leanh::lean_dec_ref(v___y_5347_);
    leanh::lean_dec(v___y_5346_);
    leanh::lean_dec_ref(v___y_5345_);
    leanh::lean_dec_ref(v_as_5341_);
    leanh::lean_dec_ref(v_ys_5340_);
    leanh::lean_dec_ref(v_indices_5339_);
    return v_res_5352_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(
    mut v_ys_5353_: *mut leanh::LeanObject,
    mut v_indices_5354_: *mut leanh::LeanObject,
    mut v_a_5355_: *mut leanh::LeanObject,
    mut v_a_5356_: *mut leanh::LeanObject,
    mut v_a_5357_: *mut leanh::LeanObject,
    mut v_a_5358_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5362_: usize = 0;
    let mut v___x_5363_: usize = 0;
    let mut v___x_5364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5368_: u8 = 0;
    let mut v_fst_5369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5377_: u8 = 0;
    let mut v_a_5378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5381_: u8 = 0;
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5385_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5360_ = leanh::lean_box(0);
                v___x_5361_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0;
                v_sz_5362_ = lean_array_size(v_indices_5354_);
                v___x_5363_ = 0usize;
                v___x_5364_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__3(v_indices_5354_, v_ys_5353_, v_indices_5354_, v_sz_5362_, v___x_5363_, v___x_5361_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_);
                if leanh::lean_obj_tag(v___x_5364_) == 0 {
                    v_a_5365_ = leanh::lean_ctor_get(v___x_5364_, 0);
                    v_isSharedCheck_5377_ = (!leanh::lean_is_exclusive(v___x_5364_)) as u8;
                    if v_isSharedCheck_5377_ == 0 {
                        v___x_5367_ = v___x_5364_;
                        v_isShared_5368_ = v_isSharedCheck_5377_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5365_);
                        leanh::lean_dec(v___x_5364_);
                        v___x_5367_ = leanh::lean_box(0);
                        v_isShared_5368_ = v_isSharedCheck_5377_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5378_ = leanh::lean_ctor_get(v___x_5364_, 0);
                    v_isSharedCheck_5385_ = (!leanh::lean_is_exclusive(v___x_5364_)) as u8;
                    if v_isSharedCheck_5385_ == 0 {
                        v___x_5380_ = v___x_5364_;
                        v_isShared_5381_ = v_isSharedCheck_5385_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5378_);
                        leanh::lean_dec(v___x_5364_);
                        v___x_5380_ = leanh::lean_box(0);
                        v_isShared_5381_ = v_isSharedCheck_5385_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5369_ = leanh::lean_ctor_get(v_a_5365_, 0);
                leanh::lean_inc(v_fst_5369_);
                leanh::lean_dec(v_a_5365_);
                if leanh::lean_obj_tag(v_fst_5369_) == 0 {
                    if v_isShared_5368_ == 0 {
                        leanh::lean_ctor_set(v___x_5367_, 0, v___x_5360_);
                        v___x_5371_ = v___x_5367_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5372_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5360_);
                        v___x_5371_ = v_reuseFailAlloc_5372_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5373_ = leanh::lean_ctor_get(v_fst_5369_, 0);
                    leanh::lean_inc(v_val_5373_);
                    leanh::lean_dec_ref_known(v_fst_5369_, 1);
                    if v_isShared_5368_ == 0 {
                        leanh::lean_ctor_set(v___x_5367_, 0, v_val_5373_);
                        v___x_5375_ = v___x_5367_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5376_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5376_, 0, v_val_5373_);
                        v___x_5375_ = v_reuseFailAlloc_5376_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5371_;
            }
            3 => {
                return v___x_5375_;
            }
            4 => {
                if v_isShared_5381_ == 0 {
                    v___x_5383_ = v___x_5380_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5384_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5384_, 0, v_a_5378_);
                    v___x_5383_ = v_reuseFailAlloc_5384_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5383_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f___boxed(
    mut v_ys_5386_: *mut leanh::LeanObject,
    mut v_indices_5387_: *mut leanh::LeanObject,
    mut v_a_5388_: *mut leanh::LeanObject,
    mut v_a_5389_: *mut leanh::LeanObject,
    mut v_a_5390_: *mut leanh::LeanObject,
    mut v_a_5391_: *mut leanh::LeanObject,
    mut v_a_5392_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5393_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_5386_, v_indices_5387_, v_a_5388_, v_a_5389_, v_a_5390_, v_a_5391_);
    leanh::lean_dec(v_a_5391_);
    leanh::lean_dec_ref(v_a_5390_);
    leanh::lean_dec(v_a_5389_);
    leanh::lean_dec_ref(v_a_5388_);
    leanh::lean_dec_ref(v_indices_5387_);
    leanh::lean_dec_ref(v_ys_5386_);
    return v_res_5393_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(
    mut v_a_5394_: *mut leanh::LeanObject,
    mut v_as_5395_: *mut leanh::LeanObject,
    mut v_sz_5396_: usize,
    mut v_i_5397_: usize,
    mut v_b_5398_: *mut leanh::LeanObject,
    mut v___y_5399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5401_: u8 = 0;
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5409_: u8 = 0;
    let mut v___x_5410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5411_: u8 = 0;
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5413_: usize = 0;
    let mut v___x_5414_: usize = 0;
    let mut v___x_5416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5423_: u8 = 0;
    let mut v_a_5424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5426_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5427_: u8 = 0;
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5431_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5401_ = lean_usize_dec_lt(v_i_5397_, v_sz_5396_);
                if v___x_5401_ == 0 {
                    leanh::lean_dec_ref(v_a_5394_);
                    v___x_5402_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5402_, 0, v_b_5398_);
                    return v___x_5402_;
                } else {
                    leanh::lean_dec_ref(v_b_5398_);
                    v_a_5403_ = lean_array_uget_borrowed(v_as_5395_, v_i_5397_);
                    v___x_5404_ = l_Lean_Expr_fvarId_x21(v_a_5403_);
                    leanh::lean_inc_ref(v_a_5394_);
                    v___x_5405_ = l_Lean_exprDependsOn___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__0___redArg(v_a_5394_, v___x_5404_, v___y_5399_);
                    if leanh::lean_obj_tag(v___x_5405_) == 0 {
                        v_a_5406_ = leanh::lean_ctor_get(v___x_5405_, 0);
                        v_isSharedCheck_5423_ =
                            (!leanh::lean_is_exclusive(v___x_5405_)) as u8;
                        if v_isSharedCheck_5423_ == 0 {
                            v___x_5408_ = v___x_5405_;
                            v_isShared_5409_ = v_isSharedCheck_5423_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5406_);
                            leanh::lean_dec(v___x_5405_);
                            v___x_5408_ = leanh::lean_box(0);
                            v_isShared_5409_ = v_isSharedCheck_5423_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_a_5394_);
                        v_a_5424_ = leanh::lean_ctor_get(v___x_5405_, 0);
                        v_isSharedCheck_5431_ =
                            (!leanh::lean_is_exclusive(v___x_5405_)) as u8;
                        if v_isSharedCheck_5431_ == 0 {
                            v___x_5426_ = v___x_5405_;
                            v_isShared_5427_ = v_isSharedCheck_5431_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5424_);
                            leanh::lean_dec(v___x_5405_);
                            v___x_5426_ = leanh::lean_box(0);
                            v_isShared_5427_ = v_isSharedCheck_5431_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_5410_ = leanh::lean_box(0);
                v___x_5411_ = (leanh::lean_unbox(v_a_5406_) as u8);
                leanh::lean_dec(v_a_5406_);
                if v___x_5411_ == 0 {
                    leanh::lean_del_object(v___x_5408_);
                    v___x_5412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0;
                    v___x_5413_ = 1usize;
                    v___x_5414_ = lean_usize_add(v_i_5397_, v___x_5413_);
                    v_i_5397_ = v___x_5414_;
                    v_b_5398_ = v___x_5412_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5403_);
                    v___x_5416_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5416_, 0, v_a_5394_);
                    leanh::lean_ctor_set(v___x_5416_, 1, v_a_5403_);
                    v___x_5417_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5417_, 0, v___x_5416_);
                    v___x_5418_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5418_, 0, v___x_5417_);
                    v___x_5419_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5419_, 0, v___x_5418_);
                    leanh::lean_ctor_set(v___x_5419_, 1, v___x_5410_);
                    if v_isShared_5409_ == 0 {
                        leanh::lean_ctor_set(v___x_5408_, 0, v___x_5419_);
                        v___x_5421_ = v___x_5408_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5422_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5422_, 0, v___x_5419_);
                        v___x_5421_ = v_reuseFailAlloc_5422_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5421_;
            }
            3 => {
                if v_isShared_5427_ == 0 {
                    v___x_5429_ = v___x_5426_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5430_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5430_, 0, v_a_5424_);
                    v___x_5429_ = v_reuseFailAlloc_5430_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5429_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg___boxed(
    mut v_a_5432_: *mut leanh::LeanObject,
    mut v_as_5433_: *mut leanh::LeanObject,
    mut v_sz_5434_: *mut leanh::LeanObject,
    mut v_i_5435_: *mut leanh::LeanObject,
    mut v_b_5436_: *mut leanh::LeanObject,
    mut v___y_5437_: *mut leanh::LeanObject,
    mut v___y_5438_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5439_: usize = 0;
    let mut v_i_boxed_5440_: usize = 0;
    let mut v_res_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5439_ = leanh::lean_unbox_usize(v_sz_5434_);
    leanh::lean_dec(v_sz_5434_);
    v_i_boxed_5440_ = leanh::lean_unbox_usize(v_i_5435_);
    leanh::lean_dec(v_i_5435_);
    v_res_5441_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_5432_, v_as_5433_, v_sz_boxed_5439_, v_i_boxed_5440_, v_b_5436_, v___y_5437_);
    leanh::lean_dec(v___y_5437_);
    leanh::lean_dec_ref(v_as_5433_);
    return v_res_5441_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(
    mut v_ys_5442_: *mut leanh::LeanObject,
    mut v_as_5443_: *mut leanh::LeanObject,
    mut v_sz_5444_: usize,
    mut v_i_5445_: usize,
    mut v_b_5446_: *mut leanh::LeanObject,
    mut v___y_5447_: *mut leanh::LeanObject,
    mut v___y_5448_: *mut leanh::LeanObject,
    mut v___y_5449_: *mut leanh::LeanObject,
    mut v___y_5450_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5452_: u8 = 0;
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5457_: usize = 0;
    let mut v___x_5458_: usize = 0;
    let mut v___x_5459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v_fst_5464_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5467_: u8 = 0;
    let mut v___x_5468_: usize = 0;
    let mut v___x_5469_: usize = 0;
    let mut v___x_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5477_: u8 = 0;
    let mut v_unused_5478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5479_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5452_ = lean_usize_dec_lt(v_i_5445_, v_sz_5444_);
                if v___x_5452_ == 0 {
                    v___x_5453_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5453_, 0, v_b_5446_);
                    return v___x_5453_;
                } else {
                    leanh::lean_dec_ref(v_b_5446_);
                    v___x_5454_ = leanh::lean_box(0);
                    v___x_5455_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0;
                    v_a_5456_ = lean_array_uget_borrowed(v_as_5443_, v_i_5445_);
                    v_sz_5457_ = lean_array_size(v_ys_5442_);
                    v___x_5458_ = 0usize;
                    leanh::lean_inc(v_a_5456_);
                    v___x_5459_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_5456_, v_ys_5442_, v_sz_5457_, v___x_5458_, v___x_5455_, v___y_5448_);
                    if leanh::lean_obj_tag(v___x_5459_) == 0 {
                        v_a_5460_ = leanh::lean_ctor_get(v___x_5459_, 0);
                        v_isSharedCheck_5479_ =
                            (!leanh::lean_is_exclusive(v___x_5459_)) as u8;
                        if v_isSharedCheck_5479_ == 0 {
                            v___x_5462_ = v___x_5459_;
                            v_isShared_5463_ = v_isSharedCheck_5479_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5460_);
                            leanh::lean_dec(v___x_5459_);
                            v___x_5462_ = leanh::lean_box(0);
                            v_isShared_5463_ = v_isSharedCheck_5479_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_5459_;
                    }
                }
            }
            1 => {
                v_fst_5464_ = leanh::lean_ctor_get(v_a_5460_, 0);
                v_isSharedCheck_5477_ = (!leanh::lean_is_exclusive(v_a_5460_)) as u8;
                if v_isSharedCheck_5477_ == 0 {
                    v_unused_5478_ = leanh::lean_ctor_get(v_a_5460_, 1);
                    leanh::lean_dec(v_unused_5478_);
                    v___x_5466_ = v_a_5460_;
                    v_isShared_5467_ = v_isSharedCheck_5477_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_5464_);
                    leanh::lean_dec(v_a_5460_);
                    v___x_5466_ = leanh::lean_box(0);
                    v_isShared_5467_ = v_isSharedCheck_5477_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_fst_5464_) == 0 {
                    leanh::lean_del_object(v___x_5466_);
                    leanh::lean_del_object(v___x_5462_);
                    v___x_5468_ = 1usize;
                    v___x_5469_ = lean_usize_add(v_i_5445_, v___x_5468_);
                    v_i_5445_ = v___x_5469_;
                    v_b_5446_ = v___x_5455_;
                    state = 0;
                    continue;
                } else {
                    if v_isShared_5467_ == 0 {
                        leanh::lean_ctor_set(v___x_5466_, 1, v___x_5454_);
                        v___x_5472_ = v___x_5466_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5476_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5476_, 0, v_fst_5464_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5476_, 1, v___x_5454_);
                        v___x_5472_ = v_reuseFailAlloc_5476_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5463_ == 0 {
                    leanh::lean_ctor_set(v___x_5462_, 0, v___x_5472_);
                    v___x_5474_ = v___x_5462_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5475_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5475_, 0, v___x_5472_);
                    v___x_5474_ = v_reuseFailAlloc_5475_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1___boxed(
    mut v_ys_5480_: *mut leanh::LeanObject,
    mut v_as_5481_: *mut leanh::LeanObject,
    mut v_sz_5482_: *mut leanh::LeanObject,
    mut v_i_5483_: *mut leanh::LeanObject,
    mut v_b_5484_: *mut leanh::LeanObject,
    mut v___y_5485_: *mut leanh::LeanObject,
    mut v___y_5486_: *mut leanh::LeanObject,
    mut v___y_5487_: *mut leanh::LeanObject,
    mut v___y_5488_: *mut leanh::LeanObject,
    mut v___y_5489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5490_: usize = 0;
    let mut v_i_boxed_5491_: usize = 0;
    let mut v_res_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5490_ = leanh::lean_unbox_usize(v_sz_5482_);
    leanh::lean_dec(v_sz_5482_);
    v_i_boxed_5491_ = leanh::lean_unbox_usize(v_i_5483_);
    leanh::lean_dec(v_i_5483_);
    v_res_5492_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_5480_, v_as_5481_, v_sz_boxed_5490_, v_i_boxed_5491_, v_b_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_);
    leanh::lean_dec(v___y_5488_);
    leanh::lean_dec_ref(v___y_5487_);
    leanh::lean_dec(v___y_5486_);
    leanh::lean_dec_ref(v___y_5485_);
    leanh::lean_dec_ref(v_as_5481_);
    leanh::lean_dec_ref(v_ys_5480_);
    return v_res_5492_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(
    mut v_ys_5493_: *mut leanh::LeanObject,
    mut v_indParams_5494_: *mut leanh::LeanObject,
    mut v_a_5495_: *mut leanh::LeanObject,
    mut v_a_5496_: *mut leanh::LeanObject,
    mut v_a_5497_: *mut leanh::LeanObject,
    mut v_a_5498_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5502_: usize = 0;
    let mut v___x_5503_: usize = 0;
    let mut v___x_5504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5508_: u8 = 0;
    let mut v_fst_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5517_: u8 = 0;
    let mut v_a_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5521_: u8 = 0;
    let mut v___x_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5525_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5500_ = leanh::lean_box(0);
                v___x_5501_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f_spec__2___closed__0;
                v_sz_5502_ = lean_array_size(v_indParams_5494_);
                v___x_5503_ = 0usize;
                v___x_5504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__1(v_ys_5493_, v_indParams_5494_, v_sz_5502_, v___x_5503_, v___x_5501_, v_a_5495_, v_a_5496_, v_a_5497_, v_a_5498_);
                if leanh::lean_obj_tag(v___x_5504_) == 0 {
                    v_a_5505_ = leanh::lean_ctor_get(v___x_5504_, 0);
                    v_isSharedCheck_5517_ = (!leanh::lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5517_ == 0 {
                        v___x_5507_ = v___x_5504_;
                        v_isShared_5508_ = v_isSharedCheck_5517_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5505_);
                        leanh::lean_dec(v___x_5504_);
                        v___x_5507_ = leanh::lean_box(0);
                        v_isShared_5508_ = v_isSharedCheck_5517_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5518_ = leanh::lean_ctor_get(v___x_5504_, 0);
                    v_isSharedCheck_5525_ = (!leanh::lean_is_exclusive(v___x_5504_)) as u8;
                    if v_isSharedCheck_5525_ == 0 {
                        v___x_5520_ = v___x_5504_;
                        v_isShared_5521_ = v_isSharedCheck_5525_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5518_);
                        leanh::lean_dec(v___x_5504_);
                        v___x_5520_ = leanh::lean_box(0);
                        v_isShared_5521_ = v_isSharedCheck_5525_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_5509_ = leanh::lean_ctor_get(v_a_5505_, 0);
                leanh::lean_inc(v_fst_5509_);
                leanh::lean_dec(v_a_5505_);
                if leanh::lean_obj_tag(v_fst_5509_) == 0 {
                    if v_isShared_5508_ == 0 {
                        leanh::lean_ctor_set(v___x_5507_, 0, v___x_5500_);
                        v___x_5511_ = v___x_5507_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5512_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5512_, 0, v___x_5500_);
                        v___x_5511_ = v_reuseFailAlloc_5512_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_5513_ = leanh::lean_ctor_get(v_fst_5509_, 0);
                    leanh::lean_inc(v_val_5513_);
                    leanh::lean_dec_ref_known(v_fst_5509_, 1);
                    if v_isShared_5508_ == 0 {
                        leanh::lean_ctor_set(v___x_5507_, 0, v_val_5513_);
                        v___x_5515_ = v___x_5507_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5516_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5516_, 0, v_val_5513_);
                        v___x_5515_ = v_reuseFailAlloc_5516_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5511_;
            }
            3 => {
                return v___x_5515_;
            }
            4 => {
                if v_isShared_5521_ == 0 {
                    v___x_5523_ = v___x_5520_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5524_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5524_, 0, v_a_5518_);
                    v___x_5523_ = v_reuseFailAlloc_5524_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f___boxed(
    mut v_ys_5526_: *mut leanh::LeanObject,
    mut v_indParams_5527_: *mut leanh::LeanObject,
    mut v_a_5528_: *mut leanh::LeanObject,
    mut v_a_5529_: *mut leanh::LeanObject,
    mut v_a_5530_: *mut leanh::LeanObject,
    mut v_a_5531_: *mut leanh::LeanObject,
    mut v_a_5532_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5533_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v_ys_5526_, v_indParams_5527_, v_a_5528_, v_a_5529_, v_a_5530_, v_a_5531_);
    leanh::lean_dec(v_a_5531_);
    leanh::lean_dec_ref(v_a_5530_);
    leanh::lean_dec(v_a_5529_);
    leanh::lean_dec_ref(v_a_5528_);
    leanh::lean_dec_ref(v_indParams_5527_);
    leanh::lean_dec_ref(v_ys_5526_);
    return v_res_5533_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(
    mut v_a_5534_: *mut leanh::LeanObject,
    mut v_as_5535_: *mut leanh::LeanObject,
    mut v_sz_5536_: usize,
    mut v_i_5537_: usize,
    mut v_b_5538_: *mut leanh::LeanObject,
    mut v___y_5539_: *mut leanh::LeanObject,
    mut v___y_5540_: *mut leanh::LeanObject,
    mut v___y_5541_: *mut leanh::LeanObject,
    mut v___y_5542_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5544_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___redArg(v_a_5534_, v_as_5535_, v_sz_5536_, v_i_5537_, v_b_5538_, v___y_5540_);
    return v___x_5544_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0___boxed(
    mut v_a_5545_: *mut leanh::LeanObject,
    mut v_as_5546_: *mut leanh::LeanObject,
    mut v_sz_5547_: *mut leanh::LeanObject,
    mut v_i_5548_: *mut leanh::LeanObject,
    mut v_b_5549_: *mut leanh::LeanObject,
    mut v___y_5550_: *mut leanh::LeanObject,
    mut v___y_5551_: *mut leanh::LeanObject,
    mut v___y_5552_: *mut leanh::LeanObject,
    mut v___y_5553_: *mut leanh::LeanObject,
    mut v___y_5554_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5555_: usize = 0;
    let mut v_i_boxed_5556_: usize = 0;
    let mut v_res_5557_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5555_ = leanh::lean_unbox_usize(v_sz_5547_);
    leanh::lean_dec(v_sz_5547_);
    v_i_boxed_5556_ = leanh::lean_unbox_usize(v_i_5548_);
    leanh::lean_dec(v_i_5548_);
    v_res_5557_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f_spec__0(v_a_5545_, v_as_5546_, v_sz_boxed_5555_, v_i_boxed_5556_, v_b_5549_, v___y_5550_, v___y_5551_, v___y_5552_, v___y_5553_);
    leanh::lean_dec(v___y_5553_);
    leanh::lean_dec_ref(v___y_5552_);
    leanh::lean_dec(v___y_5551_);
    leanh::lean_dec_ref(v___y_5550_);
    leanh::lean_dec_ref(v_as_5546_);
    return v_res_5557_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(
    mut v_msg_5558_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5559_ = leanh::lean_unsigned_to_nat(0);
    v___x_5560_ = lean_panic_fn_borrowed(v___x_5559_, v_msg_5558_);
    return v___x_5560_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(
    mut v_msg_5562_: *mut leanh::LeanObject,
    mut v___y_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
    mut v___y_5565_: *mut leanh::LeanObject,
    mut v___y_5566_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6888__overap_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5568_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___closed__0;
    v___x_6888__overap_5569_ = lean_panic_fn_borrowed(v___f_5568_, v_msg_5562_);
    leanh::lean_inc(v___y_5566_);
    leanh::lean_inc_ref(v___y_5565_);
    leanh::lean_inc(v___y_5564_);
    leanh::lean_inc_ref(v___y_5563_);
    v___x_5570_ = leanh::lean_apply_5(
        v___x_6888__overap_5569_,
        v___y_5563_,
        v___y_5564_,
        v___y_5565_,
        v___y_5566_,
        leanh::lean_box(0),
    );
    return v___x_5570_;
}
pub unsafe fn l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5___boxed(
    mut v_msg_5571_: *mut leanh::LeanObject,
    mut v___y_5572_: *mut leanh::LeanObject,
    mut v___y_5573_: *mut leanh::LeanObject,
    mut v___y_5574_: *mut leanh::LeanObject,
    mut v___y_5575_: *mut leanh::LeanObject,
    mut v___y_5576_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5577_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(
        v_msg_5571_,
        v___y_5572_,
        v___y_5573_,
        v___y_5574_,
        v___y_5575_,
    );
    leanh::lean_dec(v___y_5575_);
    leanh::lean_dec_ref(v___y_5574_);
    leanh::lean_dec(v___y_5573_);
    leanh::lean_dec_ref(v___y_5572_);
    return v_res_5577_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(
    mut v_msg_5578_: *mut leanh::LeanObject,
    mut v___y_5579_: *mut leanh::LeanObject,
    mut v___y_5580_: *mut leanh::LeanObject,
    mut v___y_5581_: *mut leanh::LeanObject,
    mut v___y_5582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5589_: u8 = 0;
    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_5584_ = leanh::lean_ctor_get(v___y_5581_, 5);
                v___x_5585_ =
                    l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(
                        v_msg_5578_,
                        v___y_5579_,
                        v___y_5580_,
                        v___y_5581_,
                        v___y_5582_,
                    );
                v_a_5586_ = leanh::lean_ctor_get(v___x_5585_, 0);
                v_isSharedCheck_5594_ = (!leanh::lean_is_exclusive(v___x_5585_)) as u8;
                if v_isSharedCheck_5594_ == 0 {
                    v___x_5588_ = v___x_5585_;
                    v_isShared_5589_ = v_isSharedCheck_5594_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_5586_);
                    leanh::lean_dec(v___x_5585_);
                    v___x_5588_ = leanh::lean_box(0);
                    v_isShared_5589_ = v_isSharedCheck_5594_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_5584_);
                v___x_5590_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5590_, 0, v_ref_5584_);
                leanh::lean_ctor_set(v___x_5590_, 1, v_a_5586_);
                if v_isShared_5589_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5588_, 1);
                    leanh::lean_ctor_set(v___x_5588_, 0, v___x_5590_);
                    v___x_5592_ = v___x_5588_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5593_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5590_);
                    v___x_5592_ = v_reuseFailAlloc_5593_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5592_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg___boxed(
    mut v_msg_5595_: *mut leanh::LeanObject,
    mut v___y_5596_: *mut leanh::LeanObject,
    mut v___y_5597_: *mut leanh::LeanObject,
    mut v___y_5598_: *mut leanh::LeanObject,
    mut v___y_5599_: *mut leanh::LeanObject,
    mut v___y_5600_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5601_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(
        v_msg_5595_,
        v___y_5596_,
        v___y_5597_,
        v___y_5598_,
        v___y_5599_,
    );
    leanh::lean_dec(v___y_5599_);
    leanh::lean_dec_ref(v___y_5598_);
    leanh::lean_dec(v___y_5597_);
    leanh::lean_dec_ref(v___y_5596_);
    return v_res_5601_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5605_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2;
    v___x_5606_ = leanh::lean_unsigned_to_nat(107);
    v___x_5607_ = leanh::lean_unsigned_to_nat(97);
    v___x_5608_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1;
    v___x_5609_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0;
    v___x_5610_ = l_mkPanicMessageWithDecl(
        v___x_5609_,
        v___x_5608_,
        v___x_5607_,
        v___x_5606_,
        v___x_5605_,
    );
    return v___x_5610_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(
    mut v_xs_5611_: *mut leanh::LeanObject,
    mut v_sz_5612_: usize,
    mut v_i_5613_: usize,
    mut v_bs_5614_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5615_: u8 = 0;
    let mut v_v_5616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_5618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5621_: usize = 0;
    let mut v___x_5622_: usize = 0;
    let mut v___x_5623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5615_ = lean_usize_dec_lt(v_i_5613_, v_sz_5612_);
                if v___x_5615_ == 0 {
                    return v_bs_5614_;
                } else {
                    v_v_5616_ = lean_array_uget(v_bs_5614_, v_i_5613_);
                    v___x_5617_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_5618_ = lean_array_uset(v_bs_5614_, v_i_5613_, v___x_5617_);
                    v___x_5625_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v_xs_5611_, v_v_5616_);
                    leanh::lean_dec(v_v_5616_);
                    if leanh::lean_obj_tag(v___x_5625_) == 0 {
                        v___x_5626_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__3);
                        v___x_5627_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(
                            v___x_5626_,
                        );
                        v___y_5620_ = v___x_5627_;
                        state = 1;
                        continue;
                    } else {
                        v_val_5628_ = leanh::lean_ctor_get(v___x_5625_, 0);
                        leanh::lean_inc(v_val_5628_);
                        leanh::lean_dec_ref_known(v___x_5625_, 1);
                        v___y_5620_ = v_val_5628_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5621_ = 1usize;
                v___x_5622_ = lean_usize_add(v_i_5613_, v___x_5621_);
                v___x_5623_ = lean_array_uset(v_bs_x27_5618_, v_i_5613_, v___y_5620_);
                v_i_5613_ = v___x_5622_;
                v_bs_5614_ = v___x_5623_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___boxed(
    mut v_xs_5629_: *mut leanh::LeanObject,
    mut v_sz_5630_: *mut leanh::LeanObject,
    mut v_i_5631_: *mut leanh::LeanObject,
    mut v_bs_5632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5633_: usize = 0;
    let mut v_i_boxed_5634_: usize = 0;
    let mut v_res_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5633_ = leanh::lean_unbox_usize(v_sz_5630_);
    leanh::lean_dec(v_sz_5630_);
    v_i_boxed_5634_ = leanh::lean_unbox_usize(v_i_5631_);
    leanh::lean_dec(v_i_5631_);
    v_res_5635_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_5629_, v_sz_boxed_5633_, v_i_boxed_5634_, v_bs_5632_);
    leanh::lean_dec_ref(v_xs_5629_);
    return v_res_5635_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(
    mut v_as_5636_: *mut leanh::LeanObject,
    mut v_a_5637_: *mut leanh::LeanObject,
    mut v_x_5638_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_zero_5639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isZero_5640_: u8 = 0;
    let mut v_one_5641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_n_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_zero_5639_ = leanh::lean_unsigned_to_nat(0);
                v_isZero_5640_ = lean_nat_dec_eq(v_x_5638_, v_zero_5639_);
                if v_isZero_5640_ == 1 {
                    leanh::lean_dec(v_x_5638_);
                    return v_isZero_5640_;
                } else {
                    v_one_5641_ = leanh::lean_unsigned_to_nat(1);
                    v_n_5642_ = lean_nat_sub(v_x_5638_, v_one_5641_);
                    leanh::lean_dec(v_x_5638_);
                    v___x_5643_ = lean_array_fget_borrowed(v_as_5636_, v_n_5642_);
                    v___x_5644_ = lean_expr_eqv(v_a_5637_, v___x_5643_);
                    if v___x_5644_ == 0 {
                        v_x_5638_ = v_n_5642_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_n_5642_);
                        return v_isZero_5640_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg___boxed(
    mut v_as_5646_: *mut leanh::LeanObject,
    mut v_a_5647_: *mut leanh::LeanObject,
    mut v_x_5648_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5649_: u8 = 0;
    let mut v_r_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5649_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_5646_, v_a_5647_, v_x_5648_);
    leanh::lean_dec_ref(v_a_5647_);
    leanh::lean_dec_ref(v_as_5646_);
    v_r_5650_ = leanh::lean_box((v_res_5649_) as usize);
    return v_r_5650_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(
    mut v_as_5651_: *mut leanh::LeanObject,
    mut v_i_5652_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5654_: u8 = 0;
    let mut v___x_5655_: u8 = 0;
    let mut v___x_5656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5657_: u8 = 0;
    let mut v___x_5658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5653_ = lean_array_get_size(v_as_5651_);
                v___x_5654_ = lean_nat_dec_lt(v_i_5652_, v___x_5653_);
                if v___x_5654_ == 0 {
                    leanh::lean_dec(v_i_5652_);
                    v___x_5655_ = 1;
                    return v___x_5655_;
                } else {
                    v___x_5656_ = lean_array_fget_borrowed(v_as_5651_, v_i_5652_);
                    leanh::lean_inc(v_i_5652_);
                    v___x_5657_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_5651_, v___x_5656_, v_i_5652_);
                    if v___x_5657_ == 0 {
                        leanh::lean_dec(v_i_5652_);
                        return v___x_5657_;
                    } else {
                        v___x_5658_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5659_ = lean_nat_add(v_i_5652_, v___x_5658_);
                        leanh::lean_dec(v_i_5652_);
                        v_i_5652_ = v___x_5659_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2___boxed(
    mut v_as_5661_: *mut leanh::LeanObject,
    mut v_i_5662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5663_: u8 = 0;
    let mut v_r_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5663_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_5661_, v_i_5662_);
    leanh::lean_dec_ref(v_as_5661_);
    v_r_5664_ = leanh::lean_box((v_res_5663_) as usize);
    return v_r_5664_;
}
pub unsafe fn l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(
    mut v_as_5665_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: u8 = 0;
    v___x_5666_ = leanh::lean_unsigned_to_nat(0);
    v___x_5667_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2(v_as_5665_, v___x_5666_);
    return v___x_5667_;
}
pub unsafe fn l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2___boxed(
    mut v_as_5668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5669_: u8 = 0;
    let mut v_r_5670_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5669_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(v_as_5668_);
    leanh::lean_dec_ref(v_as_5668_);
    v_r_5670_ = leanh::lean_box((v_res_5669_) as usize);
    return v_r_5670_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(
    mut v_as_5671_: *mut leanh::LeanObject,
    mut v_i_5672_: usize,
    mut v_stop_5673_: usize,
) -> u8 {
    let mut v___x_5674_: u8 = 0;
    let mut v___x_5675_: u8 = 0;
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: u8 = 0;
    let mut v___x_5678_: usize = 0;
    let mut v___x_5679_: usize = 0;
    let mut v___x_5681_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5674_ = lean_usize_dec_eq(v_i_5672_, v_stop_5673_);
                if v___x_5674_ == 0 {
                    v___x_5675_ = 1;
                    v___x_5676_ = lean_array_uget_borrowed(v_as_5671_, v_i_5672_);
                    v___x_5677_ = l_Lean_Expr_isFVar(v___x_5676_);
                    if v___x_5677_ == 0 {
                        return v___x_5675_;
                    } else {
                        if v___x_5674_ == 0 {
                            v___x_5678_ = 1usize;
                            v___x_5679_ = lean_usize_add(v_i_5672_, v___x_5678_);
                            v_i_5672_ = v___x_5679_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_5675_;
                        }
                    }
                } else {
                    v___x_5681_ = 0;
                    return v___x_5681_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6___boxed(
    mut v_as_5682_: *mut leanh::LeanObject,
    mut v_i_5683_: *mut leanh::LeanObject,
    mut v_stop_5684_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5685_: usize = 0;
    let mut v_stop_boxed_5686_: usize = 0;
    let mut v_res_5687_: u8 = 0;
    let mut v_r_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5685_ = leanh::lean_unbox_usize(v_i_5683_);
    leanh::lean_dec(v_i_5683_);
    v_stop_boxed_5686_ = leanh::lean_unbox_usize(v_stop_5684_);
    leanh::lean_dec(v_stop_5684_);
    v_res_5687_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v_as_5682_, v_i_boxed_5685_, v_stop_boxed_5686_);
    leanh::lean_dec_ref(v_as_5682_);
    v_r_5688_ = leanh::lean_box((v_res_5687_) as usize);
    return v_r_5688_;
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(
    mut v_xs_5689_: *mut leanh::LeanObject,
    mut v_v_5690_: *mut leanh::LeanObject,
    mut v_i_5691_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: u8 = 0;
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5696_: u8 = 0;
    let mut v___x_5697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5692_ = lean_array_get_size(v_xs_5689_);
                v___x_5693_ = lean_nat_dec_lt(v_i_5691_, v___x_5692_);
                if v___x_5693_ == 0 {
                    leanh::lean_dec(v_i_5691_);
                    v___x_5694_ = leanh::lean_box(0);
                    return v___x_5694_;
                } else {
                    v___x_5695_ = lean_array_fget_borrowed(v_xs_5689_, v_i_5691_);
                    v___x_5696_ = lean_name_eq(v___x_5695_, v_v_5690_);
                    if v___x_5696_ == 0 {
                        v___x_5697_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5698_ = lean_nat_add(v_i_5691_, v___x_5697_);
                        leanh::lean_dec(v_i_5691_);
                        v_i_5691_ = v___x_5698_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5700_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5700_, 0, v_i_5691_);
                        return v___x_5700_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7___boxed(
    mut v_xs_5701_: *mut leanh::LeanObject,
    mut v_v_5702_: *mut leanh::LeanObject,
    mut v_i_5703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5704_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_5701_, v_v_5702_, v_i_5703_);
    leanh::lean_dec(v_v_5702_);
    leanh::lean_dec_ref(v_xs_5701_);
    return v_res_5704_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(
    mut v_xs_5705_: *mut leanh::LeanObject,
    mut v_v_5706_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5707_ = leanh::lean_unsigned_to_nat(0);
    v___x_5708_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4_spec__7(v_xs_5705_, v_v_5706_, v___x_5707_);
    return v___x_5708_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4___boxed(
    mut v_xs_5709_: *mut leanh::LeanObject,
    mut v_v_5710_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5711_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_5709_, v_v_5710_);
    leanh::lean_dec(v_v_5710_);
    leanh::lean_dec_ref(v_xs_5709_);
    return v_res_5711_;
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(
    mut v_xs_5712_: *mut leanh::LeanObject,
    mut v_v_5713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5719_: u8 = 0;
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5723_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5714_ = l_Array_finIdxOf_x3f___at___00Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3_spec__4(v_xs_5712_, v_v_5713_);
                if leanh::lean_obj_tag(v___x_5714_) == 0 {
                    v___x_5715_ = leanh::lean_box(0);
                    return v___x_5715_;
                } else {
                    v_val_5716_ = leanh::lean_ctor_get(v___x_5714_, 0);
                    v_isSharedCheck_5723_ = (!leanh::lean_is_exclusive(v___x_5714_)) as u8;
                    if v_isSharedCheck_5723_ == 0 {
                        v___x_5718_ = v___x_5714_;
                        v_isShared_5719_ = v_isSharedCheck_5723_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_5716_);
                        leanh::lean_dec(v___x_5714_);
                        v___x_5718_ = leanh::lean_box(0);
                        v_isShared_5719_ = v_isSharedCheck_5723_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5719_ == 0 {
                    v___x_5721_ = v___x_5718_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5722_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5722_, 0, v_val_5716_);
                    v___x_5721_ = v_reuseFailAlloc_5722_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3___boxed(
    mut v_xs_5724_: *mut leanh::LeanObject,
    mut v_v_5725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5726_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(
        v_xs_5724_, v_v_5725_,
    );
    leanh::lean_dec(v_v_5725_);
    leanh::lean_dec_ref(v_xs_5724_);
    return v_res_5726_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5728_ = l_Lean_Elab_Structural_getRecArgInfo___closed__0;
    v___x_5729_ = l_Lean_stringToMessageData(v___x_5728_);
    return v___x_5729_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5731_ = l_Lean_Elab_Structural_getRecArgInfo___closed__2;
    v___x_5732_ = l_Lean_stringToMessageData(v___x_5731_);
    return v___x_5732_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5734_ = l_Lean_Elab_Structural_getRecArgInfo___closed__4;
    v___x_5735_ = l_Lean_stringToMessageData(v___x_5734_);
    return v___x_5735_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5737_ = l_Lean_Elab_Structural_getRecArgInfo___closed__6;
    v___x_5738_ = leanh::lean_unsigned_to_nat(59);
    v___x_5739_ = leanh::lean_unsigned_to_nat(96);
    v___x_5740_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1;
    v___x_5741_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0;
    v___x_5742_ = l_mkPanicMessageWithDecl(
        v___x_5741_,
        v___x_5740_,
        v___x_5739_,
        v___x_5738_,
        v___x_5737_,
    );
    return v___x_5742_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_5744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5744_ = l_Lean_Elab_Structural_getRecArgInfo___closed__8;
    v___x_5745_ = l_Lean_stringToMessageData(v___x_5744_);
    return v___x_5745_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_5747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5748_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5747_ = l_Lean_Elab_Structural_getRecArgInfo___closed__10;
    v___x_5748_ = l_Lean_stringToMessageData(v___x_5747_);
    return v___x_5748_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_5750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5750_ = l_Lean_Elab_Structural_getRecArgInfo___closed__12;
    v___x_5751_ = l_Lean_stringToMessageData(v___x_5750_);
    return v___x_5751_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15()
-> *mut leanh::LeanObject {
    let mut v___x_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5754_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5753_ = l_Lean_Elab_Structural_getRecArgInfo___closed__14;
    v___x_5754_ = l_Lean_stringToMessageData(v___x_5753_);
    return v___x_5754_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17()
-> *mut leanh::LeanObject {
    let mut v___x_5756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5756_ = l_Lean_Elab_Structural_getRecArgInfo___closed__16;
    v___x_5757_ = l_Lean_stringToMessageData(v___x_5756_);
    return v___x_5757_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19()
-> *mut leanh::LeanObject {
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5759_ = l_Lean_Elab_Structural_getRecArgInfo___closed__18;
    v___x_5760_ = l_Lean_stringToMessageData(v___x_5759_);
    return v___x_5760_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21()
-> *mut leanh::LeanObject {
    let mut v___x_5762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5762_ = l_Lean_Elab_Structural_getRecArgInfo___closed__20;
    v___x_5763_ = l_Lean_stringToMessageData(v___x_5762_);
    return v___x_5763_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23()
-> *mut leanh::LeanObject {
    let mut v___x_5765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5765_ = l_Lean_Elab_Structural_getRecArgInfo___closed__22;
    v___x_5766_ = l_Lean_stringToMessageData(v___x_5765_);
    return v___x_5766_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24()
-> *mut leanh::LeanObject {
    let mut v___x_5767_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5768_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5767_ = leanh::lean_box(0);
    v_dummy_5768_ = l_Lean_Expr_sort___override(v___x_5767_);
    return v_dummy_5768_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26()
-> *mut leanh::LeanObject {
    let mut v___x_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5770_ = l_Lean_Elab_Structural_getRecArgInfo___closed__25;
    v___x_5771_ = l_Lean_stringToMessageData(v___x_5770_);
    return v___x_5771_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28()
-> *mut leanh::LeanObject {
    let mut v___x_5773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5773_ = l_Lean_Elab_Structural_getRecArgInfo___closed__27;
    v___x_5774_ = leanh::lean_unsigned_to_nat(2);
    v___x_5775_ = leanh::lean_unsigned_to_nat(68);
    v___x_5776_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__1;
    v___x_5777_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0;
    v___x_5778_ = l_mkPanicMessageWithDecl(
        v___x_5777_,
        v___x_5776_,
        v___x_5775_,
        v___x_5774_,
        v___x_5773_,
    );
    return v___x_5778_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30()
-> *mut leanh::LeanObject {
    let mut v___x_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5780_ = l_Lean_Elab_Structural_getRecArgInfo___closed__29;
    v___x_5781_ = l_Lean_stringToMessageData(v___x_5780_);
    return v___x_5781_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32()
-> *mut leanh::LeanObject {
    let mut v___x_5783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5784_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5783_ = l_Lean_Elab_Structural_getRecArgInfo___closed__31;
    v___x_5784_ = l_Lean_stringToMessageData(v___x_5783_);
    return v___x_5784_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34()
-> *mut leanh::LeanObject {
    let mut v___x_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5786_ = l_Lean_Elab_Structural_getRecArgInfo___closed__33;
    v___x_5787_ = l_Lean_stringToMessageData(v___x_5786_);
    return v___x_5787_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36()
-> *mut leanh::LeanObject {
    let mut v___x_5789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5789_ = l_Lean_Elab_Structural_getRecArgInfo___closed__35;
    v___x_5790_ = l_Lean_stringToMessageData(v___x_5789_);
    return v___x_5790_;
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfo(
    mut v_fnName_5791_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_5792_: *mut leanh::LeanObject,
    mut v_xs_5793_: *mut leanh::LeanObject,
    mut v_i_5794_: *mut leanh::LeanObject,
    mut v_a_5795_: *mut leanh::LeanObject,
    mut v_a_5796_: *mut leanh::LeanObject,
    mut v_a_5797_: *mut leanh::LeanObject,
    mut v_a_5798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5819_: u8 = 0;
    let mut v_name_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5836_: u8 = 0;
    let mut v_name_5837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5840_: u8 = 0;
    let mut v___x_5841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5844_: usize = 0;
    let mut v___x_5845_: usize = 0;
    let mut v___x_5846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5857_: u8 = 0;
    let mut v_unused_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5865_: u8 = 0;
    let mut v___x_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5882_: u8 = 0;
    let mut v_isSharedCheck_5883_: u8 = 0;
    let mut v_a_5884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5887_: u8 = 0;
    let mut v___x_5889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5891_: u8 = 0;
    let mut v_val_5892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5897_: u8 = 0;
    let mut v_name_5898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5917_: u8 = 0;
    let mut v_a_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5921_: u8 = 0;
    let mut v___x_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5925_: u8 = 0;
    let mut v___y_5927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lower_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upper_5940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5944_: u8 = 0;
    let mut v___x_5945_: usize = 0;
    let mut v___x_5946_: usize = 0;
    let mut v___x_5947_: u8 = 0;
    let mut v_name_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_us_5968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_5970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5971_: u8 = 0;
    let mut v___x_5972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toConstantVal_5975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_numParams_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nargs_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_dummy_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: u8 = 0;
    let mut v_a_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5992_: u8 = 0;
    let mut v___x_5994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5996_: u8 = 0;
    let mut v___y_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6005_: u8 = 0;
    let mut v___x_6006_: u8 = 0;
    let mut v___x_6007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6012_: u8 = 0;
    let mut v___x_6014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6016_: u8 = 0;
    let mut v_a_6017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6020_: u8 = 0;
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6024_: u8 = 0;
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6027_: u8 = 0;
    let mut v___x_6028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6030_: u8 = 0;
    let mut v___x_6031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: u8 = 0;
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6053_: u8 = 0;
    let mut v___x_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6057_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6025_ = lean_array_get_size(v_fixedParamPerm_5792_);
                v___x_6026_ = lean_array_get_size(v_xs_5793_);
                v___x_6027_ = lean_nat_dec_eq(v___x_6025_, v___x_6026_);
                if v___x_6027_ == 0 {
                    leanh::lean_dec(v_i_5794_);
                    leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                    leanh::lean_dec(v_fnName_5791_);
                    v___x_6028_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__28),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfo___closed__28_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfo___closed__28,
                    );
                    v___x_6029_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(
                        v___x_6028_,
                        v_a_5795_,
                        v_a_5796_,
                        v_a_5797_,
                        v_a_5798_,
                    );
                    return v___x_6029_;
                } else {
                    v___x_6030_ = lean_nat_dec_lt(v_i_5794_, v___x_6026_);
                    if v___x_6030_ == 0 {
                        leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                        leanh::lean_dec(v_fnName_5791_);
                        v___x_6031_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__30
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__30_once
                            ),
                            _init_l_Lean_Elab_Structural_getRecArgInfo___closed__30,
                        );
                        v___x_6032_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6033_ = lean_nat_add(v_i_5794_, v___x_6032_);
                        leanh::lean_dec(v_i_5794_);
                        v___x_6034_ = l_Nat_reprFast(v___x_6033_);
                        v___x_6035_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6035_, 0, v___x_6034_);
                        v___x_6036_ = l_Lean_MessageData_ofFormat(v___x_6035_);
                        v___x_6037_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6037_, 0, v___x_6031_);
                        leanh::lean_ctor_set(v___x_6037_, 1, v___x_6036_);
                        v___x_6038_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__32
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__32_once
                            ),
                            _init_l_Lean_Elab_Structural_getRecArgInfo___closed__32,
                        );
                        v___x_6039_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6039_, 0, v___x_6037_);
                        leanh::lean_ctor_set(v___x_6039_, 1, v___x_6038_);
                        v___x_6040_ = l_Nat_reprFast(v___x_6026_);
                        v___x_6041_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6041_, 0, v___x_6040_);
                        v___x_6042_ = l_Lean_MessageData_ofFormat(v___x_6041_);
                        v___x_6043_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6043_, 0, v___x_6039_);
                        leanh::lean_ctor_set(v___x_6043_, 1, v___x_6042_);
                        v___x_6044_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__34
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__34_once
                            ),
                            _init_l_Lean_Elab_Structural_getRecArgInfo___closed__34,
                        );
                        v___x_6045_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6045_, 0, v___x_6043_);
                        leanh::lean_ctor_set(v___x_6045_, 1, v___x_6044_);
                        v___x_6046_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_6045_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_);
                        return v___x_6046_;
                    } else {
                        v___x_6047_ =
                            l_Lean_Elab_FixedParamPerm_isFixed(v_fixedParamPerm_5792_, v_i_5794_);
                        if v___x_6047_ == 0 {
                            v___y_5998_ = v_a_5795_;
                            v___y_5999_ = v_a_5796_;
                            v___y_6000_ = v_a_5797_;
                            v___y_6001_ = v_a_5798_;
                            state = 19;
                            continue;
                        } else {
                            leanh::lean_dec(v_i_5794_);
                            leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                            leanh::lean_dec(v_fnName_5791_);
                            v___x_6048_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_getRecArgInfo___closed__36
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_getRecArgInfo___closed__36_once
                                ),
                                _init_l_Lean_Elab_Structural_getRecArgInfo___closed__36,
                            );
                            v___x_6049_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_6048_, v_a_5795_, v_a_5796_, v_a_5797_, v_a_5798_);
                            v_a_6050_ = leanh::lean_ctor_get(v___x_6049_, 0);
                            v_isSharedCheck_6057_ =
                                (!leanh::lean_is_exclusive(v___x_6049_)) as u8;
                            if v_isSharedCheck_6057_ == 0 {
                                v___x_6052_ = v___x_6049_;
                                v_isShared_6053_ = v_isSharedCheck_6057_;
                                state = 24;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6050_);
                                leanh::lean_dec(v___x_6049_);
                                v___x_6052_ = leanh::lean_box(0);
                                v_isShared_6053_ = v_isSharedCheck_6057_;
                                state = 24;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_5805_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__1),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__1_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__1,
                );
                v___x_5806_ =
                    l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(
                        v___x_5805_,
                        v___y_5801_,
                        v___y_5802_,
                        v___y_5803_,
                        v___y_5804_,
                    );
                return v___x_5806_;
            }
            2 => {
                v___x_5819_ = l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(
                    v___y_5809_,
                );
                if v___x_5819_ == 0 {
                    leanh::lean_dec_ref(v___y_5818_);
                    leanh::lean_dec_ref(v___y_5816_);
                    leanh::lean_dec(v___y_5812_);
                    leanh::lean_dec_ref(v___y_5809_);
                    leanh::lean_dec(v___y_5808_);
                    leanh::lean_dec(v_i_5794_);
                    leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                    leanh::lean_dec(v_fnName_5791_);
                    v_name_5820_ = leanh::lean_ctor_get(v___y_5815_, 0);
                    leanh::lean_inc(v_name_5820_);
                    leanh::lean_dec_ref(v___y_5815_);
                    v___x_5821_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__3),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfo___closed__3_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3,
                    );
                    v___x_5822_ = l_Lean_MessageData_ofName(v_name_5820_);
                    v___x_5823_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5823_, 0, v___x_5821_);
                    leanh::lean_ctor_set(v___x_5823_, 1, v___x_5822_);
                    v___x_5824_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__5),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfo___closed__5_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfo___closed__5,
                    );
                    v___x_5825_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5825_, 0, v___x_5823_);
                    leanh::lean_ctor_set(v___x_5825_, 1, v___x_5824_);
                    v___x_5826_ = l_Lean_indentExpr(v___y_5813_);
                    v___x_5827_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5827_, 0, v___x_5825_);
                    leanh::lean_ctor_set(v___x_5827_, 1, v___x_5826_);
                    v___x_5828_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_5827_, v___y_5810_, v___y_5817_, v___y_5811_, v___y_5814_);
                    return v___x_5828_;
                } else {
                    v___x_5829_ = l_Lean_Elab_FixedParamPerm_pickVarying___redArg(
                        v_fixedParamPerm_5792_,
                        v_xs_5793_,
                    );
                    v___x_5830_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v___x_5829_, v___y_5809_, v___y_5810_, v___y_5817_, v___y_5811_, v___y_5814_);
                    if leanh::lean_obj_tag(v___x_5830_) == 0 {
                        v_a_5831_ = leanh::lean_ctor_get(v___x_5830_, 0);
                        leanh::lean_inc(v_a_5831_);
                        leanh::lean_dec_ref_known(v___x_5830_, 1);
                        if leanh::lean_obj_tag(v_a_5831_) == 0 {
                            v___x_5832_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadParamDep_x3f(v___x_5829_, v___y_5818_, v___y_5810_, v___y_5817_, v___y_5811_, v___y_5814_);
                            leanh::lean_dec_ref(v___x_5829_);
                            if leanh::lean_obj_tag(v___x_5832_) == 0 {
                                v_a_5833_ = leanh::lean_ctor_get(v___x_5832_, 0);
                                v_isSharedCheck_5883_ =
                                    (!leanh::lean_is_exclusive(v___x_5832_)) as u8;
                                if v_isSharedCheck_5883_ == 0 {
                                    v___x_5835_ = v___x_5832_;
                                    v_isShared_5836_ = v_isSharedCheck_5883_;
                                    state = 3;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5833_);
                                    leanh::lean_dec(v___x_5832_);
                                    v___x_5835_ = leanh::lean_box(0);
                                    v_isShared_5836_ = v_isSharedCheck_5883_;
                                    state = 3;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref(v___y_5818_);
                                leanh::lean_dec_ref(v___y_5816_);
                                leanh::lean_dec_ref(v___y_5815_);
                                leanh::lean_dec_ref(v___y_5813_);
                                leanh::lean_dec(v___y_5812_);
                                leanh::lean_dec_ref(v___y_5809_);
                                leanh::lean_dec(v___y_5808_);
                                leanh::lean_dec(v_i_5794_);
                                leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                                leanh::lean_dec(v_fnName_5791_);
                                v_a_5884_ = leanh::lean_ctor_get(v___x_5832_, 0);
                                v_isSharedCheck_5891_ =
                                    (!leanh::lean_is_exclusive(v___x_5832_)) as u8;
                                if v_isSharedCheck_5891_ == 0 {
                                    v___x_5886_ = v___x_5832_;
                                    v_isShared_5887_ = v_isSharedCheck_5891_;
                                    state = 9;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_5884_);
                                    leanh::lean_dec(v___x_5832_);
                                    v___x_5886_ = leanh::lean_box(0);
                                    v_isShared_5887_ = v_isSharedCheck_5891_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            leanh::lean_dec_ref(v___x_5829_);
                            leanh::lean_dec_ref(v___y_5818_);
                            leanh::lean_dec_ref(v___y_5816_);
                            leanh::lean_dec(v___y_5812_);
                            leanh::lean_dec_ref(v___y_5809_);
                            leanh::lean_dec(v___y_5808_);
                            leanh::lean_dec(v_i_5794_);
                            leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                            leanh::lean_dec(v_fnName_5791_);
                            v_val_5892_ = leanh::lean_ctor_get(v_a_5831_, 0);
                            leanh::lean_inc(v_val_5892_);
                            leanh::lean_dec_ref_known(v_a_5831_, 1);
                            v_fst_5893_ = leanh::lean_ctor_get(v_val_5892_, 0);
                            v_snd_5894_ = leanh::lean_ctor_get(v_val_5892_, 1);
                            v_isSharedCheck_5917_ =
                                (!leanh::lean_is_exclusive(v_val_5892_)) as u8;
                            if v_isSharedCheck_5917_ == 0 {
                                v___x_5896_ = v_val_5892_;
                                v_isShared_5897_ = v_isSharedCheck_5917_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_5894_);
                                leanh::lean_inc(v_fst_5893_);
                                leanh::lean_dec(v_val_5892_);
                                v___x_5896_ = leanh::lean_box(0);
                                v_isShared_5897_ = v_isSharedCheck_5917_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5829_);
                        leanh::lean_dec_ref(v___y_5818_);
                        leanh::lean_dec_ref(v___y_5816_);
                        leanh::lean_dec_ref(v___y_5815_);
                        leanh::lean_dec_ref(v___y_5813_);
                        leanh::lean_dec(v___y_5812_);
                        leanh::lean_dec_ref(v___y_5809_);
                        leanh::lean_dec(v___y_5808_);
                        leanh::lean_dec(v_i_5794_);
                        leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                        leanh::lean_dec(v_fnName_5791_);
                        v_a_5918_ = leanh::lean_ctor_get(v___x_5830_, 0);
                        v_isSharedCheck_5925_ =
                            (!leanh::lean_is_exclusive(v___x_5830_)) as u8;
                        if v_isSharedCheck_5925_ == 0 {
                            v___x_5920_ = v___x_5830_;
                            v_isShared_5921_ = v_isSharedCheck_5925_;
                            state = 13;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5918_);
                            leanh::lean_dec(v___x_5830_);
                            v___x_5920_ = leanh::lean_box(0);
                            v_isShared_5921_ = v_isSharedCheck_5925_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_5833_) == 0 {
                    leanh::lean_dec_ref(v___y_5813_);
                    v_name_5837_ = leanh::lean_ctor_get(v___y_5815_, 0);
                    v_isSharedCheck_5857_ = (!leanh::lean_is_exclusive(v___y_5815_)) as u8;
                    if v_isSharedCheck_5857_ == 0 {
                        v_unused_5858_ = leanh::lean_ctor_get(v___y_5815_, 2);
                        leanh::lean_dec(v_unused_5858_);
                        v_unused_5859_ = leanh::lean_ctor_get(v___y_5815_, 1);
                        leanh::lean_dec(v_unused_5859_);
                        v___x_5839_ = v___y_5815_;
                        v_isShared_5840_ = v_isSharedCheck_5857_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_name_5837_);
                        leanh::lean_dec(v___y_5815_);
                        v___x_5839_ = leanh::lean_box(0);
                        v_isShared_5840_ = v_isSharedCheck_5857_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5835_);
                    leanh::lean_dec_ref(v___y_5818_);
                    leanh::lean_dec_ref(v___y_5816_);
                    leanh::lean_dec_ref(v___y_5815_);
                    leanh::lean_dec(v___y_5812_);
                    leanh::lean_dec_ref(v___y_5809_);
                    leanh::lean_dec(v___y_5808_);
                    leanh::lean_dec(v_i_5794_);
                    leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                    leanh::lean_dec(v_fnName_5791_);
                    v_val_5860_ = leanh::lean_ctor_get(v_a_5833_, 0);
                    leanh::lean_inc(v_val_5860_);
                    leanh::lean_dec_ref_known(v_a_5833_, 1);
                    v_fst_5861_ = leanh::lean_ctor_get(v_val_5860_, 0);
                    v_snd_5862_ = leanh::lean_ctor_get(v_val_5860_, 1);
                    v_isSharedCheck_5882_ = (!leanh::lean_is_exclusive(v_val_5860_)) as u8;
                    if v_isSharedCheck_5882_ == 0 {
                        v___x_5864_ = v_val_5860_;
                        v_isShared_5865_ = v_isSharedCheck_5882_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5862_);
                        leanh::lean_inc(v_fst_5861_);
                        leanh::lean_dec(v_val_5860_);
                        v___x_5864_ = leanh::lean_box(0);
                        v_isShared_5865_ = v_isSharedCheck_5882_;
                        state = 7;
                        continue;
                    }
                }
            }
            4 => {
                v___x_5841_ = lean_array_mk(v___y_5812_);
                v___x_5842_ = l_Array_idxOf_x3f___at___00Lean_Elab_Structural_getRecArgInfo_spec__3(
                    v___x_5841_,
                    v_name_5837_,
                );
                leanh::lean_dec(v_name_5837_);
                leanh::lean_dec_ref(v___x_5841_);
                if leanh::lean_obj_tag(v___x_5842_) == 1 {
                    v_val_5843_ = leanh::lean_ctor_get(v___x_5842_, 0);
                    leanh::lean_inc(v_val_5843_);
                    leanh::lean_dec_ref_known(v___x_5842_, 1);
                    v_sz_5844_ = lean_array_size(v___y_5809_);
                    v___x_5845_ = 0usize;
                    v___x_5846_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4(v_xs_5793_, v_sz_5844_, v___x_5845_, v___y_5809_);
                    v___x_5847_ = l_Lean_Elab_Structural_IndGroupInfo_ofInductiveVal(v___y_5816_);
                    if v_isShared_5840_ == 0 {
                        leanh::lean_ctor_set(v___x_5839_, 2, v___y_5818_);
                        leanh::lean_ctor_set(v___x_5839_, 1, v___y_5808_);
                        leanh::lean_ctor_set(v___x_5839_, 0, v___x_5847_);
                        v___x_5849_ = v___x_5839_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5854_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 0, v___x_5847_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 1, v___y_5808_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5854_, 2, v___y_5818_);
                        v___x_5849_ = v_reuseFailAlloc_5854_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_5842_);
                    leanh::lean_del_object(v___x_5839_);
                    leanh::lean_del_object(v___x_5835_);
                    leanh::lean_dec_ref(v___y_5818_);
                    leanh::lean_dec_ref(v___y_5816_);
                    leanh::lean_dec_ref(v___y_5809_);
                    leanh::lean_dec(v___y_5808_);
                    leanh::lean_dec(v_i_5794_);
                    leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                    leanh::lean_dec(v_fnName_5791_);
                    v___x_5855_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__7),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfo___closed__7_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfo___closed__7,
                    );
                    v___x_5856_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__5(
                        v___x_5855_,
                        v___y_5810_,
                        v___y_5817_,
                        v___y_5811_,
                        v___y_5814_,
                    );
                    return v___x_5856_;
                }
            }
            5 => {
                v___x_5850_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                leanh::lean_ctor_set(v___x_5850_, 0, v_fnName_5791_);
                leanh::lean_ctor_set(v___x_5850_, 1, v_fixedParamPerm_5792_);
                leanh::lean_ctor_set(v___x_5850_, 2, v_i_5794_);
                leanh::lean_ctor_set(v___x_5850_, 3, v___x_5846_);
                leanh::lean_ctor_set(v___x_5850_, 4, v___x_5849_);
                leanh::lean_ctor_set(v___x_5850_, 5, v_val_5843_);
                if v_isShared_5836_ == 0 {
                    leanh::lean_ctor_set(v___x_5835_, 0, v___x_5850_);
                    v___x_5852_ = v___x_5835_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_5853_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5853_, 0, v___x_5850_);
                    v___x_5852_ = v_reuseFailAlloc_5853_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_5852_;
            }
            7 => {
                v___x_5866_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__9),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__9_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__9,
                );
                v___x_5867_ = l_Lean_indentExpr(v___y_5813_);
                if v_isShared_5865_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5864_, 7);
                    leanh::lean_ctor_set(v___x_5864_, 1, v___x_5867_);
                    leanh::lean_ctor_set(v___x_5864_, 0, v___x_5866_);
                    v___x_5869_ = v___x_5864_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5881_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5881_, 0, v___x_5866_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5881_, 1, v___x_5867_);
                    v___x_5869_ = v_reuseFailAlloc_5881_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_5870_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__11),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__11_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__11,
                );
                v___x_5871_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5871_, 0, v___x_5869_);
                leanh::lean_ctor_set(v___x_5871_, 1, v___x_5870_);
                v___x_5872_ = l_Lean_indentExpr(v_fst_5861_);
                v___x_5873_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5873_, 0, v___x_5871_);
                leanh::lean_ctor_set(v___x_5873_, 1, v___x_5872_);
                v___x_5874_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__13),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__13_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__13,
                );
                v___x_5875_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5875_, 0, v___x_5873_);
                leanh::lean_ctor_set(v___x_5875_, 1, v___x_5874_);
                v___x_5876_ = l_Lean_indentExpr(v_snd_5862_);
                v___x_5877_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5877_, 0, v___x_5875_);
                leanh::lean_ctor_set(v___x_5877_, 1, v___x_5876_);
                v___x_5878_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__15),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__15_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__15,
                );
                v___x_5879_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5879_, 0, v___x_5877_);
                leanh::lean_ctor_set(v___x_5879_, 1, v___x_5878_);
                v___x_5880_ =
                    l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(
                        v___x_5879_,
                        v___y_5810_,
                        v___y_5817_,
                        v___y_5811_,
                        v___y_5814_,
                    );
                return v___x_5880_;
            }
            9 => {
                if v_isShared_5887_ == 0 {
                    v___x_5889_ = v___x_5886_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5890_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5890_, 0, v_a_5884_);
                    v___x_5889_ = v_reuseFailAlloc_5890_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5889_;
            }
            11 => {
                v_name_5898_ = leanh::lean_ctor_get(v___y_5815_, 0);
                leanh::lean_inc(v_name_5898_);
                leanh::lean_dec_ref(v___y_5815_);
                v___x_5899_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__3),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__3_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3,
                );
                v___x_5900_ = l_Lean_MessageData_ofName(v_name_5898_);
                if v_isShared_5897_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_5896_, 7);
                    leanh::lean_ctor_set(v___x_5896_, 1, v___x_5900_);
                    leanh::lean_ctor_set(v___x_5896_, 0, v___x_5899_);
                    v___x_5902_ = v___x_5896_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_5916_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 0, v___x_5899_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5916_, 1, v___x_5900_);
                    v___x_5902_ = v_reuseFailAlloc_5916_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_5903_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__17),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__17_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__17,
                );
                v___x_5904_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5904_, 0, v___x_5902_);
                leanh::lean_ctor_set(v___x_5904_, 1, v___x_5903_);
                v___x_5905_ = l_Lean_indentExpr(v___y_5813_);
                v___x_5906_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5906_, 0, v___x_5904_);
                leanh::lean_ctor_set(v___x_5906_, 1, v___x_5905_);
                v___x_5907_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__19),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__19_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__19,
                );
                v___x_5908_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5908_, 0, v___x_5906_);
                leanh::lean_ctor_set(v___x_5908_, 1, v___x_5907_);
                v___x_5909_ = l_Lean_indentExpr(v_fst_5893_);
                v___x_5910_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5910_, 0, v___x_5908_);
                leanh::lean_ctor_set(v___x_5910_, 1, v___x_5909_);
                v___x_5911_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__21),
                    core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfo___closed__21_once),
                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__21,
                );
                v___x_5912_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5912_, 0, v___x_5910_);
                leanh::lean_ctor_set(v___x_5912_, 1, v___x_5911_);
                v___x_5913_ = l_Lean_indentExpr(v_snd_5894_);
                v___x_5914_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_5914_, 0, v___x_5912_);
                leanh::lean_ctor_set(v___x_5914_, 1, v___x_5913_);
                v___x_5915_ =
                    l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(
                        v___x_5914_,
                        v___y_5810_,
                        v___y_5817_,
                        v___y_5811_,
                        v___y_5814_,
                    );
                return v___x_5915_;
            }
            13 => {
                if v_isShared_5921_ == 0 {
                    v___x_5923_ = v___x_5920_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_5924_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5924_, 0, v_a_5918_);
                    v___x_5923_ = v_reuseFailAlloc_5924_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_5923_;
            }
            15 => {
                v___x_5941_ =
                    l_Array_toSubarray___redArg(v___y_5928_, v_lower_5939_, v_upper_5940_);
                v___x_5942_ = l_Subarray_copy___redArg(v___x_5941_);
                v___x_5943_ = lean_array_get_size(v___x_5942_);
                v___x_5944_ = lean_nat_dec_lt(v___y_5934_, v___x_5943_);
                leanh::lean_dec(v___y_5934_);
                if v___x_5944_ == 0 {
                    v___y_5808_ = v___y_5927_;
                    v___y_5809_ = v___x_5942_;
                    v___y_5810_ = v___y_5933_;
                    v___y_5811_ = v___y_5929_;
                    v___y_5812_ = v___y_5935_;
                    v___y_5813_ = v___y_5936_;
                    v___y_5814_ = v___y_5937_;
                    v___y_5815_ = v___y_5930_;
                    v___y_5816_ = v___y_5938_;
                    v___y_5817_ = v___y_5931_;
                    v___y_5818_ = v___y_5932_;
                    state = 2;
                    continue;
                } else {
                    if v___x_5944_ == 0 {
                        v___y_5808_ = v___y_5927_;
                        v___y_5809_ = v___x_5942_;
                        v___y_5810_ = v___y_5933_;
                        v___y_5811_ = v___y_5929_;
                        v___y_5812_ = v___y_5935_;
                        v___y_5813_ = v___y_5936_;
                        v___y_5814_ = v___y_5937_;
                        v___y_5815_ = v___y_5930_;
                        v___y_5816_ = v___y_5938_;
                        v___y_5817_ = v___y_5931_;
                        v___y_5818_ = v___y_5932_;
                        state = 2;
                        continue;
                    } else {
                        v___x_5945_ = 0usize;
                        v___x_5946_ = lean_usize_of_nat(v___x_5943_);
                        v___x_5947_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_getRecArgInfo_spec__6(v___x_5942_, v___x_5945_, v___x_5946_);
                        if v___x_5947_ == 0 {
                            v___y_5808_ = v___y_5927_;
                            v___y_5809_ = v___x_5942_;
                            v___y_5810_ = v___y_5933_;
                            v___y_5811_ = v___y_5929_;
                            v___y_5812_ = v___y_5935_;
                            v___y_5813_ = v___y_5936_;
                            v___y_5814_ = v___y_5937_;
                            v___y_5815_ = v___y_5930_;
                            v___y_5816_ = v___y_5938_;
                            v___y_5817_ = v___y_5931_;
                            v___y_5818_ = v___y_5932_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec_ref(v___x_5942_);
                            leanh::lean_dec_ref(v___y_5938_);
                            leanh::lean_dec(v___y_5935_);
                            leanh::lean_dec_ref(v___y_5932_);
                            leanh::lean_dec(v___y_5927_);
                            leanh::lean_dec(v_i_5794_);
                            leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                            leanh::lean_dec(v_fnName_5791_);
                            v_name_5948_ = leanh::lean_ctor_get(v___y_5930_, 0);
                            leanh::lean_inc(v_name_5948_);
                            leanh::lean_dec_ref(v___y_5930_);
                            v___x_5949_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_getRecArgInfo___closed__3
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_getRecArgInfo___closed__3_once
                                ),
                                _init_l_Lean_Elab_Structural_getRecArgInfo___closed__3,
                            );
                            v___x_5950_ = l_Lean_MessageData_ofName(v_name_5948_);
                            v___x_5951_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5951_, 0, v___x_5949_);
                            leanh::lean_ctor_set(v___x_5951_, 1, v___x_5950_);
                            v___x_5952_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_getRecArgInfo___closed__23
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_getRecArgInfo___closed__23_once
                                ),
                                _init_l_Lean_Elab_Structural_getRecArgInfo___closed__23,
                            );
                            v___x_5953_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5953_, 0, v___x_5951_);
                            leanh::lean_ctor_set(v___x_5953_, 1, v___x_5952_);
                            v___x_5954_ = l_Lean_indentExpr(v___y_5936_);
                            v___x_5955_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_5955_, 0, v___x_5953_);
                            leanh::lean_ctor_set(v___x_5955_, 1, v___x_5954_);
                            v___x_5956_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_5955_, v___y_5933_, v___y_5931_, v___y_5929_, v___y_5937_);
                            return v___x_5956_;
                        }
                    }
                }
            }
            16 => {
                v___x_5963_ = l_Lean_LocalDecl_type(v___y_5958_);
                leanh::lean_dec_ref(v___y_5958_);
                v___x_5964_ = l_Lean_Meta_whnfD(
                    v___x_5963_,
                    v___y_5959_,
                    v___y_5960_,
                    v___y_5961_,
                    v___y_5962_,
                );
                if leanh::lean_obj_tag(v___x_5964_) == 0 {
                    v_a_5965_ = leanh::lean_ctor_get(v___x_5964_, 0);
                    leanh::lean_inc(v_a_5965_);
                    leanh::lean_dec_ref_known(v___x_5964_, 1);
                    v___x_5966_ = l_Lean_Expr_getAppFn(v_a_5965_);
                    if leanh::lean_obj_tag(v___x_5966_) == 4 {
                        v_declName_5967_ = leanh::lean_ctor_get(v___x_5966_, 0);
                        leanh::lean_inc(v_declName_5967_);
                        v_us_5968_ = leanh::lean_ctor_get(v___x_5966_, 1);
                        leanh::lean_inc(v_us_5968_);
                        leanh::lean_dec_ref_known(v___x_5966_, 2);
                        v___x_5969_ = lean_st_ref_get(v___y_5962_);
                        v_env_5970_ = leanh::lean_ctor_get(v___x_5969_, 0);
                        leanh::lean_inc_ref(v_env_5970_);
                        leanh::lean_dec(v___x_5969_);
                        v___x_5971_ = 0;
                        v___x_5972_ =
                            l_Lean_Environment_find_x3f(v_env_5970_, v_declName_5967_, v___x_5971_);
                        if leanh::lean_obj_tag(v___x_5972_) == 0 {
                            leanh::lean_dec(v_us_5968_);
                            leanh::lean_dec(v_a_5965_);
                            leanh::lean_dec(v_i_5794_);
                            leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                            leanh::lean_dec(v_fnName_5791_);
                            v___y_5801_ = v___y_5959_;
                            v___y_5802_ = v___y_5960_;
                            v___y_5803_ = v___y_5961_;
                            v___y_5804_ = v___y_5962_;
                            state = 1;
                            continue;
                        } else {
                            v_val_5973_ = leanh::lean_ctor_get(v___x_5972_, 0);
                            leanh::lean_inc(v_val_5973_);
                            leanh::lean_dec_ref_known(v___x_5972_, 1);
                            if leanh::lean_obj_tag(v_val_5973_) == 5 {
                                v_val_5974_ = leanh::lean_ctor_get(v_val_5973_, 0);
                                leanh::lean_inc_ref(v_val_5974_);
                                leanh::lean_dec_ref_known(v_val_5973_, 1);
                                v_toConstantVal_5975_ = leanh::lean_ctor_get(v_val_5974_, 0);
                                leanh::lean_inc_ref(v_toConstantVal_5975_);
                                v_numParams_5976_ = leanh::lean_ctor_get(v_val_5974_, 1);
                                v_all_5977_ = leanh::lean_ctor_get(v_val_5974_, 3);
                                leanh::lean_inc(v_all_5977_);
                                v_nargs_5978_ = l_Lean_Expr_getAppNumArgs(v_a_5965_);
                                v_dummy_5979_ = leanh::lean_obj_once(
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Structural_getRecArgInfo___closed__24
                                    ),
                                    core::ptr::addr_of_mut!(
                                        l_Lean_Elab_Structural_getRecArgInfo___closed__24_once
                                    ),
                                    _init_l_Lean_Elab_Structural_getRecArgInfo___closed__24,
                                );
                                leanh::lean_inc(v_nargs_5978_);
                                v___x_5980_ = lean_mk_array(v_nargs_5978_, v_dummy_5979_);
                                v___x_5981_ = leanh::lean_unsigned_to_nat(1);
                                v___x_5982_ = lean_nat_sub(v_nargs_5978_, v___x_5981_);
                                leanh::lean_dec(v_nargs_5978_);
                                leanh::lean_inc(v_a_5965_);
                                v___x_5983_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(
                                    v_a_5965_,
                                    v___x_5980_,
                                    v___x_5982_,
                                );
                                v___x_5984_ = leanh::lean_unsigned_to_nat(0);
                                leanh::lean_inc(v_numParams_5976_);
                                leanh::lean_inc_ref(v___x_5983_);
                                v___x_5985_ = l_Array_toSubarray___redArg(
                                    v___x_5983_,
                                    v___x_5984_,
                                    v_numParams_5976_,
                                );
                                v___x_5986_ = l_Subarray_copy___redArg(v___x_5985_);
                                v___x_5987_ = lean_array_get_size(v___x_5983_);
                                v___x_5988_ = lean_nat_dec_le(v_numParams_5976_, v___x_5984_);
                                if v___x_5988_ == 0 {
                                    leanh::lean_inc(v_numParams_5976_);
                                    v___y_5927_ = v_us_5968_;
                                    v___y_5928_ = v___x_5983_;
                                    v___y_5929_ = v___y_5961_;
                                    v___y_5930_ = v_toConstantVal_5975_;
                                    v___y_5931_ = v___y_5960_;
                                    v___y_5932_ = v___x_5986_;
                                    v___y_5933_ = v___y_5959_;
                                    v___y_5934_ = v___x_5984_;
                                    v___y_5935_ = v_all_5977_;
                                    v___y_5936_ = v_a_5965_;
                                    v___y_5937_ = v___y_5962_;
                                    v___y_5938_ = v_val_5974_;
                                    v_lower_5939_ = v_numParams_5976_;
                                    v_upper_5940_ = v___x_5987_;
                                    state = 15;
                                    continue;
                                } else {
                                    v___y_5927_ = v_us_5968_;
                                    v___y_5928_ = v___x_5983_;
                                    v___y_5929_ = v___y_5961_;
                                    v___y_5930_ = v_toConstantVal_5975_;
                                    v___y_5931_ = v___y_5960_;
                                    v___y_5932_ = v___x_5986_;
                                    v___y_5933_ = v___y_5959_;
                                    v___y_5934_ = v___x_5984_;
                                    v___y_5935_ = v_all_5977_;
                                    v___y_5936_ = v_a_5965_;
                                    v___y_5937_ = v___y_5962_;
                                    v___y_5938_ = v_val_5974_;
                                    v_lower_5939_ = v___x_5984_;
                                    v_upper_5940_ = v___x_5987_;
                                    state = 15;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec(v_val_5973_);
                                leanh::lean_dec(v_us_5968_);
                                leanh::lean_dec(v_a_5965_);
                                leanh::lean_dec(v_i_5794_);
                                leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                                leanh::lean_dec(v_fnName_5791_);
                                v___y_5801_ = v___y_5959_;
                                v___y_5802_ = v___y_5960_;
                                v___y_5803_ = v___y_5961_;
                                v___y_5804_ = v___y_5962_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_5966_);
                        leanh::lean_dec(v_a_5965_);
                        leanh::lean_dec(v_i_5794_);
                        leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                        leanh::lean_dec(v_fnName_5791_);
                        v___y_5801_ = v___y_5959_;
                        v___y_5802_ = v___y_5960_;
                        v___y_5803_ = v___y_5961_;
                        v___y_5804_ = v___y_5962_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_i_5794_);
                    leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                    leanh::lean_dec(v_fnName_5791_);
                    v_a_5989_ = leanh::lean_ctor_get(v___x_5964_, 0);
                    v_isSharedCheck_5996_ = (!leanh::lean_is_exclusive(v___x_5964_)) as u8;
                    if v_isSharedCheck_5996_ == 0 {
                        v___x_5991_ = v___x_5964_;
                        v_isShared_5992_ = v_isSharedCheck_5996_;
                        state = 17;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5989_);
                        leanh::lean_dec(v___x_5964_);
                        v___x_5991_ = leanh::lean_box(0);
                        v_isShared_5992_ = v_isSharedCheck_5996_;
                        state = 17;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_5992_ == 0 {
                    v___x_5994_ = v___x_5991_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_5995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5995_, 0, v_a_5989_);
                    v___x_5994_ = v_reuseFailAlloc_5995_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_5994_;
            }
            19 => {
                v_x_6002_ = lean_array_fget_borrowed(v_xs_5793_, v_i_5794_);
                v___x_6003_ = l_Lean_Meta_getFVarLocalDecl___redArg(
                    v_x_6002_,
                    v___y_5998_,
                    v___y_6000_,
                    v___y_6001_,
                );
                if leanh::lean_obj_tag(v___x_6003_) == 0 {
                    v_a_6004_ = leanh::lean_ctor_get(v___x_6003_, 0);
                    leanh::lean_inc(v_a_6004_);
                    leanh::lean_dec_ref_known(v___x_6003_, 1);
                    v___x_6005_ = 0;
                    v___x_6006_ = l_Lean_LocalDecl_isLet(v_a_6004_, v___x_6005_);
                    if v___x_6006_ == 0 {
                        v___y_5958_ = v_a_6004_;
                        v___y_5959_ = v___y_5998_;
                        v___y_5960_ = v___y_5999_;
                        v___y_5961_ = v___y_6000_;
                        v___y_5962_ = v___y_6001_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_dec(v_a_6004_);
                        leanh::lean_dec(v_i_5794_);
                        leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                        leanh::lean_dec(v_fnName_5791_);
                        v___x_6007_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__26
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfo___closed__26_once
                            ),
                            _init_l_Lean_Elab_Structural_getRecArgInfo___closed__26,
                        );
                        v___x_6008_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_6007_, v___y_5998_, v___y_5999_, v___y_6000_, v___y_6001_);
                        v_a_6009_ = leanh::lean_ctor_get(v___x_6008_, 0);
                        v_isSharedCheck_6016_ =
                            (!leanh::lean_is_exclusive(v___x_6008_)) as u8;
                        if v_isSharedCheck_6016_ == 0 {
                            v___x_6011_ = v___x_6008_;
                            v_isShared_6012_ = v_isSharedCheck_6016_;
                            state = 20;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6009_);
                            leanh::lean_dec(v___x_6008_);
                            v___x_6011_ = leanh::lean_box(0);
                            v_isShared_6012_ = v_isSharedCheck_6016_;
                            state = 20;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_i_5794_);
                    leanh::lean_dec_ref(v_fixedParamPerm_5792_);
                    leanh::lean_dec(v_fnName_5791_);
                    v_a_6017_ = leanh::lean_ctor_get(v___x_6003_, 0);
                    v_isSharedCheck_6024_ = (!leanh::lean_is_exclusive(v___x_6003_)) as u8;
                    if v_isSharedCheck_6024_ == 0 {
                        v___x_6019_ = v___x_6003_;
                        v_isShared_6020_ = v_isSharedCheck_6024_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6017_);
                        leanh::lean_dec(v___x_6003_);
                        v___x_6019_ = leanh::lean_box(0);
                        v_isShared_6020_ = v_isSharedCheck_6024_;
                        state = 22;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_6012_ == 0 {
                    v___x_6014_ = v___x_6011_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_6015_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6015_, 0, v_a_6009_);
                    v___x_6014_ = v_reuseFailAlloc_6015_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_6014_;
            }
            22 => {
                if v_isShared_6020_ == 0 {
                    v___x_6022_ = v___x_6019_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_6023_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6023_, 0, v_a_6017_);
                    v___x_6022_ = v_reuseFailAlloc_6023_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_6022_;
            }
            24 => {
                if v_isShared_6053_ == 0 {
                    v___x_6055_ = v___x_6052_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_6056_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6056_, 0, v_a_6050_);
                    v___x_6055_ = v_reuseFailAlloc_6056_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_6055_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfo___boxed(
    mut v_fnName_6058_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6059_: *mut leanh::LeanObject,
    mut v_xs_6060_: *mut leanh::LeanObject,
    mut v_i_6061_: *mut leanh::LeanObject,
    mut v_a_6062_: *mut leanh::LeanObject,
    mut v_a_6063_: *mut leanh::LeanObject,
    mut v_a_6064_: *mut leanh::LeanObject,
    mut v_a_6065_: *mut leanh::LeanObject,
    mut v_a_6066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6067_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6067_ = l_Lean_Elab_Structural_getRecArgInfo(
        v_fnName_6058_,
        v_fixedParamPerm_6059_,
        v_xs_6060_,
        v_i_6061_,
        v_a_6062_,
        v_a_6063_,
        v_a_6064_,
        v_a_6065_,
    );
    leanh::lean_dec(v_a_6065_);
    leanh::lean_dec_ref(v_a_6064_);
    leanh::lean_dec(v_a_6063_);
    leanh::lean_dec_ref(v_a_6062_);
    leanh::lean_dec_ref(v_xs_6060_);
    return v_res_6067_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(
    mut v_00_u03b1_6068_: *mut leanh::LeanObject,
    mut v_msg_6069_: *mut leanh::LeanObject,
    mut v___y_6070_: *mut leanh::LeanObject,
    mut v___y_6071_: *mut leanh::LeanObject,
    mut v___y_6072_: *mut leanh::LeanObject,
    mut v___y_6073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6075_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(
        v_msg_6069_,
        v___y_6070_,
        v___y_6071_,
        v___y_6072_,
        v___y_6073_,
    );
    return v___x_6075_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___boxed(
    mut v_00_u03b1_6076_: *mut leanh::LeanObject,
    mut v_msg_6077_: *mut leanh::LeanObject,
    mut v___y_6078_: *mut leanh::LeanObject,
    mut v___y_6079_: *mut leanh::LeanObject,
    mut v___y_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
    mut v___y_6082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6083_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0(
        v_00_u03b1_6076_,
        v_msg_6077_,
        v___y_6078_,
        v___y_6079_,
        v___y_6080_,
        v___y_6081_,
    );
    leanh::lean_dec(v___y_6081_);
    leanh::lean_dec_ref(v___y_6080_);
    leanh::lean_dec(v___y_6079_);
    leanh::lean_dec_ref(v___y_6078_);
    return v_res_6083_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(
    mut v_as_6084_: *mut leanh::LeanObject,
    mut v_a_6085_: *mut leanh::LeanObject,
    mut v_x_6086_: *mut leanh::LeanObject,
    mut v_x_6087_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6088_: u8 = 0;
    v___x_6088_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___redArg(v_as_6084_, v_a_6085_, v_x_6086_);
    return v___x_6088_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4___boxed(
    mut v_as_6089_: *mut leanh::LeanObject,
    mut v_a_6090_: *mut leanh::LeanObject,
    mut v_x_6091_: *mut leanh::LeanObject,
    mut v_x_6092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6093_: u8 = 0;
    let mut v_r_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6093_ = l___private_Init_Data_Array_Basic_0__Array_allDiffAuxAux___at___00__private_Init_Data_Array_Basic_0__Array_allDiffAux___at___00Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2_spec__2_spec__4(v_as_6089_, v_a_6090_, v_x_6091_, v_x_6092_);
    leanh::lean_dec_ref(v_a_6090_);
    leanh::lean_dec_ref(v_as_6089_);
    v_r_6094_ = leanh::lean_box((v_res_6093_) as usize);
    return v_r_6094_;
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfos___lam__0(
    mut v___x_6095_: *mut leanh::LeanObject,
    mut v_e_6096_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6097_ = l_Lean_indentD(v_e_6096_);
    v___x_6098_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6098_, 0, v___x_6095_);
    leanh::lean_ctor_set(v___x_6098_, 1, v___x_6097_);
    return v___x_6098_;
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfos___lam__1(
    mut v_val_6099_: *mut leanh::LeanObject,
    mut v_fnName_6100_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6101_: *mut leanh::LeanObject,
    mut v_args_6102_: *mut leanh::LeanObject,
    mut v___y_6103_: *mut leanh::LeanObject,
    mut v___y_6104_: *mut leanh::LeanObject,
    mut v___y_6105_: *mut leanh::LeanObject,
    mut v___y_6106_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6114_: u8 = 0;
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6118_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6108_ = l_Lean_Elab_TerminationMeasure_structuralArg(
                    v_val_6099_,
                    v___y_6103_,
                    v___y_6104_,
                    v___y_6105_,
                    v___y_6106_,
                );
                if leanh::lean_obj_tag(v___x_6108_) == 0 {
                    v_a_6109_ = leanh::lean_ctor_get(v___x_6108_, 0);
                    leanh::lean_inc(v_a_6109_);
                    leanh::lean_dec_ref_known(v___x_6108_, 1);
                    v___x_6110_ = l_Lean_Elab_Structural_getRecArgInfo(
                        v_fnName_6100_,
                        v_fixedParamPerm_6101_,
                        v_args_6102_,
                        v_a_6109_,
                        v___y_6103_,
                        v___y_6104_,
                        v___y_6105_,
                        v___y_6106_,
                    );
                    return v___x_6110_;
                } else {
                    leanh::lean_dec_ref(v_fixedParamPerm_6101_);
                    leanh::lean_dec(v_fnName_6100_);
                    v_a_6111_ = leanh::lean_ctor_get(v___x_6108_, 0);
                    v_isSharedCheck_6118_ = (!leanh::lean_is_exclusive(v___x_6108_)) as u8;
                    if v_isSharedCheck_6118_ == 0 {
                        v___x_6113_ = v___x_6108_;
                        v_isShared_6114_ = v_isSharedCheck_6118_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6111_);
                        leanh::lean_dec(v___x_6108_);
                        v___x_6113_ = leanh::lean_box(0);
                        v_isShared_6114_ = v_isSharedCheck_6118_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_6114_ == 0 {
                    v___x_6116_ = v___x_6113_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6117_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6117_, 0, v_a_6111_);
                    v___x_6116_ = v_reuseFailAlloc_6117_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6116_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed(
    mut v_val_6119_: *mut leanh::LeanObject,
    mut v_fnName_6120_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6121_: *mut leanh::LeanObject,
    mut v_args_6122_: *mut leanh::LeanObject,
    mut v___y_6123_: *mut leanh::LeanObject,
    mut v___y_6124_: *mut leanh::LeanObject,
    mut v___y_6125_: *mut leanh::LeanObject,
    mut v___y_6126_: *mut leanh::LeanObject,
    mut v___y_6127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6128_ = l_Lean_Elab_Structural_getRecArgInfos___lam__1(
        v_val_6119_,
        v_fnName_6120_,
        v_fixedParamPerm_6121_,
        v_args_6122_,
        v___y_6123_,
        v___y_6124_,
        v___y_6125_,
        v___y_6126_,
    );
    leanh::lean_dec(v___y_6126_);
    leanh::lean_dec_ref(v___y_6125_);
    leanh::lean_dec(v___y_6124_);
    leanh::lean_dec_ref(v___y_6123_);
    leanh::lean_dec_ref(v_args_6122_);
    return v_res_6128_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6130_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__0;
    v___x_6131_ = l_Lean_stringToMessageData(v___x_6130_);
    return v___x_6131_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6133_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__2;
    v___x_6134_ = l_Lean_stringToMessageData(v___x_6133_);
    return v___x_6134_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_6138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6138_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__5;
    v___x_6139_ = l_Lean_MessageData_ofFormat(v___x_6138_);
    return v___x_6139_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(
    mut v_upperBound_6140_: *mut leanh::LeanObject,
    mut v_fnName_6141_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6142_: *mut leanh::LeanObject,
    mut v_args_6143_: *mut leanh::LeanObject,
    mut v_a_6144_: *mut leanh::LeanObject,
    mut v_b_6145_: *mut leanh::LeanObject,
    mut v___y_6146_: *mut leanh::LeanObject,
    mut v___y_6147_: *mut leanh::LeanObject,
    mut v___y_6148_: *mut leanh::LeanObject,
    mut v___y_6149_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6158_: u8 = 0;
    let mut v___x_6159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6164_: u8 = 0;
    let mut v___x_6165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6171_: u8 = 0;
    let mut v___y_6173_: u8 = 0;
    let mut v___x_6174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6195_: u8 = 0;
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6199_: u8 = 0;
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6203_: u8 = 0;
    let mut v___x_6204_: u8 = 0;
    let mut v_isSharedCheck_6205_: u8 = 0;
    let mut v_isSharedCheck_6206_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6158_ = lean_nat_dec_lt(v_a_6144_, v_upperBound_6140_);
                if v___x_6158_ == 0 {
                    leanh::lean_dec(v_a_6144_);
                    leanh::lean_dec_ref(v_fixedParamPerm_6142_);
                    leanh::lean_dec(v_fnName_6141_);
                    v___x_6159_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6159_, 0, v_b_6145_);
                    return v___x_6159_;
                } else {
                    v_fst_6160_ = leanh::lean_ctor_get(v_b_6145_, 0);
                    v_snd_6161_ = leanh::lean_ctor_get(v_b_6145_, 1);
                    v_isSharedCheck_6206_ = (!leanh::lean_is_exclusive(v_b_6145_)) as u8;
                    if v_isSharedCheck_6206_ == 0 {
                        v___x_6163_ = v_b_6145_;
                        v_isShared_6164_ = v_isSharedCheck_6206_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6161_);
                        leanh::lean_inc(v_fst_6160_);
                        leanh::lean_dec(v_b_6145_);
                        v___x_6163_ = leanh::lean_box(0);
                        v_isShared_6164_ = v_isSharedCheck_6206_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6154_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6154_, 0, v_fst_6152_);
                leanh::lean_ctor_set(v___x_6154_, 1, v_snd_6153_);
                v___x_6155_ = leanh::lean_unsigned_to_nat(1);
                v___x_6156_ = lean_nat_add(v_a_6144_, v___x_6155_);
                leanh::lean_dec(v_a_6144_);
                v_a_6144_ = v___x_6156_;
                v_b_6145_ = v___x_6154_;
                state = 0;
                continue;
            }
            2 => {
                leanh::lean_inc(v_a_6144_);
                leanh::lean_inc_ref(v_fixedParamPerm_6142_);
                leanh::lean_inc(v_fnName_6141_);
                v___x_6165_ = l_Lean_Elab_Structural_getRecArgInfo(
                    v_fnName_6141_,
                    v_fixedParamPerm_6142_,
                    v_args_6143_,
                    v_a_6144_,
                    v___y_6146_,
                    v___y_6147_,
                    v___y_6148_,
                    v___y_6149_,
                );
                if leanh::lean_obj_tag(v___x_6165_) == 0 {
                    leanh::lean_del_object(v___x_6163_);
                    v_a_6166_ = leanh::lean_ctor_get(v___x_6165_, 0);
                    leanh::lean_inc(v_a_6166_);
                    leanh::lean_dec_ref_known(v___x_6165_, 1);
                    v___x_6167_ = lean_array_push(v_fst_6160_, v_a_6166_);
                    v_fst_6152_ = v___x_6167_;
                    v_snd_6153_ = v_snd_6161_;
                    state = 1;
                    continue;
                } else {
                    v_a_6168_ = leanh::lean_ctor_get(v___x_6165_, 0);
                    v_isSharedCheck_6205_ = (!leanh::lean_is_exclusive(v___x_6165_)) as u8;
                    if v_isSharedCheck_6205_ == 0 {
                        v___x_6170_ = v___x_6165_;
                        v_isShared_6171_ = v_isSharedCheck_6205_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6168_);
                        leanh::lean_dec(v___x_6165_);
                        v___x_6170_ = leanh::lean_box(0);
                        v_isShared_6171_ = v_isSharedCheck_6205_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                v___x_6203_ = l_Lean_Exception_isInterrupt(v_a_6168_);
                if v___x_6203_ == 0 {
                    leanh::lean_inc(v_a_6168_);
                    v___x_6204_ = l_Lean_Exception_isRuntime(v_a_6168_);
                    v___y_6173_ = v___x_6204_;
                    state = 4;
                    continue;
                } else {
                    v___y_6173_ = v___x_6203_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v___y_6173_ == 0 {
                    leanh::lean_del_object(v___x_6170_);
                    v___x_6174_ = l_Lean_Elab_Structural_prettyParam(
                        v_args_6143_,
                        v_a_6144_,
                        v___y_6146_,
                        v___y_6147_,
                        v___y_6148_,
                        v___y_6149_,
                    );
                    if leanh::lean_obj_tag(v___x_6174_) == 0 {
                        v_a_6175_ = leanh::lean_ctor_get(v___x_6174_, 0);
                        leanh::lean_inc(v_a_6175_);
                        leanh::lean_dec_ref_known(v___x_6174_, 1);
                        v___x_6176_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__1);
                        if v_isShared_6164_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_6163_, 7);
                            leanh::lean_ctor_set(v___x_6163_, 1, v_a_6175_);
                            leanh::lean_ctor_set(v___x_6163_, 0, v___x_6176_);
                            v___x_6178_ = v___x_6163_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_6191_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6191_, 0, v___x_6176_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_6191_, 1, v_a_6175_);
                            v___x_6178_ = v_reuseFailAlloc_6191_;
                            state = 5;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6168_);
                        leanh::lean_del_object(v___x_6163_);
                        leanh::lean_dec(v_snd_6161_);
                        leanh::lean_dec(v_fst_6160_);
                        leanh::lean_dec(v_a_6144_);
                        leanh::lean_dec_ref(v_fixedParamPerm_6142_);
                        leanh::lean_dec(v_fnName_6141_);
                        v_a_6192_ = leanh::lean_ctor_get(v___x_6174_, 0);
                        v_isSharedCheck_6199_ =
                            (!leanh::lean_is_exclusive(v___x_6174_)) as u8;
                        if v_isSharedCheck_6199_ == 0 {
                            v___x_6194_ = v___x_6174_;
                            v_isShared_6195_ = v_isSharedCheck_6199_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6192_);
                            leanh::lean_dec(v___x_6174_);
                            v___x_6194_ = leanh::lean_box(0);
                            v_isShared_6195_ = v_isSharedCheck_6199_;
                            state = 6;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_6163_);
                    leanh::lean_dec(v_snd_6161_);
                    leanh::lean_dec(v_fst_6160_);
                    leanh::lean_dec(v_a_6144_);
                    leanh::lean_dec_ref(v_fixedParamPerm_6142_);
                    leanh::lean_dec(v_fnName_6141_);
                    if v_isShared_6171_ == 0 {
                        v___x_6201_ = v___x_6170_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6202_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6202_, 0, v_a_6168_);
                        v___x_6201_ = v_reuseFailAlloc_6202_;
                        state = 8;
                        continue;
                    }
                }
            }
            5 => {
                v___x_6179_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_prettyParameterSet_spec__0___closed__1);
                v___x_6180_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6180_, 0, v___x_6178_);
                leanh::lean_ctor_set(v___x_6180_, 1, v___x_6179_);
                leanh::lean_inc(v_fnName_6141_);
                v___x_6181_ = l_Lean_MessageData_ofName(v_fnName_6141_);
                v___x_6182_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6182_, 0, v___x_6180_);
                leanh::lean_ctor_set(v___x_6182_, 1, v___x_6181_);
                v___x_6183_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
                v___x_6184_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6184_, 0, v___x_6182_);
                leanh::lean_ctor_set(v___x_6184_, 1, v___x_6183_);
                v___x_6185_ = l_Lean_Exception_toMessageData(v_a_6168_);
                v___x_6186_ = l_Lean_indentD(v___x_6185_);
                v___x_6187_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6187_, 0, v___x_6184_);
                leanh::lean_ctor_set(v___x_6187_, 1, v___x_6186_);
                v___x_6188_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6188_, 0, v_snd_6161_);
                leanh::lean_ctor_set(v___x_6188_, 1, v___x_6187_);
                v___x_6189_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__6);
                v___x_6190_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6190_, 0, v___x_6188_);
                leanh::lean_ctor_set(v___x_6190_, 1, v___x_6189_);
                v_fst_6152_ = v_fst_6160_;
                v_snd_6153_ = v___x_6190_;
                state = 1;
                continue;
            }
            6 => {
                if v_isShared_6195_ == 0 {
                    v___x_6197_ = v___x_6194_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6198_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6198_, 0, v_a_6192_);
                    v___x_6197_ = v_reuseFailAlloc_6198_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6197_;
            }
            8 => {
                return v___x_6201_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___boxed(
    mut v_upperBound_6207_: *mut leanh::LeanObject,
    mut v_fnName_6208_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6209_: *mut leanh::LeanObject,
    mut v_args_6210_: *mut leanh::LeanObject,
    mut v_a_6211_: *mut leanh::LeanObject,
    mut v_b_6212_: *mut leanh::LeanObject,
    mut v___y_6213_: *mut leanh::LeanObject,
    mut v___y_6214_: *mut leanh::LeanObject,
    mut v___y_6215_: *mut leanh::LeanObject,
    mut v___y_6216_: *mut leanh::LeanObject,
    mut v___y_6217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6218_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6218_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(
            v_upperBound_6207_,
            v_fnName_6208_,
            v_fixedParamPerm_6209_,
            v_args_6210_,
            v_a_6211_,
            v_b_6212_,
            v___y_6213_,
            v___y_6214_,
            v___y_6215_,
            v___y_6216_,
        );
    leanh::lean_dec(v___y_6216_);
    leanh::lean_dec_ref(v___y_6215_);
    leanh::lean_dec(v___y_6214_);
    leanh::lean_dec_ref(v___y_6213_);
    leanh::lean_dec_ref(v_args_6210_);
    leanh::lean_dec(v_upperBound_6207_);
    return v_res_6218_;
}
pub unsafe fn _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0()
-> f64 {
    let mut v___x_6219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6220_: f64 = 0.0;
    v___x_6219_ = leanh::lean_unsigned_to_nat(0);
    v___x_6220_ = lean_float_of_nat(v___x_6219_);
    return v___x_6220_;
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(
    mut v_cls_6222_: *mut leanh::LeanObject,
    mut v_msg_6223_: *mut leanh::LeanObject,
    mut v___y_6224_: *mut leanh::LeanObject,
    mut v___y_6225_: *mut leanh::LeanObject,
    mut v___y_6226_: *mut leanh::LeanObject,
    mut v___y_6227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6234_: u8 = 0;
    let mut v___x_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6247_: u8 = 0;
    let mut v_tid_6248_: u64 = 0;
    let mut v_traces_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6252_: u8 = 0;
    let mut v___x_6253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6254_: f64 = 0.0;
    let mut v___x_6255_: u8 = 0;
    let mut v___x_6256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6273_: u8 = 0;
    let mut v_isSharedCheck_6274_: u8 = 0;
    let mut v_isSharedCheck_6275_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6229_ = leanh::lean_ctor_get(v___y_6226_, 5);
                v___x_6230_ =
                    l_Lean_addMessageContextFull___at___00Lean_Elab_Structural_prettyParam_spec__0(
                        v_msg_6223_,
                        v___y_6224_,
                        v___y_6225_,
                        v___y_6226_,
                        v___y_6227_,
                    );
                v_a_6231_ = leanh::lean_ctor_get(v___x_6230_, 0);
                v_isSharedCheck_6275_ = (!leanh::lean_is_exclusive(v___x_6230_)) as u8;
                if v_isSharedCheck_6275_ == 0 {
                    v___x_6233_ = v___x_6230_;
                    v_isShared_6234_ = v_isSharedCheck_6275_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6231_);
                    leanh::lean_dec(v___x_6230_);
                    v___x_6233_ = leanh::lean_box(0);
                    v_isShared_6234_ = v_isSharedCheck_6275_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6235_ = lean_st_ref_take(v___y_6227_);
                v_traceState_6236_ = leanh::lean_ctor_get(v___x_6235_, 4);
                v_env_6237_ = leanh::lean_ctor_get(v___x_6235_, 0);
                v_nextMacroScope_6238_ = leanh::lean_ctor_get(v___x_6235_, 1);
                v_ngen_6239_ = leanh::lean_ctor_get(v___x_6235_, 2);
                v_auxDeclNGen_6240_ = leanh::lean_ctor_get(v___x_6235_, 3);
                v_cache_6241_ = leanh::lean_ctor_get(v___x_6235_, 5);
                v_messages_6242_ = leanh::lean_ctor_get(v___x_6235_, 6);
                v_infoState_6243_ = leanh::lean_ctor_get(v___x_6235_, 7);
                v_snapshotTasks_6244_ = leanh::lean_ctor_get(v___x_6235_, 8);
                v_isSharedCheck_6274_ = (!leanh::lean_is_exclusive(v___x_6235_)) as u8;
                if v_isSharedCheck_6274_ == 0 {
                    v___x_6246_ = v___x_6235_;
                    v_isShared_6247_ = v_isSharedCheck_6274_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6244_);
                    leanh::lean_inc(v_infoState_6243_);
                    leanh::lean_inc(v_messages_6242_);
                    leanh::lean_inc(v_cache_6241_);
                    leanh::lean_inc(v_traceState_6236_);
                    leanh::lean_inc(v_auxDeclNGen_6240_);
                    leanh::lean_inc(v_ngen_6239_);
                    leanh::lean_inc(v_nextMacroScope_6238_);
                    leanh::lean_inc(v_env_6237_);
                    leanh::lean_dec(v___x_6235_);
                    v___x_6246_ = leanh::lean_box(0);
                    v_isShared_6247_ = v_isSharedCheck_6274_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_6248_ = leanh::lean_ctor_get_uint64(
                    v_traceState_6236_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_6249_ = leanh::lean_ctor_get(v_traceState_6236_, 0);
                v_isSharedCheck_6273_ =
                    (!leanh::lean_is_exclusive(v_traceState_6236_)) as u8;
                if v_isSharedCheck_6273_ == 0 {
                    v___x_6251_ = v_traceState_6236_;
                    v_isShared_6252_ = v_isSharedCheck_6273_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_6249_);
                    leanh::lean_dec(v_traceState_6236_);
                    v___x_6251_ = leanh::lean_box(0);
                    v_isShared_6252_ = v_isSharedCheck_6273_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6253_ = leanh::lean_box(0);
                v___x_6254_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0_once), _init_l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__0);
                v___x_6255_ = 0;
                v___x_6256_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1;
                v___x_6257_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v___x_6257_, 0, v_cls_6222_);
                leanh::lean_ctor_set(v___x_6257_, 1, v___x_6253_);
                leanh::lean_ctor_set(v___x_6257_, 2, v___x_6256_);
                leanh::lean_ctor_set_float(
                    v___x_6257_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_6254_,
                );
                leanh::lean_ctor_set_float(
                    v___x_6257_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_6254_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_6257_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v___x_6255_,
                );
                v___x_6258_ = l_Lean_Elab_Structural_prettyParameterSet___closed__0;
                v___x_6259_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6259_, 0, v___x_6257_);
                leanh::lean_ctor_set(v___x_6259_, 1, v_a_6231_);
                leanh::lean_ctor_set(v___x_6259_, 2, v___x_6258_);
                leanh::lean_inc(v_ref_6229_);
                v___x_6260_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6260_, 0, v_ref_6229_);
                leanh::lean_ctor_set(v___x_6260_, 1, v___x_6259_);
                v___x_6261_ = l_Lean_PersistentArray_push___redArg(v_traces_6249_, v___x_6260_);
                if v_isShared_6252_ == 0 {
                    leanh::lean_ctor_set(v___x_6251_, 0, v___x_6261_);
                    v___x_6263_ = v___x_6251_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6272_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6272_, 0, v___x_6261_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_6272_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_6248_,
                    );
                    v___x_6263_ = v_reuseFailAlloc_6272_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6247_ == 0 {
                    leanh::lean_ctor_set(v___x_6246_, 4, v___x_6263_);
                    v___x_6265_ = v___x_6246_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6271_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 0, v_env_6237_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 1, v_nextMacroScope_6238_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 2, v_ngen_6239_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 3, v_auxDeclNGen_6240_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 4, v___x_6263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 5, v_cache_6241_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 6, v_messages_6242_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 7, v_infoState_6243_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 8, v_snapshotTasks_6244_);
                    v___x_6265_ = v_reuseFailAlloc_6271_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_6266_ = lean_st_ref_set(v___y_6227_, v___x_6265_);
                v___x_6267_ = leanh::lean_box(0);
                if v_isShared_6234_ == 0 {
                    leanh::lean_ctor_set(v___x_6233_, 0, v___x_6267_);
                    v___x_6269_ = v___x_6233_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6270_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6270_, 0, v___x_6267_);
                    v___x_6269_ = v_reuseFailAlloc_6270_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6269_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___boxed(
    mut v_cls_6276_: *mut leanh::LeanObject,
    mut v_msg_6277_: *mut leanh::LeanObject,
    mut v___y_6278_: *mut leanh::LeanObject,
    mut v___y_6279_: *mut leanh::LeanObject,
    mut v___y_6280_: *mut leanh::LeanObject,
    mut v___y_6281_: *mut leanh::LeanObject,
    mut v___y_6282_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6283_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(
        v_cls_6276_,
        v_msg_6277_,
        v___y_6278_,
        v___y_6279_,
        v___y_6280_,
        v___y_6281_,
    );
    leanh::lean_dec(v___y_6281_);
    leanh::lean_dec_ref(v___y_6280_);
    leanh::lean_dec(v___y_6279_);
    leanh::lean_dec_ref(v___y_6278_);
    return v_res_6283_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6285_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__0;
    v___x_6286_ = l_Lean_stringToMessageData(v___x_6285_);
    return v___x_6286_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6287_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1_once),
        _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__1,
    );
    v___f_6288_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Structural_getRecArgInfos___lam__0 as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6288_, 0, v___x_6287_);
    return v___f_6288_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6289_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0___closed__1;
    v___x_6290_ = l_Lean_stringToMessageData(v___x_6289_);
    return v___x_6290_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5()
-> *mut leanh::LeanObject {
    let mut v_report_6293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgInfos_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_report_6293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once),
        _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3,
    );
    v_recArgInfos_6294_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4;
    v___x_6295_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6295_, 0, v_recArgInfos_6294_);
    leanh::lean_ctor_set(v___x_6295_, 1, v_report_6293_);
    return v___x_6295_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_6306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6306_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9;
    v___x_6307_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__11;
    v___x_6308_ = l_Lean_Name_append(v___x_6307_, v___x_6306_);
    return v___x_6308_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14()
-> *mut leanh::LeanObject {
    let mut v___x_6310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6310_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__13;
    v___x_6311_ = l_Lean_stringToMessageData(v___x_6310_);
    return v___x_6311_;
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfos___lam__2(
    mut v_termMeasure_x3f_6312_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6313_: *mut leanh::LeanObject,
    mut v_xs_6314_: *mut leanh::LeanObject,
    mut v_fnName_6315_: *mut leanh::LeanObject,
    mut v_ys_6316_: *mut leanh::LeanObject,
    mut v_x_6317_: *mut leanh::LeanObject,
    mut v___y_6318_: *mut leanh::LeanObject,
    mut v___y_6319_: *mut leanh::LeanObject,
    mut v___y_6320_: *mut leanh::LeanObject,
    mut v___y_6321_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_val_6323_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileName_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_6326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_6334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_6337_: u8 = 0;
    let mut v_cancelTk_x3f_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_6339_: u8 = 0;
    let mut v_inheritedTraceOptions_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_args_6342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6350_: u8 = 0;
    let mut v___x_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6359_: u8 = 0;
    let mut v_a_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6363_: u8 = 0;
    let mut v___x_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6367_: u8 = 0;
    let mut v_args_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6376_: u8 = 0;
    let mut v_fst_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6381_: u8 = 0;
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_6390_: u8 = 0;
    let mut v_inheritedTraceOptions_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6394_: u8 = 0;
    let mut v___x_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6401_: u8 = 0;
    let mut v___x_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6405_: u8 = 0;
    let mut v_isSharedCheck_6406_: u8 = 0;
    let mut v_isSharedCheck_6407_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_termMeasure_x3f_6312_) == 1 {
                    v_val_6323_ = leanh::lean_ctor_get(v_termMeasure_x3f_6312_, 0);
                    leanh::lean_inc(v_val_6323_);
                    leanh::lean_dec_ref_known(v_termMeasure_x3f_6312_, 1);
                    v_ref_6324_ = leanh::lean_ctor_get(v_val_6323_, 0);
                    leanh::lean_inc(v_ref_6324_);
                    v_fileName_6325_ = leanh::lean_ctor_get(v___y_6320_, 0);
                    v_fileMap_6326_ = leanh::lean_ctor_get(v___y_6320_, 1);
                    v_options_6327_ = leanh::lean_ctor_get(v___y_6320_, 2);
                    v_currRecDepth_6328_ = leanh::lean_ctor_get(v___y_6320_, 3);
                    v_maxRecDepth_6329_ = leanh::lean_ctor_get(v___y_6320_, 4);
                    v_ref_6330_ = leanh::lean_ctor_get(v___y_6320_, 5);
                    v_currNamespace_6331_ = leanh::lean_ctor_get(v___y_6320_, 6);
                    v_openDecls_6332_ = leanh::lean_ctor_get(v___y_6320_, 7);
                    v_initHeartbeats_6333_ = leanh::lean_ctor_get(v___y_6320_, 8);
                    v_maxHeartbeats_6334_ = leanh::lean_ctor_get(v___y_6320_, 9);
                    v_quotContext_6335_ = leanh::lean_ctor_get(v___y_6320_, 10);
                    v_currMacroScope_6336_ = leanh::lean_ctor_get(v___y_6320_, 11);
                    v_diag_6337_ = leanh::lean_ctor_get_uint8(
                        v___y_6320_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    );
                    v_cancelTk_x3f_6338_ = leanh::lean_ctor_get(v___y_6320_, 12);
                    v_suppressElabErrors_6339_ = leanh::lean_ctor_get_uint8(
                        v___y_6320_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    );
                    v_inheritedTraceOptions_6340_ = leanh::lean_ctor_get(v___y_6320_, 13);
                    v___f_6341_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__2,
                    );
                    leanh::lean_inc_ref(v_fixedParamPerm_6313_);
                    v_args_6342_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(
                        v_fixedParamPerm_6313_,
                        v_xs_6314_,
                        v_ys_6316_,
                    );
                    v___f_6343_ = leanh::lean_alloc_closure(
                        l_Lean_Elab_Structural_getRecArgInfos___lam__1___boxed
                            as *mut core::ffi::c_void,
                        9,
                        4,
                    );
                    leanh::lean_closure_set(v___f_6343_, 0, v_val_6323_);
                    leanh::lean_closure_set(v___f_6343_, 1, v_fnName_6315_);
                    leanh::lean_closure_set(v___f_6343_, 2, v_fixedParamPerm_6313_);
                    leanh::lean_closure_set(v___f_6343_, 3, v_args_6342_);
                    v_ref_6344_ = l_Lean_replaceRef(v_ref_6324_, v_ref_6330_);
                    leanh::lean_dec(v_ref_6324_);
                    leanh::lean_inc_ref(v_inheritedTraceOptions_6340_);
                    leanh::lean_inc(v_cancelTk_x3f_6338_);
                    leanh::lean_inc(v_currMacroScope_6336_);
                    leanh::lean_inc(v_quotContext_6335_);
                    leanh::lean_inc(v_maxHeartbeats_6334_);
                    leanh::lean_inc(v_initHeartbeats_6333_);
                    leanh::lean_inc(v_openDecls_6332_);
                    leanh::lean_inc(v_currNamespace_6331_);
                    leanh::lean_inc(v_maxRecDepth_6329_);
                    leanh::lean_inc(v_currRecDepth_6328_);
                    leanh::lean_inc_ref(v_options_6327_);
                    leanh::lean_inc_ref(v_fileMap_6326_);
                    leanh::lean_inc_ref(v_fileName_6325_);
                    v___x_6345_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                    leanh::lean_ctor_set(v___x_6345_, 0, v_fileName_6325_);
                    leanh::lean_ctor_set(v___x_6345_, 1, v_fileMap_6326_);
                    leanh::lean_ctor_set(v___x_6345_, 2, v_options_6327_);
                    leanh::lean_ctor_set(v___x_6345_, 3, v_currRecDepth_6328_);
                    leanh::lean_ctor_set(v___x_6345_, 4, v_maxRecDepth_6329_);
                    leanh::lean_ctor_set(v___x_6345_, 5, v_ref_6344_);
                    leanh::lean_ctor_set(v___x_6345_, 6, v_currNamespace_6331_);
                    leanh::lean_ctor_set(v___x_6345_, 7, v_openDecls_6332_);
                    leanh::lean_ctor_set(v___x_6345_, 8, v_initHeartbeats_6333_);
                    leanh::lean_ctor_set(v___x_6345_, 9, v_maxHeartbeats_6334_);
                    leanh::lean_ctor_set(v___x_6345_, 10, v_quotContext_6335_);
                    leanh::lean_ctor_set(v___x_6345_, 11, v_currMacroScope_6336_);
                    leanh::lean_ctor_set(v___x_6345_, 12, v_cancelTk_x3f_6338_);
                    leanh::lean_ctor_set(v___x_6345_, 13, v_inheritedTraceOptions_6340_);
                    leanh::lean_ctor_set_uint8(
                        v___x_6345_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                        v_diag_6337_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v___x_6345_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                        v_suppressElabErrors_6339_,
                    );
                    v___x_6346_ = l_Lean_Meta_mapErrorImp___redArg(
                        v___f_6343_,
                        v___f_6341_,
                        v___y_6318_,
                        v___y_6319_,
                        v___x_6345_,
                        v___y_6321_,
                    );
                    leanh::lean_dec_ref_known(v___x_6345_, 14);
                    if leanh::lean_obj_tag(v___x_6346_) == 0 {
                        v_a_6347_ = leanh::lean_ctor_get(v___x_6346_, 0);
                        v_isSharedCheck_6359_ =
                            (!leanh::lean_is_exclusive(v___x_6346_)) as u8;
                        if v_isSharedCheck_6359_ == 0 {
                            v___x_6349_ = v___x_6346_;
                            v_isShared_6350_ = v_isSharedCheck_6359_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6347_);
                            leanh::lean_dec(v___x_6346_);
                            v___x_6349_ = leanh::lean_box(0);
                            v_isShared_6350_ = v_isSharedCheck_6359_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6360_ = leanh::lean_ctor_get(v___x_6346_, 0);
                        v_isSharedCheck_6367_ =
                            (!leanh::lean_is_exclusive(v___x_6346_)) as u8;
                        if v_isSharedCheck_6367_ == 0 {
                            v___x_6362_ = v___x_6346_;
                            v_isShared_6363_ = v_isSharedCheck_6367_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6360_);
                            leanh::lean_dec(v___x_6346_);
                            v___x_6362_ = leanh::lean_box(0);
                            v_isShared_6363_ = v_isSharedCheck_6367_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_termMeasure_x3f_6312_);
                    leanh::lean_inc_ref(v_fixedParamPerm_6313_);
                    v_args_6368_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(
                        v_fixedParamPerm_6313_,
                        v_xs_6314_,
                        v_ys_6316_,
                    );
                    v___x_6369_ = lean_array_get_size(v_args_6368_);
                    v___x_6370_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6371_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__5,
                    );
                    v___x_6372_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(v___x_6369_, v_fnName_6315_, v_fixedParamPerm_6313_, v_args_6368_, v___x_6370_, v___x_6371_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_);
                    leanh::lean_dec_ref(v_args_6368_);
                    if leanh::lean_obj_tag(v___x_6372_) == 0 {
                        v_a_6373_ = leanh::lean_ctor_get(v___x_6372_, 0);
                        v_isSharedCheck_6407_ =
                            (!leanh::lean_is_exclusive(v___x_6372_)) as u8;
                        if v_isSharedCheck_6407_ == 0 {
                            v___x_6375_ = v___x_6372_;
                            v_isShared_6376_ = v_isSharedCheck_6407_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6373_);
                            leanh::lean_dec(v___x_6372_);
                            v___x_6375_ = leanh::lean_box(0);
                            v_isShared_6376_ = v_isSharedCheck_6407_;
                            state = 5;
                            continue;
                        }
                    } else {
                        return v___x_6372_;
                    }
                }
            }
            1 => {
                v___x_6351_ = leanh::lean_unsigned_to_nat(1);
                v___x_6352_ = lean_mk_empty_array_with_capacity(v___x_6351_);
                v___x_6353_ = lean_array_push(v___x_6352_, v_a_6347_);
                v___x_6354_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once
                    ),
                    _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3,
                );
                v___x_6355_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6355_, 0, v___x_6353_);
                leanh::lean_ctor_set(v___x_6355_, 1, v___x_6354_);
                if v_isShared_6350_ == 0 {
                    leanh::lean_ctor_set(v___x_6349_, 0, v___x_6355_);
                    v___x_6357_ = v___x_6349_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6358_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6358_, 0, v___x_6355_);
                    v___x_6357_ = v_reuseFailAlloc_6358_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6357_;
            }
            3 => {
                if v_isShared_6363_ == 0 {
                    v___x_6365_ = v___x_6362_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6366_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6366_, 0, v_a_6360_);
                    v___x_6365_ = v_reuseFailAlloc_6366_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6365_;
            }
            5 => {
                v_fst_6377_ = leanh::lean_ctor_get(v_a_6373_, 0);
                v_snd_6378_ = leanh::lean_ctor_get(v_a_6373_, 1);
                v_isSharedCheck_6406_ = (!leanh::lean_is_exclusive(v_a_6373_)) as u8;
                if v_isSharedCheck_6406_ == 0 {
                    v___x_6380_ = v_a_6373_;
                    v_isShared_6381_ = v_isSharedCheck_6406_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_6378_);
                    leanh::lean_inc(v_fst_6377_);
                    leanh::lean_dec(v_a_6373_);
                    v___x_6380_ = leanh::lean_box(0);
                    v_isShared_6381_ = v_isSharedCheck_6406_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                v_options_6389_ = leanh::lean_ctor_get(v___y_6320_, 2);
                v_hasTrace_6390_ = leanh::lean_ctor_get_uint8(
                    v_options_6389_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                if v_hasTrace_6390_ == 0 {
                    state = 7;
                    continue;
                } else {
                    v_inheritedTraceOptions_6391_ = leanh::lean_ctor_get(v___y_6320_, 13);
                    v___x_6392_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9;
                    v___x_6393_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12,
                    );
                    v___x_6394_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_6391_,
                        v_options_6389_,
                        v___x_6393_,
                    );
                    if v___x_6394_ == 0 {
                        state = 7;
                        continue;
                    } else {
                        v___x_6395_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14_once
                            ),
                            _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__14,
                        );
                        leanh::lean_inc(v_snd_6378_);
                        v___x_6396_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6396_, 0, v___x_6395_);
                        leanh::lean_ctor_set(v___x_6396_, 1, v_snd_6378_);
                        v___x_6397_ =
                            l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(
                                v___x_6392_,
                                v___x_6396_,
                                v___y_6318_,
                                v___y_6319_,
                                v___y_6320_,
                                v___y_6321_,
                            );
                        if leanh::lean_obj_tag(v___x_6397_) == 0 {
                            leanh::lean_dec_ref_known(v___x_6397_, 1);
                            state = 7;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_6380_);
                            leanh::lean_dec(v_snd_6378_);
                            leanh::lean_dec(v_fst_6377_);
                            leanh::lean_del_object(v___x_6375_);
                            v_a_6398_ = leanh::lean_ctor_get(v___x_6397_, 0);
                            v_isSharedCheck_6405_ =
                                (!leanh::lean_is_exclusive(v___x_6397_)) as u8;
                            if v_isSharedCheck_6405_ == 0 {
                                v___x_6400_ = v___x_6397_;
                                v_isShared_6401_ = v_isSharedCheck_6405_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6398_);
                                leanh::lean_dec(v___x_6397_);
                                v___x_6400_ = leanh::lean_box(0);
                                v_isShared_6401_ = v_isSharedCheck_6405_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                }
            }
            7 => {
                if v_isShared_6381_ == 0 {
                    v___x_6384_ = v___x_6380_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6388_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6388_, 0, v_fst_6377_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6388_, 1, v_snd_6378_);
                    v___x_6384_ = v_reuseFailAlloc_6388_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                if v_isShared_6376_ == 0 {
                    leanh::lean_ctor_set(v___x_6375_, 0, v___x_6384_);
                    v___x_6386_ = v___x_6375_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6387_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6387_, 0, v___x_6384_);
                    v___x_6386_ = v_reuseFailAlloc_6387_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6386_;
            }
            10 => {
                if v_isShared_6401_ == 0 {
                    v___x_6403_ = v___x_6400_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_6404_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6404_, 0, v_a_6398_);
                    v___x_6403_ = v_reuseFailAlloc_6404_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_6403_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed(
    mut v_termMeasure_x3f_6408_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6409_: *mut leanh::LeanObject,
    mut v_xs_6410_: *mut leanh::LeanObject,
    mut v_fnName_6411_: *mut leanh::LeanObject,
    mut v_ys_6412_: *mut leanh::LeanObject,
    mut v_x_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
    mut v___y_6418_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6419_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6419_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2(
        v_termMeasure_x3f_6408_,
        v_fixedParamPerm_6409_,
        v_xs_6410_,
        v_fnName_6411_,
        v_ys_6412_,
        v_x_6413_,
        v___y_6414_,
        v___y_6415_,
        v___y_6416_,
        v___y_6417_,
    );
    leanh::lean_dec(v___y_6417_);
    leanh::lean_dec_ref(v___y_6416_);
    leanh::lean_dec(v___y_6415_);
    leanh::lean_dec_ref(v___y_6414_);
    leanh::lean_dec_ref(v_x_6413_);
    leanh::lean_dec_ref(v_xs_6410_);
    return v_res_6419_;
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfos(
    mut v_fnName_6420_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6421_: *mut leanh::LeanObject,
    mut v_xs_6422_: *mut leanh::LeanObject,
    mut v_value_6423_: *mut leanh::LeanObject,
    mut v_termMeasure_x3f_6424_: *mut leanh::LeanObject,
    mut v_a_6425_: *mut leanh::LeanObject,
    mut v_a_6426_: *mut leanh::LeanObject,
    mut v_a_6427_: *mut leanh::LeanObject,
    mut v_a_6428_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: u8 = 0;
    let mut v___x_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6430_ = leanh::lean_alloc_closure(
        l_Lean_Elab_Structural_getRecArgInfos___lam__2___boxed as *mut core::ffi::c_void,
        11,
        4,
    );
    leanh::lean_closure_set(v___f_6430_, 0, v_termMeasure_x3f_6424_);
    leanh::lean_closure_set(v___f_6430_, 1, v_fixedParamPerm_6421_);
    leanh::lean_closure_set(v___f_6430_, 2, v_xs_6422_);
    leanh::lean_closure_set(v___f_6430_, 3, v_fnName_6420_);
    v___x_6431_ = 0;
    v___x_6432_ =
        l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(
            v_value_6423_,
            v___f_6430_,
            v___x_6431_,
            v_a_6425_,
            v_a_6426_,
            v_a_6427_,
            v_a_6428_,
        );
    return v___x_6432_;
}
pub unsafe fn l_Lean_Elab_Structural_getRecArgInfos___boxed(
    mut v_fnName_6433_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6434_: *mut leanh::LeanObject,
    mut v_xs_6435_: *mut leanh::LeanObject,
    mut v_value_6436_: *mut leanh::LeanObject,
    mut v_termMeasure_x3f_6437_: *mut leanh::LeanObject,
    mut v_a_6438_: *mut leanh::LeanObject,
    mut v_a_6439_: *mut leanh::LeanObject,
    mut v_a_6440_: *mut leanh::LeanObject,
    mut v_a_6441_: *mut leanh::LeanObject,
    mut v_a_6442_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6443_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6443_ = l_Lean_Elab_Structural_getRecArgInfos(
        v_fnName_6433_,
        v_fixedParamPerm_6434_,
        v_xs_6435_,
        v_value_6436_,
        v_termMeasure_x3f_6437_,
        v_a_6438_,
        v_a_6439_,
        v_a_6440_,
        v_a_6441_,
    );
    leanh::lean_dec(v_a_6441_);
    leanh::lean_dec_ref(v_a_6440_);
    leanh::lean_dec(v_a_6439_);
    leanh::lean_dec_ref(v_a_6438_);
    return v_res_6443_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(
    mut v_upperBound_6444_: *mut leanh::LeanObject,
    mut v_fnName_6445_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6446_: *mut leanh::LeanObject,
    mut v_args_6447_: *mut leanh::LeanObject,
    mut v_inst_6448_: *mut leanh::LeanObject,
    mut v_R_6449_: *mut leanh::LeanObject,
    mut v_a_6450_: *mut leanh::LeanObject,
    mut v_b_6451_: *mut leanh::LeanObject,
    mut v_c_6452_: *mut leanh::LeanObject,
    mut v___y_6453_: *mut leanh::LeanObject,
    mut v___y_6454_: *mut leanh::LeanObject,
    mut v___y_6455_: *mut leanh::LeanObject,
    mut v___y_6456_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6458_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg(
            v_upperBound_6444_,
            v_fnName_6445_,
            v_fixedParamPerm_6446_,
            v_args_6447_,
            v_a_6450_,
            v_b_6451_,
            v___y_6453_,
            v___y_6454_,
            v___y_6455_,
            v___y_6456_,
        );
    return v___x_6458_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___boxed(
    mut v_upperBound_6459_: *mut leanh::LeanObject,
    mut v_fnName_6460_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_6461_: *mut leanh::LeanObject,
    mut v_args_6462_: *mut leanh::LeanObject,
    mut v_inst_6463_: *mut leanh::LeanObject,
    mut v_R_6464_: *mut leanh::LeanObject,
    mut v_a_6465_: *mut leanh::LeanObject,
    mut v_b_6466_: *mut leanh::LeanObject,
    mut v_c_6467_: *mut leanh::LeanObject,
    mut v___y_6468_: *mut leanh::LeanObject,
    mut v___y_6469_: *mut leanh::LeanObject,
    mut v___y_6470_: *mut leanh::LeanObject,
    mut v___y_6471_: *mut leanh::LeanObject,
    mut v___y_6472_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6473_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1(
            v_upperBound_6459_,
            v_fnName_6460_,
            v_fixedParamPerm_6461_,
            v_args_6462_,
            v_inst_6463_,
            v_R_6464_,
            v_a_6465_,
            v_b_6466_,
            v_c_6467_,
            v___y_6468_,
            v___y_6469_,
            v___y_6470_,
            v___y_6471_,
        );
    leanh::lean_dec(v___y_6471_);
    leanh::lean_dec_ref(v___y_6470_);
    leanh::lean_dec(v___y_6469_);
    leanh::lean_dec_ref(v___y_6468_);
    leanh::lean_dec_ref(v_args_6462_);
    leanh::lean_dec(v_upperBound_6459_);
    return v_res_6473_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(
    mut v_x_6474_: *mut leanh::LeanObject,
    mut v_x_6475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6481_: u8 = 0;
    let mut v___x_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: u64 = 0;
    let mut v___x_6484_: u64 = 0;
    let mut v___x_6485_: u64 = 0;
    let mut v_fold_6486_: u64 = 0;
    let mut v___x_6487_: u64 = 0;
    let mut v___x_6488_: u64 = 0;
    let mut v___x_6489_: u64 = 0;
    let mut v___x_6490_: usize = 0;
    let mut v___x_6491_: usize = 0;
    let mut v___x_6492_: usize = 0;
    let mut v___x_6493_: usize = 0;
    let mut v___x_6494_: usize = 0;
    let mut v___x_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6501_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6475_) == 0 {
                    return v_x_6474_;
                } else {
                    v_key_6476_ = leanh::lean_ctor_get(v_x_6475_, 0);
                    v_value_6477_ = leanh::lean_ctor_get(v_x_6475_, 1);
                    v_tail_6478_ = leanh::lean_ctor_get(v_x_6475_, 2);
                    v_isSharedCheck_6501_ = (!leanh::lean_is_exclusive(v_x_6475_)) as u8;
                    if v_isSharedCheck_6501_ == 0 {
                        v___x_6480_ = v_x_6475_;
                        v_isShared_6481_ = v_isSharedCheck_6501_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_6478_);
                        leanh::lean_inc(v_value_6477_);
                        leanh::lean_inc(v_key_6476_);
                        leanh::lean_dec(v_x_6475_);
                        v___x_6480_ = leanh::lean_box(0);
                        v_isShared_6481_ = v_isSharedCheck_6501_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6482_ = lean_array_get_size(v_x_6474_);
                v___x_6483_ = lean_uint64_of_nat(v_key_6476_);
                v___x_6484_ = 32u64;
                v___x_6485_ = lean_uint64_shift_right(v___x_6483_, v___x_6484_);
                v_fold_6486_ = lean_uint64_xor(v___x_6483_, v___x_6485_);
                v___x_6487_ = 16u64;
                v___x_6488_ = lean_uint64_shift_right(v_fold_6486_, v___x_6487_);
                v___x_6489_ = lean_uint64_xor(v_fold_6486_, v___x_6488_);
                v___x_6490_ = lean_uint64_to_usize(v___x_6489_);
                v___x_6491_ = lean_usize_of_nat(v___x_6482_);
                v___x_6492_ = 1usize;
                v___x_6493_ = lean_usize_sub(v___x_6491_, v___x_6492_);
                v___x_6494_ = lean_usize_land(v___x_6490_, v___x_6493_);
                v___x_6495_ = lean_array_uget_borrowed(v_x_6474_, v___x_6494_);
                leanh::lean_inc(v___x_6495_);
                if v_isShared_6481_ == 0 {
                    leanh::lean_ctor_set(v___x_6480_, 2, v___x_6495_);
                    v___x_6497_ = v___x_6480_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6500_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 0, v_key_6476_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 1, v_value_6477_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6500_, 2, v___x_6495_);
                    v___x_6497_ = v_reuseFailAlloc_6500_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6498_ = lean_array_uset(v_x_6474_, v___x_6494_, v___x_6497_);
                v_x_6474_ = v___x_6498_;
                v_x_6475_ = v_tail_6478_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(
    mut v_i_6502_: *mut leanh::LeanObject,
    mut v_source_6503_: *mut leanh::LeanObject,
    mut v_target_6504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6506_: u8 = 0;
    let mut v_es_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6505_ = lean_array_get_size(v_source_6503_);
                v___x_6506_ = lean_nat_dec_lt(v_i_6502_, v___x_6505_);
                if v___x_6506_ == 0 {
                    leanh::lean_dec_ref(v_source_6503_);
                    leanh::lean_dec(v_i_6502_);
                    return v_target_6504_;
                } else {
                    v_es_6507_ = lean_array_fget(v_source_6503_, v_i_6502_);
                    v___x_6508_ = leanh::lean_box(0);
                    v_source_6509_ = lean_array_fset(v_source_6503_, v_i_6502_, v___x_6508_);
                    v_target_6510_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_target_6504_, v_es_6507_);
                    v___x_6511_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6512_ = lean_nat_add(v_i_6502_, v___x_6511_);
                    leanh::lean_dec(v_i_6502_);
                    v_i_6502_ = v___x_6512_;
                    v_source_6503_ = v_source_6509_;
                    v_target_6504_ = v_target_6510_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(
    mut v_data_6514_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_6517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6515_ = lean_array_get_size(v_data_6514_);
    v___x_6516_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_6517_ = lean_nat_mul(v___x_6515_, v___x_6516_);
    v___x_6518_ = leanh::lean_unsigned_to_nat(0);
    v___x_6519_ = leanh::lean_box(0);
    v___x_6520_ = lean_mk_array(v_nbuckets_6517_, v___x_6519_);
    v___x_6521_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v___x_6518_, v_data_6514_, v___x_6520_);
    return v___x_6521_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(
    mut v_a_6522_: *mut leanh::LeanObject,
    mut v_x_6523_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6524_: u8 = 0;
    let mut v_key_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6527_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6523_) == 0 {
                    v___x_6524_ = 0;
                    return v___x_6524_;
                } else {
                    v_key_6525_ = leanh::lean_ctor_get(v_x_6523_, 0);
                    v_tail_6526_ = leanh::lean_ctor_get(v_x_6523_, 2);
                    v___x_6527_ = lean_nat_dec_eq(v_key_6525_, v_a_6522_);
                    if v___x_6527_ == 0 {
                        v_x_6523_ = v_tail_6526_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_6527_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg___boxed(
    mut v_a_6529_: *mut leanh::LeanObject,
    mut v_x_6530_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6531_: u8 = 0;
    let mut v_r_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6531_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_6529_, v_x_6530_);
    leanh::lean_dec(v_x_6530_);
    leanh::lean_dec(v_a_6529_);
    v_r_6532_ = leanh::lean_box((v_res_6531_) as usize);
    return v_r_6532_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(
    mut v_m_6533_: *mut leanh::LeanObject,
    mut v_a_6534_: *mut leanh::LeanObject,
    mut v_b_6535_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6539_: u64 = 0;
    let mut v___x_6540_: u64 = 0;
    let mut v___x_6541_: u64 = 0;
    let mut v_fold_6542_: u64 = 0;
    let mut v___x_6543_: u64 = 0;
    let mut v___x_6544_: u64 = 0;
    let mut v___x_6545_: u64 = 0;
    let mut v___x_6546_: usize = 0;
    let mut v___x_6547_: usize = 0;
    let mut v___x_6548_: usize = 0;
    let mut v___x_6549_: usize = 0;
    let mut v___x_6550_: usize = 0;
    let mut v_bkt_6551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6552_: u8 = 0;
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6555_: u8 = 0;
    let mut v___x_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_6557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_6559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6565_: u8 = 0;
    let mut v_val_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6573_: u8 = 0;
    let mut v_unused_6574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_6536_ = leanh::lean_ctor_get(v_m_6533_, 0);
                v_buckets_6537_ = leanh::lean_ctor_get(v_m_6533_, 1);
                v___x_6538_ = lean_array_get_size(v_buckets_6537_);
                v___x_6539_ = lean_uint64_of_nat(v_a_6534_);
                v___x_6540_ = 32u64;
                v___x_6541_ = lean_uint64_shift_right(v___x_6539_, v___x_6540_);
                v_fold_6542_ = lean_uint64_xor(v___x_6539_, v___x_6541_);
                v___x_6543_ = 16u64;
                v___x_6544_ = lean_uint64_shift_right(v_fold_6542_, v___x_6543_);
                v___x_6545_ = lean_uint64_xor(v_fold_6542_, v___x_6544_);
                v___x_6546_ = lean_uint64_to_usize(v___x_6545_);
                v___x_6547_ = lean_usize_of_nat(v___x_6538_);
                v___x_6548_ = 1usize;
                v___x_6549_ = lean_usize_sub(v___x_6547_, v___x_6548_);
                v___x_6550_ = lean_usize_land(v___x_6546_, v___x_6549_);
                v_bkt_6551_ = lean_array_uget_borrowed(v_buckets_6537_, v___x_6550_);
                v___x_6552_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_6534_, v_bkt_6551_);
                if v___x_6552_ == 0 {
                    leanh::lean_inc_ref(v_buckets_6537_);
                    leanh::lean_inc(v_size_6536_);
                    v_isSharedCheck_6573_ = (!leanh::lean_is_exclusive(v_m_6533_)) as u8;
                    if v_isSharedCheck_6573_ == 0 {
                        v_unused_6574_ = leanh::lean_ctor_get(v_m_6533_, 1);
                        leanh::lean_dec(v_unused_6574_);
                        v_unused_6575_ = leanh::lean_ctor_get(v_m_6533_, 0);
                        leanh::lean_dec(v_unused_6575_);
                        v___x_6554_ = v_m_6533_;
                        v_isShared_6555_ = v_isSharedCheck_6573_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v_m_6533_);
                        v___x_6554_ = leanh::lean_box(0);
                        v_isShared_6555_ = v_isSharedCheck_6573_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_b_6535_);
                    leanh::lean_dec(v_a_6534_);
                    return v_m_6533_;
                }
            }
            1 => {
                v___x_6556_ = leanh::lean_unsigned_to_nat(1);
                v_size_x27_6557_ = lean_nat_add(v_size_6536_, v___x_6556_);
                leanh::lean_dec(v_size_6536_);
                leanh::lean_inc(v_bkt_6551_);
                v___x_6558_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_6558_, 0, v_a_6534_);
                leanh::lean_ctor_set(v___x_6558_, 1, v_b_6535_);
                leanh::lean_ctor_set(v___x_6558_, 2, v_bkt_6551_);
                v_buckets_x27_6559_ = lean_array_uset(v_buckets_6537_, v___x_6550_, v___x_6558_);
                v___x_6560_ = leanh::lean_unsigned_to_nat(4);
                v___x_6561_ = lean_nat_mul(v_size_x27_6557_, v___x_6560_);
                v___x_6562_ = leanh::lean_unsigned_to_nat(3);
                v___x_6563_ = lean_nat_div(v___x_6561_, v___x_6562_);
                leanh::lean_dec(v___x_6561_);
                v___x_6564_ = lean_array_get_size(v_buckets_x27_6559_);
                v___x_6565_ = lean_nat_dec_le(v___x_6563_, v___x_6564_);
                leanh::lean_dec(v___x_6563_);
                if v___x_6565_ == 0 {
                    v_val_6566_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_buckets_x27_6559_);
                    if v_isShared_6555_ == 0 {
                        leanh::lean_ctor_set(v___x_6554_, 1, v_val_6566_);
                        leanh::lean_ctor_set(v___x_6554_, 0, v_size_x27_6557_);
                        v___x_6568_ = v___x_6554_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6569_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6569_, 0, v_size_x27_6557_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6569_, 1, v_val_6566_);
                        v___x_6568_ = v_reuseFailAlloc_6569_;
                        state = 2;
                        continue;
                    }
                } else {
                    if v_isShared_6555_ == 0 {
                        leanh::lean_ctor_set(v___x_6554_, 1, v_buckets_x27_6559_);
                        leanh::lean_ctor_set(v___x_6554_, 0, v_size_x27_6557_);
                        v___x_6571_ = v___x_6554_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6572_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 0, v_size_x27_6557_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6572_, 1, v_buckets_x27_6559_);
                        v___x_6571_ = v_reuseFailAlloc_6572_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6568_;
            }
            3 => {
                return v___x_6571_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(
    mut v_as_6576_: *mut leanh::LeanObject,
    mut v_sz_6577_: usize,
    mut v_i_6578_: usize,
    mut v_b_6579_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6580_: u8 = 0;
    let mut v_a_6581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: usize = 0;
    let mut v___x_6585_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6580_ = lean_usize_dec_lt(v_i_6578_, v_sz_6577_);
                if v___x_6580_ == 0 {
                    return v_b_6579_;
                } else {
                    v_a_6581_ = lean_array_uget_borrowed(v_as_6576_, v_i_6578_);
                    v___x_6582_ = leanh::lean_box(0);
                    leanh::lean_inc(v_a_6581_);
                    v___x_6583_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_b_6579_, v_a_6581_, v___x_6582_);
                    v___x_6584_ = 1usize;
                    v___x_6585_ = lean_usize_add(v_i_6578_, v___x_6584_);
                    v_i_6578_ = v___x_6585_;
                    v_b_6579_ = v___x_6583_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1___boxed(
    mut v_as_6587_: *mut leanh::LeanObject,
    mut v_sz_6588_: *mut leanh::LeanObject,
    mut v_i_6589_: *mut leanh::LeanObject,
    mut v_b_6590_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6591_: usize = 0;
    let mut v_i_boxed_6592_: usize = 0;
    let mut v_res_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6591_ = leanh::lean_unbox_usize(v_sz_6588_);
    leanh::lean_dec(v_sz_6588_);
    v_i_boxed_6592_ = leanh::lean_unbox_usize(v_i_6589_);
    leanh::lean_dec(v_i_6589_);
    v_res_6593_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_as_6587_, v_sz_boxed_6591_, v_i_boxed_6592_, v_b_6590_);
    leanh::lean_dec_ref(v_as_6587_);
    return v_res_6593_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(
    mut v_as_6594_: *mut leanh::LeanObject,
    mut v_sz_6595_: usize,
    mut v_i_6596_: usize,
    mut v_b_6597_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6598_: u8 = 0;
    let mut v_a_6599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_6600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6601_: usize = 0;
    let mut v___x_6602_: usize = 0;
    let mut v___x_6603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6604_: usize = 0;
    let mut v___x_6605_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6598_ = lean_usize_dec_lt(v_i_6596_, v_sz_6595_);
                if v___x_6598_ == 0 {
                    return v_b_6597_;
                } else {
                    v_a_6599_ = lean_array_uget_borrowed(v_as_6594_, v_i_6596_);
                    v_indicesPos_6600_ = leanh::lean_ctor_get(v_a_6599_, 3);
                    v_sz_6601_ = lean_array_size(v_indicesPos_6600_);
                    v___x_6602_ = 0usize;
                    v___x_6603_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__1(v_indicesPos_6600_, v_sz_6601_, v___x_6602_, v_b_6597_);
                    v___x_6604_ = 1usize;
                    v___x_6605_ = lean_usize_add(v_i_6596_, v___x_6604_);
                    v_i_6596_ = v___x_6605_;
                    v_b_6597_ = v___x_6603_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2___boxed(
    mut v_as_6607_: *mut leanh::LeanObject,
    mut v_sz_6608_: *mut leanh::LeanObject,
    mut v_i_6609_: *mut leanh::LeanObject,
    mut v_b_6610_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6611_: usize = 0;
    let mut v_i_boxed_6612_: usize = 0;
    let mut v_res_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6611_ = leanh::lean_unbox_usize(v_sz_6608_);
    leanh::lean_dec(v_sz_6608_);
    v_i_boxed_6612_ = leanh::lean_unbox_usize(v_i_6609_);
    leanh::lean_dec(v_i_6609_);
    v_res_6613_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_as_6607_, v_sz_boxed_6611_, v_i_boxed_6612_, v_b_6610_);
    leanh::lean_dec_ref(v_as_6607_);
    return v_res_6613_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(
    mut v_m_6614_: *mut leanh::LeanObject,
    mut v_a_6615_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_6616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: u64 = 0;
    let mut v___x_6619_: u64 = 0;
    let mut v___x_6620_: u64 = 0;
    let mut v_fold_6621_: u64 = 0;
    let mut v___x_6622_: u64 = 0;
    let mut v___x_6623_: u64 = 0;
    let mut v___x_6624_: u64 = 0;
    let mut v___x_6625_: usize = 0;
    let mut v___x_6626_: usize = 0;
    let mut v___x_6627_: usize = 0;
    let mut v___x_6628_: usize = 0;
    let mut v___x_6629_: usize = 0;
    let mut v___x_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6631_: u8 = 0;
    v_buckets_6616_ = leanh::lean_ctor_get(v_m_6614_, 1);
    v___x_6617_ = lean_array_get_size(v_buckets_6616_);
    v___x_6618_ = lean_uint64_of_nat(v_a_6615_);
    v___x_6619_ = 32u64;
    v___x_6620_ = lean_uint64_shift_right(v___x_6618_, v___x_6619_);
    v_fold_6621_ = lean_uint64_xor(v___x_6618_, v___x_6620_);
    v___x_6622_ = 16u64;
    v___x_6623_ = lean_uint64_shift_right(v_fold_6621_, v___x_6622_);
    v___x_6624_ = lean_uint64_xor(v_fold_6621_, v___x_6623_);
    v___x_6625_ = lean_uint64_to_usize(v___x_6624_);
    v___x_6626_ = lean_usize_of_nat(v___x_6617_);
    v___x_6627_ = 1usize;
    v___x_6628_ = lean_usize_sub(v___x_6626_, v___x_6627_);
    v___x_6629_ = lean_usize_land(v___x_6625_, v___x_6628_);
    v___x_6630_ = lean_array_uget_borrowed(v_buckets_6616_, v___x_6629_);
    v___x_6631_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_6615_, v___x_6630_);
    return v___x_6631_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg___boxed(
    mut v_m_6632_: *mut leanh::LeanObject,
    mut v_a_6633_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6634_: u8 = 0;
    let mut v_r_6635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6634_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_6632_, v_a_6633_);
    leanh::lean_dec(v_a_6633_);
    leanh::lean_dec_ref(v_m_6632_);
    v_r_6635_ = leanh::lean_box((v_res_6634_) as usize);
    return v_r_6635_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(
    mut v___x_6636_: *mut leanh::LeanObject,
    mut v_as_6637_: *mut leanh::LeanObject,
    mut v_sz_6638_: usize,
    mut v_i_6639_: usize,
    mut v_b_6640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: usize = 0;
    let mut v___x_6644_: usize = 0;
    let mut v___x_6646_: u8 = 0;
    let mut v_fst_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6651_: u8 = 0;
    let mut v_a_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: u8 = 0;
    let mut v___x_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6663_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6646_ = lean_usize_dec_lt(v_i_6639_, v_sz_6638_);
                if v___x_6646_ == 0 {
                    return v_b_6640_;
                } else {
                    v_fst_6647_ = leanh::lean_ctor_get(v_b_6640_, 0);
                    v_snd_6648_ = leanh::lean_ctor_get(v_b_6640_, 1);
                    v_isSharedCheck_6663_ = (!leanh::lean_is_exclusive(v_b_6640_)) as u8;
                    if v_isSharedCheck_6663_ == 0 {
                        v___x_6650_ = v_b_6640_;
                        v_isShared_6651_ = v_isSharedCheck_6663_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6648_);
                        leanh::lean_inc(v_fst_6647_);
                        leanh::lean_dec(v_b_6640_);
                        v___x_6650_ = leanh::lean_box(0);
                        v_isShared_6651_ = v_isSharedCheck_6663_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6643_ = 1usize;
                v___x_6644_ = lean_usize_add(v_i_6639_, v___x_6643_);
                v_i_6639_ = v___x_6644_;
                v_b_6640_ = v_a_6642_;
                state = 0;
                continue;
            }
            2 => {
                v_a_6652_ = lean_array_uget_borrowed(v_as_6637_, v_i_6639_);
                v_recArgPos_6653_ = leanh::lean_ctor_get(v_a_6652_, 2);
                v___x_6654_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v___x_6636_, v_recArgPos_6653_);
                if v___x_6654_ == 0 {
                    leanh::lean_inc(v_a_6652_);
                    v___x_6655_ = lean_array_push(v_snd_6648_, v_a_6652_);
                    if v_isShared_6651_ == 0 {
                        leanh::lean_ctor_set(v___x_6650_, 1, v___x_6655_);
                        v___x_6657_ = v___x_6650_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6658_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6658_, 0, v_fst_6647_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6658_, 1, v___x_6655_);
                        v___x_6657_ = v_reuseFailAlloc_6658_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_a_6652_);
                    v___x_6659_ = lean_array_push(v_fst_6647_, v_a_6652_);
                    if v_isShared_6651_ == 0 {
                        leanh::lean_ctor_set(v___x_6650_, 0, v___x_6659_);
                        v___x_6661_ = v___x_6650_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6662_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6662_, 0, v___x_6659_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6662_, 1, v_snd_6648_);
                        v___x_6661_ = v_reuseFailAlloc_6662_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                v_a_6642_ = v___x_6657_;
                state = 1;
                continue;
            }
            4 => {
                v_a_6642_ = v___x_6661_;
                state = 1;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4___boxed(
    mut v___x_6664_: *mut leanh::LeanObject,
    mut v_as_6665_: *mut leanh::LeanObject,
    mut v_sz_6666_: *mut leanh::LeanObject,
    mut v_i_6667_: *mut leanh::LeanObject,
    mut v_b_6668_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6669_: usize = 0;
    let mut v_i_boxed_6670_: usize = 0;
    let mut v_res_6671_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6669_ = leanh::lean_unbox_usize(v_sz_6666_);
    leanh::lean_dec(v_sz_6666_);
    v_i_boxed_6670_ = leanh::lean_unbox_usize(v_i_6667_);
    leanh::lean_dec(v_i_6667_);
    v_res_6671_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_6664_, v_as_6665_, v_sz_boxed_6669_, v_i_boxed_6670_, v_b_6668_);
    leanh::lean_dec_ref(v_as_6665_);
    leanh::lean_dec_ref(v___x_6664_);
    return v_res_6671_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6672_ = leanh::lean_box(0);
    v___x_6673_ = leanh::lean_unsigned_to_nat(16);
    v___x_6674_ = lean_mk_array(v___x_6673_, v___x_6672_);
    return v___x_6674_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indicesPos_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6675_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_nonIndicesFirst___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_nonIndicesFirst___closed__0_once),
        _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__0,
    );
    v___x_6676_ = leanh::lean_unsigned_to_nat(0);
    v_indicesPos_6677_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v_indicesPos_6677_, 0, v___x_6676_);
    leanh::lean_ctor_set(v_indicesPos_6677_, 1, v___x_6675_);
    return v_indicesPos_6677_;
}
pub unsafe fn l_Lean_Elab_Structural_nonIndicesFirst(
    mut v_recArgInfos_6680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_indicesPos_6681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6682_: usize = 0;
    let mut v___x_6683_: usize = 0;
    let mut v___x_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_indicesPos_6681_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_nonIndicesFirst___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Elab_Structural_nonIndicesFirst___closed__1_once),
        _init_l_Lean_Elab_Structural_nonIndicesFirst___closed__1,
    );
    v_sz_6682_ = lean_array_size(v_recArgInfos_6680_);
    v___x_6683_ = 0usize;
    v___x_6684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__2(v_recArgInfos_6680_, v_sz_6682_, v___x_6683_, v_indicesPos_6681_);
    v___x_6685_ = l_Lean_Elab_Structural_nonIndicesFirst___closed__2;
    v___x_6686_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_nonIndicesFirst_spec__4(v___x_6684_, v_recArgInfos_6680_, v_sz_6682_, v___x_6683_, v___x_6685_);
    leanh::lean_dec_ref(v___x_6684_);
    v_fst_6687_ = leanh::lean_ctor_get(v___x_6686_, 0);
    leanh::lean_inc(v_fst_6687_);
    v_snd_6688_ = leanh::lean_ctor_get(v___x_6686_, 1);
    leanh::lean_inc(v_snd_6688_);
    leanh::lean_dec_ref(v___x_6686_);
    v___x_6689_ = l_Array_append___redArg(v_snd_6688_, v_fst_6687_);
    leanh::lean_dec(v_fst_6687_);
    return v___x_6689_;
}
pub unsafe fn l_Lean_Elab_Structural_nonIndicesFirst___boxed(
    mut v_recArgInfos_6690_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6691_ = l_Lean_Elab_Structural_nonIndicesFirst(v_recArgInfos_6690_);
    leanh::lean_dec_ref(v_recArgInfos_6690_);
    return v_res_6691_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0(
    mut v_00_u03b2_6692_: *mut leanh::LeanObject,
    mut v_m_6693_: *mut leanh::LeanObject,
    mut v_a_6694_: *mut leanh::LeanObject,
    mut v_b_6695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6696_ = l_Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0___redArg(v_m_6693_, v_a_6694_, v_b_6695_);
    return v___x_6696_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(
    mut v_00_u03b2_6697_: *mut leanh::LeanObject,
    mut v_m_6698_: *mut leanh::LeanObject,
    mut v_a_6699_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6700_: u8 = 0;
    v___x_6700_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___redArg(v_m_6698_, v_a_6699_);
    return v___x_6700_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3___boxed(
    mut v_00_u03b2_6701_: *mut leanh::LeanObject,
    mut v_m_6702_: *mut leanh::LeanObject,
    mut v_a_6703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6704_: u8 = 0;
    let mut v_r_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6704_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Elab_Structural_nonIndicesFirst_spec__3(v_00_u03b2_6701_, v_m_6702_, v_a_6703_);
    leanh::lean_dec(v_a_6703_);
    leanh::lean_dec_ref(v_m_6702_);
    v_r_6705_ = leanh::lean_box((v_res_6704_) as usize);
    return v_r_6705_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(
    mut v_00_u03b2_6706_: *mut leanh::LeanObject,
    mut v_a_6707_: *mut leanh::LeanObject,
    mut v_x_6708_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6709_: u8 = 0;
    v___x_6709_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___redArg(v_a_6707_, v_x_6708_);
    return v___x_6709_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0___boxed(
    mut v_00_u03b2_6710_: *mut leanh::LeanObject,
    mut v_a_6711_: *mut leanh::LeanObject,
    mut v_x_6712_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6713_: u8 = 0;
    let mut v_r_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6713_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__0(v_00_u03b2_6710_, v_a_6711_, v_x_6712_);
    leanh::lean_dec(v_x_6712_);
    leanh::lean_dec(v_a_6711_);
    v_r_6714_ = leanh::lean_box((v_res_6713_) as usize);
    return v_r_6714_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1(
    mut v_00_u03b2_6715_: *mut leanh::LeanObject,
    mut v_data_6716_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6717_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6717_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1___redArg(v_data_6716_);
    return v___x_6717_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2(
    mut v_00_u03b2_6718_: *mut leanh::LeanObject,
    mut v_i_6719_: *mut leanh::LeanObject,
    mut v_source_6720_: *mut leanh::LeanObject,
    mut v_target_6721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6722_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2___redArg(v_i_6719_, v_source_6720_, v_target_6721_);
    return v___x_6722_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7(
    mut v_00_u03b2_6723_: *mut leanh::LeanObject,
    mut v_x_6724_: *mut leanh::LeanObject,
    mut v_x_6725_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6726_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6726_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insertIfNew___at___00Lean_Elab_Structural_nonIndicesFirst_spec__0_spec__1_spec__2_spec__7___redArg(v_x_6724_, v_x_6725_);
    return v___x_6726_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(
    mut v___y_6727_: *mut leanh::LeanObject,
    mut v_a_6728_: *mut leanh::LeanObject,
    mut v_toPure_6729_: *mut leanh::LeanObject,
    mut v_____do__lift_6730_: u8,
) -> *mut leanh::LeanObject {
    if v_____do__lift_6730_ == 0 {
        let mut v___x_6731_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6732_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6733_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6731_ = lean_array_push(v___y_6727_, v_a_6728_);
        v___x_6732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6732_, 0, v___x_6731_);
        v___x_6733_ =
            leanh::lean_apply_2(v_toPure_6729_, leanh::lean_box(0), v___x_6732_);
        return v___x_6733_;
    } else {
        let mut v___x_6734_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6735_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_6728_);
        v___x_6734_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6734_, 0, v___y_6727_);
        v___x_6735_ =
            leanh::lean_apply_2(v_toPure_6729_, leanh::lean_box(0), v___x_6734_);
        return v___x_6735_;
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed(
    mut v___y_6736_: *mut leanh::LeanObject,
    mut v_a_6737_: *mut leanh::LeanObject,
    mut v_toPure_6738_: *mut leanh::LeanObject,
    mut v_____do__lift_6739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_192__boxed_6740_: u8 = 0;
    let mut v_res_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_192__boxed_6740_ = (leanh::lean_unbox(v_____do__lift_6739_) as u8);
    v_res_6741_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0(v___y_6736_, v_a_6737_, v_toPure_6738_, v_____do__lift_192__boxed_6740_);
    return v_res_6741_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1(
    mut v_eq_6742_: *mut leanh::LeanObject,
    mut v_a_6743_: *mut leanh::LeanObject,
    mut v_x_6744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6745_ = leanh::lean_apply_2(v_eq_6742_, v_x_6744_, v_a_6743_);
    return v___x_6745_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(
    mut v_toPure_6746_: *mut leanh::LeanObject,
    mut v___x_6747_: *mut leanh::LeanObject,
    mut v_toBind_6748_: *mut leanh::LeanObject,
    mut v_eq_6749_: *mut leanh::LeanObject,
    mut v_inst_6750_: *mut leanh::LeanObject,
    mut v_a_6751_: *mut leanh::LeanObject,
    mut v_x_6752_: *mut leanh::LeanObject,
    mut v___y_6753_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6756_: u8 = 0;
    leanh::lean_inc(v_toPure_6746_);
    leanh::lean_inc(v_a_6751_);
    leanh::lean_inc_ref(v___y_6753_);
    v___f_6754_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
    leanh::lean_closure_set(v___f_6754_, 0, v___y_6753_);
    leanh::lean_closure_set(v___f_6754_, 1, v_a_6751_);
    leanh::lean_closure_set(v___f_6754_, 2, v_toPure_6746_);
    v___x_6755_ = lean_array_get_size(v___y_6753_);
    v___x_6756_ = lean_nat_dec_lt(v___x_6747_, v___x_6755_);
    if v___x_6756_ == 0 {
        let mut v___x_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6759_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v___y_6753_);
        leanh::lean_dec(v_a_6751_);
        leanh::lean_dec_ref(v_inst_6750_);
        leanh::lean_dec(v_eq_6749_);
        v___x_6757_ = leanh::lean_box((v___x_6756_) as usize);
        v___x_6758_ =
            leanh::lean_apply_2(v_toPure_6746_, leanh::lean_box(0), v___x_6757_);
        v___x_6759_ = leanh::lean_apply_4(
            v_toBind_6748_,
            leanh::lean_box(0),
            leanh::lean_box(0),
            v___x_6758_,
            v___f_6754_,
        );
        return v___x_6759_;
    } else {
        if v___x_6756_ == 0 {
            let mut v___x_6760_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6761_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6762_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref(v___y_6753_);
            leanh::lean_dec(v_a_6751_);
            leanh::lean_dec_ref(v_inst_6750_);
            leanh::lean_dec(v_eq_6749_);
            v___x_6760_ = leanh::lean_box((v___x_6756_) as usize);
            v___x_6761_ =
                leanh::lean_apply_2(v_toPure_6746_, leanh::lean_box(0), v___x_6760_);
            v___x_6762_ = leanh::lean_apply_4(
                v_toBind_6748_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_6761_,
                v___f_6754_,
            );
            return v___x_6762_;
        } else {
            let mut v___f_6763_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6764_: usize = 0;
            let mut v___x_6765_: usize = 0;
            let mut v___x_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6767_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec(v_toPure_6746_);
            v___f_6763_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__1 as *mut core::ffi::c_void, 3, 2);
            leanh::lean_closure_set(v___f_6763_, 0, v_eq_6749_);
            leanh::lean_closure_set(v___f_6763_, 1, v_a_6751_);
            v___x_6764_ = 0usize;
            v___x_6765_ = lean_usize_of_nat(v___x_6755_);
            v___x_6766_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any(
                leanh::lean_box(0),
                leanh::lean_box(0),
                v_inst_6750_,
                v___f_6763_,
                v___y_6753_,
                v___x_6764_,
                v___x_6765_,
            );
            v___x_6767_ = leanh::lean_apply_4(
                v_toBind_6748_,
                leanh::lean_box(0),
                leanh::lean_box(0),
                v___x_6766_,
                v___f_6754_,
            );
            return v___x_6767_;
        }
    }
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed(
    mut v_toPure_6768_: *mut leanh::LeanObject,
    mut v___x_6769_: *mut leanh::LeanObject,
    mut v_toBind_6770_: *mut leanh::LeanObject,
    mut v_eq_6771_: *mut leanh::LeanObject,
    mut v_inst_6772_: *mut leanh::LeanObject,
    mut v_a_6773_: *mut leanh::LeanObject,
    mut v_x_6774_: *mut leanh::LeanObject,
    mut v___y_6775_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6776_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2(v_toPure_6768_, v___x_6769_, v_toBind_6770_, v_eq_6771_, v_inst_6772_, v_a_6773_, v_x_6774_, v___y_6775_);
    leanh::lean_dec(v___x_6769_);
    return v_res_6776_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3(
    mut v_toPure_6777_: *mut leanh::LeanObject,
    mut v_____s_6778_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6779_ =
        leanh::lean_apply_2(v_toPure_6777_, leanh::lean_box(0), v_____s_6778_);
    return v___x_6779_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(
    mut v_inst_6782_: *mut leanh::LeanObject,
    mut v_eq_6783_: *mut leanh::LeanObject,
    mut v_xs_6784_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toApplicative_6785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toBind_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toPure_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ret_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6792_: usize = 0;
    let mut v___x_6793_: usize = 0;
    let mut v___x_6794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toApplicative_6785_ = leanh::lean_ctor_get(v_inst_6782_, 0);
    v_toBind_6786_ = leanh::lean_ctor_get(v_inst_6782_, 1);
    leanh::lean_inc_n(v_toBind_6786_, 2);
    v_toPure_6787_ = leanh::lean_ctor_get(v_toApplicative_6785_, 1);
    v___x_6788_ = leanh::lean_unsigned_to_nat(0);
    v_ret_6789_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0;
    leanh::lean_inc_ref(v_inst_6782_);
    leanh::lean_inc_n(v_toPure_6787_, 2);
    v___f_6790_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__2___boxed as *mut core::ffi::c_void, 8, 5);
    leanh::lean_closure_set(v___f_6790_, 0, v_toPure_6787_);
    leanh::lean_closure_set(v___f_6790_, 1, v___x_6788_);
    leanh::lean_closure_set(v___f_6790_, 2, v_toBind_6786_);
    leanh::lean_closure_set(v___f_6790_, 3, v_eq_6783_);
    leanh::lean_closure_set(v___f_6790_, 4, v_inst_6782_);
    v___f_6791_ = leanh::lean_alloc_closure(l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___lam__3 as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_6791_, 0, v_toPure_6787_);
    v_sz_6792_ = lean_array_size(v_xs_6784_);
    v___x_6793_ = 0usize;
    v___x_6794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop(
        leanh::lean_box(0),
        leanh::lean_box(0),
        leanh::lean_box(0),
        v_inst_6782_,
        v_xs_6784_,
        v___f_6790_,
        v_sz_6792_,
        v___x_6793_,
        v_ret_6789_,
    );
    v___x_6795_ = leanh::lean_apply_4(
        v_toBind_6786_,
        leanh::lean_box(0),
        leanh::lean_box(0),
        v___x_6794_,
        v___f_6791_,
    );
    return v___x_6795_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup(
    mut v_m_6796_: *mut leanh::LeanObject,
    mut v_00_u03b1_6797_: *mut leanh::LeanObject,
    mut v_inst_6798_: *mut leanh::LeanObject,
    mut v_eq_6799_: *mut leanh::LeanObject,
    mut v_xs_6800_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6801_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg(v_inst_6798_, v_eq_6799_, v_xs_6800_);
    return v___x_6801_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(
    mut v_sz_6802_: usize,
    mut v_i_6803_: usize,
    mut v_bs_6804_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6805_: u8 = 0;
    let mut v_v_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_6807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: usize = 0;
    let mut v___x_6811_: usize = 0;
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6805_ = lean_usize_dec_lt(v_i_6803_, v_sz_6802_);
                if v___x_6805_ == 0 {
                    return v_bs_6804_;
                } else {
                    v_v_6806_ = lean_array_uget_borrowed(v_bs_6804_, v_i_6803_);
                    v_indGroupInst_6807_ = leanh::lean_ctor_get(v_v_6806_, 4);
                    leanh::lean_inc_ref(v_indGroupInst_6807_);
                    v___x_6808_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_6809_ = lean_array_uset(v_bs_6804_, v_i_6803_, v___x_6808_);
                    v___x_6810_ = 1usize;
                    v___x_6811_ = lean_usize_add(v_i_6803_, v___x_6810_);
                    v___x_6812_ = lean_array_uset(v_bs_x27_6809_, v_i_6803_, v_indGroupInst_6807_);
                    v_i_6803_ = v___x_6811_;
                    v_bs_6804_ = v___x_6812_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0___boxed(
    mut v_sz_6814_: *mut leanh::LeanObject,
    mut v_i_6815_: *mut leanh::LeanObject,
    mut v_bs_6816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6817_: usize = 0;
    let mut v_i_boxed_6818_: usize = 0;
    let mut v_res_6819_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6817_ = leanh::lean_unbox_usize(v_sz_6814_);
    leanh::lean_dec(v_sz_6814_);
    v_i_boxed_6818_ = leanh::lean_unbox_usize(v_i_6815_);
    leanh::lean_dec(v_i_6815_);
    v_res_6819_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_boxed_6817_, v_i_boxed_6818_, v_bs_6816_);
    return v_res_6819_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(
    mut v_eq_6820_: *mut leanh::LeanObject,
    mut v_a_6821_: *mut leanh::LeanObject,
    mut v_as_6822_: *mut leanh::LeanObject,
    mut v_i_6823_: usize,
    mut v_stop_6824_: usize,
    mut v___y_6825_: *mut leanh::LeanObject,
    mut v___y_6826_: *mut leanh::LeanObject,
    mut v___y_6827_: *mut leanh::LeanObject,
    mut v___y_6828_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6830_: u8 = 0;
    let mut v___x_6831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6836_: u8 = 0;
    let mut v___x_6837_: u8 = 0;
    let mut v___x_6838_: usize = 0;
    let mut v___x_6839_: usize = 0;
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6844_: u8 = 0;
    let mut v___x_6845_: u8 = 0;
    let mut v___x_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6830_ = lean_usize_dec_eq(v_i_6823_, v_stop_6824_);
                if v___x_6830_ == 0 {
                    v___x_6831_ = lean_array_uget_borrowed(v_as_6822_, v_i_6823_);
                    leanh::lean_inc_ref(v_eq_6820_);
                    leanh::lean_inc(v___y_6828_);
                    leanh::lean_inc_ref(v___y_6827_);
                    leanh::lean_inc(v___y_6826_);
                    leanh::lean_inc_ref(v___y_6825_);
                    leanh::lean_inc(v_a_6821_);
                    leanh::lean_inc(v___x_6831_);
                    v___x_6832_ = leanh::lean_apply_7(
                        v_eq_6820_,
                        v___x_6831_,
                        v_a_6821_,
                        v___y_6825_,
                        v___y_6826_,
                        v___y_6827_,
                        v___y_6828_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_6832_) == 0 {
                        v_a_6833_ = leanh::lean_ctor_get(v___x_6832_, 0);
                        v_isSharedCheck_6844_ =
                            (!leanh::lean_is_exclusive(v___x_6832_)) as u8;
                        if v_isSharedCheck_6844_ == 0 {
                            v___x_6835_ = v___x_6832_;
                            v_isShared_6836_ = v_isSharedCheck_6844_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6833_);
                            leanh::lean_dec(v___x_6832_);
                            v___x_6835_ = leanh::lean_box(0);
                            v_isShared_6836_ = v_isSharedCheck_6844_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_6821_);
                        leanh::lean_dec_ref(v_eq_6820_);
                        return v___x_6832_;
                    }
                } else {
                    leanh::lean_dec(v_a_6821_);
                    leanh::lean_dec_ref(v_eq_6820_);
                    v___x_6845_ = 0;
                    v___x_6846_ = leanh::lean_box((v___x_6845_) as usize);
                    v___x_6847_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6847_, 0, v___x_6846_);
                    return v___x_6847_;
                }
            }
            1 => {
                v___x_6837_ = (leanh::lean_unbox(v_a_6833_) as u8);
                if v___x_6837_ == 0 {
                    leanh::lean_del_object(v___x_6835_);
                    leanh::lean_dec(v_a_6833_);
                    v___x_6838_ = 1usize;
                    v___x_6839_ = lean_usize_add(v_i_6823_, v___x_6838_);
                    v_i_6823_ = v___x_6839_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_6821_);
                    leanh::lean_dec_ref(v_eq_6820_);
                    if v_isShared_6836_ == 0 {
                        v___x_6842_ = v___x_6835_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6843_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6843_, 0, v_a_6833_);
                        v___x_6842_ = v_reuseFailAlloc_6843_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg___boxed(
    mut v_eq_6848_: *mut leanh::LeanObject,
    mut v_a_6849_: *mut leanh::LeanObject,
    mut v_as_6850_: *mut leanh::LeanObject,
    mut v_i_6851_: *mut leanh::LeanObject,
    mut v_stop_6852_: *mut leanh::LeanObject,
    mut v___y_6853_: *mut leanh::LeanObject,
    mut v___y_6854_: *mut leanh::LeanObject,
    mut v___y_6855_: *mut leanh::LeanObject,
    mut v___y_6856_: *mut leanh::LeanObject,
    mut v___y_6857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_6858_: usize = 0;
    let mut v_stop_boxed_6859_: usize = 0;
    let mut v_res_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6858_ = leanh::lean_unbox_usize(v_i_6851_);
    leanh::lean_dec(v_i_6851_);
    v_stop_boxed_6859_ = leanh::lean_unbox_usize(v_stop_6852_);
    leanh::lean_dec(v_stop_6852_);
    v_res_6860_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_6848_, v_a_6849_, v_as_6850_, v_i_boxed_6858_, v_stop_boxed_6859_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_);
    leanh::lean_dec(v___y_6856_);
    leanh::lean_dec_ref(v___y_6855_);
    leanh::lean_dec(v___y_6854_);
    leanh::lean_dec_ref(v___y_6853_);
    leanh::lean_dec_ref(v_as_6850_);
    return v_res_6860_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(
    mut v_b_6861_: *mut leanh::LeanObject,
    mut v_a_6862_: *mut leanh::LeanObject,
    mut v_____do__lift_6863_: u8,
    mut v___y_6864_: *mut leanh::LeanObject,
    mut v___y_6865_: *mut leanh::LeanObject,
    mut v___y_6866_: *mut leanh::LeanObject,
    mut v___y_6867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v_____do__lift_6863_ == 0 {
        let mut v___x_6869_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6870_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6871_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_6869_ = lean_array_push(v_b_6861_, v_a_6862_);
        v___x_6870_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6870_, 0, v___x_6869_);
        v___x_6871_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6871_, 0, v___x_6870_);
        return v___x_6871_;
    } else {
        let mut v___x_6872_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6873_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec(v_a_6862_);
        v___x_6872_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6872_, 0, v_b_6861_);
        v___x_6873_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_6873_, 0, v___x_6872_);
        return v___x_6873_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0___boxed(
    mut v_b_6874_: *mut leanh::LeanObject,
    mut v_a_6875_: *mut leanh::LeanObject,
    mut v_____do__lift_6876_: *mut leanh::LeanObject,
    mut v___y_6877_: *mut leanh::LeanObject,
    mut v___y_6878_: *mut leanh::LeanObject,
    mut v___y_6879_: *mut leanh::LeanObject,
    mut v___y_6880_: *mut leanh::LeanObject,
    mut v___y_6881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____do__lift_1292__boxed_6882_: u8 = 0;
    let mut v_res_6883_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_____do__lift_1292__boxed_6882_ = (leanh::lean_unbox(v_____do__lift_6876_) as u8);
    v_res_6883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_6874_, v_a_6875_, v_____do__lift_1292__boxed_6882_, v___y_6877_, v___y_6878_, v___y_6879_, v___y_6880_);
    leanh::lean_dec(v___y_6880_);
    leanh::lean_dec_ref(v___y_6879_);
    leanh::lean_dec(v___y_6878_);
    leanh::lean_dec_ref(v___y_6877_);
    return v_res_6883_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(
    mut v_eq_6884_: *mut leanh::LeanObject,
    mut v_as_6885_: *mut leanh::LeanObject,
    mut v_sz_6886_: usize,
    mut v_i_6887_: usize,
    mut v_b_6888_: *mut leanh::LeanObject,
    mut v___y_6889_: *mut leanh::LeanObject,
    mut v___y_6890_: *mut leanh::LeanObject,
    mut v___y_6891_: *mut leanh::LeanObject,
    mut v___y_6892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6896_: usize = 0;
    let mut v___x_6897_: usize = 0;
    let mut v___y_6900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6904_: u8 = 0;
    let mut v_a_6905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6910_: u8 = 0;
    let mut v_a_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6914_: u8 = 0;
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6918_: u8 = 0;
    let mut v___x_6919_: u8 = 0;
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: u8 = 0;
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: usize = 0;
    let mut v___x_6928_: usize = 0;
    let mut v___x_6929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6931_: u8 = 0;
    let mut v___x_6932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6936_: u8 = 0;
    let mut v___x_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6940_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6919_ = lean_usize_dec_lt(v_i_6887_, v_sz_6886_);
                if v___x_6919_ == 0 {
                    leanh::lean_dec_ref(v_eq_6884_);
                    v___x_6920_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6920_, 0, v_b_6888_);
                    return v___x_6920_;
                } else {
                    v___x_6921_ = leanh::lean_unsigned_to_nat(0);
                    v_a_6922_ = lean_array_uget_borrowed(v_as_6885_, v_i_6887_);
                    v___x_6923_ = lean_array_get_size(v_b_6888_);
                    v___x_6924_ = lean_nat_dec_lt(v___x_6921_, v___x_6923_);
                    if v___x_6924_ == 0 {
                        leanh::lean_inc(v_a_6922_);
                        v___x_6925_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_6888_, v_a_6922_, v___x_6924_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_);
                        v___y_6900_ = v___x_6925_;
                        state = 2;
                        continue;
                    } else {
                        if v___x_6924_ == 0 {
                            leanh::lean_inc(v_a_6922_);
                            v___x_6926_ = lean_array_push(v_b_6888_, v_a_6922_);
                            v_a_6895_ = v___x_6926_;
                            state = 1;
                            continue;
                        } else {
                            v___x_6927_ = 0usize;
                            v___x_6928_ = lean_usize_of_nat(v___x_6923_);
                            leanh::lean_inc(v_a_6922_);
                            leanh::lean_inc_ref(v_eq_6884_);
                            v___x_6929_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_6884_, v_a_6922_, v_b_6888_, v___x_6927_, v___x_6928_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_);
                            if leanh::lean_obj_tag(v___x_6929_) == 0 {
                                v_a_6930_ = leanh::lean_ctor_get(v___x_6929_, 0);
                                leanh::lean_inc(v_a_6930_);
                                leanh::lean_dec_ref_known(v___x_6929_, 1);
                                v___x_6931_ = (leanh::lean_unbox(v_a_6930_) as u8);
                                leanh::lean_dec(v_a_6930_);
                                leanh::lean_inc(v_a_6922_);
                                v___x_6932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___lam__0(v_b_6888_, v_a_6922_, v___x_6931_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_);
                                v___y_6900_ = v___x_6932_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_dec_ref(v_b_6888_);
                                leanh::lean_dec_ref(v_eq_6884_);
                                v_a_6933_ = leanh::lean_ctor_get(v___x_6929_, 0);
                                v_isSharedCheck_6940_ =
                                    (!leanh::lean_is_exclusive(v___x_6929_)) as u8;
                                if v_isSharedCheck_6940_ == 0 {
                                    v___x_6935_ = v___x_6929_;
                                    v_isShared_6936_ = v_isSharedCheck_6940_;
                                    state = 7;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_6933_);
                                    leanh::lean_dec(v___x_6929_);
                                    v___x_6935_ = leanh::lean_box(0);
                                    v_isShared_6936_ = v_isSharedCheck_6940_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_6896_ = 1usize;
                v___x_6897_ = lean_usize_add(v_i_6887_, v___x_6896_);
                v_i_6887_ = v___x_6897_;
                v_b_6888_ = v_a_6895_;
                state = 0;
                continue;
            }
            2 => {
                if leanh::lean_obj_tag(v___y_6900_) == 0 {
                    v_a_6901_ = leanh::lean_ctor_get(v___y_6900_, 0);
                    v_isSharedCheck_6910_ = (!leanh::lean_is_exclusive(v___y_6900_)) as u8;
                    if v_isSharedCheck_6910_ == 0 {
                        v___x_6903_ = v___y_6900_;
                        v_isShared_6904_ = v_isSharedCheck_6910_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6901_);
                        leanh::lean_dec(v___y_6900_);
                        v___x_6903_ = leanh::lean_box(0);
                        v_isShared_6904_ = v_isSharedCheck_6910_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_eq_6884_);
                    v_a_6911_ = leanh::lean_ctor_get(v___y_6900_, 0);
                    v_isSharedCheck_6918_ = (!leanh::lean_is_exclusive(v___y_6900_)) as u8;
                    if v_isSharedCheck_6918_ == 0 {
                        v___x_6913_ = v___y_6900_;
                        v_isShared_6914_ = v_isSharedCheck_6918_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6911_);
                        leanh::lean_dec(v___y_6900_);
                        v___x_6913_ = leanh::lean_box(0);
                        v_isShared_6914_ = v_isSharedCheck_6918_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if leanh::lean_obj_tag(v_a_6901_) == 0 {
                    leanh::lean_dec_ref(v_eq_6884_);
                    v_a_6905_ = leanh::lean_ctor_get(v_a_6901_, 0);
                    leanh::lean_inc(v_a_6905_);
                    leanh::lean_dec_ref_known(v_a_6901_, 1);
                    if v_isShared_6904_ == 0 {
                        leanh::lean_ctor_set(v___x_6903_, 0, v_a_6905_);
                        v___x_6907_ = v___x_6903_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6908_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6908_, 0, v_a_6905_);
                        v___x_6907_ = v_reuseFailAlloc_6908_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6903_);
                    v_a_6909_ = leanh::lean_ctor_get(v_a_6901_, 0);
                    leanh::lean_inc(v_a_6909_);
                    leanh::lean_dec_ref_known(v_a_6901_, 1);
                    v_a_6895_ = v_a_6909_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                return v___x_6907_;
            }
            5 => {
                if v_isShared_6914_ == 0 {
                    v___x_6916_ = v___x_6913_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6917_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6917_, 0, v_a_6911_);
                    v___x_6916_ = v_reuseFailAlloc_6917_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6916_;
            }
            7 => {
                if v_isShared_6936_ == 0 {
                    v___x_6938_ = v___x_6935_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_6939_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6939_, 0, v_a_6933_);
                    v___x_6938_ = v_reuseFailAlloc_6939_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_6938_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg___boxed(
    mut v_eq_6941_: *mut leanh::LeanObject,
    mut v_as_6942_: *mut leanh::LeanObject,
    mut v_sz_6943_: *mut leanh::LeanObject,
    mut v_i_6944_: *mut leanh::LeanObject,
    mut v_b_6945_: *mut leanh::LeanObject,
    mut v___y_6946_: *mut leanh::LeanObject,
    mut v___y_6947_: *mut leanh::LeanObject,
    mut v___y_6948_: *mut leanh::LeanObject,
    mut v___y_6949_: *mut leanh::LeanObject,
    mut v___y_6950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6951_: usize = 0;
    let mut v_i_boxed_6952_: usize = 0;
    let mut v_res_6953_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6951_ = leanh::lean_unbox_usize(v_sz_6943_);
    leanh::lean_dec(v_sz_6943_);
    v_i_boxed_6952_ = leanh::lean_unbox_usize(v_i_6944_);
    leanh::lean_dec(v_i_6944_);
    v_res_6953_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_6941_, v_as_6942_, v_sz_boxed_6951_, v_i_boxed_6952_, v_b_6945_, v___y_6946_, v___y_6947_, v___y_6948_, v___y_6949_);
    leanh::lean_dec(v___y_6949_);
    leanh::lean_dec_ref(v___y_6948_);
    leanh::lean_dec(v___y_6947_);
    leanh::lean_dec_ref(v___y_6946_);
    leanh::lean_dec_ref(v_as_6942_);
    return v_res_6953_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(
    mut v_eq_6954_: *mut leanh::LeanObject,
    mut v_xs_6955_: *mut leanh::LeanObject,
    mut v___y_6956_: *mut leanh::LeanObject,
    mut v___y_6957_: *mut leanh::LeanObject,
    mut v___y_6958_: *mut leanh::LeanObject,
    mut v___y_6959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ret_6961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6962_: usize = 0;
    let mut v___x_6963_: usize = 0;
    let mut v___x_6964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_ret_6961_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0;
    v_sz_6962_ = lean_array_size(v_xs_6955_);
    v___x_6963_ = 0usize;
    v___x_6964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_6954_, v_xs_6955_, v_sz_6962_, v___x_6963_, v_ret_6961_, v___y_6956_, v___y_6957_, v___y_6958_, v___y_6959_);
    return v___x_6964_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg___boxed(
    mut v_eq_6965_: *mut leanh::LeanObject,
    mut v_xs_6966_: *mut leanh::LeanObject,
    mut v___y_6967_: *mut leanh::LeanObject,
    mut v___y_6968_: *mut leanh::LeanObject,
    mut v___y_6969_: *mut leanh::LeanObject,
    mut v___y_6970_: *mut leanh::LeanObject,
    mut v___y_6971_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6972_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_6965_, v_xs_6966_, v___y_6967_, v___y_6968_, v___y_6969_, v___y_6970_);
    leanh::lean_dec(v___y_6970_);
    leanh::lean_dec_ref(v___y_6969_);
    leanh::lean_dec(v___y_6968_);
    leanh::lean_dec_ref(v___y_6967_);
    leanh::lean_dec_ref(v_xs_6966_);
    return v_res_6972_;
}
pub unsafe fn l_Lean_Elab_Structural_inductiveGroups(
    mut v_recArgInfos_6974_: *mut leanh::LeanObject,
    mut v_a_6975_: *mut leanh::LeanObject,
    mut v_a_6976_: *mut leanh::LeanObject,
    mut v_a_6977_: *mut leanh::LeanObject,
    mut v_a_6978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6981_: usize = 0;
    let mut v___x_6982_: usize = 0;
    let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6980_ = l_Lean_Elab_Structural_inductiveGroups___closed__0;
    v_sz_6981_ = lean_array_size(v_recArgInfos_6974_);
    v___x_6982_ = 0usize;
    v___x_6983_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_inductiveGroups_spec__0(v_sz_6981_, v___x_6982_, v_recArgInfos_6974_);
    v___x_6984_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v___x_6980_, v___x_6983_, v_a_6975_, v_a_6976_, v_a_6977_, v_a_6978_);
    leanh::lean_dec_ref(v___x_6983_);
    return v___x_6984_;
}
pub unsafe fn l_Lean_Elab_Structural_inductiveGroups___boxed(
    mut v_recArgInfos_6985_: *mut leanh::LeanObject,
    mut v_a_6986_: *mut leanh::LeanObject,
    mut v_a_6987_: *mut leanh::LeanObject,
    mut v_a_6988_: *mut leanh::LeanObject,
    mut v_a_6989_: *mut leanh::LeanObject,
    mut v_a_6990_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6991_ = l_Lean_Elab_Structural_inductiveGroups(
        v_recArgInfos_6985_,
        v_a_6986_,
        v_a_6987_,
        v_a_6988_,
        v_a_6989_,
    );
    leanh::lean_dec(v_a_6989_);
    leanh::lean_dec_ref(v_a_6988_);
    leanh::lean_dec(v_a_6987_);
    leanh::lean_dec_ref(v_a_6986_);
    return v_res_6991_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(
    mut v_00_u03b1_6992_: *mut leanh::LeanObject,
    mut v_eq_6993_: *mut leanh::LeanObject,
    mut v_xs_6994_: *mut leanh::LeanObject,
    mut v___y_6995_: *mut leanh::LeanObject,
    mut v___y_6996_: *mut leanh::LeanObject,
    mut v___y_6997_: *mut leanh::LeanObject,
    mut v___y_6998_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7000_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7000_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___redArg(v_eq_6993_, v_xs_6994_, v___y_6995_, v___y_6996_, v___y_6997_, v___y_6998_);
    return v___x_7000_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1___boxed(
    mut v_00_u03b1_7001_: *mut leanh::LeanObject,
    mut v_eq_7002_: *mut leanh::LeanObject,
    mut v_xs_7003_: *mut leanh::LeanObject,
    mut v___y_7004_: *mut leanh::LeanObject,
    mut v___y_7005_: *mut leanh::LeanObject,
    mut v___y_7006_: *mut leanh::LeanObject,
    mut v___y_7007_: *mut leanh::LeanObject,
    mut v___y_7008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7009_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7009_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1(v_00_u03b1_7001_, v_eq_7002_, v_xs_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_);
    leanh::lean_dec(v___y_7007_);
    leanh::lean_dec_ref(v___y_7006_);
    leanh::lean_dec(v___y_7005_);
    leanh::lean_dec_ref(v___y_7004_);
    leanh::lean_dec_ref(v_xs_7003_);
    return v_res_7009_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(
    mut v_00_u03b1_7010_: *mut leanh::LeanObject,
    mut v_eq_7011_: *mut leanh::LeanObject,
    mut v_a_7012_: *mut leanh::LeanObject,
    mut v_as_7013_: *mut leanh::LeanObject,
    mut v_i_7014_: usize,
    mut v_stop_7015_: usize,
    mut v___y_7016_: *mut leanh::LeanObject,
    mut v___y_7017_: *mut leanh::LeanObject,
    mut v___y_7018_: *mut leanh::LeanObject,
    mut v___y_7019_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7021_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___redArg(v_eq_7011_, v_a_7012_, v_as_7013_, v_i_7014_, v_stop_7015_, v___y_7016_, v___y_7017_, v___y_7018_, v___y_7019_);
    return v___x_7021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1___boxed(
    mut v_00_u03b1_7022_: *mut leanh::LeanObject,
    mut v_eq_7023_: *mut leanh::LeanObject,
    mut v_a_7024_: *mut leanh::LeanObject,
    mut v_as_7025_: *mut leanh::LeanObject,
    mut v_i_7026_: *mut leanh::LeanObject,
    mut v_stop_7027_: *mut leanh::LeanObject,
    mut v___y_7028_: *mut leanh::LeanObject,
    mut v___y_7029_: *mut leanh::LeanObject,
    mut v___y_7030_: *mut leanh::LeanObject,
    mut v___y_7031_: *mut leanh::LeanObject,
    mut v___y_7032_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7033_: usize = 0;
    let mut v_stop_boxed_7034_: usize = 0;
    let mut v_res_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7033_ = leanh::lean_unbox_usize(v_i_7026_);
    leanh::lean_dec(v_i_7026_);
    v_stop_boxed_7034_ = leanh::lean_unbox_usize(v_stop_7027_);
    leanh::lean_dec(v_stop_7027_);
    v_res_7035_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__1(v_00_u03b1_7022_, v_eq_7023_, v_a_7024_, v_as_7025_, v_i_boxed_7033_, v_stop_boxed_7034_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_);
    leanh::lean_dec(v___y_7031_);
    leanh::lean_dec_ref(v___y_7030_);
    leanh::lean_dec(v___y_7029_);
    leanh::lean_dec_ref(v___y_7028_);
    leanh::lean_dec_ref(v_as_7025_);
    return v_res_7035_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(
    mut v_00_u03b1_7036_: *mut leanh::LeanObject,
    mut v_eq_7037_: *mut leanh::LeanObject,
    mut v_as_7038_: *mut leanh::LeanObject,
    mut v_sz_7039_: usize,
    mut v_i_7040_: usize,
    mut v_b_7041_: *mut leanh::LeanObject,
    mut v___y_7042_: *mut leanh::LeanObject,
    mut v___y_7043_: *mut leanh::LeanObject,
    mut v___y_7044_: *mut leanh::LeanObject,
    mut v___y_7045_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7047_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___redArg(v_eq_7037_, v_as_7038_, v_sz_7039_, v_i_7040_, v_b_7041_, v___y_7042_, v___y_7043_, v___y_7044_, v___y_7045_);
    return v___x_7047_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2___boxed(
    mut v_00_u03b1_7048_: *mut leanh::LeanObject,
    mut v_eq_7049_: *mut leanh::LeanObject,
    mut v_as_7050_: *mut leanh::LeanObject,
    mut v_sz_7051_: *mut leanh::LeanObject,
    mut v_i_7052_: *mut leanh::LeanObject,
    mut v_b_7053_: *mut leanh::LeanObject,
    mut v___y_7054_: *mut leanh::LeanObject,
    mut v___y_7055_: *mut leanh::LeanObject,
    mut v___y_7056_: *mut leanh::LeanObject,
    mut v___y_7057_: *mut leanh::LeanObject,
    mut v___y_7058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7059_: usize = 0;
    let mut v_i_boxed_7060_: usize = 0;
    let mut v_res_7061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7059_ = leanh::lean_unbox_usize(v_sz_7051_);
    leanh::lean_dec(v_sz_7051_);
    v_i_boxed_7060_ = leanh::lean_unbox_usize(v_i_7052_);
    leanh::lean_dec(v_i_7052_);
    v_res_7061_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___at___00Lean_Elab_Structural_inductiveGroups_spec__1_spec__2(v_00_u03b1_7048_, v_eq_7049_, v_as_7050_, v_sz_boxed_7059_, v_i_boxed_7060_, v_b_7053_, v___y_7054_, v___y_7055_, v___y_7056_, v___y_7057_);
    leanh::lean_dec(v___y_7057_);
    leanh::lean_dec_ref(v___y_7056_);
    leanh::lean_dec(v___y_7055_);
    leanh::lean_dec_ref(v___y_7054_);
    leanh::lean_dec_ref(v_as_7050_);
    return v_res_7061_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(
    mut v_e_7062_: *mut leanh::LeanObject,
    mut v___y_7063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7065_: u8 = 0;
    let mut v___x_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_zetaDeltaFVarIds_7074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_postponed_7075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7079_: u8 = 0;
    let mut v___x_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7085_: u8 = 0;
    let mut v_unused_7086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7065_ = l_Lean_Expr_hasMVar(v_e_7062_);
                if v___x_7065_ == 0 {
                    v___x_7066_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7066_, 0, v_e_7062_);
                    return v___x_7066_;
                } else {
                    v___x_7067_ = lean_st_ref_get(v___y_7063_);
                    v_mctx_7068_ = leanh::lean_ctor_get(v___x_7067_, 0);
                    leanh::lean_inc_ref(v_mctx_7068_);
                    leanh::lean_dec(v___x_7067_);
                    v___x_7069_ = l_Lean_instantiateMVarsCore(v_mctx_7068_, v_e_7062_);
                    v_fst_7070_ = leanh::lean_ctor_get(v___x_7069_, 0);
                    leanh::lean_inc(v_fst_7070_);
                    v_snd_7071_ = leanh::lean_ctor_get(v___x_7069_, 1);
                    leanh::lean_inc(v_snd_7071_);
                    leanh::lean_dec_ref(v___x_7069_);
                    v___x_7072_ = lean_st_ref_take(v___y_7063_);
                    v_cache_7073_ = leanh::lean_ctor_get(v___x_7072_, 1);
                    v_zetaDeltaFVarIds_7074_ = leanh::lean_ctor_get(v___x_7072_, 2);
                    v_postponed_7075_ = leanh::lean_ctor_get(v___x_7072_, 3);
                    v_diag_7076_ = leanh::lean_ctor_get(v___x_7072_, 4);
                    v_isSharedCheck_7085_ = (!leanh::lean_is_exclusive(v___x_7072_)) as u8;
                    if v_isSharedCheck_7085_ == 0 {
                        v_unused_7086_ = leanh::lean_ctor_get(v___x_7072_, 0);
                        leanh::lean_dec(v_unused_7086_);
                        v___x_7078_ = v___x_7072_;
                        v_isShared_7079_ = v_isSharedCheck_7085_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_diag_7076_);
                        leanh::lean_inc(v_postponed_7075_);
                        leanh::lean_inc(v_zetaDeltaFVarIds_7074_);
                        leanh::lean_inc(v_cache_7073_);
                        leanh::lean_dec(v___x_7072_);
                        v___x_7078_ = leanh::lean_box(0);
                        v_isShared_7079_ = v_isSharedCheck_7085_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7079_ == 0 {
                    leanh::lean_ctor_set(v___x_7078_, 0, v_snd_7071_);
                    v___x_7081_ = v___x_7078_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7084_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7084_, 0, v_snd_7071_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7084_, 1, v_cache_7073_);
                    leanh::lean_ctor_set(
                        v_reuseFailAlloc_7084_,
                        2,
                        v_zetaDeltaFVarIds_7074_,
                    );
                    leanh::lean_ctor_set(v_reuseFailAlloc_7084_, 3, v_postponed_7075_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7084_, 4, v_diag_7076_);
                    v___x_7081_ = v_reuseFailAlloc_7084_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7082_ = lean_st_ref_set(v___y_7063_, v___x_7081_);
                v___x_7083_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7083_, 0, v_fst_7070_);
                return v___x_7083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg___boxed(
    mut v_e_7087_: *mut leanh::LeanObject,
    mut v___y_7088_: *mut leanh::LeanObject,
    mut v___y_7089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7090_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7090_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(
            v_e_7087_,
            v___y_7088_,
        );
    leanh::lean_dec(v___y_7088_);
    return v_res_7090_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(
    mut v_e_7091_: *mut leanh::LeanObject,
    mut v___y_7092_: *mut leanh::LeanObject,
    mut v___y_7093_: *mut leanh::LeanObject,
    mut v___y_7094_: *mut leanh::LeanObject,
    mut v___y_7095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7097_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7097_ =
        l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(
            v_e_7091_,
            v___y_7093_,
        );
    return v___x_7097_;
}
pub unsafe fn l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___boxed(
    mut v_e_7098_: *mut leanh::LeanObject,
    mut v___y_7099_: *mut leanh::LeanObject,
    mut v___y_7100_: *mut leanh::LeanObject,
    mut v___y_7101_: *mut leanh::LeanObject,
    mut v___y_7102_: *mut leanh::LeanObject,
    mut v___y_7103_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7104_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7104_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0(
        v_e_7098_,
        v___y_7099_,
        v___y_7100_,
        v___y_7101_,
        v___y_7102_,
    );
    leanh::lean_dec(v___y_7102_);
    leanh::lean_dec_ref(v___y_7101_);
    leanh::lean_dec(v___y_7100_);
    leanh::lean_dec_ref(v___y_7099_);
    return v_res_7104_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7111_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7106_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__2;
    v___x_7107_ = leanh::lean_unsigned_to_nat(109);
    v___x_7108_ = leanh::lean_unsigned_to_nat(216);
    v___x_7109_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__0;
    v___x_7110_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_getRecArgInfo_spec__4___closed__0;
    v___x_7111_ = l_mkPanicMessageWithDecl(
        v___x_7110_,
        v___x_7109_,
        v___x_7108_,
        v___x_7107_,
        v___x_7106_,
    );
    return v___x_7111_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(
    mut v___x_7112_: *mut leanh::LeanObject,
    mut v_sz_7113_: usize,
    mut v_i_7114_: usize,
    mut v_bs_7115_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7116_: u8 = 0;
    let mut v_v_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7122_: usize = 0;
    let mut v___x_7123_: usize = 0;
    let mut v___x_7124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7116_ = lean_usize_dec_lt(v_i_7114_, v_sz_7113_);
                if v___x_7116_ == 0 {
                    return v_bs_7115_;
                } else {
                    v_v_7117_ = lean_array_uget(v_bs_7115_, v_i_7114_);
                    v___x_7118_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_7119_ = lean_array_uset(v_bs_7115_, v_i_7114_, v___x_7118_);
                    v___x_7126_ = l_Array_idxOf_x3f___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_getIndexMinPos_spec__0(v___x_7112_, v_v_7117_);
                    leanh::lean_dec(v_v_7117_);
                    if leanh::lean_obj_tag(v___x_7126_) == 0 {
                        v___x_7127_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___closed__1);
                        v___x_7128_ = l_panic___at___00Lean_Elab_Structural_getRecArgInfo_spec__1(
                            v___x_7127_,
                        );
                        v___y_7121_ = v___x_7128_;
                        state = 1;
                        continue;
                    } else {
                        v_val_7129_ = leanh::lean_ctor_get(v___x_7126_, 0);
                        leanh::lean_inc(v_val_7129_);
                        leanh::lean_dec_ref_known(v___x_7126_, 1);
                        v___y_7121_ = v_val_7129_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7122_ = 1usize;
                v___x_7123_ = lean_usize_add(v_i_7114_, v___x_7122_);
                v___x_7124_ = lean_array_uset(v_bs_x27_7119_, v_i_7114_, v___y_7121_);
                v_i_7114_ = v___x_7123_;
                v_bs_7115_ = v___x_7124_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2___boxed(
    mut v___x_7130_: *mut leanh::LeanObject,
    mut v_sz_7131_: *mut leanh::LeanObject,
    mut v_i_7132_: *mut leanh::LeanObject,
    mut v_bs_7133_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7134_: usize = 0;
    let mut v_i_boxed_7135_: usize = 0;
    let mut v_res_7136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7134_ = leanh::lean_unbox_usize(v_sz_7131_);
    leanh::lean_dec(v_sz_7131_);
    v_i_boxed_7135_ = leanh::lean_unbox_usize(v_i_7132_);
    leanh::lean_dec(v_i_7132_);
    v_res_7136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_7130_, v_sz_boxed_7134_, v_i_boxed_7135_, v_bs_7133_);
    leanh::lean_dec_ref(v___x_7130_);
    return v_res_7136_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(
    mut v_sz_7137_: usize,
    mut v_i_7138_: usize,
    mut v_bs_7139_: *mut leanh::LeanObject,
    mut v___y_7140_: *mut leanh::LeanObject,
    mut v___y_7141_: *mut leanh::LeanObject,
    mut v___y_7142_: *mut leanh::LeanObject,
    mut v___y_7143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7145_: u8 = 0;
    let mut v___x_7146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_7147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7151_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7152_: usize = 0;
    let mut v___x_7153_: usize = 0;
    let mut v___x_7154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7159_: u8 = 0;
    let mut v___x_7161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7163_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7145_ = lean_usize_dec_lt(v_i_7138_, v_sz_7137_);
                if v___x_7145_ == 0 {
                    v___x_7146_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7146_, 0, v_bs_7139_);
                    return v___x_7146_;
                } else {
                    v_v_7147_ = lean_array_uget_borrowed(v_bs_7139_, v_i_7138_);
                    leanh::lean_inc(v_v_7147_);
                    v___x_7148_ = l_Lean_instantiateMVars___at___00Lean_Elab_Structural_argsInGroup_spec__0___redArg(v_v_7147_, v___y_7141_);
                    if leanh::lean_obj_tag(v___x_7148_) == 0 {
                        v_a_7149_ = leanh::lean_ctor_get(v___x_7148_, 0);
                        leanh::lean_inc(v_a_7149_);
                        leanh::lean_dec_ref_known(v___x_7148_, 1);
                        v___x_7150_ = leanh::lean_unsigned_to_nat(0);
                        v_bs_x27_7151_ = lean_array_uset(v_bs_7139_, v_i_7138_, v___x_7150_);
                        v___x_7152_ = 1usize;
                        v___x_7153_ = lean_usize_add(v_i_7138_, v___x_7152_);
                        v___x_7154_ = lean_array_uset(v_bs_x27_7151_, v_i_7138_, v_a_7149_);
                        v_i_7138_ = v___x_7153_;
                        v_bs_7139_ = v___x_7154_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v_bs_7139_);
                        v_a_7156_ = leanh::lean_ctor_get(v___x_7148_, 0);
                        v_isSharedCheck_7163_ =
                            (!leanh::lean_is_exclusive(v___x_7148_)) as u8;
                        if v_isSharedCheck_7163_ == 0 {
                            v___x_7158_ = v___x_7148_;
                            v_isShared_7159_ = v_isSharedCheck_7163_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7156_);
                            leanh::lean_dec(v___x_7148_);
                            v___x_7158_ = leanh::lean_box(0);
                            v_isShared_7159_ = v_isSharedCheck_7163_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7159_ == 0 {
                    v___x_7161_ = v___x_7158_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7162_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7162_, 0, v_a_7156_);
                    v___x_7161_ = v_reuseFailAlloc_7162_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7161_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1___boxed(
    mut v_sz_7164_: *mut leanh::LeanObject,
    mut v_i_7165_: *mut leanh::LeanObject,
    mut v_bs_7166_: *mut leanh::LeanObject,
    mut v___y_7167_: *mut leanh::LeanObject,
    mut v___y_7168_: *mut leanh::LeanObject,
    mut v___y_7169_: *mut leanh::LeanObject,
    mut v___y_7170_: *mut leanh::LeanObject,
    mut v___y_7171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7172_: usize = 0;
    let mut v_i_boxed_7173_: usize = 0;
    let mut v_res_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7172_ = leanh::lean_unbox_usize(v_sz_7164_);
    leanh::lean_dec(v_sz_7164_);
    v_i_boxed_7173_ = leanh::lean_unbox_usize(v_i_7165_);
    leanh::lean_dec(v_i_7165_);
    v_res_7174_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_boxed_7172_, v_i_boxed_7173_, v_bs_7166_, v___y_7167_, v___y_7168_, v___y_7169_, v___y_7170_);
    leanh::lean_dec(v___y_7170_);
    leanh::lean_dec_ref(v___y_7169_);
    leanh::lean_dec(v___y_7168_);
    leanh::lean_dec_ref(v___y_7167_);
    return v_res_7174_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(
    mut v_a_7175_: u8,
    mut v___x_7176_: *mut leanh::LeanObject,
    mut v_as_7177_: *mut leanh::LeanObject,
    mut v_i_7178_: usize,
    mut v_stop_7179_: usize,
) -> u8 {
    let mut v___x_7180_: u8 = 0;
    let mut v___x_7181_: u8 = 0;
    let mut v___y_7183_: u8 = 0;
    let mut v___x_7184_: usize = 0;
    let mut v___x_7185_: usize = 0;
    let mut v___x_7187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7188_: u8 = 0;
    let mut v___x_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7190_: u8 = 0;
    let mut v___x_7191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7180_ = lean_usize_dec_eq(v_i_7178_, v_stop_7179_);
                if v___x_7180_ == 0 {
                    v___x_7181_ = 1;
                    v___x_7187_ = lean_array_uget_borrowed(v_as_7177_, v_i_7178_);
                    v___x_7188_ = l_Lean_Expr_isFVar(v___x_7187_);
                    if v___x_7188_ == 0 {
                        v___y_7183_ = v_a_7175_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7189_ = leanh::lean_unsigned_to_nat(0);
                        v___x_7190_ = lean_nat_dec_eq(v___x_7176_, v___x_7189_);
                        v___y_7183_ = v___x_7190_;
                        state = 1;
                        continue;
                    }
                } else {
                    v___x_7191_ = 0;
                    return v___x_7191_;
                }
            }
            1 => {
                if v___y_7183_ == 0 {
                    v___x_7184_ = 1usize;
                    v___x_7185_ = lean_usize_add(v_i_7178_, v___x_7184_);
                    v_i_7178_ = v___x_7185_;
                    state = 0;
                    continue;
                } else {
                    return v___x_7181_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3___boxed(
    mut v_a_7192_: *mut leanh::LeanObject,
    mut v___x_7193_: *mut leanh::LeanObject,
    mut v_as_7194_: *mut leanh::LeanObject,
    mut v_i_7195_: *mut leanh::LeanObject,
    mut v_stop_7196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_9779__boxed_7197_: u8 = 0;
    let mut v_i_boxed_7198_: usize = 0;
    let mut v_stop_boxed_7199_: usize = 0;
    let mut v_res_7200_: u8 = 0;
    let mut v_r_7201_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_a_9779__boxed_7197_ = (leanh::lean_unbox(v_a_7192_) as u8);
    v_i_boxed_7198_ = leanh::lean_unbox_usize(v_i_7195_);
    leanh::lean_dec(v_i_7195_);
    v_stop_boxed_7199_ = leanh::lean_unbox_usize(v_stop_7196_);
    leanh::lean_dec(v_stop_7196_);
    v_res_7200_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v_a_9779__boxed_7197_, v___x_7193_, v_as_7194_, v_i_boxed_7198_, v_stop_boxed_7199_);
    leanh::lean_dec_ref(v_as_7194_);
    leanh::lean_dec(v___x_7193_);
    v_r_7201_ = leanh::lean_box((v_res_7200_) as usize);
    return v_r_7201_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(
    mut v___x_7202_: *mut leanh::LeanObject,
    mut v___x_7203_: *mut leanh::LeanObject,
    mut v_ys_7204_: *mut leanh::LeanObject,
    mut v___x_7205_: *mut leanh::LeanObject,
    mut v_recArgInfo_7206_: *mut leanh::LeanObject,
    mut v___x_7207_: *mut leanh::LeanObject,
    mut v___x_7208_: *mut leanh::LeanObject,
    mut v_group_7209_: *mut leanh::LeanObject,
    mut v_as_7210_: *mut leanh::LeanObject,
    mut v_sz_7211_: usize,
    mut v_i_7212_: usize,
    mut v_b_7213_: *mut leanh::LeanObject,
    mut v___y_7214_: *mut leanh::LeanObject,
    mut v___y_7215_: *mut leanh::LeanObject,
    mut v___y_7216_: *mut leanh::LeanObject,
    mut v___y_7217_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: usize = 0;
    let mut v___x_7222_: usize = 0;
    let mut v___x_7224_: u8 = 0;
    let mut v___x_7225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7229_: u8 = 0;
    let mut v_next_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_7231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7241_: u8 = 0;
    let mut v___x_7242_: u8 = 0;
    let mut v___x_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7245_: u8 = 0;
    let mut v___x_7246_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7251_: u8 = 0;
    let mut v___x_7252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7258_: u8 = 0;
    let mut v_snd_7259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7262_: u8 = 0;
    let mut v___x_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7271_: u8 = 0;
    let mut v___x_7273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7275_: usize = 0;
    let mut v___x_7276_: usize = 0;
    let mut v___x_7277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: u8 = 0;
    let mut v___x_7286_: u8 = 0;
    let mut v___x_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7294_: u8 = 0;
    let mut v___x_7296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnName_7298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7301_: u8 = 0;
    let mut v_sz_7302_: usize = 0;
    let mut v___x_7303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7307_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7315_: u8 = 0;
    let mut v_unused_7316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7321_: u8 = 0;
    let mut v_a_7322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7325_: u8 = 0;
    let mut v___x_7327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7329_: u8 = 0;
    let mut v___x_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7331_: u8 = 0;
    let mut v___x_7332_: usize = 0;
    let mut v___x_7333_: u8 = 0;
    let mut v___x_7334_: u8 = 0;
    let mut v_a_7335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7338_: u8 = 0;
    let mut v___x_7340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7341_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7342_: u8 = 0;
    let mut v_reuseFailAlloc_7343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7348_: u8 = 0;
    let mut v___x_7350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7352_: u8 = 0;
    let mut v_isSharedCheck_7353_: u8 = 0;
    let mut v_unused_7354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7355_: u8 = 0;
    let mut v_a_7356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7359_: u8 = 0;
    let mut v___x_7361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7363_: u8 = 0;
    let mut v_a_7364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7367_: u8 = 0;
    let mut v___x_7369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7371_: u8 = 0;
    let mut v_a_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7375_: u8 = 0;
    let mut v___x_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7379_: u8 = 0;
    let mut v_isSharedCheck_7380_: u8 = 0;
    let mut v_unused_7381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7383_: u8 = 0;
    let mut v_isSharedCheck_7384_: u8 = 0;
    let mut v_unused_7385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7224_ = lean_usize_dec_lt(v_i_7212_, v_sz_7211_);
                if v___x_7224_ == 0 {
                    leanh::lean_dec_ref(v_group_7209_);
                    leanh::lean_dec(v___x_7208_);
                    leanh::lean_dec_ref(v___x_7207_);
                    leanh::lean_dec_ref(v_recArgInfo_7206_);
                    leanh::lean_dec_ref(v___x_7202_);
                    v___x_7225_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7225_, 0, v_b_7213_);
                    return v___x_7225_;
                } else {
                    v_snd_7226_ = leanh::lean_ctor_get(v_b_7213_, 1);
                    v_isSharedCheck_7384_ = (!leanh::lean_is_exclusive(v_b_7213_)) as u8;
                    if v_isSharedCheck_7384_ == 0 {
                        v_unused_7385_ = leanh::lean_ctor_get(v_b_7213_, 0);
                        leanh::lean_dec(v_unused_7385_);
                        v___x_7228_ = v_b_7213_;
                        v_isShared_7229_ = v_isSharedCheck_7384_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_7226_);
                        leanh::lean_dec(v_b_7213_);
                        v___x_7228_ = leanh::lean_box(0);
                        v_isShared_7229_ = v_isSharedCheck_7384_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7221_ = 1usize;
                v___x_7222_ = lean_usize_add(v_i_7212_, v___x_7221_);
                v_i_7212_ = v___x_7222_;
                v_b_7213_ = v_a_7220_;
                state = 0;
                continue;
            }
            2 => {
                v_next_7230_ = leanh::lean_ctor_get(v_snd_7226_, 0);
                leanh::lean_inc(v_next_7230_);
                v_upperBound_7231_ = leanh::lean_ctor_get(v_snd_7226_, 1);
                v___x_7232_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v_next_7230_) == 0 {
                    leanh::lean_dec_ref(v_group_7209_);
                    leanh::lean_dec(v___x_7208_);
                    leanh::lean_dec_ref(v___x_7207_);
                    leanh::lean_dec_ref(v_recArgInfo_7206_);
                    leanh::lean_dec_ref(v___x_7202_);
                    state = 3;
                    continue;
                } else {
                    v_val_7238_ = leanh::lean_ctor_get(v_next_7230_, 0);
                    v_isSharedCheck_7383_ = (!leanh::lean_is_exclusive(v_next_7230_)) as u8;
                    if v_isSharedCheck_7383_ == 0 {
                        v___x_7240_ = v_next_7230_;
                        v_isShared_7241_ = v_isSharedCheck_7383_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7238_);
                        leanh::lean_dec(v_next_7230_);
                        v___x_7240_ = leanh::lean_box(0);
                        v_isShared_7241_ = v_isSharedCheck_7383_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7229_ == 0 {
                    leanh::lean_ctor_set(v___x_7228_, 0, v___x_7232_);
                    v___x_7235_ = v___x_7228_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7237_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7237_, 0, v___x_7232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7237_, 1, v_snd_7226_);
                    v___x_7235_ = v_reuseFailAlloc_7237_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7236_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7236_, 0, v___x_7235_);
                return v___x_7236_;
            }
            5 => {
                v___x_7242_ = lean_nat_dec_lt(v_val_7238_, v_upperBound_7231_);
                if v___x_7242_ == 0 {
                    leanh::lean_del_object(v___x_7240_);
                    leanh::lean_dec(v_val_7238_);
                    leanh::lean_dec_ref(v_group_7209_);
                    leanh::lean_dec(v___x_7208_);
                    leanh::lean_dec_ref(v___x_7207_);
                    leanh::lean_dec_ref(v_recArgInfo_7206_);
                    leanh::lean_dec_ref(v___x_7202_);
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_upperBound_7231_);
                    leanh::lean_del_object(v___x_7228_);
                    v_isSharedCheck_7380_ = (!leanh::lean_is_exclusive(v_snd_7226_)) as u8;
                    if v_isSharedCheck_7380_ == 0 {
                        v_unused_7381_ = leanh::lean_ctor_get(v_snd_7226_, 1);
                        leanh::lean_dec(v_unused_7381_);
                        v_unused_7382_ = leanh::lean_ctor_get(v_snd_7226_, 0);
                        leanh::lean_dec(v_unused_7382_);
                        v___x_7244_ = v_snd_7226_;
                        v_isShared_7245_ = v_isSharedCheck_7380_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_7226_);
                        v___x_7244_ = leanh::lean_box(0);
                        v_isShared_7245_ = v_isSharedCheck_7380_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                leanh::lean_inc(v___y_7217_);
                leanh::lean_inc_ref(v___y_7216_);
                leanh::lean_inc(v___y_7215_);
                leanh::lean_inc_ref(v___y_7214_);
                leanh::lean_inc_ref(v___x_7202_);
                v___x_7246_ = lean_infer_type(
                    v___x_7202_,
                    v___y_7214_,
                    v___y_7215_,
                    v___y_7216_,
                    v___y_7217_,
                );
                if leanh::lean_obj_tag(v___x_7246_) == 0 {
                    v_a_7247_ = leanh::lean_ctor_get(v___x_7246_, 0);
                    leanh::lean_inc(v_a_7247_);
                    leanh::lean_dec_ref_known(v___x_7246_, 1);
                    v___x_7248_ = l_Lean_Meta_whnfD(
                        v_a_7247_,
                        v___y_7214_,
                        v___y_7215_,
                        v___y_7216_,
                        v___y_7217_,
                    );
                    if leanh::lean_obj_tag(v___x_7248_) == 0 {
                        v_a_7249_ = leanh::lean_ctor_get(v___x_7248_, 0);
                        leanh::lean_inc(v_a_7249_);
                        leanh::lean_dec_ref_known(v___x_7248_, 1);
                        v_a_7250_ = lean_array_uget_borrowed(v_as_7210_, v_i_7212_);
                        v___x_7251_ = 0;
                        leanh::lean_inc(v_a_7250_);
                        v___x_7252_ = l_Lean_Meta_forallMetaTelescope(
                            v_a_7250_,
                            v___x_7251_,
                            v___y_7214_,
                            v___y_7215_,
                            v___y_7216_,
                            v___y_7217_,
                        );
                        if leanh::lean_obj_tag(v___x_7252_) == 0 {
                            v_a_7253_ = leanh::lean_ctor_get(v___x_7252_, 0);
                            leanh::lean_inc(v_a_7253_);
                            leanh::lean_dec_ref_known(v___x_7252_, 1);
                            v_snd_7254_ = leanh::lean_ctor_get(v_a_7253_, 1);
                            v_fst_7255_ = leanh::lean_ctor_get(v_a_7253_, 0);
                            v_isSharedCheck_7355_ =
                                (!leanh::lean_is_exclusive(v_a_7253_)) as u8;
                            if v_isSharedCheck_7355_ == 0 {
                                v___x_7257_ = v_a_7253_;
                                v_isShared_7258_ = v_isSharedCheck_7355_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_7254_);
                                leanh::lean_inc(v_fst_7255_);
                                leanh::lean_dec(v_a_7253_);
                                v___x_7257_ = leanh::lean_box(0);
                                v_isShared_7258_ = v_isSharedCheck_7355_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7249_);
                            leanh::lean_del_object(v___x_7244_);
                            leanh::lean_del_object(v___x_7240_);
                            leanh::lean_dec(v_val_7238_);
                            leanh::lean_dec(v_upperBound_7231_);
                            leanh::lean_dec_ref(v_group_7209_);
                            leanh::lean_dec(v___x_7208_);
                            leanh::lean_dec_ref(v___x_7207_);
                            leanh::lean_dec_ref(v_recArgInfo_7206_);
                            leanh::lean_dec_ref(v___x_7202_);
                            v_a_7356_ = leanh::lean_ctor_get(v___x_7252_, 0);
                            v_isSharedCheck_7363_ =
                                (!leanh::lean_is_exclusive(v___x_7252_)) as u8;
                            if v_isSharedCheck_7363_ == 0 {
                                v___x_7358_ = v___x_7252_;
                                v_isShared_7359_ = v_isSharedCheck_7363_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7356_);
                                leanh::lean_dec(v___x_7252_);
                                v___x_7358_ = leanh::lean_box(0);
                                v_isShared_7359_ = v_isSharedCheck_7363_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_7244_);
                        leanh::lean_del_object(v___x_7240_);
                        leanh::lean_dec(v_val_7238_);
                        leanh::lean_dec(v_upperBound_7231_);
                        leanh::lean_dec_ref(v_group_7209_);
                        leanh::lean_dec(v___x_7208_);
                        leanh::lean_dec_ref(v___x_7207_);
                        leanh::lean_dec_ref(v_recArgInfo_7206_);
                        leanh::lean_dec_ref(v___x_7202_);
                        v_a_7364_ = leanh::lean_ctor_get(v___x_7248_, 0);
                        v_isSharedCheck_7371_ =
                            (!leanh::lean_is_exclusive(v___x_7248_)) as u8;
                        if v_isSharedCheck_7371_ == 0 {
                            v___x_7366_ = v___x_7248_;
                            v_isShared_7367_ = v_isSharedCheck_7371_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7364_);
                            leanh::lean_dec(v___x_7248_);
                            v___x_7366_ = leanh::lean_box(0);
                            v_isShared_7367_ = v_isSharedCheck_7371_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7244_);
                    leanh::lean_del_object(v___x_7240_);
                    leanh::lean_dec(v_val_7238_);
                    leanh::lean_dec(v_upperBound_7231_);
                    leanh::lean_dec_ref(v_group_7209_);
                    leanh::lean_dec(v___x_7208_);
                    leanh::lean_dec_ref(v___x_7207_);
                    leanh::lean_dec_ref(v_recArgInfo_7206_);
                    leanh::lean_dec_ref(v___x_7202_);
                    v_a_7372_ = leanh::lean_ctor_get(v___x_7246_, 0);
                    v_isSharedCheck_7379_ = (!leanh::lean_is_exclusive(v___x_7246_)) as u8;
                    if v_isSharedCheck_7379_ == 0 {
                        v___x_7374_ = v___x_7246_;
                        v_isShared_7375_ = v_isSharedCheck_7379_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7372_);
                        leanh::lean_dec(v___x_7246_);
                        v___x_7374_ = leanh::lean_box(0);
                        v_isShared_7375_ = v_isSharedCheck_7379_;
                        state = 32;
                        continue;
                    }
                }
            }
            7 => {
                v_snd_7259_ = leanh::lean_ctor_get(v_snd_7254_, 1);
                v_isSharedCheck_7353_ = (!leanh::lean_is_exclusive(v_snd_7254_)) as u8;
                if v_isSharedCheck_7353_ == 0 {
                    v_unused_7354_ = leanh::lean_ctor_get(v_snd_7254_, 0);
                    leanh::lean_dec(v_unused_7354_);
                    v___x_7261_ = v_snd_7254_;
                    v_isShared_7262_ = v_isSharedCheck_7353_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7259_);
                    leanh::lean_dec(v_snd_7254_);
                    v___x_7261_ = leanh::lean_box(0);
                    v_isShared_7262_ = v_isSharedCheck_7353_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7263_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_snd_7259_,
                    v_a_7249_,
                    v___y_7214_,
                    v___y_7215_,
                    v___y_7216_,
                    v___y_7217_,
                );
                if leanh::lean_obj_tag(v___x_7263_) == 0 {
                    v_a_7264_ = leanh::lean_ctor_get(v___x_7263_, 0);
                    leanh::lean_inc(v_a_7264_);
                    leanh::lean_dec_ref_known(v___x_7263_, 1);
                    v___x_7265_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7266_ = lean_nat_add(v_val_7238_, v___x_7265_);
                    if v_isShared_7241_ == 0 {
                        leanh::lean_ctor_set(v___x_7240_, 0, v___x_7266_);
                        v___x_7268_ = v___x_7240_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_7344_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7344_, 0, v___x_7266_);
                        v___x_7268_ = v_reuseFailAlloc_7344_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7261_);
                    leanh::lean_del_object(v___x_7257_);
                    leanh::lean_dec(v_fst_7255_);
                    leanh::lean_del_object(v___x_7244_);
                    leanh::lean_del_object(v___x_7240_);
                    leanh::lean_dec(v_val_7238_);
                    leanh::lean_dec(v_upperBound_7231_);
                    leanh::lean_dec_ref(v_group_7209_);
                    leanh::lean_dec(v___x_7208_);
                    leanh::lean_dec_ref(v___x_7207_);
                    leanh::lean_dec_ref(v_recArgInfo_7206_);
                    leanh::lean_dec_ref(v___x_7202_);
                    v_a_7345_ = leanh::lean_ctor_get(v___x_7263_, 0);
                    v_isSharedCheck_7352_ = (!leanh::lean_is_exclusive(v___x_7263_)) as u8;
                    if v_isSharedCheck_7352_ == 0 {
                        v___x_7347_ = v___x_7263_;
                        v_isShared_7348_ = v_isSharedCheck_7352_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7345_);
                        leanh::lean_dec(v___x_7263_);
                        v___x_7347_ = leanh::lean_box(0);
                        v_isShared_7348_ = v_isSharedCheck_7352_;
                        state = 26;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_7245_ == 0 {
                    leanh::lean_ctor_set(v___x_7244_, 0, v___x_7268_);
                    v___x_7270_ = v___x_7244_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7343_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7343_, 0, v___x_7268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7343_, 1, v_upperBound_7231_);
                    v___x_7270_ = v_reuseFailAlloc_7343_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_7271_ = (leanh::lean_unbox(v_a_7264_) as u8);
                if v___x_7271_ == 0 {
                    leanh::lean_dec(v_a_7264_);
                    leanh::lean_del_object(v___x_7257_);
                    leanh::lean_dec(v_fst_7255_);
                    leanh::lean_dec(v_val_7238_);
                    if v_isShared_7262_ == 0 {
                        leanh::lean_ctor_set(v___x_7261_, 1, v___x_7270_);
                        leanh::lean_ctor_set(v___x_7261_, 0, v___x_7232_);
                        v___x_7273_ = v___x_7261_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_7274_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7274_, 0, v___x_7232_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7274_, 1, v___x_7270_);
                        v___x_7273_ = v_reuseFailAlloc_7274_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_sz_7275_ = lean_array_size(v_fst_7255_);
                    v___x_7276_ = 0usize;
                    v___x_7277_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_7275_, v___x_7276_, v_fst_7255_, v___y_7214_, v___y_7215_, v___y_7216_, v___y_7217_);
                    if leanh::lean_obj_tag(v___x_7277_) == 0 {
                        v_a_7278_ = leanh::lean_ctor_get(v___x_7277_, 0);
                        leanh::lean_inc(v_a_7278_);
                        leanh::lean_dec_ref_known(v___x_7277_, 1);
                        v___x_7283_ = leanh::lean_unsigned_to_nat(0);
                        v___x_7284_ = lean_nat_dec_eq(v___x_7203_, v___x_7283_);
                        v___x_7330_ = lean_array_get_size(v_a_7278_);
                        v___x_7331_ = lean_nat_dec_lt(v___x_7283_, v___x_7330_);
                        if v___x_7331_ == 0 {
                            leanh::lean_dec(v_a_7264_);
                            state = 14;
                            continue;
                        } else {
                            if v___x_7331_ == 0 {
                                leanh::lean_dec(v_a_7264_);
                                state = 14;
                                continue;
                            } else {
                                v___x_7332_ = lean_usize_of_nat(v___x_7330_);
                                v___x_7333_ = (leanh::lean_unbox(v_a_7264_) as u8);
                                leanh::lean_dec(v_a_7264_);
                                v___x_7334_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_7333_, v___x_7203_, v_a_7278_, v___x_7276_, v___x_7332_);
                                if v___x_7334_ == 0 {
                                    state = 14;
                                    continue;
                                } else {
                                    if v___x_7284_ == 0 {
                                        leanh::lean_dec(v_a_7278_);
                                        leanh::lean_del_object(v___x_7257_);
                                        leanh::lean_dec(v_val_7238_);
                                        state = 12;
                                        continue;
                                    } else {
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_7270_);
                        leanh::lean_dec(v_a_7264_);
                        leanh::lean_del_object(v___x_7261_);
                        leanh::lean_del_object(v___x_7257_);
                        leanh::lean_dec(v_val_7238_);
                        leanh::lean_dec_ref(v_group_7209_);
                        leanh::lean_dec(v___x_7208_);
                        leanh::lean_dec_ref(v___x_7207_);
                        leanh::lean_dec_ref(v_recArgInfo_7206_);
                        leanh::lean_dec_ref(v___x_7202_);
                        v_a_7335_ = leanh::lean_ctor_get(v___x_7277_, 0);
                        v_isSharedCheck_7342_ =
                            (!leanh::lean_is_exclusive(v___x_7277_)) as u8;
                        if v_isSharedCheck_7342_ == 0 {
                            v___x_7337_ = v___x_7277_;
                            v_isShared_7338_ = v_isSharedCheck_7342_;
                            state = 24;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7335_);
                            leanh::lean_dec(v___x_7277_);
                            v___x_7337_ = leanh::lean_box(0);
                            v_isShared_7338_ = v_isSharedCheck_7342_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v_a_7220_ = v___x_7273_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_7262_ == 0 {
                    leanh::lean_ctor_set(v___x_7261_, 1, v___x_7270_);
                    leanh::lean_ctor_set(v___x_7261_, 0, v___x_7232_);
                    v___x_7281_ = v___x_7261_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7282_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7282_, 0, v___x_7232_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7282_, 1, v___x_7270_);
                    v___x_7281_ = v_reuseFailAlloc_7282_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_7220_ = v___x_7281_;
                state = 1;
                continue;
            }
            14 => {
                if v___x_7284_ == 0 {
                    leanh::lean_del_object(v___x_7261_);
                    v___x_7286_ =
                        l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(
                            v_a_7278_,
                        );
                    if v___x_7286_ == 0 {
                        leanh::lean_dec(v_a_7278_);
                        leanh::lean_dec(v_val_7238_);
                        if v_isShared_7258_ == 0 {
                            leanh::lean_ctor_set(v___x_7257_, 1, v___x_7270_);
                            leanh::lean_ctor_set(v___x_7257_, 0, v___x_7232_);
                            v___x_7288_ = v___x_7257_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_7289_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 0, v___x_7232_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7289_, 1, v___x_7270_);
                            v___x_7288_ = v_reuseFailAlloc_7289_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_7290_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_7204_, v_a_7278_, v___y_7214_, v___y_7215_, v___y_7216_, v___y_7217_);
                        if leanh::lean_obj_tag(v___x_7290_) == 0 {
                            v_a_7291_ = leanh::lean_ctor_get(v___x_7290_, 0);
                            v_isSharedCheck_7321_ =
                                (!leanh::lean_is_exclusive(v___x_7290_)) as u8;
                            if v_isSharedCheck_7321_ == 0 {
                                v___x_7293_ = v___x_7290_;
                                v_isShared_7294_ = v_isSharedCheck_7321_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7291_);
                                leanh::lean_dec(v___x_7290_);
                                v___x_7293_ = leanh::lean_box(0);
                                v_isShared_7294_ = v_isSharedCheck_7321_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7278_);
                            leanh::lean_dec_ref(v___x_7270_);
                            leanh::lean_del_object(v___x_7257_);
                            leanh::lean_dec(v_val_7238_);
                            leanh::lean_dec_ref(v_group_7209_);
                            leanh::lean_dec(v___x_7208_);
                            leanh::lean_dec_ref(v___x_7207_);
                            leanh::lean_dec_ref(v_recArgInfo_7206_);
                            leanh::lean_dec_ref(v___x_7202_);
                            v_a_7322_ = leanh::lean_ctor_get(v___x_7290_, 0);
                            v_isSharedCheck_7329_ =
                                (!leanh::lean_is_exclusive(v___x_7290_)) as u8;
                            if v_isSharedCheck_7329_ == 0 {
                                v___x_7324_ = v___x_7290_;
                                v_isShared_7325_ = v_isSharedCheck_7329_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7322_);
                                leanh::lean_dec(v___x_7290_);
                                v___x_7324_ = leanh::lean_box(0);
                                v_isShared_7325_ = v_isSharedCheck_7329_;
                                state = 22;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_7278_);
                    leanh::lean_del_object(v___x_7257_);
                    leanh::lean_dec(v_val_7238_);
                    state = 12;
                    continue;
                }
            }
            15 => {
                v_a_7220_ = v___x_7288_;
                state = 1;
                continue;
            }
            16 => {
                if leanh::lean_obj_tag(v_a_7291_) == 1 {
                    leanh::lean_dec_ref_known(v_a_7291_, 1);
                    leanh::lean_del_object(v___x_7293_);
                    leanh::lean_dec(v_a_7278_);
                    leanh::lean_dec(v_val_7238_);
                    if v_isShared_7258_ == 0 {
                        leanh::lean_ctor_set(v___x_7257_, 1, v___x_7270_);
                        leanh::lean_ctor_set(v___x_7257_, 0, v___x_7232_);
                        v___x_7296_ = v___x_7257_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_7297_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7297_, 0, v___x_7232_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7297_, 1, v___x_7270_);
                        v___x_7296_ = v_reuseFailAlloc_7297_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7291_);
                    leanh::lean_dec_ref(v___x_7202_);
                    v_fnName_7298_ = leanh::lean_ctor_get(v_recArgInfo_7206_, 0);
                    v_isSharedCheck_7315_ =
                        (!leanh::lean_is_exclusive(v_recArgInfo_7206_)) as u8;
                    if v_isSharedCheck_7315_ == 0 {
                        v_unused_7316_ = leanh::lean_ctor_get(v_recArgInfo_7206_, 5);
                        leanh::lean_dec(v_unused_7316_);
                        v_unused_7317_ = leanh::lean_ctor_get(v_recArgInfo_7206_, 4);
                        leanh::lean_dec(v_unused_7317_);
                        v_unused_7318_ = leanh::lean_ctor_get(v_recArgInfo_7206_, 3);
                        leanh::lean_dec(v_unused_7318_);
                        v_unused_7319_ = leanh::lean_ctor_get(v_recArgInfo_7206_, 2);
                        leanh::lean_dec(v_unused_7319_);
                        v_unused_7320_ = leanh::lean_ctor_get(v_recArgInfo_7206_, 1);
                        leanh::lean_dec(v_unused_7320_);
                        v___x_7300_ = v_recArgInfo_7206_;
                        v_isShared_7301_ = v_isSharedCheck_7315_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_fnName_7298_);
                        leanh::lean_dec(v_recArgInfo_7206_);
                        v___x_7300_ = leanh::lean_box(0);
                        v_isShared_7301_ = v_isSharedCheck_7315_;
                        state = 18;
                        continue;
                    }
                }
            }
            17 => {
                v_a_7220_ = v___x_7296_;
                state = 1;
                continue;
            }
            18 => {
                v_sz_7302_ = lean_array_size(v_a_7278_);
                v___x_7303_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_7205_, v_sz_7302_, v___x_7276_, v_a_7278_);
                if v_isShared_7301_ == 0 {
                    leanh::lean_ctor_set(v___x_7300_, 5, v_val_7238_);
                    leanh::lean_ctor_set(v___x_7300_, 4, v_group_7209_);
                    leanh::lean_ctor_set(v___x_7300_, 3, v___x_7303_);
                    leanh::lean_ctor_set(v___x_7300_, 2, v___x_7208_);
                    leanh::lean_ctor_set(v___x_7300_, 1, v___x_7207_);
                    v___x_7305_ = v___x_7300_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7314_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7314_, 0, v_fnName_7298_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7314_, 1, v___x_7207_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7314_, 2, v___x_7208_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7314_, 3, v___x_7303_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7314_, 4, v_group_7209_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7314_, 5, v_val_7238_);
                    v___x_7305_ = v_reuseFailAlloc_7314_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_7306_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7306_, 0, v___x_7305_);
                v___x_7307_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7307_, 0, v___x_7306_);
                if v_isShared_7258_ == 0 {
                    leanh::lean_ctor_set(v___x_7257_, 1, v___x_7270_);
                    leanh::lean_ctor_set(v___x_7257_, 0, v___x_7307_);
                    v___x_7309_ = v___x_7257_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7313_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7313_, 0, v___x_7307_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7313_, 1, v___x_7270_);
                    v___x_7309_ = v_reuseFailAlloc_7313_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_7294_ == 0 {
                    leanh::lean_ctor_set(v___x_7293_, 0, v___x_7309_);
                    v___x_7311_ = v___x_7293_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7312_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7312_, 0, v___x_7309_);
                    v___x_7311_ = v_reuseFailAlloc_7312_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7311_;
            }
            22 => {
                if v_isShared_7325_ == 0 {
                    v___x_7327_ = v___x_7324_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7328_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7328_, 0, v_a_7322_);
                    v___x_7327_ = v_reuseFailAlloc_7328_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7327_;
            }
            24 => {
                if v_isShared_7338_ == 0 {
                    v___x_7340_ = v___x_7337_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7341_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7341_, 0, v_a_7335_);
                    v___x_7340_ = v_reuseFailAlloc_7341_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7340_;
            }
            26 => {
                if v_isShared_7348_ == 0 {
                    v___x_7350_ = v___x_7347_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7351_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7351_, 0, v_a_7345_);
                    v___x_7350_ = v_reuseFailAlloc_7351_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_7350_;
            }
            28 => {
                if v_isShared_7359_ == 0 {
                    v___x_7361_ = v___x_7358_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_7362_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7362_, 0, v_a_7356_);
                    v___x_7361_ = v_reuseFailAlloc_7362_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_7361_;
            }
            30 => {
                if v_isShared_7367_ == 0 {
                    v___x_7369_ = v___x_7366_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7370_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7370_, 0, v_a_7364_);
                    v___x_7369_ = v_reuseFailAlloc_7370_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7369_;
            }
            32 => {
                if v_isShared_7375_ == 0 {
                    v___x_7377_ = v___x_7374_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7378_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7378_, 0, v_a_7372_);
                    v___x_7377_ = v_reuseFailAlloc_7378_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7377_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7386_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_7387_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_ys_7388_: *mut leanh::LeanObject = *_args.add(2);
    let mut v___x_7389_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_recArgInfo_7390_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_7391_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_7392_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_group_7393_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_as_7394_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_sz_7395_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_i_7396_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_b_7397_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_7398_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7399_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7400_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7401_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7402_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_7403_: usize = 0;
    let mut v_i_boxed_7404_: usize = 0;
    let mut v_res_7405_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7403_ = leanh::lean_unbox_usize(v_sz_7395_);
    leanh::lean_dec(v_sz_7395_);
    v_i_boxed_7404_ = leanh::lean_unbox_usize(v_i_7396_);
    leanh::lean_dec(v_i_7396_);
    v_res_7405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_7386_, v___x_7387_, v_ys_7388_, v___x_7389_, v_recArgInfo_7390_, v___x_7391_, v___x_7392_, v_group_7393_, v_as_7394_, v_sz_boxed_7403_, v_i_boxed_7404_, v_b_7397_, v___y_7398_, v___y_7399_, v___y_7400_, v___y_7401_);
    leanh::lean_dec(v___y_7401_);
    leanh::lean_dec_ref(v___y_7400_);
    leanh::lean_dec(v___y_7399_);
    leanh::lean_dec_ref(v___y_7398_);
    leanh::lean_dec_ref(v_as_7394_);
    leanh::lean_dec_ref(v___x_7389_);
    leanh::lean_dec_ref(v_ys_7388_);
    leanh::lean_dec(v___x_7387_);
    return v_res_7405_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(
    mut v___x_7406_: *mut leanh::LeanObject,
    mut v___x_7407_: *mut leanh::LeanObject,
    mut v___x_7408_: *mut leanh::LeanObject,
    mut v_ys_7409_: *mut leanh::LeanObject,
    mut v_recArgInfo_7410_: *mut leanh::LeanObject,
    mut v___x_7411_: *mut leanh::LeanObject,
    mut v___x_7412_: *mut leanh::LeanObject,
    mut v_group_7413_: *mut leanh::LeanObject,
    mut v_as_7414_: *mut leanh::LeanObject,
    mut v_sz_7415_: usize,
    mut v_i_7416_: usize,
    mut v_b_7417_: *mut leanh::LeanObject,
    mut v___y_7418_: *mut leanh::LeanObject,
    mut v___y_7419_: *mut leanh::LeanObject,
    mut v___y_7420_: *mut leanh::LeanObject,
    mut v___y_7421_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7424_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7425_: usize = 0;
    let mut v___x_7426_: usize = 0;
    let mut v___x_7427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: u8 = 0;
    let mut v___x_7429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7433_: u8 = 0;
    let mut v_next_7434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_upperBound_7435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7445_: u8 = 0;
    let mut v___x_7446_: u8 = 0;
    let mut v___x_7448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7449_: u8 = 0;
    let mut v___x_7450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7455_: u8 = 0;
    let mut v___x_7456_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7462_: u8 = 0;
    let mut v_snd_7463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7466_: u8 = 0;
    let mut v___x_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7475_: u8 = 0;
    let mut v___x_7477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7479_: usize = 0;
    let mut v___x_7480_: usize = 0;
    let mut v___x_7481_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7488_: u8 = 0;
    let mut v___x_7490_: u8 = 0;
    let mut v___x_7492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7498_: u8 = 0;
    let mut v___x_7500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fnName_7502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7505_: u8 = 0;
    let mut v_sz_7506_: usize = 0;
    let mut v___x_7507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7519_: u8 = 0;
    let mut v_unused_7520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7525_: u8 = 0;
    let mut v_a_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7529_: u8 = 0;
    let mut v___x_7531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7533_: u8 = 0;
    let mut v___x_7534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7535_: u8 = 0;
    let mut v___x_7536_: usize = 0;
    let mut v___x_7537_: u8 = 0;
    let mut v___x_7538_: u8 = 0;
    let mut v_a_7539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7542_: u8 = 0;
    let mut v___x_7544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7546_: u8 = 0;
    let mut v_reuseFailAlloc_7547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7551_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7552_: u8 = 0;
    let mut v___x_7554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7556_: u8 = 0;
    let mut v_isSharedCheck_7557_: u8 = 0;
    let mut v_unused_7558_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7559_: u8 = 0;
    let mut v_a_7560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7563_: u8 = 0;
    let mut v___x_7565_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7567_: u8 = 0;
    let mut v_a_7568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7571_: u8 = 0;
    let mut v___x_7573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7575_: u8 = 0;
    let mut v_a_7576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7579_: u8 = 0;
    let mut v___x_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7583_: u8 = 0;
    let mut v_isSharedCheck_7584_: u8 = 0;
    let mut v_unused_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7587_: u8 = 0;
    let mut v_isSharedCheck_7588_: u8 = 0;
    let mut v_unused_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7428_ = lean_usize_dec_lt(v_i_7416_, v_sz_7415_);
                if v___x_7428_ == 0 {
                    leanh::lean_dec_ref(v_group_7413_);
                    leanh::lean_dec(v___x_7412_);
                    leanh::lean_dec_ref(v___x_7411_);
                    leanh::lean_dec_ref(v_recArgInfo_7410_);
                    leanh::lean_dec_ref(v___x_7406_);
                    v___x_7429_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7429_, 0, v_b_7417_);
                    return v___x_7429_;
                } else {
                    v_snd_7430_ = leanh::lean_ctor_get(v_b_7417_, 1);
                    v_isSharedCheck_7588_ = (!leanh::lean_is_exclusive(v_b_7417_)) as u8;
                    if v_isSharedCheck_7588_ == 0 {
                        v_unused_7589_ = leanh::lean_ctor_get(v_b_7417_, 0);
                        leanh::lean_dec(v_unused_7589_);
                        v___x_7432_ = v_b_7417_;
                        v_isShared_7433_ = v_isSharedCheck_7588_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_7430_);
                        leanh::lean_dec(v_b_7417_);
                        v___x_7432_ = leanh::lean_box(0);
                        v_isShared_7433_ = v_isSharedCheck_7588_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7425_ = 1usize;
                v___x_7426_ = lean_usize_add(v_i_7416_, v___x_7425_);
                v___x_7427_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4_spec__4(v___x_7406_, v___x_7407_, v_ys_7409_, v___x_7408_, v_recArgInfo_7410_, v___x_7411_, v___x_7412_, v_group_7413_, v_as_7414_, v_sz_7415_, v___x_7426_, v_a_7424_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_);
                return v___x_7427_;
            }
            2 => {
                v_next_7434_ = leanh::lean_ctor_get(v_snd_7430_, 0);
                leanh::lean_inc(v_next_7434_);
                v_upperBound_7435_ = leanh::lean_ctor_get(v_snd_7430_, 1);
                v___x_7436_ = leanh::lean_box(0);
                if leanh::lean_obj_tag(v_next_7434_) == 0 {
                    leanh::lean_dec_ref(v_group_7413_);
                    leanh::lean_dec(v___x_7412_);
                    leanh::lean_dec_ref(v___x_7411_);
                    leanh::lean_dec_ref(v_recArgInfo_7410_);
                    leanh::lean_dec_ref(v___x_7406_);
                    state = 3;
                    continue;
                } else {
                    v_val_7442_ = leanh::lean_ctor_get(v_next_7434_, 0);
                    v_isSharedCheck_7587_ = (!leanh::lean_is_exclusive(v_next_7434_)) as u8;
                    if v_isSharedCheck_7587_ == 0 {
                        v___x_7444_ = v_next_7434_;
                        v_isShared_7445_ = v_isSharedCheck_7587_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_7442_);
                        leanh::lean_dec(v_next_7434_);
                        v___x_7444_ = leanh::lean_box(0);
                        v_isShared_7445_ = v_isSharedCheck_7587_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7433_ == 0 {
                    leanh::lean_ctor_set(v___x_7432_, 0, v___x_7436_);
                    v___x_7439_ = v___x_7432_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7441_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7441_, 0, v___x_7436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7441_, 1, v_snd_7430_);
                    v___x_7439_ = v_reuseFailAlloc_7441_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7440_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7440_, 0, v___x_7439_);
                return v___x_7440_;
            }
            5 => {
                v___x_7446_ = lean_nat_dec_lt(v_val_7442_, v_upperBound_7435_);
                if v___x_7446_ == 0 {
                    leanh::lean_del_object(v___x_7444_);
                    leanh::lean_dec(v_val_7442_);
                    leanh::lean_dec_ref(v_group_7413_);
                    leanh::lean_dec(v___x_7412_);
                    leanh::lean_dec_ref(v___x_7411_);
                    leanh::lean_dec_ref(v_recArgInfo_7410_);
                    leanh::lean_dec_ref(v___x_7406_);
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_upperBound_7435_);
                    leanh::lean_del_object(v___x_7432_);
                    v_isSharedCheck_7584_ = (!leanh::lean_is_exclusive(v_snd_7430_)) as u8;
                    if v_isSharedCheck_7584_ == 0 {
                        v_unused_7585_ = leanh::lean_ctor_get(v_snd_7430_, 1);
                        leanh::lean_dec(v_unused_7585_);
                        v_unused_7586_ = leanh::lean_ctor_get(v_snd_7430_, 0);
                        leanh::lean_dec(v_unused_7586_);
                        v___x_7448_ = v_snd_7430_;
                        v_isShared_7449_ = v_isSharedCheck_7584_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_7430_);
                        v___x_7448_ = leanh::lean_box(0);
                        v_isShared_7449_ = v_isSharedCheck_7584_;
                        state = 6;
                        continue;
                    }
                }
            }
            6 => {
                leanh::lean_inc(v___y_7421_);
                leanh::lean_inc_ref(v___y_7420_);
                leanh::lean_inc(v___y_7419_);
                leanh::lean_inc_ref(v___y_7418_);
                leanh::lean_inc_ref(v___x_7406_);
                v___x_7450_ = lean_infer_type(
                    v___x_7406_,
                    v___y_7418_,
                    v___y_7419_,
                    v___y_7420_,
                    v___y_7421_,
                );
                if leanh::lean_obj_tag(v___x_7450_) == 0 {
                    v_a_7451_ = leanh::lean_ctor_get(v___x_7450_, 0);
                    leanh::lean_inc(v_a_7451_);
                    leanh::lean_dec_ref_known(v___x_7450_, 1);
                    v___x_7452_ = l_Lean_Meta_whnfD(
                        v_a_7451_,
                        v___y_7418_,
                        v___y_7419_,
                        v___y_7420_,
                        v___y_7421_,
                    );
                    if leanh::lean_obj_tag(v___x_7452_) == 0 {
                        v_a_7453_ = leanh::lean_ctor_get(v___x_7452_, 0);
                        leanh::lean_inc(v_a_7453_);
                        leanh::lean_dec_ref_known(v___x_7452_, 1);
                        v_a_7454_ = lean_array_uget_borrowed(v_as_7414_, v_i_7416_);
                        v___x_7455_ = 0;
                        leanh::lean_inc(v_a_7454_);
                        v___x_7456_ = l_Lean_Meta_forallMetaTelescope(
                            v_a_7454_,
                            v___x_7455_,
                            v___y_7418_,
                            v___y_7419_,
                            v___y_7420_,
                            v___y_7421_,
                        );
                        if leanh::lean_obj_tag(v___x_7456_) == 0 {
                            v_a_7457_ = leanh::lean_ctor_get(v___x_7456_, 0);
                            leanh::lean_inc(v_a_7457_);
                            leanh::lean_dec_ref_known(v___x_7456_, 1);
                            v_snd_7458_ = leanh::lean_ctor_get(v_a_7457_, 1);
                            v_fst_7459_ = leanh::lean_ctor_get(v_a_7457_, 0);
                            v_isSharedCheck_7559_ =
                                (!leanh::lean_is_exclusive(v_a_7457_)) as u8;
                            if v_isSharedCheck_7559_ == 0 {
                                v___x_7461_ = v_a_7457_;
                                v_isShared_7462_ = v_isSharedCheck_7559_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_7458_);
                                leanh::lean_inc(v_fst_7459_);
                                leanh::lean_dec(v_a_7457_);
                                v___x_7461_ = leanh::lean_box(0);
                                v_isShared_7462_ = v_isSharedCheck_7559_;
                                state = 7;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7453_);
                            leanh::lean_del_object(v___x_7448_);
                            leanh::lean_del_object(v___x_7444_);
                            leanh::lean_dec(v_val_7442_);
                            leanh::lean_dec(v_upperBound_7435_);
                            leanh::lean_dec_ref(v_group_7413_);
                            leanh::lean_dec(v___x_7412_);
                            leanh::lean_dec_ref(v___x_7411_);
                            leanh::lean_dec_ref(v_recArgInfo_7410_);
                            leanh::lean_dec_ref(v___x_7406_);
                            v_a_7560_ = leanh::lean_ctor_get(v___x_7456_, 0);
                            v_isSharedCheck_7567_ =
                                (!leanh::lean_is_exclusive(v___x_7456_)) as u8;
                            if v_isSharedCheck_7567_ == 0 {
                                v___x_7562_ = v___x_7456_;
                                v_isShared_7563_ = v_isSharedCheck_7567_;
                                state = 28;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7560_);
                                leanh::lean_dec(v___x_7456_);
                                v___x_7562_ = leanh::lean_box(0);
                                v_isShared_7563_ = v_isSharedCheck_7567_;
                                state = 28;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_del_object(v___x_7448_);
                        leanh::lean_del_object(v___x_7444_);
                        leanh::lean_dec(v_val_7442_);
                        leanh::lean_dec(v_upperBound_7435_);
                        leanh::lean_dec_ref(v_group_7413_);
                        leanh::lean_dec(v___x_7412_);
                        leanh::lean_dec_ref(v___x_7411_);
                        leanh::lean_dec_ref(v_recArgInfo_7410_);
                        leanh::lean_dec_ref(v___x_7406_);
                        v_a_7568_ = leanh::lean_ctor_get(v___x_7452_, 0);
                        v_isSharedCheck_7575_ =
                            (!leanh::lean_is_exclusive(v___x_7452_)) as u8;
                        if v_isSharedCheck_7575_ == 0 {
                            v___x_7570_ = v___x_7452_;
                            v_isShared_7571_ = v_isSharedCheck_7575_;
                            state = 30;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7568_);
                            leanh::lean_dec(v___x_7452_);
                            v___x_7570_ = leanh::lean_box(0);
                            v_isShared_7571_ = v_isSharedCheck_7575_;
                            state = 30;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_7448_);
                    leanh::lean_del_object(v___x_7444_);
                    leanh::lean_dec(v_val_7442_);
                    leanh::lean_dec(v_upperBound_7435_);
                    leanh::lean_dec_ref(v_group_7413_);
                    leanh::lean_dec(v___x_7412_);
                    leanh::lean_dec_ref(v___x_7411_);
                    leanh::lean_dec_ref(v_recArgInfo_7410_);
                    leanh::lean_dec_ref(v___x_7406_);
                    v_a_7576_ = leanh::lean_ctor_get(v___x_7450_, 0);
                    v_isSharedCheck_7583_ = (!leanh::lean_is_exclusive(v___x_7450_)) as u8;
                    if v_isSharedCheck_7583_ == 0 {
                        v___x_7578_ = v___x_7450_;
                        v_isShared_7579_ = v_isSharedCheck_7583_;
                        state = 32;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7576_);
                        leanh::lean_dec(v___x_7450_);
                        v___x_7578_ = leanh::lean_box(0);
                        v_isShared_7579_ = v_isSharedCheck_7583_;
                        state = 32;
                        continue;
                    }
                }
            }
            7 => {
                v_snd_7463_ = leanh::lean_ctor_get(v_snd_7458_, 1);
                v_isSharedCheck_7557_ = (!leanh::lean_is_exclusive(v_snd_7458_)) as u8;
                if v_isSharedCheck_7557_ == 0 {
                    v_unused_7558_ = leanh::lean_ctor_get(v_snd_7458_, 0);
                    leanh::lean_dec(v_unused_7558_);
                    v___x_7465_ = v_snd_7458_;
                    v_isShared_7466_ = v_isSharedCheck_7557_;
                    state = 8;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7463_);
                    leanh::lean_dec(v_snd_7458_);
                    v___x_7465_ = leanh::lean_box(0);
                    v_isShared_7466_ = v_isSharedCheck_7557_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7467_ = l_Lean_Meta_isExprDefEqGuarded(
                    v_snd_7463_,
                    v_a_7453_,
                    v___y_7418_,
                    v___y_7419_,
                    v___y_7420_,
                    v___y_7421_,
                );
                if leanh::lean_obj_tag(v___x_7467_) == 0 {
                    v_a_7468_ = leanh::lean_ctor_get(v___x_7467_, 0);
                    leanh::lean_inc(v_a_7468_);
                    leanh::lean_dec_ref_known(v___x_7467_, 1);
                    v___x_7469_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7470_ = lean_nat_add(v_val_7442_, v___x_7469_);
                    if v_isShared_7445_ == 0 {
                        leanh::lean_ctor_set(v___x_7444_, 0, v___x_7470_);
                        v___x_7472_ = v___x_7444_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_7548_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7548_, 0, v___x_7470_);
                        v___x_7472_ = v_reuseFailAlloc_7548_;
                        state = 9;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7465_);
                    leanh::lean_del_object(v___x_7461_);
                    leanh::lean_dec(v_fst_7459_);
                    leanh::lean_del_object(v___x_7448_);
                    leanh::lean_del_object(v___x_7444_);
                    leanh::lean_dec(v_val_7442_);
                    leanh::lean_dec(v_upperBound_7435_);
                    leanh::lean_dec_ref(v_group_7413_);
                    leanh::lean_dec(v___x_7412_);
                    leanh::lean_dec_ref(v___x_7411_);
                    leanh::lean_dec_ref(v_recArgInfo_7410_);
                    leanh::lean_dec_ref(v___x_7406_);
                    v_a_7549_ = leanh::lean_ctor_get(v___x_7467_, 0);
                    v_isSharedCheck_7556_ = (!leanh::lean_is_exclusive(v___x_7467_)) as u8;
                    if v_isSharedCheck_7556_ == 0 {
                        v___x_7551_ = v___x_7467_;
                        v_isShared_7552_ = v_isSharedCheck_7556_;
                        state = 26;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7549_);
                        leanh::lean_dec(v___x_7467_);
                        v___x_7551_ = leanh::lean_box(0);
                        v_isShared_7552_ = v_isSharedCheck_7556_;
                        state = 26;
                        continue;
                    }
                }
            }
            9 => {
                if v_isShared_7449_ == 0 {
                    leanh::lean_ctor_set(v___x_7448_, 0, v___x_7472_);
                    v___x_7474_ = v___x_7448_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_7547_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7547_, 0, v___x_7472_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7547_, 1, v_upperBound_7435_);
                    v___x_7474_ = v_reuseFailAlloc_7547_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_7475_ = (leanh::lean_unbox(v_a_7468_) as u8);
                if v___x_7475_ == 0 {
                    leanh::lean_dec(v_a_7468_);
                    leanh::lean_del_object(v___x_7461_);
                    leanh::lean_dec(v_fst_7459_);
                    leanh::lean_dec(v_val_7442_);
                    if v_isShared_7466_ == 0 {
                        leanh::lean_ctor_set(v___x_7465_, 1, v___x_7474_);
                        leanh::lean_ctor_set(v___x_7465_, 0, v___x_7436_);
                        v___x_7477_ = v___x_7465_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_7478_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7478_, 0, v___x_7436_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7478_, 1, v___x_7474_);
                        v___x_7477_ = v_reuseFailAlloc_7478_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_sz_7479_ = lean_array_size(v_fst_7459_);
                    v___x_7480_ = 0usize;
                    v___x_7481_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__1(v_sz_7479_, v___x_7480_, v_fst_7459_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_);
                    if leanh::lean_obj_tag(v___x_7481_) == 0 {
                        v_a_7482_ = leanh::lean_ctor_get(v___x_7481_, 0);
                        leanh::lean_inc(v_a_7482_);
                        leanh::lean_dec_ref_known(v___x_7481_, 1);
                        v___x_7487_ = leanh::lean_unsigned_to_nat(0);
                        v___x_7488_ = lean_nat_dec_eq(v___x_7407_, v___x_7487_);
                        v___x_7534_ = lean_array_get_size(v_a_7482_);
                        v___x_7535_ = lean_nat_dec_lt(v___x_7487_, v___x_7534_);
                        if v___x_7535_ == 0 {
                            leanh::lean_dec(v_a_7468_);
                            state = 14;
                            continue;
                        } else {
                            if v___x_7535_ == 0 {
                                leanh::lean_dec(v_a_7468_);
                                state = 14;
                                continue;
                            } else {
                                v___x_7536_ = lean_usize_of_nat(v___x_7534_);
                                v___x_7537_ = (leanh::lean_unbox(v_a_7468_) as u8);
                                leanh::lean_dec(v_a_7468_);
                                v___x_7538_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Elab_Structural_argsInGroup_spec__3(v___x_7537_, v___x_7407_, v_a_7482_, v___x_7480_, v___x_7536_);
                                if v___x_7538_ == 0 {
                                    state = 14;
                                    continue;
                                } else {
                                    if v___x_7488_ == 0 {
                                        leanh::lean_dec(v_a_7482_);
                                        leanh::lean_del_object(v___x_7461_);
                                        leanh::lean_dec(v_val_7442_);
                                        state = 12;
                                        continue;
                                    } else {
                                        state = 14;
                                        continue;
                                    }
                                }
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v___x_7474_);
                        leanh::lean_dec(v_a_7468_);
                        leanh::lean_del_object(v___x_7465_);
                        leanh::lean_del_object(v___x_7461_);
                        leanh::lean_dec(v_val_7442_);
                        leanh::lean_dec_ref(v_group_7413_);
                        leanh::lean_dec(v___x_7412_);
                        leanh::lean_dec_ref(v___x_7411_);
                        leanh::lean_dec_ref(v_recArgInfo_7410_);
                        leanh::lean_dec_ref(v___x_7406_);
                        v_a_7539_ = leanh::lean_ctor_get(v___x_7481_, 0);
                        v_isSharedCheck_7546_ =
                            (!leanh::lean_is_exclusive(v___x_7481_)) as u8;
                        if v_isSharedCheck_7546_ == 0 {
                            v___x_7541_ = v___x_7481_;
                            v_isShared_7542_ = v_isSharedCheck_7546_;
                            state = 24;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7539_);
                            leanh::lean_dec(v___x_7481_);
                            v___x_7541_ = leanh::lean_box(0);
                            v_isShared_7542_ = v_isSharedCheck_7546_;
                            state = 24;
                            continue;
                        }
                    }
                }
            }
            11 => {
                v_a_7424_ = v___x_7477_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_7466_ == 0 {
                    leanh::lean_ctor_set(v___x_7465_, 1, v___x_7474_);
                    leanh::lean_ctor_set(v___x_7465_, 0, v___x_7436_);
                    v___x_7485_ = v___x_7465_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7486_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7486_, 0, v___x_7436_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7486_, 1, v___x_7474_);
                    v___x_7485_ = v_reuseFailAlloc_7486_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v_a_7424_ = v___x_7485_;
                state = 1;
                continue;
            }
            14 => {
                if v___x_7488_ == 0 {
                    leanh::lean_del_object(v___x_7465_);
                    v___x_7490_ =
                        l_Array_allDiff___at___00Lean_Elab_Structural_getRecArgInfo_spec__2(
                            v_a_7482_,
                        );
                    if v___x_7490_ == 0 {
                        leanh::lean_dec(v_a_7482_);
                        leanh::lean_dec(v_val_7442_);
                        if v_isShared_7462_ == 0 {
                            leanh::lean_ctor_set(v___x_7461_, 1, v___x_7474_);
                            leanh::lean_ctor_set(v___x_7461_, 0, v___x_7436_);
                            v___x_7492_ = v___x_7461_;
                            state = 15;
                            continue;
                        } else {
                            v_reuseFailAlloc_7493_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7493_, 0, v___x_7436_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7493_, 1, v___x_7474_);
                            v___x_7492_ = v_reuseFailAlloc_7493_;
                            state = 15;
                            continue;
                        }
                    } else {
                        v___x_7494_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_hasBadIndexDep_x3f(v_ys_7409_, v_a_7482_, v___y_7418_, v___y_7419_, v___y_7420_, v___y_7421_);
                        if leanh::lean_obj_tag(v___x_7494_) == 0 {
                            v_a_7495_ = leanh::lean_ctor_get(v___x_7494_, 0);
                            v_isSharedCheck_7525_ =
                                (!leanh::lean_is_exclusive(v___x_7494_)) as u8;
                            if v_isSharedCheck_7525_ == 0 {
                                v___x_7497_ = v___x_7494_;
                                v_isShared_7498_ = v_isSharedCheck_7525_;
                                state = 16;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7495_);
                                leanh::lean_dec(v___x_7494_);
                                v___x_7497_ = leanh::lean_box(0);
                                v_isShared_7498_ = v_isSharedCheck_7525_;
                                state = 16;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_a_7482_);
                            leanh::lean_dec_ref(v___x_7474_);
                            leanh::lean_del_object(v___x_7461_);
                            leanh::lean_dec(v_val_7442_);
                            leanh::lean_dec_ref(v_group_7413_);
                            leanh::lean_dec(v___x_7412_);
                            leanh::lean_dec_ref(v___x_7411_);
                            leanh::lean_dec_ref(v_recArgInfo_7410_);
                            leanh::lean_dec_ref(v___x_7406_);
                            v_a_7526_ = leanh::lean_ctor_get(v___x_7494_, 0);
                            v_isSharedCheck_7533_ =
                                (!leanh::lean_is_exclusive(v___x_7494_)) as u8;
                            if v_isSharedCheck_7533_ == 0 {
                                v___x_7528_ = v___x_7494_;
                                v_isShared_7529_ = v_isSharedCheck_7533_;
                                state = 22;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7526_);
                                leanh::lean_dec(v___x_7494_);
                                v___x_7528_ = leanh::lean_box(0);
                                v_isShared_7529_ = v_isSharedCheck_7533_;
                                state = 22;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_7482_);
                    leanh::lean_del_object(v___x_7461_);
                    leanh::lean_dec(v_val_7442_);
                    state = 12;
                    continue;
                }
            }
            15 => {
                v_a_7424_ = v___x_7492_;
                state = 1;
                continue;
            }
            16 => {
                if leanh::lean_obj_tag(v_a_7495_) == 1 {
                    leanh::lean_dec_ref_known(v_a_7495_, 1);
                    leanh::lean_del_object(v___x_7497_);
                    leanh::lean_dec(v_a_7482_);
                    leanh::lean_dec(v_val_7442_);
                    if v_isShared_7462_ == 0 {
                        leanh::lean_ctor_set(v___x_7461_, 1, v___x_7474_);
                        leanh::lean_ctor_set(v___x_7461_, 0, v___x_7436_);
                        v___x_7500_ = v___x_7461_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_7501_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7501_, 0, v___x_7436_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7501_, 1, v___x_7474_);
                        v___x_7500_ = v_reuseFailAlloc_7501_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_a_7495_);
                    leanh::lean_dec_ref(v___x_7406_);
                    v_fnName_7502_ = leanh::lean_ctor_get(v_recArgInfo_7410_, 0);
                    v_isSharedCheck_7519_ =
                        (!leanh::lean_is_exclusive(v_recArgInfo_7410_)) as u8;
                    if v_isSharedCheck_7519_ == 0 {
                        v_unused_7520_ = leanh::lean_ctor_get(v_recArgInfo_7410_, 5);
                        leanh::lean_dec(v_unused_7520_);
                        v_unused_7521_ = leanh::lean_ctor_get(v_recArgInfo_7410_, 4);
                        leanh::lean_dec(v_unused_7521_);
                        v_unused_7522_ = leanh::lean_ctor_get(v_recArgInfo_7410_, 3);
                        leanh::lean_dec(v_unused_7522_);
                        v_unused_7523_ = leanh::lean_ctor_get(v_recArgInfo_7410_, 2);
                        leanh::lean_dec(v_unused_7523_);
                        v_unused_7524_ = leanh::lean_ctor_get(v_recArgInfo_7410_, 1);
                        leanh::lean_dec(v_unused_7524_);
                        v___x_7504_ = v_recArgInfo_7410_;
                        v_isShared_7505_ = v_isSharedCheck_7519_;
                        state = 18;
                        continue;
                    } else {
                        leanh::lean_inc(v_fnName_7502_);
                        leanh::lean_dec(v_recArgInfo_7410_);
                        v___x_7504_ = leanh::lean_box(0);
                        v_isShared_7505_ = v_isSharedCheck_7519_;
                        state = 18;
                        continue;
                    }
                }
            }
            17 => {
                v_a_7424_ = v___x_7500_;
                state = 1;
                continue;
            }
            18 => {
                v_sz_7506_ = lean_array_size(v_a_7482_);
                v___x_7507_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_argsInGroup_spec__2(v___x_7408_, v_sz_7506_, v___x_7480_, v_a_7482_);
                if v_isShared_7505_ == 0 {
                    leanh::lean_ctor_set(v___x_7504_, 5, v_val_7442_);
                    leanh::lean_ctor_set(v___x_7504_, 4, v_group_7413_);
                    leanh::lean_ctor_set(v___x_7504_, 3, v___x_7507_);
                    leanh::lean_ctor_set(v___x_7504_, 2, v___x_7412_);
                    leanh::lean_ctor_set(v___x_7504_, 1, v___x_7411_);
                    v___x_7509_ = v___x_7504_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_7518_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7518_, 0, v_fnName_7502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7518_, 1, v___x_7411_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7518_, 2, v___x_7412_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7518_, 3, v___x_7507_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7518_, 4, v_group_7413_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7518_, 5, v_val_7442_);
                    v___x_7509_ = v_reuseFailAlloc_7518_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_7510_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7510_, 0, v___x_7509_);
                v___x_7511_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7511_, 0, v___x_7510_);
                if v_isShared_7462_ == 0 {
                    leanh::lean_ctor_set(v___x_7461_, 1, v___x_7474_);
                    leanh::lean_ctor_set(v___x_7461_, 0, v___x_7511_);
                    v___x_7513_ = v___x_7461_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7517_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7517_, 0, v___x_7511_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7517_, 1, v___x_7474_);
                    v___x_7513_ = v_reuseFailAlloc_7517_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_7498_ == 0 {
                    leanh::lean_ctor_set(v___x_7497_, 0, v___x_7513_);
                    v___x_7515_ = v___x_7497_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_7516_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7516_, 0, v___x_7513_);
                    v___x_7515_ = v_reuseFailAlloc_7516_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_7515_;
            }
            22 => {
                if v_isShared_7529_ == 0 {
                    v___x_7531_ = v___x_7528_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_7532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7532_, 0, v_a_7526_);
                    v___x_7531_ = v_reuseFailAlloc_7532_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_7531_;
            }
            24 => {
                if v_isShared_7542_ == 0 {
                    v___x_7544_ = v___x_7541_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_7545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7545_, 0, v_a_7539_);
                    v___x_7544_ = v_reuseFailAlloc_7545_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                return v___x_7544_;
            }
            26 => {
                if v_isShared_7552_ == 0 {
                    v___x_7554_ = v___x_7551_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_7555_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7555_, 0, v_a_7549_);
                    v___x_7554_ = v_reuseFailAlloc_7555_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                return v___x_7554_;
            }
            28 => {
                if v_isShared_7563_ == 0 {
                    v___x_7565_ = v___x_7562_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_7566_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7566_, 0, v_a_7560_);
                    v___x_7565_ = v_reuseFailAlloc_7566_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_7565_;
            }
            30 => {
                if v_isShared_7571_ == 0 {
                    v___x_7573_ = v___x_7570_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_7574_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7574_, 0, v_a_7568_);
                    v___x_7573_ = v_reuseFailAlloc_7574_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_7573_;
            }
            32 => {
                if v_isShared_7579_ == 0 {
                    v___x_7581_ = v___x_7578_;
                    state = 33;
                    continue;
                } else {
                    v_reuseFailAlloc_7582_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7582_, 0, v_a_7576_);
                    v___x_7581_ = v_reuseFailAlloc_7582_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                return v___x_7581_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7590_: *mut leanh::LeanObject = *_args.add(0);
    let mut v___x_7591_: *mut leanh::LeanObject = *_args.add(1);
    let mut v___x_7592_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_ys_7593_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_recArgInfo_7594_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___x_7595_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___x_7596_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_group_7597_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_as_7598_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_sz_7599_: *mut leanh::LeanObject = *_args.add(9);
    let mut v_i_7600_: *mut leanh::LeanObject = *_args.add(10);
    let mut v_b_7601_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_7602_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7603_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7604_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7605_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7606_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_7607_: usize = 0;
    let mut v_i_boxed_7608_: usize = 0;
    let mut v_res_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7607_ = leanh::lean_unbox_usize(v_sz_7599_);
    leanh::lean_dec(v_sz_7599_);
    v_i_boxed_7608_ = leanh::lean_unbox_usize(v_i_7600_);
    leanh::lean_dec(v_i_7600_);
    v_res_7609_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_7590_, v___x_7591_, v___x_7592_, v_ys_7593_, v_recArgInfo_7594_, v___x_7595_, v___x_7596_, v_group_7597_, v_as_7598_, v_sz_boxed_7607_, v_i_boxed_7608_, v_b_7601_, v___y_7602_, v___y_7603_, v___y_7604_, v___y_7605_);
    leanh::lean_dec(v___y_7605_);
    leanh::lean_dec_ref(v___y_7604_);
    leanh::lean_dec(v___y_7603_);
    leanh::lean_dec_ref(v___y_7602_);
    leanh::lean_dec_ref(v_as_7598_);
    leanh::lean_dec_ref(v_ys_7593_);
    leanh::lean_dec_ref(v___x_7592_);
    leanh::lean_dec(v___x_7591_);
    return v_res_7609_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(
    mut v_group_7610_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_7611_: *mut leanh::LeanObject,
    mut v_xs_7612_: *mut leanh::LeanObject,
    mut v_recArgPos_7613_: *mut leanh::LeanObject,
    mut v_a_7614_: *mut leanh::LeanObject,
    mut v___x_7615_: *mut leanh::LeanObject,
    mut v___x_7616_: *mut leanh::LeanObject,
    mut v_ys_7617_: *mut leanh::LeanObject,
    mut v_x_7618_: *mut leanh::LeanObject,
    mut v___y_7619_: *mut leanh::LeanObject,
    mut v___y_7620_: *mut leanh::LeanObject,
    mut v___y_7621_: *mut leanh::LeanObject,
    mut v___y_7622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toIndGroupInfo_7624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_all_7625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7633_: u8 = 0;
    let mut v___x_7634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7639_: usize = 0;
    let mut v___x_7640_: usize = 0;
    let mut v___x_7641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7645_: u8 = 0;
    let mut v_fst_7646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7654_: u8 = 0;
    let mut v_a_7655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7658_: u8 = 0;
    let mut v___x_7660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7662_: u8 = 0;
    let mut v_reuseFailAlloc_7663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7664_: u8 = 0;
    let mut v_unused_7665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_7666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toIndGroupInfo_7624_ = leanh::lean_ctor_get(v_group_7610_, 0);
                leanh::lean_inc_ref(v_toIndGroupInfo_7624_);
                v_all_7625_ = leanh::lean_ctor_get(v_toIndGroupInfo_7624_, 0);
                leanh::lean_inc_ref(v_ys_7617_);
                leanh::lean_inc_ref(v_fixedParamPerm_7611_);
                v___x_7626_ = l_Lean_Elab_FixedParamPerm_buildArgs___redArg(
                    v_fixedParamPerm_7611_,
                    v_xs_7612_,
                    v_ys_7617_,
                );
                v___x_7627_ = l_Lean_instInhabitedExpr;
                v___x_7628_ = lean_array_get(v___x_7627_, v___x_7626_, v_recArgPos_7613_);
                v___x_7629_ = lean_array_get_size(v_all_7625_);
                v___x_7630_ =
                    l_Lean_Elab_Structural_IndGroupInfo_numMotives(v_toIndGroupInfo_7624_);
                v_isSharedCheck_7664_ =
                    (!leanh::lean_is_exclusive(v_toIndGroupInfo_7624_)) as u8;
                if v_isSharedCheck_7664_ == 0 {
                    v_unused_7665_ = leanh::lean_ctor_get(v_toIndGroupInfo_7624_, 1);
                    leanh::lean_dec(v_unused_7665_);
                    v_unused_7666_ = leanh::lean_ctor_get(v_toIndGroupInfo_7624_, 0);
                    leanh::lean_dec(v_unused_7666_);
                    v___x_7632_ = v_toIndGroupInfo_7624_;
                    v_isShared_7633_ = v_isSharedCheck_7664_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_dec(v_toIndGroupInfo_7624_);
                    v___x_7632_ = leanh::lean_box(0);
                    v_isShared_7633_ = v_isSharedCheck_7664_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7634_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7634_, 0, v___x_7629_);
                if v_isShared_7633_ == 0 {
                    leanh::lean_ctor_set(v___x_7632_, 1, v___x_7630_);
                    leanh::lean_ctor_set(v___x_7632_, 0, v___x_7634_);
                    v___x_7636_ = v___x_7632_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7663_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7663_, 0, v___x_7634_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7663_, 1, v___x_7630_);
                    v___x_7636_ = v_reuseFailAlloc_7663_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7637_ = leanh::lean_box(0);
                v___x_7638_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7638_, 0, v___x_7637_);
                leanh::lean_ctor_set(v___x_7638_, 1, v___x_7636_);
                v_sz_7639_ = lean_array_size(v_a_7614_);
                v___x_7640_ = 0usize;
                v___x_7641_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_argsInGroup_spec__4(v___x_7628_, v___x_7615_, v___x_7626_, v_ys_7617_, v___x_7616_, v_fixedParamPerm_7611_, v_recArgPos_7613_, v_group_7610_, v_a_7614_, v_sz_7639_, v___x_7640_, v___x_7638_, v___y_7619_, v___y_7620_, v___y_7621_, v___y_7622_);
                leanh::lean_dec_ref(v_ys_7617_);
                leanh::lean_dec_ref(v___x_7626_);
                if leanh::lean_obj_tag(v___x_7641_) == 0 {
                    v_a_7642_ = leanh::lean_ctor_get(v___x_7641_, 0);
                    v_isSharedCheck_7654_ = (!leanh::lean_is_exclusive(v___x_7641_)) as u8;
                    if v_isSharedCheck_7654_ == 0 {
                        v___x_7644_ = v___x_7641_;
                        v_isShared_7645_ = v_isSharedCheck_7654_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7642_);
                        leanh::lean_dec(v___x_7641_);
                        v___x_7644_ = leanh::lean_box(0);
                        v_isShared_7645_ = v_isSharedCheck_7654_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_7655_ = leanh::lean_ctor_get(v___x_7641_, 0);
                    v_isSharedCheck_7662_ = (!leanh::lean_is_exclusive(v___x_7641_)) as u8;
                    if v_isSharedCheck_7662_ == 0 {
                        v___x_7657_ = v___x_7641_;
                        v_isShared_7658_ = v_isSharedCheck_7662_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7655_);
                        leanh::lean_dec(v___x_7641_);
                        v___x_7657_ = leanh::lean_box(0);
                        v_isShared_7658_ = v_isSharedCheck_7662_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_7646_ = leanh::lean_ctor_get(v_a_7642_, 0);
                leanh::lean_inc(v_fst_7646_);
                leanh::lean_dec(v_a_7642_);
                if leanh::lean_obj_tag(v_fst_7646_) == 0 {
                    if v_isShared_7645_ == 0 {
                        leanh::lean_ctor_set(v___x_7644_, 0, v___x_7637_);
                        v___x_7648_ = v___x_7644_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_7649_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7649_, 0, v___x_7637_);
                        v___x_7648_ = v_reuseFailAlloc_7649_;
                        state = 4;
                        continue;
                    }
                } else {
                    v_val_7650_ = leanh::lean_ctor_get(v_fst_7646_, 0);
                    leanh::lean_inc(v_val_7650_);
                    leanh::lean_dec_ref_known(v_fst_7646_, 1);
                    if v_isShared_7645_ == 0 {
                        leanh::lean_ctor_set(v___x_7644_, 0, v_val_7650_);
                        v___x_7652_ = v___x_7644_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_7653_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7653_, 0, v_val_7650_);
                        v___x_7652_ = v_reuseFailAlloc_7653_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7648_;
            }
            5 => {
                return v___x_7652_;
            }
            6 => {
                if v_isShared_7658_ == 0 {
                    v___x_7660_ = v___x_7657_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7661_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7661_, 0, v_a_7655_);
                    v___x_7660_ = v_reuseFailAlloc_7661_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_7660_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed(
    mut v_group_7667_: *mut leanh::LeanObject,
    mut v_fixedParamPerm_7668_: *mut leanh::LeanObject,
    mut v_xs_7669_: *mut leanh::LeanObject,
    mut v_recArgPos_7670_: *mut leanh::LeanObject,
    mut v_a_7671_: *mut leanh::LeanObject,
    mut v___x_7672_: *mut leanh::LeanObject,
    mut v___x_7673_: *mut leanh::LeanObject,
    mut v_ys_7674_: *mut leanh::LeanObject,
    mut v_x_7675_: *mut leanh::LeanObject,
    mut v___y_7676_: *mut leanh::LeanObject,
    mut v___y_7677_: *mut leanh::LeanObject,
    mut v___y_7678_: *mut leanh::LeanObject,
    mut v___y_7679_: *mut leanh::LeanObject,
    mut v___y_7680_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7681_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7681_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0(v_group_7667_, v_fixedParamPerm_7668_, v_xs_7669_, v_recArgPos_7670_, v_a_7671_, v___x_7672_, v___x_7673_, v_ys_7674_, v_x_7675_, v___y_7676_, v___y_7677_, v___y_7678_, v___y_7679_);
    leanh::lean_dec(v___y_7679_);
    leanh::lean_dec_ref(v___y_7678_);
    leanh::lean_dec(v___y_7677_);
    leanh::lean_dec_ref(v___y_7676_);
    leanh::lean_dec_ref(v_x_7675_);
    leanh::lean_dec(v___x_7672_);
    leanh::lean_dec_ref(v_a_7671_);
    leanh::lean_dec_ref(v_xs_7669_);
    return v_res_7681_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(
    mut v_group_7682_: *mut leanh::LeanObject,
    mut v_a_7683_: *mut leanh::LeanObject,
    mut v_xs_7684_: *mut leanh::LeanObject,
    mut v_value_7685_: *mut leanh::LeanObject,
    mut v_as_7686_: *mut leanh::LeanObject,
    mut v_i_7687_: usize,
    mut v_stop_7688_: usize,
    mut v_b_7689_: *mut leanh::LeanObject,
    mut v___y_7690_: *mut leanh::LeanObject,
    mut v___y_7691_: *mut leanh::LeanObject,
    mut v___y_7692_: *mut leanh::LeanObject,
    mut v___y_7693_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7697_: usize = 0;
    let mut v___x_7698_: usize = 0;
    let mut v_val_7701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7703_: u8 = 0;
    let mut v___x_7704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fixedParamPerm_7705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgPos_7706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_indGroupInst_7707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7710_: u8 = 0;
    let mut v___x_7711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: u8 = 0;
    let mut v___f_7714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7721_: u8 = 0;
    let mut v___x_7723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7725_: u8 = 0;
    let mut v_a_7726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7729_: u8 = 0;
    let mut v___x_7731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7733_: u8 = 0;
    let mut v___x_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7703_ = lean_usize_dec_eq(v_i_7687_, v_stop_7688_);
                if v___x_7703_ == 0 {
                    v___x_7704_ = lean_array_uget_borrowed(v_as_7686_, v_i_7687_);
                    v_fixedParamPerm_7705_ = leanh::lean_ctor_get(v___x_7704_, 1);
                    v_recArgPos_7706_ = leanh::lean_ctor_get(v___x_7704_, 2);
                    v_indGroupInst_7707_ = leanh::lean_ctor_get(v___x_7704_, 4);
                    leanh::lean_inc_ref(v_indGroupInst_7707_);
                    leanh::lean_inc_ref(v_group_7682_);
                    v___x_7708_ = l_Lean_Elab_Structural_IndGroupInst_isDefEq(
                        v_group_7682_,
                        v_indGroupInst_7707_,
                        v___y_7690_,
                        v___y_7691_,
                        v___y_7692_,
                        v___y_7693_,
                    );
                    if leanh::lean_obj_tag(v___x_7708_) == 0 {
                        v_a_7709_ = leanh::lean_ctor_get(v___x_7708_, 0);
                        leanh::lean_inc(v_a_7709_);
                        leanh::lean_dec_ref_known(v___x_7708_, 1);
                        v___x_7710_ = (leanh::lean_unbox(v_a_7709_) as u8);
                        leanh::lean_dec(v_a_7709_);
                        if v___x_7710_ == 0 {
                            v___x_7711_ = lean_array_get_size(v_a_7683_);
                            v___x_7712_ = leanh::lean_unsigned_to_nat(0);
                            v___x_7713_ = lean_nat_dec_eq(v___x_7711_, v___x_7712_);
                            if v___x_7713_ == 0 {
                                leanh::lean_inc(v___x_7704_);
                                leanh::lean_inc_ref(v_a_7683_);
                                leanh::lean_inc(v_recArgPos_7706_);
                                leanh::lean_inc_ref(v_xs_7684_);
                                leanh::lean_inc_ref(v_fixedParamPerm_7705_);
                                leanh::lean_inc_ref(v_group_7682_);
                                v___f_7714_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___lam__0___boxed as *mut core::ffi::c_void, 14, 7);
                                leanh::lean_closure_set(v___f_7714_, 0, v_group_7682_);
                                leanh::lean_closure_set(
                                    v___f_7714_,
                                    1,
                                    v_fixedParamPerm_7705_,
                                );
                                leanh::lean_closure_set(v___f_7714_, 2, v_xs_7684_);
                                leanh::lean_closure_set(v___f_7714_, 3, v_recArgPos_7706_);
                                leanh::lean_closure_set(v___f_7714_, 4, v_a_7683_);
                                leanh::lean_closure_set(v___f_7714_, 5, v___x_7711_);
                                leanh::lean_closure_set(v___f_7714_, 6, v___x_7704_);
                                leanh::lean_inc_ref(v_value_7685_);
                                v___x_7715_ = l_Lean_Meta_lambdaTelescope___at___00Lean_Elab_Structural_prettyRecArg_spec__0___redArg(v_value_7685_, v___f_7714_, v___x_7713_, v___y_7690_, v___y_7691_, v___y_7692_, v___y_7693_);
                                if leanh::lean_obj_tag(v___x_7715_) == 0 {
                                    v_a_7716_ = leanh::lean_ctor_get(v___x_7715_, 0);
                                    leanh::lean_inc(v_a_7716_);
                                    leanh::lean_dec_ref_known(v___x_7715_, 1);
                                    if leanh::lean_obj_tag(v_a_7716_) == 0 {
                                        v_a_7696_ = v_b_7689_;
                                        state = 1;
                                        continue;
                                    } else {
                                        v_val_7717_ = leanh::lean_ctor_get(v_a_7716_, 0);
                                        leanh::lean_inc(v_val_7717_);
                                        leanh::lean_dec_ref_known(v_a_7716_, 1);
                                        v_val_7701_ = v_val_7717_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref(v_b_7689_);
                                    leanh::lean_dec_ref(v_value_7685_);
                                    leanh::lean_dec_ref(v_xs_7684_);
                                    leanh::lean_dec_ref(v_a_7683_);
                                    leanh::lean_dec_ref(v_group_7682_);
                                    v_a_7718_ = leanh::lean_ctor_get(v___x_7715_, 0);
                                    v_isSharedCheck_7725_ =
                                        (!leanh::lean_is_exclusive(v___x_7715_)) as u8;
                                    if v_isSharedCheck_7725_ == 0 {
                                        v___x_7720_ = v___x_7715_;
                                        v_isShared_7721_ = v_isSharedCheck_7725_;
                                        state = 3;
                                        continue;
                                    } else {
                                        leanh::lean_inc(v_a_7718_);
                                        leanh::lean_dec(v___x_7715_);
                                        v___x_7720_ = leanh::lean_box(0);
                                        v_isShared_7721_ = v_isSharedCheck_7725_;
                                        state = 3;
                                        continue;
                                    }
                                }
                            } else {
                                v_a_7696_ = v_b_7689_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_inc(v___x_7704_);
                            v_val_7701_ = v___x_7704_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_7689_);
                        leanh::lean_dec_ref(v_value_7685_);
                        leanh::lean_dec_ref(v_xs_7684_);
                        leanh::lean_dec_ref(v_a_7683_);
                        leanh::lean_dec_ref(v_group_7682_);
                        v_a_7726_ = leanh::lean_ctor_get(v___x_7708_, 0);
                        v_isSharedCheck_7733_ =
                            (!leanh::lean_is_exclusive(v___x_7708_)) as u8;
                        if v_isSharedCheck_7733_ == 0 {
                            v___x_7728_ = v___x_7708_;
                            v_isShared_7729_ = v_isSharedCheck_7733_;
                            state = 5;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7726_);
                            leanh::lean_dec(v___x_7708_);
                            v___x_7728_ = leanh::lean_box(0);
                            v_isShared_7729_ = v_isSharedCheck_7733_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_value_7685_);
                    leanh::lean_dec_ref(v_xs_7684_);
                    leanh::lean_dec_ref(v_a_7683_);
                    leanh::lean_dec_ref(v_group_7682_);
                    v___x_7734_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7734_, 0, v_b_7689_);
                    return v___x_7734_;
                }
            }
            1 => {
                v___x_7697_ = 1usize;
                v___x_7698_ = lean_usize_add(v_i_7687_, v___x_7697_);
                v_i_7687_ = v___x_7698_;
                v_b_7689_ = v_a_7696_;
                state = 0;
                continue;
            }
            2 => {
                v___x_7702_ = lean_array_push(v_b_7689_, v_val_7701_);
                v_a_7696_ = v___x_7702_;
                state = 1;
                continue;
            }
            3 => {
                if v_isShared_7721_ == 0 {
                    v___x_7723_ = v___x_7720_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7724_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7724_, 0, v_a_7718_);
                    v___x_7723_ = v_reuseFailAlloc_7724_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7723_;
            }
            5 => {
                if v_isShared_7729_ == 0 {
                    v___x_7731_ = v___x_7728_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7732_, 0, v_a_7726_);
                    v___x_7731_ = v_reuseFailAlloc_7732_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6___boxed(
    mut v_group_7735_: *mut leanh::LeanObject,
    mut v_a_7736_: *mut leanh::LeanObject,
    mut v_xs_7737_: *mut leanh::LeanObject,
    mut v_value_7738_: *mut leanh::LeanObject,
    mut v_as_7739_: *mut leanh::LeanObject,
    mut v_i_7740_: *mut leanh::LeanObject,
    mut v_stop_7741_: *mut leanh::LeanObject,
    mut v_b_7742_: *mut leanh::LeanObject,
    mut v___y_7743_: *mut leanh::LeanObject,
    mut v___y_7744_: *mut leanh::LeanObject,
    mut v___y_7745_: *mut leanh::LeanObject,
    mut v___y_7746_: *mut leanh::LeanObject,
    mut v___y_7747_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7748_: usize = 0;
    let mut v_stop_boxed_7749_: usize = 0;
    let mut v_res_7750_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7748_ = leanh::lean_unbox_usize(v_i_7740_);
    leanh::lean_dec(v_i_7740_);
    v_stop_boxed_7749_ = leanh::lean_unbox_usize(v_stop_7741_);
    leanh::lean_dec(v_stop_7741_);
    v_res_7750_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_7735_, v_a_7736_, v_xs_7737_, v_value_7738_, v_as_7739_, v_i_boxed_7748_, v_stop_boxed_7749_, v_b_7742_, v___y_7743_, v___y_7744_, v___y_7745_, v___y_7746_);
    leanh::lean_dec(v___y_7746_);
    leanh::lean_dec_ref(v___y_7745_);
    leanh::lean_dec(v___y_7744_);
    leanh::lean_dec_ref(v___y_7743_);
    leanh::lean_dec_ref(v_as_7739_);
    return v_res_7750_;
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(
    mut v_group_7751_: *mut leanh::LeanObject,
    mut v_a_7752_: *mut leanh::LeanObject,
    mut v_xs_7753_: *mut leanh::LeanObject,
    mut v_value_7754_: *mut leanh::LeanObject,
    mut v_as_7755_: *mut leanh::LeanObject,
    mut v_start_7756_: *mut leanh::LeanObject,
    mut v_stop_7757_: *mut leanh::LeanObject,
    mut v___y_7758_: *mut leanh::LeanObject,
    mut v___y_7759_: *mut leanh::LeanObject,
    mut v___y_7760_: *mut leanh::LeanObject,
    mut v___y_7761_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7764_: u8 = 0;
    v___x_7763_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__4;
    v___x_7764_ = lean_nat_dec_lt(v_start_7756_, v_stop_7757_);
    if v___x_7764_ == 0 {
        let mut v___x_7765_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_value_7754_);
        leanh::lean_dec_ref(v_xs_7753_);
        leanh::lean_dec_ref(v_a_7752_);
        leanh::lean_dec_ref(v_group_7751_);
        v___x_7765_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_7765_, 0, v___x_7763_);
        return v___x_7765_;
    } else {
        let mut v___x_7766_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7767_: u8 = 0;
        v___x_7766_ = lean_array_get_size(v_as_7755_);
        v___x_7767_ = lean_nat_dec_le(v_stop_7757_, v___x_7766_);
        if v___x_7767_ == 0 {
            let mut v___x_7768_: u8 = 0;
            v___x_7768_ = lean_nat_dec_lt(v_start_7756_, v___x_7766_);
            if v___x_7768_ == 0 {
                let mut v___x_7769_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref(v_value_7754_);
                leanh::lean_dec_ref(v_xs_7753_);
                leanh::lean_dec_ref(v_a_7752_);
                leanh::lean_dec_ref(v_group_7751_);
                v___x_7769_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7769_, 0, v___x_7763_);
                return v___x_7769_;
            } else {
                let mut v___x_7770_: usize = 0;
                let mut v___x_7771_: usize = 0;
                let mut v___x_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_7770_ = lean_usize_of_nat(v_start_7756_);
                v___x_7771_ = lean_usize_of_nat(v___x_7766_);
                v___x_7772_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_7751_, v_a_7752_, v_xs_7753_, v_value_7754_, v_as_7755_, v___x_7770_, v___x_7771_, v___x_7763_, v___y_7758_, v___y_7759_, v___y_7760_, v___y_7761_);
                return v___x_7772_;
            }
        } else {
            let mut v___x_7773_: usize = 0;
            let mut v___x_7774_: usize = 0;
            let mut v___x_7775_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_7773_ = lean_usize_of_nat(v_start_7756_);
            v___x_7774_ = lean_usize_of_nat(v_stop_7757_);
            v___x_7775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5_spec__6(v_group_7751_, v_a_7752_, v_xs_7753_, v_value_7754_, v_as_7755_, v___x_7773_, v___x_7774_, v___x_7763_, v___y_7758_, v___y_7759_, v___y_7760_, v___y_7761_);
            return v___x_7775_;
        }
    }
}
pub unsafe fn l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5___boxed(
    mut v_group_7776_: *mut leanh::LeanObject,
    mut v_a_7777_: *mut leanh::LeanObject,
    mut v_xs_7778_: *mut leanh::LeanObject,
    mut v_value_7779_: *mut leanh::LeanObject,
    mut v_as_7780_: *mut leanh::LeanObject,
    mut v_start_7781_: *mut leanh::LeanObject,
    mut v_stop_7782_: *mut leanh::LeanObject,
    mut v___y_7783_: *mut leanh::LeanObject,
    mut v___y_7784_: *mut leanh::LeanObject,
    mut v___y_7785_: *mut leanh::LeanObject,
    mut v___y_7786_: *mut leanh::LeanObject,
    mut v___y_7787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7788_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7788_ = l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(
        v_group_7776_,
        v_a_7777_,
        v_xs_7778_,
        v_value_7779_,
        v_as_7780_,
        v_start_7781_,
        v_stop_7782_,
        v___y_7783_,
        v___y_7784_,
        v___y_7785_,
        v___y_7786_,
    );
    leanh::lean_dec(v___y_7786_);
    leanh::lean_dec_ref(v___y_7785_);
    leanh::lean_dec(v___y_7784_);
    leanh::lean_dec_ref(v___y_7783_);
    leanh::lean_dec(v_stop_7782_);
    leanh::lean_dec(v_start_7781_);
    leanh::lean_dec_ref(v_as_7780_);
    return v_res_7788_;
}
pub unsafe fn l_Lean_Elab_Structural_argsInGroup(
    mut v_group_7789_: *mut leanh::LeanObject,
    mut v_xs_7790_: *mut leanh::LeanObject,
    mut v_value_7791_: *mut leanh::LeanObject,
    mut v_recArgInfos_7792_: *mut leanh::LeanObject,
    mut v_a_7793_: *mut leanh::LeanObject,
    mut v_a_7794_: *mut leanh::LeanObject,
    mut v_a_7795_: *mut leanh::LeanObject,
    mut v_a_7796_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7806_: u8 = 0;
    let mut v___x_7808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7810_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                leanh::lean_inc_ref(v_group_7789_);
                v___x_7798_ = l_Lean_Elab_Structural_IndGroupInst_nestedTypeFormers(
                    v_group_7789_,
                    v_a_7793_,
                    v_a_7794_,
                    v_a_7795_,
                    v_a_7796_,
                );
                if leanh::lean_obj_tag(v___x_7798_) == 0 {
                    v_a_7799_ = leanh::lean_ctor_get(v___x_7798_, 0);
                    leanh::lean_inc(v_a_7799_);
                    leanh::lean_dec_ref_known(v___x_7798_, 1);
                    v___x_7800_ = leanh::lean_unsigned_to_nat(0);
                    v___x_7801_ = lean_array_get_size(v_recArgInfos_7792_);
                    v___x_7802_ =
                        l_Array_filterMapM___at___00Lean_Elab_Structural_argsInGroup_spec__5(
                            v_group_7789_,
                            v_a_7799_,
                            v_xs_7790_,
                            v_value_7791_,
                            v_recArgInfos_7792_,
                            v___x_7800_,
                            v___x_7801_,
                            v_a_7793_,
                            v_a_7794_,
                            v_a_7795_,
                            v_a_7796_,
                        );
                    return v___x_7802_;
                } else {
                    leanh::lean_dec_ref(v_value_7791_);
                    leanh::lean_dec_ref(v_xs_7790_);
                    leanh::lean_dec_ref(v_group_7789_);
                    v_a_7803_ = leanh::lean_ctor_get(v___x_7798_, 0);
                    v_isSharedCheck_7810_ = (!leanh::lean_is_exclusive(v___x_7798_)) as u8;
                    if v_isSharedCheck_7810_ == 0 {
                        v___x_7805_ = v___x_7798_;
                        v_isShared_7806_ = v_isSharedCheck_7810_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7803_);
                        leanh::lean_dec(v___x_7798_);
                        v___x_7805_ = leanh::lean_box(0);
                        v_isShared_7806_ = v_isSharedCheck_7810_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7806_ == 0 {
                    v___x_7808_ = v___x_7805_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7809_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7809_, 0, v_a_7803_);
                    v___x_7808_ = v_reuseFailAlloc_7809_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7808_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_argsInGroup___boxed(
    mut v_group_7811_: *mut leanh::LeanObject,
    mut v_xs_7812_: *mut leanh::LeanObject,
    mut v_value_7813_: *mut leanh::LeanObject,
    mut v_recArgInfos_7814_: *mut leanh::LeanObject,
    mut v_a_7815_: *mut leanh::LeanObject,
    mut v_a_7816_: *mut leanh::LeanObject,
    mut v_a_7817_: *mut leanh::LeanObject,
    mut v_a_7818_: *mut leanh::LeanObject,
    mut v_a_7819_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7820_ = l_Lean_Elab_Structural_argsInGroup(
        v_group_7811_,
        v_xs_7812_,
        v_value_7813_,
        v_recArgInfos_7814_,
        v_a_7815_,
        v_a_7816_,
        v_a_7817_,
        v_a_7818_,
    );
    leanh::lean_dec(v_a_7818_);
    leanh::lean_dec_ref(v_a_7817_);
    leanh::lean_dec(v_a_7816_);
    leanh::lean_dec_ref(v_a_7815_);
    leanh::lean_dec_ref(v_recArgInfos_7814_);
    return v_res_7820_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_maxCombinationSize() -> *mut leanh::LeanObject {
    let mut v___x_7821_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7821_ = leanh::lean_unsigned_to_nat(10);
    return v___x_7821_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(
    mut v_xss_7824_: *mut leanh::LeanObject,
    mut v_i_7825_: *mut leanh::LeanObject,
    mut v_acc_7826_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7828_: u8 = 0;
    v___x_7827_ = lean_array_get_size(v_xss_7824_);
    v___x_7828_ = lean_nat_dec_lt(v_i_7825_, v___x_7827_);
    if v___x_7828_ == 0 {
        let mut v___x_7829_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7830_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7831_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7829_ = leanh::lean_unsigned_to_nat(1);
        v___x_7830_ = lean_mk_empty_array_with_capacity(v___x_7829_);
        v___x_7831_ = lean_array_push(v___x_7830_, v_acc_7826_);
        return v___x_7831_;
    } else {
        let mut v___x_7832_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7833_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7834_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7835_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_7836_: u8 = 0;
        v___x_7832_ = lean_array_fget_borrowed(v_xss_7824_, v_i_7825_);
        v___x_7833_ = leanh::lean_unsigned_to_nat(0);
        v___x_7834_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___closed__0;
        v___x_7835_ = lean_array_get_size(v___x_7832_);
        v___x_7836_ = lean_nat_dec_lt(v___x_7833_, v___x_7835_);
        if v___x_7836_ == 0 {
            leanh::lean_dec_ref(v_acc_7826_);
            return v___x_7834_;
        } else {
            let mut v___x_7837_: u8 = 0;
            v___x_7837_ = lean_nat_dec_le(v___x_7835_, v___x_7835_);
            if v___x_7837_ == 0 {
                if v___x_7836_ == 0 {
                    leanh::lean_dec_ref(v_acc_7826_);
                    return v___x_7834_;
                } else {
                    let mut v___x_7838_: usize = 0;
                    let mut v___x_7839_: usize = 0;
                    let mut v___x_7840_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_7838_ = 0usize;
                    v___x_7839_ = lean_usize_of_nat(v___x_7835_);
                    v___x_7840_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_7825_, v_acc_7826_, v_xss_7824_, v___x_7832_, v___x_7838_, v___x_7839_, v___x_7834_);
                    return v___x_7840_;
                }
            } else {
                let mut v___x_7841_: usize = 0;
                let mut v___x_7842_: usize = 0;
                let mut v___x_7843_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_7841_ = 0usize;
                v___x_7842_ = lean_usize_of_nat(v___x_7835_);
                v___x_7843_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_7825_, v_acc_7826_, v_xss_7824_, v___x_7832_, v___x_7841_, v___x_7842_, v___x_7834_);
                return v___x_7843_;
            }
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(
    mut v_i_7844_: *mut leanh::LeanObject,
    mut v_acc_7845_: *mut leanh::LeanObject,
    mut v_xss_7846_: *mut leanh::LeanObject,
    mut v_as_7847_: *mut leanh::LeanObject,
    mut v_i_7848_: usize,
    mut v_stop_7849_: usize,
    mut v_b_7850_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7851_: u8 = 0;
    let mut v___x_7852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7858_: usize = 0;
    let mut v___x_7859_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7851_ = lean_usize_dec_eq(v_i_7848_, v_stop_7849_);
                if v___x_7851_ == 0 {
                    v___x_7852_ = lean_array_uget_borrowed(v_as_7847_, v_i_7848_);
                    v___x_7853_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7854_ = lean_nat_add(v_i_7844_, v___x_7853_);
                    leanh::lean_inc(v___x_7852_);
                    leanh::lean_inc_ref(v_acc_7845_);
                    v___x_7855_ = lean_array_push(v_acc_7845_, v___x_7852_);
                    v___x_7856_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_7846_, v___x_7854_, v___x_7855_);
                    leanh::lean_dec(v___x_7854_);
                    v___x_7857_ = l_Array_append___redArg(v_b_7850_, v___x_7856_);
                    leanh::lean_dec_ref(v___x_7856_);
                    v___x_7858_ = 1usize;
                    v___x_7859_ = lean_usize_add(v_i_7848_, v___x_7858_);
                    v_i_7848_ = v___x_7859_;
                    v_b_7850_ = v___x_7857_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec_ref(v_acc_7845_);
                    return v_b_7850_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg___boxed(
    mut v_i_7861_: *mut leanh::LeanObject,
    mut v_acc_7862_: *mut leanh::LeanObject,
    mut v_xss_7863_: *mut leanh::LeanObject,
    mut v_as_7864_: *mut leanh::LeanObject,
    mut v_i_7865_: *mut leanh::LeanObject,
    mut v_stop_7866_: *mut leanh::LeanObject,
    mut v_b_7867_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7868_: usize = 0;
    let mut v_stop_boxed_7869_: usize = 0;
    let mut v_res_7870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7868_ = leanh::lean_unbox_usize(v_i_7865_);
    leanh::lean_dec(v_i_7865_);
    v_stop_boxed_7869_ = leanh::lean_unbox_usize(v_stop_7866_);
    leanh::lean_dec(v_stop_7866_);
    v_res_7870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_7861_, v_acc_7862_, v_xss_7863_, v_as_7864_, v_i_boxed_7868_, v_stop_boxed_7869_, v_b_7867_);
    leanh::lean_dec_ref(v_as_7864_);
    leanh::lean_dec_ref(v_xss_7863_);
    leanh::lean_dec(v_i_7861_);
    return v_res_7870_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg___boxed(
    mut v_xss_7871_: *mut leanh::LeanObject,
    mut v_i_7872_: *mut leanh::LeanObject,
    mut v_acc_7873_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7874_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7874_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_7871_, v_i_7872_, v_acc_7873_);
    leanh::lean_dec(v_i_7872_);
    leanh::lean_dec_ref(v_xss_7871_);
    return v_res_7874_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(
    mut v_00_u03b1_7875_: *mut leanh::LeanObject,
    mut v_xss_7876_: *mut leanh::LeanObject,
    mut v_i_7877_: *mut leanh::LeanObject,
    mut v_acc_7878_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7879_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_7876_, v_i_7877_, v_acc_7878_);
    return v___x_7879_;
}
pub unsafe fn l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___boxed(
    mut v_00_u03b1_7880_: *mut leanh::LeanObject,
    mut v_xss_7881_: *mut leanh::LeanObject,
    mut v_i_7882_: *mut leanh::LeanObject,
    mut v_acc_7883_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7884_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7884_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go(v_00_u03b1_7880_, v_xss_7881_, v_i_7882_, v_acc_7883_);
    leanh::lean_dec(v_i_7882_);
    leanh::lean_dec_ref(v_xss_7881_);
    return v_res_7884_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(
    mut v_00_u03b1_7885_: *mut leanh::LeanObject,
    mut v_i_7886_: *mut leanh::LeanObject,
    mut v_acc_7887_: *mut leanh::LeanObject,
    mut v_xss_7888_: *mut leanh::LeanObject,
    mut v_as_7889_: *mut leanh::LeanObject,
    mut v_i_7890_: usize,
    mut v_stop_7891_: usize,
    mut v_b_7892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7893_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7893_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___redArg(v_i_7886_, v_acc_7887_, v_xss_7888_, v_as_7889_, v_i_7890_, v_stop_7891_, v_b_7892_);
    return v___x_7893_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0___boxed(
    mut v_00_u03b1_7894_: *mut leanh::LeanObject,
    mut v_i_7895_: *mut leanh::LeanObject,
    mut v_acc_7896_: *mut leanh::LeanObject,
    mut v_xss_7897_: *mut leanh::LeanObject,
    mut v_as_7898_: *mut leanh::LeanObject,
    mut v_i_7899_: *mut leanh::LeanObject,
    mut v_stop_7900_: *mut leanh::LeanObject,
    mut v_b_7901_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7902_: usize = 0;
    let mut v_stop_boxed_7903_: usize = 0;
    let mut v_res_7904_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7902_ = leanh::lean_unbox_usize(v_i_7899_);
    leanh::lean_dec(v_i_7899_);
    v_stop_boxed_7903_ = leanh::lean_unbox_usize(v_stop_7900_);
    leanh::lean_dec(v_stop_7900_);
    v_res_7904_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go_spec__0(v_00_u03b1_7894_, v_i_7895_, v_acc_7896_, v_xss_7897_, v_as_7898_, v_i_boxed_7902_, v_stop_boxed_7903_, v_b_7901_);
    leanh::lean_dec_ref(v_as_7898_);
    leanh::lean_dec_ref(v_xss_7897_);
    leanh::lean_dec(v_i_7895_);
    return v_res_7904_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(
    mut v_as_7905_: *mut leanh::LeanObject,
    mut v_i_7906_: usize,
    mut v_stop_7907_: usize,
    mut v_b_7908_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7909_: u8 = 0;
    let mut v___x_7910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: usize = 0;
    let mut v___x_7914_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7909_ = lean_usize_dec_eq(v_i_7906_, v_stop_7907_);
                if v___x_7909_ == 0 {
                    v___x_7910_ = lean_array_uget_borrowed(v_as_7905_, v_i_7906_);
                    v___x_7911_ = lean_array_get_size(v___x_7910_);
                    v___x_7912_ = lean_nat_mul(v_b_7908_, v___x_7911_);
                    leanh::lean_dec(v_b_7908_);
                    v___x_7913_ = 1usize;
                    v___x_7914_ = lean_usize_add(v_i_7906_, v___x_7913_);
                    v_i_7906_ = v___x_7914_;
                    v_b_7908_ = v___x_7912_;
                    state = 0;
                    continue;
                } else {
                    return v_b_7908_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg___boxed(
    mut v_as_7916_: *mut leanh::LeanObject,
    mut v_i_7917_: *mut leanh::LeanObject,
    mut v_stop_7918_: *mut leanh::LeanObject,
    mut v_b_7919_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7920_: usize = 0;
    let mut v_stop_boxed_7921_: usize = 0;
    let mut v_res_7922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7920_ = leanh::lean_unbox_usize(v_i_7917_);
    leanh::lean_dec(v_i_7917_);
    v_stop_boxed_7921_ = leanh::lean_unbox_usize(v_stop_7918_);
    leanh::lean_dec(v_stop_7918_);
    v_res_7922_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_7916_, v_i_boxed_7920_, v_stop_boxed_7921_, v_b_7919_);
    leanh::lean_dec_ref(v_as_7916_);
    return v_res_7922_;
}
pub unsafe fn l_Lean_Elab_Structural_allCombinations___redArg(
    mut v_xss_7923_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7929_: u8 = 0;
    let mut v___x_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7935_: u8 = 0;
    let mut v___x_7936_: u8 = 0;
    let mut v___x_7937_: usize = 0;
    let mut v___x_7938_: usize = 0;
    let mut v___x_7939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7940_: usize = 0;
    let mut v___x_7941_: usize = 0;
    let mut v___x_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7924_ = leanh::lean_unsigned_to_nat(10);
                v___x_7925_ = leanh::lean_unsigned_to_nat(1);
                v___x_7926_ = leanh::lean_unsigned_to_nat(0);
                v___x_7934_ = lean_array_get_size(v_xss_7923_);
                v___x_7935_ = lean_nat_dec_lt(v___x_7926_, v___x_7934_);
                if v___x_7935_ == 0 {
                    v___y_7928_ = v___x_7925_;
                    state = 1;
                    continue;
                } else {
                    v___x_7936_ = lean_nat_dec_le(v___x_7934_, v___x_7934_);
                    if v___x_7936_ == 0 {
                        if v___x_7935_ == 0 {
                            v___y_7928_ = v___x_7925_;
                            state = 1;
                            continue;
                        } else {
                            v___x_7937_ = 0usize;
                            v___x_7938_ = lean_usize_of_nat(v___x_7934_);
                            v___x_7939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_7923_, v___x_7937_, v___x_7938_, v___x_7925_);
                            v___y_7928_ = v___x_7939_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v___x_7940_ = 0usize;
                        v___x_7941_ = lean_usize_of_nat(v___x_7934_);
                        v___x_7942_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_xss_7923_, v___x_7940_, v___x_7941_, v___x_7925_);
                        v___y_7928_ = v___x_7942_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7929_ = lean_nat_dec_lt(v___x_7924_, v___y_7928_);
                leanh::lean_dec(v___y_7928_);
                if v___x_7929_ == 0 {
                    v___x_7930_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_dedup___redArg___closed__0;
                    v___x_7931_ = l___private_Lean_Elab_PreDefinition_Structural_FindRecArg_0__Lean_Elab_Structural_allCombinations_go___redArg(v_xss_7923_, v___x_7926_, v___x_7930_);
                    v___x_7932_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7932_, 0, v___x_7931_);
                    return v___x_7932_;
                } else {
                    v___x_7933_ = leanh::lean_box(0);
                    return v___x_7933_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_allCombinations___redArg___boxed(
    mut v_xss_7943_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7944_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_7943_);
    leanh::lean_dec_ref(v_xss_7943_);
    return v_res_7944_;
}
pub unsafe fn l_Lean_Elab_Structural_allCombinations(
    mut v_00_u03b1_7945_: *mut leanh::LeanObject,
    mut v_xss_7946_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7947_ = l_Lean_Elab_Structural_allCombinations___redArg(v_xss_7946_);
    return v___x_7947_;
}
pub unsafe fn l_Lean_Elab_Structural_allCombinations___boxed(
    mut v_00_u03b1_7948_: *mut leanh::LeanObject,
    mut v_xss_7949_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7950_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7950_ = l_Lean_Elab_Structural_allCombinations(v_00_u03b1_7948_, v_xss_7949_);
    leanh::lean_dec_ref(v_xss_7949_);
    return v_res_7950_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(
    mut v_00_u03b1_7951_: *mut leanh::LeanObject,
    mut v_as_7952_: *mut leanh::LeanObject,
    mut v_i_7953_: usize,
    mut v_stop_7954_: usize,
    mut v_b_7955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7956_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7956_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___redArg(v_as_7952_, v_i_7953_, v_stop_7954_, v_b_7955_);
    return v___x_7956_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0___boxed(
    mut v_00_u03b1_7957_: *mut leanh::LeanObject,
    mut v_as_7958_: *mut leanh::LeanObject,
    mut v_i_7959_: *mut leanh::LeanObject,
    mut v_stop_7960_: *mut leanh::LeanObject,
    mut v_b_7961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7962_: usize = 0;
    let mut v_stop_boxed_7963_: usize = 0;
    let mut v_res_7964_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7962_ = leanh::lean_unbox_usize(v_i_7959_);
    leanh::lean_dec(v_i_7959_);
    v_stop_boxed_7963_ = leanh::lean_unbox_usize(v_stop_7960_);
    leanh::lean_dec(v_stop_7960_);
    v_res_7964_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_allCombinations_spec__0(v_00_u03b1_7957_, v_as_7958_, v_i_boxed_7962_, v_stop_boxed_7963_, v_b_7961_);
    leanh::lean_dec_ref(v_as_7958_);
    return v_res_7964_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(
    mut v_as_7965_: *mut leanh::LeanObject,
    mut v_i_7966_: usize,
    mut v_stop_7967_: usize,
    mut v_b_7968_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7969_: u8 = 0;
    let mut v___x_7970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7972_: usize = 0;
    let mut v___x_7973_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7969_ = lean_usize_dec_eq(v_i_7966_, v_stop_7967_);
                if v___x_7969_ == 0 {
                    v___x_7970_ = lean_array_uget_borrowed(v_as_7965_, v_i_7966_);
                    v___x_7971_ = l_Array_append___redArg(v_b_7968_, v___x_7970_);
                    v___x_7972_ = 1usize;
                    v___x_7973_ = lean_usize_add(v_i_7966_, v___x_7972_);
                    v_i_7966_ = v___x_7973_;
                    v_b_7968_ = v___x_7971_;
                    state = 0;
                    continue;
                } else {
                    return v_b_7968_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7___boxed(
    mut v_as_7975_: *mut leanh::LeanObject,
    mut v_i_7976_: *mut leanh::LeanObject,
    mut v_stop_7977_: *mut leanh::LeanObject,
    mut v_b_7978_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_7979_: usize = 0;
    let mut v_stop_boxed_7980_: usize = 0;
    let mut v_res_7981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7979_ = leanh::lean_unbox_usize(v_i_7976_);
    leanh::lean_dec(v_i_7976_);
    v_stop_boxed_7980_ = leanh::lean_unbox_usize(v_stop_7977_);
    leanh::lean_dec(v_stop_7977_);
    v_res_7981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v_as_7975_, v_i_boxed_7979_, v_stop_boxed_7980_, v_b_7978_);
    leanh::lean_dec_ref(v_as_7975_);
    return v_res_7981_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(
    mut v_a_7982_: *mut leanh::LeanObject,
    mut v_a_7983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_7985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_7986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7989_: u8 = 0;
    let mut v___x_7990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7996_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_7982_) == 0 {
                    v___x_7984_ = l_List_reverse___redArg(v_a_7983_);
                    return v___x_7984_;
                } else {
                    v_head_7985_ = leanh::lean_ctor_get(v_a_7982_, 0);
                    v_tail_7986_ = leanh::lean_ctor_get(v_a_7982_, 1);
                    v_isSharedCheck_7996_ = (!leanh::lean_is_exclusive(v_a_7982_)) as u8;
                    if v_isSharedCheck_7996_ == 0 {
                        v___x_7988_ = v_a_7982_;
                        v_isShared_7989_ = v_isSharedCheck_7996_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_7986_);
                        leanh::lean_inc(v_head_7985_);
                        leanh::lean_dec(v_a_7982_);
                        v___x_7988_ = leanh::lean_box(0);
                        v_isShared_7989_ = v_isSharedCheck_7996_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7990_ = l_Lean_Elab_Structural_instReprRecArgInfo_repr___redArg(v_head_7985_);
                v___x_7991_ = l_Lean_MessageData_ofFormat(v___x_7990_);
                if v_isShared_7989_ == 0 {
                    leanh::lean_ctor_set(v___x_7988_, 1, v_a_7983_);
                    leanh::lean_ctor_set(v___x_7988_, 0, v___x_7991_);
                    v___x_7993_ = v___x_7988_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7995_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7995_, 0, v___x_7991_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7995_, 1, v_a_7983_);
                    v___x_7993_ = v_reuseFailAlloc_7995_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_7982_ = v_tail_7986_;
                v_a_7983_ = v___x_7993_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(
    mut v_sz_7997_: usize,
    mut v_i_7998_: usize,
    mut v_bs_7999_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8000_: u8 = 0;
    let mut v_v_8001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_8003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8005_: usize = 0;
    let mut v___x_8006_: usize = 0;
    let mut v___x_8007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8000_ = lean_usize_dec_lt(v_i_7998_, v_sz_7997_);
                if v___x_8000_ == 0 {
                    return v_bs_7999_;
                } else {
                    v_v_8001_ = lean_array_uget(v_bs_7999_, v_i_7998_);
                    v___x_8002_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_8003_ = lean_array_uset(v_bs_7999_, v_i_7998_, v___x_8002_);
                    v___x_8004_ = l_Lean_Elab_Structural_nonIndicesFirst(v_v_8001_);
                    leanh::lean_dec(v_v_8001_);
                    v___x_8005_ = 1usize;
                    v___x_8006_ = lean_usize_add(v_i_7998_, v___x_8005_);
                    v___x_8007_ = lean_array_uset(v_bs_x27_8003_, v_i_7998_, v___x_8004_);
                    v_i_7998_ = v___x_8006_;
                    v_bs_7999_ = v___x_8007_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1___boxed(
    mut v_sz_8009_: *mut leanh::LeanObject,
    mut v_i_8010_: *mut leanh::LeanObject,
    mut v_bs_8011_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8012_: usize = 0;
    let mut v_i_boxed_8013_: usize = 0;
    let mut v_res_8014_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8012_ = leanh::lean_unbox_usize(v_sz_8009_);
    leanh::lean_dec(v_sz_8009_);
    v_i_boxed_8013_ = leanh::lean_unbox_usize(v_i_8010_);
    leanh::lean_dec(v_i_8010_);
    v_res_8014_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_boxed_8012_, v_i_boxed_8013_, v_bs_8011_);
    return v_res_8014_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(
    mut v_xs_8015_: *mut leanh::LeanObject,
    mut v_as_8016_: *mut leanh::LeanObject,
    mut v_sz_8017_: usize,
    mut v_i_8018_: usize,
    mut v_b_8019_: *mut leanh::LeanObject,
    mut v___y_8020_: *mut leanh::LeanObject,
    mut v___y_8021_: *mut leanh::LeanObject,
    mut v___y_8022_: *mut leanh::LeanObject,
    mut v___y_8023_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8025_: u8 = 0;
    let mut v___x_8026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8034_: u8 = 0;
    let mut v_fst_8035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8038_: u8 = 0;
    let mut v_fst_8039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8042_: u8 = 0;
    let mut v_fst_8043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8046_: u8 = 0;
    let mut v_array_8047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_8048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_8049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8050_: u8 = 0;
    let mut v___x_8052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8063_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8066_: u8 = 0;
    let mut v_array_8067_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_8068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_8069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8071_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8075_: u8 = 0;
    let mut v___x_8077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8091_: u8 = 0;
    let mut v_array_8092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_8093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_8094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8099_: u8 = 0;
    let mut v___x_8101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8115_: u8 = 0;
    let mut v_a_8116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8124_: u8 = 0;
    let mut v___x_8125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8133_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8138_: usize = 0;
    let mut v___x_8139_: usize = 0;
    let mut v_reuseFailAlloc_8141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8146_: u8 = 0;
    let mut v_a_8147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8150_: u8 = 0;
    let mut v___x_8152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8153_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8154_: u8 = 0;
    let mut v_isSharedCheck_8155_: u8 = 0;
    let mut v_unused_8156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8160_: u8 = 0;
    let mut v_unused_8161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8165_: u8 = 0;
    let mut v_unused_8166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8169_: u8 = 0;
    let mut v_unused_8170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8171_: u8 = 0;
    let mut v_unused_8172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8173_: u8 = 0;
    let mut v_unused_8174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8175_: u8 = 0;
    let mut v_unused_8176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8025_ = lean_usize_dec_lt(v_i_8018_, v_sz_8017_);
                if v___x_8025_ == 0 {
                    leanh::lean_dec_ref(v_xs_8015_);
                    v___x_8026_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8026_, 0, v_b_8019_);
                    return v___x_8026_;
                } else {
                    v_snd_8027_ = leanh::lean_ctor_get(v_b_8019_, 1);
                    leanh::lean_inc(v_snd_8027_);
                    v_snd_8028_ = leanh::lean_ctor_get(v_snd_8027_, 1);
                    leanh::lean_inc(v_snd_8028_);
                    v_snd_8029_ = leanh::lean_ctor_get(v_snd_8028_, 1);
                    leanh::lean_inc(v_snd_8029_);
                    v_snd_8030_ = leanh::lean_ctor_get(v_snd_8029_, 1);
                    leanh::lean_inc(v_snd_8030_);
                    v_fst_8031_ = leanh::lean_ctor_get(v_b_8019_, 0);
                    v_isSharedCheck_8175_ = (!leanh::lean_is_exclusive(v_b_8019_)) as u8;
                    if v_isSharedCheck_8175_ == 0 {
                        v_unused_8176_ = leanh::lean_ctor_get(v_b_8019_, 1);
                        leanh::lean_dec(v_unused_8176_);
                        v___x_8033_ = v_b_8019_;
                        v_isShared_8034_ = v_isSharedCheck_8175_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_8031_);
                        leanh::lean_dec(v_b_8019_);
                        v___x_8033_ = leanh::lean_box(0);
                        v_isShared_8034_ = v_isSharedCheck_8175_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_8035_ = leanh::lean_ctor_get(v_snd_8027_, 0);
                v_isSharedCheck_8173_ = (!leanh::lean_is_exclusive(v_snd_8027_)) as u8;
                if v_isSharedCheck_8173_ == 0 {
                    v_unused_8174_ = leanh::lean_ctor_get(v_snd_8027_, 1);
                    leanh::lean_dec(v_unused_8174_);
                    v___x_8037_ = v_snd_8027_;
                    v_isShared_8038_ = v_isSharedCheck_8173_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_8035_);
                    leanh::lean_dec(v_snd_8027_);
                    v___x_8037_ = leanh::lean_box(0);
                    v_isShared_8038_ = v_isSharedCheck_8173_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_fst_8039_ = leanh::lean_ctor_get(v_snd_8028_, 0);
                v_isSharedCheck_8171_ = (!leanh::lean_is_exclusive(v_snd_8028_)) as u8;
                if v_isSharedCheck_8171_ == 0 {
                    v_unused_8172_ = leanh::lean_ctor_get(v_snd_8028_, 1);
                    leanh::lean_dec(v_unused_8172_);
                    v___x_8041_ = v_snd_8028_;
                    v_isShared_8042_ = v_isSharedCheck_8171_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_8039_);
                    leanh::lean_dec(v_snd_8028_);
                    v___x_8041_ = leanh::lean_box(0);
                    v_isShared_8042_ = v_isSharedCheck_8171_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_fst_8043_ = leanh::lean_ctor_get(v_snd_8029_, 0);
                v_isSharedCheck_8169_ = (!leanh::lean_is_exclusive(v_snd_8029_)) as u8;
                if v_isSharedCheck_8169_ == 0 {
                    v_unused_8170_ = leanh::lean_ctor_get(v_snd_8029_, 1);
                    leanh::lean_dec(v_unused_8170_);
                    v___x_8045_ = v_snd_8029_;
                    v_isShared_8046_ = v_isSharedCheck_8169_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_8043_);
                    leanh::lean_dec(v_snd_8029_);
                    v___x_8045_ = leanh::lean_box(0);
                    v_isShared_8046_ = v_isSharedCheck_8169_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_array_8047_ = leanh::lean_ctor_get(v_snd_8030_, 0);
                v_start_8048_ = leanh::lean_ctor_get(v_snd_8030_, 1);
                v_stop_8049_ = leanh::lean_ctor_get(v_snd_8030_, 2);
                v___x_8050_ = lean_nat_dec_lt(v_start_8048_, v_stop_8049_);
                if v___x_8050_ == 0 {
                    leanh::lean_dec_ref(v_xs_8015_);
                    if v_isShared_8046_ == 0 {
                        v___x_8052_ = v___x_8045_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_8063_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8063_, 0, v_fst_8043_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8063_, 1, v_snd_8030_);
                        v___x_8052_ = v_reuseFailAlloc_8063_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_8049_);
                    leanh::lean_inc(v_start_8048_);
                    leanh::lean_inc_ref(v_array_8047_);
                    v_isSharedCheck_8165_ = (!leanh::lean_is_exclusive(v_snd_8030_)) as u8;
                    if v_isSharedCheck_8165_ == 0 {
                        v_unused_8166_ = leanh::lean_ctor_get(v_snd_8030_, 2);
                        leanh::lean_dec(v_unused_8166_);
                        v_unused_8167_ = leanh::lean_ctor_get(v_snd_8030_, 1);
                        leanh::lean_dec(v_unused_8167_);
                        v_unused_8168_ = leanh::lean_ctor_get(v_snd_8030_, 0);
                        leanh::lean_dec(v_unused_8168_);
                        v___x_8065_ = v_snd_8030_;
                        v_isShared_8066_ = v_isSharedCheck_8165_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_8030_);
                        v___x_8065_ = leanh::lean_box(0);
                        v_isShared_8066_ = v_isSharedCheck_8165_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_8042_ == 0 {
                    leanh::lean_ctor_set(v___x_8041_, 1, v___x_8052_);
                    v___x_8054_ = v___x_8041_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_8062_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8062_, 0, v_fst_8039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8062_, 1, v___x_8052_);
                    v___x_8054_ = v_reuseFailAlloc_8062_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_8038_ == 0 {
                    leanh::lean_ctor_set(v___x_8037_, 1, v___x_8054_);
                    v___x_8056_ = v___x_8037_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8061_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8061_, 0, v_fst_8035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8061_, 1, v___x_8054_);
                    v___x_8056_ = v_reuseFailAlloc_8061_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_8034_ == 0 {
                    leanh::lean_ctor_set(v___x_8033_, 1, v___x_8056_);
                    v___x_8058_ = v___x_8033_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8060_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8060_, 0, v_fst_8031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8060_, 1, v___x_8056_);
                    v___x_8058_ = v_reuseFailAlloc_8060_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_8059_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8059_, 0, v___x_8058_);
                return v___x_8059_;
            }
            9 => {
                v_array_8067_ = leanh::lean_ctor_get(v_fst_8043_, 0);
                v_start_8068_ = leanh::lean_ctor_get(v_fst_8043_, 1);
                v_stop_8069_ = leanh::lean_ctor_get(v_fst_8043_, 2);
                v___x_8070_ = lean_array_fget(v_array_8047_, v_start_8048_);
                v___x_8071_ = leanh::lean_unsigned_to_nat(1);
                v___x_8072_ = lean_nat_add(v_start_8048_, v___x_8071_);
                leanh::lean_dec(v_start_8048_);
                if v_isShared_8066_ == 0 {
                    leanh::lean_ctor_set(v___x_8065_, 1, v___x_8072_);
                    v___x_8074_ = v___x_8065_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8164_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8164_, 0, v_array_8047_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8164_, 1, v___x_8072_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8164_, 2, v_stop_8049_);
                    v___x_8074_ = v_reuseFailAlloc_8164_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v___x_8075_ = lean_nat_dec_lt(v_start_8068_, v_stop_8069_);
                if v___x_8075_ == 0 {
                    leanh::lean_dec(v___x_8070_);
                    leanh::lean_dec_ref(v_xs_8015_);
                    if v_isShared_8046_ == 0 {
                        leanh::lean_ctor_set(v___x_8045_, 1, v___x_8074_);
                        v___x_8077_ = v___x_8045_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_8088_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8088_, 0, v_fst_8043_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8088_, 1, v___x_8074_);
                        v___x_8077_ = v_reuseFailAlloc_8088_;
                        state = 11;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_8069_);
                    leanh::lean_inc(v_start_8068_);
                    leanh::lean_inc_ref(v_array_8067_);
                    v_isSharedCheck_8160_ = (!leanh::lean_is_exclusive(v_fst_8043_)) as u8;
                    if v_isSharedCheck_8160_ == 0 {
                        v_unused_8161_ = leanh::lean_ctor_get(v_fst_8043_, 2);
                        leanh::lean_dec(v_unused_8161_);
                        v_unused_8162_ = leanh::lean_ctor_get(v_fst_8043_, 1);
                        leanh::lean_dec(v_unused_8162_);
                        v_unused_8163_ = leanh::lean_ctor_get(v_fst_8043_, 0);
                        leanh::lean_dec(v_unused_8163_);
                        v___x_8090_ = v_fst_8043_;
                        v_isShared_8091_ = v_isSharedCheck_8160_;
                        state = 15;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_8043_);
                        v___x_8090_ = leanh::lean_box(0);
                        v_isShared_8091_ = v_isSharedCheck_8160_;
                        state = 15;
                        continue;
                    }
                }
            }
            11 => {
                if v_isShared_8042_ == 0 {
                    leanh::lean_ctor_set(v___x_8041_, 1, v___x_8077_);
                    v___x_8079_ = v___x_8041_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8087_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8087_, 0, v_fst_8039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8087_, 1, v___x_8077_);
                    v___x_8079_ = v_reuseFailAlloc_8087_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                if v_isShared_8038_ == 0 {
                    leanh::lean_ctor_set(v___x_8037_, 1, v___x_8079_);
                    v___x_8081_ = v___x_8037_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_8086_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8086_, 0, v_fst_8035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8086_, 1, v___x_8079_);
                    v___x_8081_ = v_reuseFailAlloc_8086_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_8034_ == 0 {
                    leanh::lean_ctor_set(v___x_8033_, 1, v___x_8081_);
                    v___x_8083_ = v___x_8033_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_8085_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 0, v_fst_8031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8085_, 1, v___x_8081_);
                    v___x_8083_ = v_reuseFailAlloc_8085_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_8084_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8084_, 0, v___x_8083_);
                return v___x_8084_;
            }
            15 => {
                v_array_8092_ = leanh::lean_ctor_get(v_fst_8039_, 0);
                v_start_8093_ = leanh::lean_ctor_get(v_fst_8039_, 1);
                v_stop_8094_ = leanh::lean_ctor_get(v_fst_8039_, 2);
                v___x_8095_ = lean_array_fget(v_array_8067_, v_start_8068_);
                v___x_8096_ = lean_nat_add(v_start_8068_, v___x_8071_);
                leanh::lean_dec(v_start_8068_);
                if v_isShared_8091_ == 0 {
                    leanh::lean_ctor_set(v___x_8090_, 1, v___x_8096_);
                    v___x_8098_ = v___x_8090_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_8159_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8159_, 0, v_array_8067_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8159_, 1, v___x_8096_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8159_, 2, v_stop_8069_);
                    v___x_8098_ = v_reuseFailAlloc_8159_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___x_8099_ = lean_nat_dec_lt(v_start_8093_, v_stop_8094_);
                if v___x_8099_ == 0 {
                    leanh::lean_dec(v___x_8095_);
                    leanh::lean_dec(v___x_8070_);
                    leanh::lean_dec_ref(v_xs_8015_);
                    if v_isShared_8046_ == 0 {
                        leanh::lean_ctor_set(v___x_8045_, 1, v___x_8074_);
                        leanh::lean_ctor_set(v___x_8045_, 0, v___x_8098_);
                        v___x_8101_ = v___x_8045_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_8112_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 0, v___x_8098_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8112_, 1, v___x_8074_);
                        v___x_8101_ = v_reuseFailAlloc_8112_;
                        state = 17;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_8094_);
                    leanh::lean_inc(v_start_8093_);
                    leanh::lean_inc_ref(v_array_8092_);
                    leanh::lean_del_object(v___x_8033_);
                    v_isSharedCheck_8155_ = (!leanh::lean_is_exclusive(v_fst_8039_)) as u8;
                    if v_isSharedCheck_8155_ == 0 {
                        v_unused_8156_ = leanh::lean_ctor_get(v_fst_8039_, 2);
                        leanh::lean_dec(v_unused_8156_);
                        v_unused_8157_ = leanh::lean_ctor_get(v_fst_8039_, 1);
                        leanh::lean_dec(v_unused_8157_);
                        v_unused_8158_ = leanh::lean_ctor_get(v_fst_8039_, 0);
                        leanh::lean_dec(v_unused_8158_);
                        v___x_8114_ = v_fst_8039_;
                        v_isShared_8115_ = v_isSharedCheck_8155_;
                        state = 21;
                        continue;
                    } else {
                        leanh::lean_dec(v_fst_8039_);
                        v___x_8114_ = leanh::lean_box(0);
                        v_isShared_8115_ = v_isSharedCheck_8155_;
                        state = 21;
                        continue;
                    }
                }
            }
            17 => {
                if v_isShared_8042_ == 0 {
                    leanh::lean_ctor_set(v___x_8041_, 1, v___x_8101_);
                    v___x_8103_ = v___x_8041_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_8111_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8111_, 0, v_fst_8039_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8111_, 1, v___x_8101_);
                    v___x_8103_ = v_reuseFailAlloc_8111_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                if v_isShared_8038_ == 0 {
                    leanh::lean_ctor_set(v___x_8037_, 1, v___x_8103_);
                    v___x_8105_ = v___x_8037_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_8110_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8110_, 0, v_fst_8035_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8110_, 1, v___x_8103_);
                    v___x_8105_ = v_reuseFailAlloc_8110_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                if v_isShared_8034_ == 0 {
                    leanh::lean_ctor_set(v___x_8033_, 1, v___x_8105_);
                    v___x_8107_ = v___x_8033_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_8109_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8109_, 0, v_fst_8031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8109_, 1, v___x_8105_);
                    v___x_8107_ = v_reuseFailAlloc_8109_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___x_8108_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8108_, 0, v___x_8107_);
                return v___x_8108_;
            }
            21 => {
                v_a_8116_ = lean_array_uget_borrowed(v_as_8016_, v_i_8018_);
                v___x_8117_ = lean_array_fget_borrowed(v_array_8092_, v_start_8093_);
                leanh::lean_inc(v___x_8117_);
                leanh::lean_inc_ref(v_xs_8015_);
                leanh::lean_inc(v_a_8116_);
                v___x_8118_ = l_Lean_Elab_Structural_getRecArgInfos(
                    v_a_8116_,
                    v___x_8070_,
                    v_xs_8015_,
                    v___x_8117_,
                    v___x_8095_,
                    v___y_8020_,
                    v___y_8021_,
                    v___y_8022_,
                    v___y_8023_,
                );
                if leanh::lean_obj_tag(v___x_8118_) == 0 {
                    v_a_8119_ = leanh::lean_ctor_get(v___x_8118_, 0);
                    leanh::lean_inc(v_a_8119_);
                    leanh::lean_dec_ref_known(v___x_8118_, 1);
                    v_fst_8120_ = leanh::lean_ctor_get(v_a_8119_, 0);
                    v_snd_8121_ = leanh::lean_ctor_get(v_a_8119_, 1);
                    v_isSharedCheck_8146_ = (!leanh::lean_is_exclusive(v_a_8119_)) as u8;
                    if v_isSharedCheck_8146_ == 0 {
                        v___x_8123_ = v_a_8119_;
                        v_isShared_8124_ = v_isSharedCheck_8146_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8121_);
                        leanh::lean_inc(v_fst_8120_);
                        leanh::lean_dec(v_a_8119_);
                        v___x_8123_ = leanh::lean_box(0);
                        v_isShared_8124_ = v_isSharedCheck_8146_;
                        state = 22;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8114_);
                    leanh::lean_dec_ref(v___x_8098_);
                    leanh::lean_dec(v_stop_8094_);
                    leanh::lean_dec(v_start_8093_);
                    leanh::lean_dec_ref(v_array_8092_);
                    leanh::lean_dec_ref(v___x_8074_);
                    leanh::lean_del_object(v___x_8045_);
                    leanh::lean_del_object(v___x_8041_);
                    leanh::lean_del_object(v___x_8037_);
                    leanh::lean_dec(v_fst_8035_);
                    leanh::lean_dec(v_fst_8031_);
                    leanh::lean_dec_ref(v_xs_8015_);
                    v_a_8147_ = leanh::lean_ctor_get(v___x_8118_, 0);
                    v_isSharedCheck_8154_ = (!leanh::lean_is_exclusive(v___x_8118_)) as u8;
                    if v_isSharedCheck_8154_ == 0 {
                        v___x_8149_ = v___x_8118_;
                        v_isShared_8150_ = v_isSharedCheck_8154_;
                        state = 28;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8147_);
                        leanh::lean_dec(v___x_8118_);
                        v___x_8149_ = leanh::lean_box(0);
                        v_isShared_8150_ = v_isSharedCheck_8154_;
                        state = 28;
                        continue;
                    }
                }
            }
            22 => {
                v___x_8125_ = lean_nat_add(v_start_8093_, v___x_8071_);
                leanh::lean_dec(v_start_8093_);
                if v_isShared_8115_ == 0 {
                    leanh::lean_ctor_set(v___x_8114_, 1, v___x_8125_);
                    v___x_8127_ = v___x_8114_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_8145_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8145_, 0, v_array_8092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8145_, 1, v___x_8125_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8145_, 2, v_stop_8094_);
                    v___x_8127_ = v_reuseFailAlloc_8145_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                v___x_8128_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8128_, 0, v_fst_8031_);
                leanh::lean_ctor_set(v___x_8128_, 1, v_snd_8121_);
                v___x_8129_ = lean_array_push(v_fst_8035_, v_fst_8120_);
                if v_isShared_8124_ == 0 {
                    leanh::lean_ctor_set(v___x_8123_, 1, v___x_8074_);
                    leanh::lean_ctor_set(v___x_8123_, 0, v___x_8098_);
                    v___x_8131_ = v___x_8123_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_8144_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8144_, 0, v___x_8098_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8144_, 1, v___x_8074_);
                    v___x_8131_ = v_reuseFailAlloc_8144_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                if v_isShared_8046_ == 0 {
                    leanh::lean_ctor_set(v___x_8045_, 1, v___x_8131_);
                    leanh::lean_ctor_set(v___x_8045_, 0, v___x_8127_);
                    v___x_8133_ = v___x_8045_;
                    state = 25;
                    continue;
                } else {
                    v_reuseFailAlloc_8143_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 0, v___x_8127_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8143_, 1, v___x_8131_);
                    v___x_8133_ = v_reuseFailAlloc_8143_;
                    state = 25;
                    continue;
                }
            }
            25 => {
                if v_isShared_8042_ == 0 {
                    leanh::lean_ctor_set(v___x_8041_, 1, v___x_8133_);
                    leanh::lean_ctor_set(v___x_8041_, 0, v___x_8129_);
                    v___x_8135_ = v___x_8041_;
                    state = 26;
                    continue;
                } else {
                    v_reuseFailAlloc_8142_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8142_, 0, v___x_8129_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8142_, 1, v___x_8133_);
                    v___x_8135_ = v_reuseFailAlloc_8142_;
                    state = 26;
                    continue;
                }
            }
            26 => {
                if v_isShared_8038_ == 0 {
                    leanh::lean_ctor_set(v___x_8037_, 1, v___x_8135_);
                    leanh::lean_ctor_set(v___x_8037_, 0, v___x_8128_);
                    v___x_8137_ = v___x_8037_;
                    state = 27;
                    continue;
                } else {
                    v_reuseFailAlloc_8141_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8141_, 0, v___x_8128_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8141_, 1, v___x_8135_);
                    v___x_8137_ = v_reuseFailAlloc_8141_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_8138_ = 1usize;
                v___x_8139_ = lean_usize_add(v_i_8018_, v___x_8138_);
                v_i_8018_ = v___x_8139_;
                v_b_8019_ = v___x_8137_;
                state = 0;
                continue;
            }
            28 => {
                if v_isShared_8150_ == 0 {
                    v___x_8152_ = v___x_8149_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_8153_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8153_, 0, v_a_8147_);
                    v___x_8152_ = v_reuseFailAlloc_8153_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_8152_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0___boxed(
    mut v_xs_8177_: *mut leanh::LeanObject,
    mut v_as_8178_: *mut leanh::LeanObject,
    mut v_sz_8179_: *mut leanh::LeanObject,
    mut v_i_8180_: *mut leanh::LeanObject,
    mut v_b_8181_: *mut leanh::LeanObject,
    mut v___y_8182_: *mut leanh::LeanObject,
    mut v___y_8183_: *mut leanh::LeanObject,
    mut v___y_8184_: *mut leanh::LeanObject,
    mut v___y_8185_: *mut leanh::LeanObject,
    mut v___y_8186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8187_: usize = 0;
    let mut v_i_boxed_8188_: usize = 0;
    let mut v_res_8189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8187_ = leanh::lean_unbox_usize(v_sz_8179_);
    leanh::lean_dec(v_sz_8179_);
    v_i_boxed_8188_ = leanh::lean_unbox_usize(v_i_8180_);
    leanh::lean_dec(v_i_8180_);
    v_res_8189_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_8177_, v_as_8178_, v_sz_boxed_8187_, v_i_boxed_8188_, v_b_8181_, v___y_8182_, v___y_8183_, v___y_8184_, v___y_8185_);
    leanh::lean_dec(v___y_8185_);
    leanh::lean_dec_ref(v___y_8184_);
    leanh::lean_dec(v___y_8183_);
    leanh::lean_dec_ref(v___y_8182_);
    leanh::lean_dec_ref(v_as_8178_);
    return v_res_8189_;
}
pub unsafe fn l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(
    mut v_a_8190_: *mut leanh::LeanObject,
    mut v_a_8191_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_head_8193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_8194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8196_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8197_: u8 = 0;
    let mut v___x_8198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8203_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_8190_) == 0 {
                    v___x_8192_ = l_List_reverse___redArg(v_a_8191_);
                    return v___x_8192_;
                } else {
                    v_head_8193_ = leanh::lean_ctor_get(v_a_8190_, 0);
                    v_tail_8194_ = leanh::lean_ctor_get(v_a_8190_, 1);
                    v_isSharedCheck_8203_ = (!leanh::lean_is_exclusive(v_a_8190_)) as u8;
                    if v_isSharedCheck_8203_ == 0 {
                        v___x_8196_ = v_a_8190_;
                        v_isShared_8197_ = v_isSharedCheck_8203_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_8194_);
                        leanh::lean_inc(v_head_8193_);
                        leanh::lean_dec(v_a_8190_);
                        v___x_8196_ = leanh::lean_box(0);
                        v_isShared_8197_ = v_isSharedCheck_8203_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_8198_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_head_8193_);
                if v_isShared_8197_ == 0 {
                    leanh::lean_ctor_set(v___x_8196_, 1, v_a_8191_);
                    leanh::lean_ctor_set(v___x_8196_, 0, v___x_8198_);
                    v___x_8200_ = v___x_8196_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8202_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8202_, 0, v___x_8198_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8202_, 1, v_a_8191_);
                    v___x_8200_ = v_reuseFailAlloc_8202_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_a_8190_ = v_tail_8194_;
                v_a_8191_ = v___x_8200_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(
    mut v_as_8204_: *mut leanh::LeanObject,
    mut v_j_8205_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8207_: u8 = 0;
    let mut v___x_8208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8211_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8212_: u8 = 0;
    let mut v___x_8213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8206_ = lean_array_get_size(v_as_8204_);
                v___x_8207_ = lean_nat_dec_lt(v_j_8205_, v___x_8206_);
                if v___x_8207_ == 0 {
                    leanh::lean_dec(v_j_8205_);
                    v___x_8208_ = leanh::lean_box(0);
                    return v___x_8208_;
                } else {
                    v___x_8209_ = lean_array_fget_borrowed(v_as_8204_, v_j_8205_);
                    v___x_8210_ = lean_array_get_size(v___x_8209_);
                    v___x_8211_ = leanh::lean_unsigned_to_nat(0);
                    v___x_8212_ = lean_nat_dec_eq(v___x_8210_, v___x_8211_);
                    if v___x_8212_ == 0 {
                        v___x_8213_ = leanh::lean_unsigned_to_nat(1);
                        v___x_8214_ = lean_nat_add(v_j_8205_, v___x_8213_);
                        leanh::lean_dec(v_j_8205_);
                        v_j_8205_ = v___x_8214_;
                        state = 0;
                        continue;
                    } else {
                        v___x_8216_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_8216_, 0, v_j_8205_);
                        return v___x_8216_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3___boxed(
    mut v_as_8217_: *mut leanh::LeanObject,
    mut v_j_8218_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8219_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8219_ =
        l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(
            v_as_8217_, v_j_8218_,
        );
    leanh::lean_dec_ref(v_as_8217_);
    return v_res_8219_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(
    mut v_a_8220_: *mut leanh::LeanObject,
    mut v_as_8221_: *mut leanh::LeanObject,
    mut v_sz_8222_: usize,
    mut v_i_8223_: usize,
    mut v_b_8224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8226_: u8 = 0;
    let mut v___x_8227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8228_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8231_: usize = 0;
    let mut v___x_8232_: usize = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8226_ = lean_usize_dec_lt(v_i_8223_, v_sz_8222_);
                if v___x_8226_ == 0 {
                    leanh::lean_dec_ref(v_a_8220_);
                    v___x_8227_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8227_, 0, v_b_8224_);
                    return v___x_8227_;
                } else {
                    v_a_8228_ = lean_array_uget_borrowed(v_as_8221_, v_i_8223_);
                    leanh::lean_inc(v_a_8228_);
                    leanh::lean_inc_ref(v_a_8220_);
                    v___x_8229_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8229_, 0, v_a_8220_);
                    leanh::lean_ctor_set(v___x_8229_, 1, v_a_8228_);
                    v___x_8230_ = lean_array_push(v_b_8224_, v___x_8229_);
                    v___x_8231_ = 1usize;
                    v___x_8232_ = lean_usize_add(v_i_8223_, v___x_8231_);
                    v_i_8223_ = v___x_8232_;
                    v_b_8224_ = v___x_8230_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg___boxed(
    mut v_a_8234_: *mut leanh::LeanObject,
    mut v_as_8235_: *mut leanh::LeanObject,
    mut v_sz_8236_: *mut leanh::LeanObject,
    mut v_i_8237_: *mut leanh::LeanObject,
    mut v_b_8238_: *mut leanh::LeanObject,
    mut v___y_8239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8240_: usize = 0;
    let mut v_i_boxed_8241_: usize = 0;
    let mut v_res_8242_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8240_ = leanh::lean_unbox_usize(v_sz_8236_);
    leanh::lean_dec(v_sz_8236_);
    v_i_boxed_8241_ = leanh::lean_unbox_usize(v_i_8237_);
    leanh::lean_dec(v_i_8237_);
    v_res_8242_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_8234_, v_as_8235_, v_sz_boxed_8240_, v_i_boxed_8241_, v_b_8238_);
    leanh::lean_dec_ref(v_as_8235_);
    return v_res_8242_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(
    mut v_a_8243_: *mut leanh::LeanObject,
    mut v_xs_8244_: *mut leanh::LeanObject,
    mut v_as_8245_: *mut leanh::LeanObject,
    mut v_sz_8246_: usize,
    mut v_i_8247_: usize,
    mut v_b_8248_: *mut leanh::LeanObject,
    mut v___y_8249_: *mut leanh::LeanObject,
    mut v___y_8250_: *mut leanh::LeanObject,
    mut v___y_8251_: *mut leanh::LeanObject,
    mut v___y_8252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8254_: u8 = 0;
    let mut v___x_8255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8260_: u8 = 0;
    let mut v_array_8261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_start_8262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_stop_8263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8264_: u8 = 0;
    let mut v___x_8266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8271_: u8 = 0;
    let mut v_a_8272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8283_: usize = 0;
    let mut v___x_8284_: usize = 0;
    let mut v_reuseFailAlloc_8286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8291_: u8 = 0;
    let mut v___x_8293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8295_: u8 = 0;
    let mut v_isSharedCheck_8296_: u8 = 0;
    let mut v_unused_8297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_8299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8300_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8254_ = lean_usize_dec_lt(v_i_8247_, v_sz_8246_);
                if v___x_8254_ == 0 {
                    leanh::lean_dec_ref(v_xs_8244_);
                    leanh::lean_dec_ref(v_a_8243_);
                    v___x_8255_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8255_, 0, v_b_8248_);
                    return v___x_8255_;
                } else {
                    v_snd_8256_ = leanh::lean_ctor_get(v_b_8248_, 1);
                    v_fst_8257_ = leanh::lean_ctor_get(v_b_8248_, 0);
                    v_isSharedCheck_8300_ = (!leanh::lean_is_exclusive(v_b_8248_)) as u8;
                    if v_isSharedCheck_8300_ == 0 {
                        v___x_8259_ = v_b_8248_;
                        v_isShared_8260_ = v_isSharedCheck_8300_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8256_);
                        leanh::lean_inc(v_fst_8257_);
                        leanh::lean_dec(v_b_8248_);
                        v___x_8259_ = leanh::lean_box(0);
                        v_isShared_8260_ = v_isSharedCheck_8300_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_array_8261_ = leanh::lean_ctor_get(v_snd_8256_, 0);
                v_start_8262_ = leanh::lean_ctor_get(v_snd_8256_, 1);
                v_stop_8263_ = leanh::lean_ctor_get(v_snd_8256_, 2);
                v___x_8264_ = lean_nat_dec_lt(v_start_8262_, v_stop_8263_);
                if v___x_8264_ == 0 {
                    leanh::lean_dec_ref(v_xs_8244_);
                    leanh::lean_dec_ref(v_a_8243_);
                    if v_isShared_8260_ == 0 {
                        v___x_8266_ = v___x_8259_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8268_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8268_, 0, v_fst_8257_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8268_, 1, v_snd_8256_);
                        v___x_8266_ = v_reuseFailAlloc_8268_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc(v_stop_8263_);
                    leanh::lean_inc(v_start_8262_);
                    leanh::lean_inc_ref(v_array_8261_);
                    v_isSharedCheck_8296_ = (!leanh::lean_is_exclusive(v_snd_8256_)) as u8;
                    if v_isSharedCheck_8296_ == 0 {
                        v_unused_8297_ = leanh::lean_ctor_get(v_snd_8256_, 2);
                        leanh::lean_dec(v_unused_8297_);
                        v_unused_8298_ = leanh::lean_ctor_get(v_snd_8256_, 1);
                        leanh::lean_dec(v_unused_8298_);
                        v_unused_8299_ = leanh::lean_ctor_get(v_snd_8256_, 0);
                        leanh::lean_dec(v_unused_8299_);
                        v___x_8270_ = v_snd_8256_;
                        v_isShared_8271_ = v_isSharedCheck_8296_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_dec(v_snd_8256_);
                        v___x_8270_ = leanh::lean_box(0);
                        v_isShared_8271_ = v_isSharedCheck_8296_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_8267_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8267_, 0, v___x_8266_);
                return v___x_8267_;
            }
            3 => {
                v_a_8272_ = lean_array_uget_borrowed(v_as_8245_, v_i_8247_);
                v___x_8273_ = lean_array_fget_borrowed(v_array_8261_, v_start_8262_);
                leanh::lean_inc(v_a_8272_);
                leanh::lean_inc_ref(v_xs_8244_);
                leanh::lean_inc_ref(v_a_8243_);
                v___x_8274_ = l_Lean_Elab_Structural_argsInGroup(
                    v_a_8243_,
                    v_xs_8244_,
                    v_a_8272_,
                    v___x_8273_,
                    v___y_8249_,
                    v___y_8250_,
                    v___y_8251_,
                    v___y_8252_,
                );
                if leanh::lean_obj_tag(v___x_8274_) == 0 {
                    v_a_8275_ = leanh::lean_ctor_get(v___x_8274_, 0);
                    leanh::lean_inc(v_a_8275_);
                    leanh::lean_dec_ref_known(v___x_8274_, 1);
                    v___x_8276_ = leanh::lean_unsigned_to_nat(1);
                    v___x_8277_ = lean_nat_add(v_start_8262_, v___x_8276_);
                    leanh::lean_dec(v_start_8262_);
                    if v_isShared_8271_ == 0 {
                        leanh::lean_ctor_set(v___x_8270_, 1, v___x_8277_);
                        v___x_8279_ = v___x_8270_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8287_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8287_, 0, v_array_8261_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8287_, 1, v___x_8277_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8287_, 2, v_stop_8263_);
                        v___x_8279_ = v_reuseFailAlloc_8287_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_8270_);
                    leanh::lean_dec(v_stop_8263_);
                    leanh::lean_dec(v_start_8262_);
                    leanh::lean_dec_ref(v_array_8261_);
                    leanh::lean_del_object(v___x_8259_);
                    leanh::lean_dec(v_fst_8257_);
                    leanh::lean_dec_ref(v_xs_8244_);
                    leanh::lean_dec_ref(v_a_8243_);
                    v_a_8288_ = leanh::lean_ctor_get(v___x_8274_, 0);
                    v_isSharedCheck_8295_ = (!leanh::lean_is_exclusive(v___x_8274_)) as u8;
                    if v_isSharedCheck_8295_ == 0 {
                        v___x_8290_ = v___x_8274_;
                        v_isShared_8291_ = v_isSharedCheck_8295_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8288_);
                        leanh::lean_dec(v___x_8274_);
                        v___x_8290_ = leanh::lean_box(0);
                        v_isShared_8291_ = v_isSharedCheck_8295_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                v___x_8280_ = lean_array_push(v_fst_8257_, v_a_8275_);
                if v_isShared_8260_ == 0 {
                    leanh::lean_ctor_set(v___x_8259_, 1, v___x_8279_);
                    leanh::lean_ctor_set(v___x_8259_, 0, v___x_8280_);
                    v___x_8282_ = v___x_8259_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8286_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8286_, 0, v___x_8280_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8286_, 1, v___x_8279_);
                    v___x_8282_ = v_reuseFailAlloc_8286_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_8283_ = 1usize;
                v___x_8284_ = lean_usize_add(v_i_8247_, v___x_8283_);
                v_i_8247_ = v___x_8284_;
                v_b_8248_ = v___x_8282_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_8291_ == 0 {
                    v___x_8293_ = v___x_8290_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8294_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8294_, 0, v_a_8288_);
                    v___x_8293_ = v_reuseFailAlloc_8294_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2___boxed(
    mut v_a_8301_: *mut leanh::LeanObject,
    mut v_xs_8302_: *mut leanh::LeanObject,
    mut v_as_8303_: *mut leanh::LeanObject,
    mut v_sz_8304_: *mut leanh::LeanObject,
    mut v_i_8305_: *mut leanh::LeanObject,
    mut v_b_8306_: *mut leanh::LeanObject,
    mut v___y_8307_: *mut leanh::LeanObject,
    mut v___y_8308_: *mut leanh::LeanObject,
    mut v___y_8309_: *mut leanh::LeanObject,
    mut v___y_8310_: *mut leanh::LeanObject,
    mut v___y_8311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8312_: usize = 0;
    let mut v_i_boxed_8313_: usize = 0;
    let mut v_res_8314_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8312_ = leanh::lean_unbox_usize(v_sz_8304_);
    leanh::lean_dec(v_sz_8304_);
    v_i_boxed_8313_ = leanh::lean_unbox_usize(v_i_8305_);
    leanh::lean_dec(v_i_8305_);
    v_res_8314_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_8301_, v_xs_8302_, v_as_8303_, v_sz_boxed_8312_, v_i_boxed_8313_, v_b_8306_, v___y_8307_, v___y_8308_, v___y_8309_, v___y_8310_);
    leanh::lean_dec(v___y_8310_);
    leanh::lean_dec_ref(v___y_8309_);
    leanh::lean_dec(v___y_8308_);
    leanh::lean_dec_ref(v___y_8307_);
    leanh::lean_dec_ref(v_as_8303_);
    return v_res_8314_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_8318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8318_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__1;
    v___x_8319_ = l_Lean_stringToMessageData(v___x_8318_);
    return v___x_8319_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_8321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8321_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__3;
    v___x_8322_ = l_Lean_stringToMessageData(v___x_8321_);
    return v___x_8322_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_8324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8324_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__5;
    v___x_8325_ = l_Lean_stringToMessageData(v___x_8324_);
    return v___x_8325_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_8327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8327_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__7;
    v___x_8328_ = l_Lean_stringToMessageData(v___x_8327_);
    return v___x_8328_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_8330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8330_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__9;
    v___x_8331_ = l_Lean_stringToMessageData(v___x_8330_);
    return v___x_8331_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12()
-> *mut leanh::LeanObject {
    let mut v___x_8333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8334_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8333_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__11;
    v___x_8334_ = l_Lean_stringToMessageData(v___x_8333_);
    return v___x_8334_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(
    mut v___x_8335_: *mut leanh::LeanObject,
    mut v_values_8336_: *mut leanh::LeanObject,
    mut v_xs_8337_: *mut leanh::LeanObject,
    mut v_fnNames_8338_: *mut leanh::LeanObject,
    mut v_as_8339_: *mut leanh::LeanObject,
    mut v_sz_8340_: usize,
    mut v_i_8341_: usize,
    mut v_b_8342_: *mut leanh::LeanObject,
    mut v___y_8343_: *mut leanh::LeanObject,
    mut v___y_8344_: *mut leanh::LeanObject,
    mut v___y_8345_: *mut leanh::LeanObject,
    mut v___y_8346_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_8349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8350_: usize = 0;
    let mut v___x_8351_: usize = 0;
    let mut v___x_8353_: u8 = 0;
    let mut v___x_8354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgInfoss_8356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8361_: usize = 0;
    let mut v___x_8362_: usize = 0;
    let mut v___x_8363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8369_: u8 = 0;
    let mut v_fst_8370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8373_: u8 = 0;
    let mut v___x_8374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8394_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8395_: usize = 0;
    let mut v___x_8396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8404_: u8 = 0;
    let mut v___x_8406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8407_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8408_: u8 = 0;
    let mut v___x_8409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8422_: u8 = 0;
    let mut v_unused_8423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8424_: u8 = 0;
    let mut v_a_8425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8428_: u8 = 0;
    let mut v___x_8430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8432_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8353_ = lean_usize_dec_lt(v_i_8341_, v_sz_8340_);
                if v___x_8353_ == 0 {
                    leanh::lean_dec_ref(v_xs_8337_);
                    leanh::lean_dec_ref(v___x_8335_);
                    v___x_8354_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8354_, 0, v_b_8342_);
                    return v___x_8354_;
                } else {
                    v___x_8355_ = leanh::lean_unsigned_to_nat(0);
                    v_recArgInfoss_8356_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0;
                    v_a_8357_ = lean_array_uget_borrowed(v_as_8339_, v_i_8341_);
                    v___x_8358_ = lean_array_get_size(v___x_8335_);
                    leanh::lean_inc_ref(v___x_8335_);
                    v___x_8359_ =
                        l_Array_toSubarray___redArg(v___x_8335_, v___x_8355_, v___x_8358_);
                    v___x_8360_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8360_, 0, v_recArgInfoss_8356_);
                    leanh::lean_ctor_set(v___x_8360_, 1, v___x_8359_);
                    v_sz_8361_ = lean_array_size(v_values_8336_);
                    v___x_8362_ = 0usize;
                    leanh::lean_inc_ref(v_xs_8337_);
                    leanh::lean_inc(v_a_8357_);
                    v___x_8363_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_8357_, v_xs_8337_, v_values_8336_, v_sz_8361_, v___x_8362_, v___x_8360_, v___y_8343_, v___y_8344_, v___y_8345_, v___y_8346_);
                    if leanh::lean_obj_tag(v___x_8363_) == 0 {
                        v_a_8364_ = leanh::lean_ctor_get(v___x_8363_, 0);
                        leanh::lean_inc(v_a_8364_);
                        leanh::lean_dec_ref_known(v___x_8363_, 1);
                        v_fst_8365_ = leanh::lean_ctor_get(v_b_8342_, 0);
                        v_snd_8366_ = leanh::lean_ctor_get(v_b_8342_, 1);
                        v_isSharedCheck_8424_ = (!leanh::lean_is_exclusive(v_b_8342_)) as u8;
                        if v_isSharedCheck_8424_ == 0 {
                            v___x_8368_ = v_b_8342_;
                            v_isShared_8369_ = v_isSharedCheck_8424_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_8366_);
                            leanh::lean_inc(v_fst_8365_);
                            leanh::lean_dec(v_b_8342_);
                            v___x_8368_ = leanh::lean_box(0);
                            v_isShared_8369_ = v_isSharedCheck_8424_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_8342_);
                        leanh::lean_dec_ref(v_xs_8337_);
                        leanh::lean_dec_ref(v___x_8335_);
                        v_a_8425_ = leanh::lean_ctor_get(v___x_8363_, 0);
                        v_isSharedCheck_8432_ =
                            (!leanh::lean_is_exclusive(v___x_8363_)) as u8;
                        if v_isSharedCheck_8432_ == 0 {
                            v___x_8427_ = v___x_8363_;
                            v_isShared_8428_ = v_isSharedCheck_8432_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8425_);
                            leanh::lean_dec(v___x_8363_);
                            v___x_8427_ = leanh::lean_box(0);
                            v_isShared_8428_ = v_isSharedCheck_8432_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_8350_ = 1usize;
                v___x_8351_ = lean_usize_add(v_i_8341_, v___x_8350_);
                v_i_8341_ = v___x_8351_;
                v_b_8342_ = v_a_8349_;
                state = 0;
                continue;
            }
            2 => {
                v_fst_8370_ = leanh::lean_ctor_get(v_a_8364_, 0);
                v_isSharedCheck_8422_ = (!leanh::lean_is_exclusive(v_a_8364_)) as u8;
                if v_isSharedCheck_8422_ == 0 {
                    v_unused_8423_ = leanh::lean_ctor_get(v_a_8364_, 1);
                    leanh::lean_dec(v_unused_8423_);
                    v___x_8372_ = v_a_8364_;
                    v_isShared_8373_ = v_isSharedCheck_8422_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_8370_);
                    leanh::lean_dec(v_a_8364_);
                    v___x_8372_ = leanh::lean_box(0);
                    v_isShared_8373_ = v_isSharedCheck_8422_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8374_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_8370_, v___x_8355_);
                if leanh::lean_obj_tag(v___x_8374_) == 1 {
                    leanh::lean_dec(v_fst_8370_);
                    v_val_8375_ = leanh::lean_ctor_get(v___x_8374_, 0);
                    leanh::lean_inc(v_val_8375_);
                    leanh::lean_dec_ref_known(v___x_8374_, 1);
                    v___x_8376_ = leanh::lean_box(0);
                    v___x_8377_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
                    leanh::lean_inc(v_a_8357_);
                    v___x_8378_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_8357_);
                    if v_isShared_8369_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_8368_, 7);
                        leanh::lean_ctor_set(v___x_8368_, 1, v___x_8378_);
                        leanh::lean_ctor_set(v___x_8368_, 0, v___x_8377_);
                        v___x_8380_ = v___x_8368_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8392_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8392_, 0, v___x_8377_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8392_, 1, v___x_8378_);
                        v___x_8380_ = v_reuseFailAlloc_8392_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_8374_);
                    v___x_8393_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_8370_);
                    leanh::lean_dec(v_fst_8370_);
                    if leanh::lean_obj_tag(v___x_8393_) == 1 {
                        leanh::lean_del_object(v___x_8368_);
                        v_val_8394_ = leanh::lean_ctor_get(v___x_8393_, 0);
                        leanh::lean_inc(v_val_8394_);
                        leanh::lean_dec_ref_known(v___x_8393_, 1);
                        v_sz_8395_ = lean_array_size(v_val_8394_);
                        leanh::lean_inc(v_a_8357_);
                        v___x_8396_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_8357_, v_val_8394_, v_sz_8395_, v___x_8362_, v_snd_8366_);
                        leanh::lean_dec(v_val_8394_);
                        if leanh::lean_obj_tag(v___x_8396_) == 0 {
                            v_a_8397_ = leanh::lean_ctor_get(v___x_8396_, 0);
                            leanh::lean_inc(v_a_8397_);
                            leanh::lean_dec_ref_known(v___x_8396_, 1);
                            if v_isShared_8373_ == 0 {
                                leanh::lean_ctor_set(v___x_8372_, 1, v_a_8397_);
                                leanh::lean_ctor_set(v___x_8372_, 0, v_fst_8365_);
                                v___x_8399_ = v___x_8372_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_8400_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_8400_, 0, v_fst_8365_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_8400_, 1, v_a_8397_);
                                v___x_8399_ = v_reuseFailAlloc_8400_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_8372_);
                            leanh::lean_dec(v_fst_8365_);
                            leanh::lean_dec_ref(v_xs_8337_);
                            leanh::lean_dec_ref(v___x_8335_);
                            v_a_8401_ = leanh::lean_ctor_get(v___x_8396_, 0);
                            v_isSharedCheck_8408_ =
                                (!leanh::lean_is_exclusive(v___x_8396_)) as u8;
                            if v_isSharedCheck_8408_ == 0 {
                                v___x_8403_ = v___x_8396_;
                                v_isShared_8404_ = v_isSharedCheck_8408_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8401_);
                                leanh::lean_dec(v___x_8396_);
                                v___x_8403_ = leanh::lean_box(0);
                                v_isShared_8404_ = v_isSharedCheck_8408_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_8393_);
                        v___x_8409_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
                        leanh::lean_inc(v_a_8357_);
                        v___x_8410_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_8357_);
                        if v_isShared_8369_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_8368_, 7);
                            leanh::lean_ctor_set(v___x_8368_, 1, v___x_8410_);
                            leanh::lean_ctor_set(v___x_8368_, 0, v___x_8409_);
                            v___x_8412_ = v___x_8368_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_8421_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8421_, 0, v___x_8409_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8421_, 1, v___x_8410_);
                            v___x_8412_ = v_reuseFailAlloc_8421_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_8381_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
                v___x_8382_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8382_, 0, v___x_8380_);
                leanh::lean_ctor_set(v___x_8382_, 1, v___x_8381_);
                v___x_8383_ = lean_array_get_borrowed(v___x_8376_, v_fnNames_8338_, v_val_8375_);
                leanh::lean_dec(v_val_8375_);
                leanh::lean_inc(v___x_8383_);
                v___x_8384_ = l_Lean_MessageData_ofName(v___x_8383_);
                v___x_8385_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8385_, 0, v___x_8382_);
                leanh::lean_ctor_set(v___x_8385_, 1, v___x_8384_);
                v___x_8386_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
                v___x_8387_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8387_, 0, v___x_8385_);
                leanh::lean_ctor_set(v___x_8387_, 1, v___x_8386_);
                v___x_8388_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8388_, 0, v_fst_8365_);
                leanh::lean_ctor_set(v___x_8388_, 1, v___x_8387_);
                if v_isShared_8373_ == 0 {
                    leanh::lean_ctor_set(v___x_8372_, 1, v_snd_8366_);
                    leanh::lean_ctor_set(v___x_8372_, 0, v___x_8388_);
                    v___x_8390_ = v___x_8372_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8391_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8391_, 0, v___x_8388_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8391_, 1, v_snd_8366_);
                    v___x_8390_ = v_reuseFailAlloc_8391_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_8349_ = v___x_8390_;
                state = 1;
                continue;
            }
            6 => {
                v_a_8349_ = v___x_8399_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_8404_ == 0 {
                    v___x_8406_ = v___x_8403_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8407_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8407_, 0, v_a_8401_);
                    v___x_8406_ = v_reuseFailAlloc_8407_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8406_;
            }
            9 => {
                v___x_8413_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
                v___x_8414_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8414_, 0, v___x_8412_);
                leanh::lean_ctor_set(v___x_8414_, 1, v___x_8413_);
                v___x_8415_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8415_, 0, v_fst_8365_);
                leanh::lean_ctor_set(v___x_8415_, 1, v___x_8414_);
                v___x_8416_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
                v___x_8417_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8417_, 0, v___x_8415_);
                leanh::lean_ctor_set(v___x_8417_, 1, v___x_8416_);
                if v_isShared_8373_ == 0 {
                    leanh::lean_ctor_set(v___x_8372_, 1, v_snd_8366_);
                    leanh::lean_ctor_set(v___x_8372_, 0, v___x_8417_);
                    v___x_8419_ = v___x_8372_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8420_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8420_, 0, v___x_8417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8420_, 1, v_snd_8366_);
                    v___x_8419_ = v_reuseFailAlloc_8420_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_8349_ = v___x_8419_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_8428_ == 0 {
                    v___x_8430_ = v___x_8427_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8431_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8431_, 0, v_a_8425_);
                    v___x_8430_ = v_reuseFailAlloc_8431_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8430_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___boxed(
    mut v___x_8433_: *mut leanh::LeanObject,
    mut v_values_8434_: *mut leanh::LeanObject,
    mut v_xs_8435_: *mut leanh::LeanObject,
    mut v_fnNames_8436_: *mut leanh::LeanObject,
    mut v_as_8437_: *mut leanh::LeanObject,
    mut v_sz_8438_: *mut leanh::LeanObject,
    mut v_i_8439_: *mut leanh::LeanObject,
    mut v_b_8440_: *mut leanh::LeanObject,
    mut v___y_8441_: *mut leanh::LeanObject,
    mut v___y_8442_: *mut leanh::LeanObject,
    mut v___y_8443_: *mut leanh::LeanObject,
    mut v___y_8444_: *mut leanh::LeanObject,
    mut v___y_8445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8446_: usize = 0;
    let mut v_i_boxed_8447_: usize = 0;
    let mut v_res_8448_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8446_ = leanh::lean_unbox_usize(v_sz_8438_);
    leanh::lean_dec(v_sz_8438_);
    v_i_boxed_8447_ = leanh::lean_unbox_usize(v_i_8439_);
    leanh::lean_dec(v_i_8439_);
    v_res_8448_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_8433_, v_values_8434_, v_xs_8435_, v_fnNames_8436_, v_as_8437_, v_sz_boxed_8446_, v_i_boxed_8447_, v_b_8440_, v___y_8441_, v___y_8442_, v___y_8443_, v___y_8444_);
    leanh::lean_dec(v___y_8444_);
    leanh::lean_dec_ref(v___y_8443_);
    leanh::lean_dec(v___y_8442_);
    leanh::lean_dec_ref(v___y_8441_);
    leanh::lean_dec_ref(v_as_8437_);
    leanh::lean_dec_ref(v_fnNames_8436_);
    leanh::lean_dec_ref(v_values_8434_);
    return v_res_8448_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(
    mut v_xs_8449_: *mut leanh::LeanObject,
    mut v___x_8450_: *mut leanh::LeanObject,
    mut v_values_8451_: *mut leanh::LeanObject,
    mut v_fnNames_8452_: *mut leanh::LeanObject,
    mut v_as_8453_: *mut leanh::LeanObject,
    mut v_sz_8454_: usize,
    mut v_i_8455_: usize,
    mut v_b_8456_: *mut leanh::LeanObject,
    mut v___y_8457_: *mut leanh::LeanObject,
    mut v___y_8458_: *mut leanh::LeanObject,
    mut v___y_8459_: *mut leanh::LeanObject,
    mut v___y_8460_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_8463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8464_: usize = 0;
    let mut v___x_8465_: usize = 0;
    let mut v___x_8466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8467_: u8 = 0;
    let mut v___x_8468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgInfoss_8470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8475_: usize = 0;
    let mut v___x_8476_: usize = 0;
    let mut v___x_8477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8483_: u8 = 0;
    let mut v_fst_8484_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8487_: u8 = 0;
    let mut v___x_8488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8509_: usize = 0;
    let mut v___x_8510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8515_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8518_: u8 = 0;
    let mut v___x_8520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8522_: u8 = 0;
    let mut v___x_8523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8536_: u8 = 0;
    let mut v_unused_8537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8538_: u8 = 0;
    let mut v_a_8539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8542_: u8 = 0;
    let mut v___x_8544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8546_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8467_ = lean_usize_dec_lt(v_i_8455_, v_sz_8454_);
                if v___x_8467_ == 0 {
                    leanh::lean_dec_ref(v___x_8450_);
                    leanh::lean_dec_ref(v_xs_8449_);
                    v___x_8468_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8468_, 0, v_b_8456_);
                    return v___x_8468_;
                } else {
                    v___x_8469_ = leanh::lean_unsigned_to_nat(0);
                    v_recArgInfoss_8470_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0;
                    v_a_8471_ = lean_array_uget_borrowed(v_as_8453_, v_i_8455_);
                    v___x_8472_ = lean_array_get_size(v___x_8450_);
                    leanh::lean_inc_ref(v___x_8450_);
                    v___x_8473_ =
                        l_Array_toSubarray___redArg(v___x_8450_, v___x_8469_, v___x_8472_);
                    v___x_8474_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_8474_, 0, v_recArgInfoss_8470_);
                    leanh::lean_ctor_set(v___x_8474_, 1, v___x_8473_);
                    v_sz_8475_ = lean_array_size(v_values_8451_);
                    v___x_8476_ = 0usize;
                    leanh::lean_inc_ref(v_xs_8449_);
                    leanh::lean_inc(v_a_8471_);
                    v___x_8477_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__2(v_a_8471_, v_xs_8449_, v_values_8451_, v_sz_8475_, v___x_8476_, v___x_8474_, v___y_8457_, v___y_8458_, v___y_8459_, v___y_8460_);
                    if leanh::lean_obj_tag(v___x_8477_) == 0 {
                        v_a_8478_ = leanh::lean_ctor_get(v___x_8477_, 0);
                        leanh::lean_inc(v_a_8478_);
                        leanh::lean_dec_ref_known(v___x_8477_, 1);
                        v_fst_8479_ = leanh::lean_ctor_get(v_b_8456_, 0);
                        v_snd_8480_ = leanh::lean_ctor_get(v_b_8456_, 1);
                        v_isSharedCheck_8538_ = (!leanh::lean_is_exclusive(v_b_8456_)) as u8;
                        if v_isSharedCheck_8538_ == 0 {
                            v___x_8482_ = v_b_8456_;
                            v_isShared_8483_ = v_isSharedCheck_8538_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_snd_8480_);
                            leanh::lean_inc(v_fst_8479_);
                            leanh::lean_dec(v_b_8456_);
                            v___x_8482_ = leanh::lean_box(0);
                            v_isShared_8483_ = v_isSharedCheck_8538_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_b_8456_);
                        leanh::lean_dec_ref(v___x_8450_);
                        leanh::lean_dec_ref(v_xs_8449_);
                        v_a_8539_ = leanh::lean_ctor_get(v___x_8477_, 0);
                        v_isSharedCheck_8546_ =
                            (!leanh::lean_is_exclusive(v___x_8477_)) as u8;
                        if v_isSharedCheck_8546_ == 0 {
                            v___x_8541_ = v___x_8477_;
                            v_isShared_8542_ = v_isSharedCheck_8546_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8539_);
                            leanh::lean_dec(v___x_8477_);
                            v___x_8541_ = leanh::lean_box(0);
                            v_isShared_8542_ = v_isSharedCheck_8546_;
                            state = 11;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_8464_ = 1usize;
                v___x_8465_ = lean_usize_add(v_i_8455_, v___x_8464_);
                v___x_8466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5(v___x_8450_, v_values_8451_, v_xs_8449_, v_fnNames_8452_, v_as_8453_, v_sz_8454_, v___x_8465_, v_a_8463_, v___y_8457_, v___y_8458_, v___y_8459_, v___y_8460_);
                return v___x_8466_;
            }
            2 => {
                v_fst_8484_ = leanh::lean_ctor_get(v_a_8478_, 0);
                v_isSharedCheck_8536_ = (!leanh::lean_is_exclusive(v_a_8478_)) as u8;
                if v_isSharedCheck_8536_ == 0 {
                    v_unused_8537_ = leanh::lean_ctor_get(v_a_8478_, 1);
                    leanh::lean_dec(v_unused_8537_);
                    v___x_8486_ = v_a_8478_;
                    v_isShared_8487_ = v_isSharedCheck_8536_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_8484_);
                    leanh::lean_dec(v_a_8478_);
                    v___x_8486_ = leanh::lean_box(0);
                    v_isShared_8487_ = v_isSharedCheck_8536_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_8488_ = l_Array_findIdx_x3f_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__3(v_fst_8484_, v___x_8469_);
                if leanh::lean_obj_tag(v___x_8488_) == 1 {
                    leanh::lean_dec(v_fst_8484_);
                    v_val_8489_ = leanh::lean_ctor_get(v___x_8488_, 0);
                    leanh::lean_inc(v_val_8489_);
                    leanh::lean_dec_ref_known(v___x_8488_, 1);
                    v___x_8490_ = leanh::lean_box(0);
                    v___x_8491_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__2);
                    leanh::lean_inc(v_a_8471_);
                    v___x_8492_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_8471_);
                    if v_isShared_8483_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_8482_, 7);
                        leanh::lean_ctor_set(v___x_8482_, 1, v___x_8492_);
                        leanh::lean_ctor_set(v___x_8482_, 0, v___x_8491_);
                        v___x_8494_ = v___x_8482_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_8506_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8506_, 0, v___x_8491_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8506_, 1, v___x_8492_);
                        v___x_8494_ = v_reuseFailAlloc_8506_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_8488_);
                    v___x_8507_ = l_Lean_Elab_Structural_allCombinations___redArg(v_fst_8484_);
                    leanh::lean_dec(v_fst_8484_);
                    if leanh::lean_obj_tag(v___x_8507_) == 1 {
                        leanh::lean_del_object(v___x_8482_);
                        v_val_8508_ = leanh::lean_ctor_get(v___x_8507_, 0);
                        leanh::lean_inc(v_val_8508_);
                        leanh::lean_dec_ref_known(v___x_8507_, 1);
                        v_sz_8509_ = lean_array_size(v_val_8508_);
                        leanh::lean_inc(v_a_8471_);
                        v___x_8510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_8471_, v_val_8508_, v_sz_8509_, v___x_8476_, v_snd_8480_);
                        leanh::lean_dec(v_val_8508_);
                        if leanh::lean_obj_tag(v___x_8510_) == 0 {
                            v_a_8511_ = leanh::lean_ctor_get(v___x_8510_, 0);
                            leanh::lean_inc(v_a_8511_);
                            leanh::lean_dec_ref_known(v___x_8510_, 1);
                            if v_isShared_8487_ == 0 {
                                leanh::lean_ctor_set(v___x_8486_, 1, v_a_8511_);
                                leanh::lean_ctor_set(v___x_8486_, 0, v_fst_8479_);
                                v___x_8513_ = v___x_8486_;
                                state = 6;
                                continue;
                            } else {
                                v_reuseFailAlloc_8514_ =
                                    leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_8514_, 0, v_fst_8479_);
                                leanh::lean_ctor_set(v_reuseFailAlloc_8514_, 1, v_a_8511_);
                                v___x_8513_ = v_reuseFailAlloc_8514_;
                                state = 6;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_8486_);
                            leanh::lean_dec(v_fst_8479_);
                            leanh::lean_dec_ref(v___x_8450_);
                            leanh::lean_dec_ref(v_xs_8449_);
                            v_a_8515_ = leanh::lean_ctor_get(v___x_8510_, 0);
                            v_isSharedCheck_8522_ =
                                (!leanh::lean_is_exclusive(v___x_8510_)) as u8;
                            if v_isSharedCheck_8522_ == 0 {
                                v___x_8517_ = v___x_8510_;
                                v_isShared_8518_ = v_isSharedCheck_8522_;
                                state = 7;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8515_);
                                leanh::lean_dec(v___x_8510_);
                                v___x_8517_ = leanh::lean_box(0);
                                v_isShared_8518_ = v_isSharedCheck_8522_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v___x_8507_);
                        v___x_8523_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__8);
                        leanh::lean_inc(v_a_8471_);
                        v___x_8524_ = l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_a_8471_);
                        if v_isShared_8483_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_8482_, 7);
                            leanh::lean_ctor_set(v___x_8482_, 1, v___x_8524_);
                            leanh::lean_ctor_set(v___x_8482_, 0, v___x_8523_);
                            v___x_8526_ = v___x_8482_;
                            state = 9;
                            continue;
                        } else {
                            v_reuseFailAlloc_8535_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8535_, 0, v___x_8523_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_8535_, 1, v___x_8524_);
                            v___x_8526_ = v_reuseFailAlloc_8535_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_8495_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__4);
                v___x_8496_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8496_, 0, v___x_8494_);
                leanh::lean_ctor_set(v___x_8496_, 1, v___x_8495_);
                v___x_8497_ = lean_array_get_borrowed(v___x_8490_, v_fnNames_8452_, v_val_8489_);
                leanh::lean_dec(v_val_8489_);
                leanh::lean_inc(v___x_8497_);
                v___x_8498_ = l_Lean_MessageData_ofName(v___x_8497_);
                v___x_8499_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8499_, 0, v___x_8496_);
                leanh::lean_ctor_set(v___x_8499_, 1, v___x_8498_);
                v___x_8500_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__6);
                v___x_8501_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8501_, 0, v___x_8499_);
                leanh::lean_ctor_set(v___x_8501_, 1, v___x_8500_);
                v___x_8502_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8502_, 0, v_fst_8479_);
                leanh::lean_ctor_set(v___x_8502_, 1, v___x_8501_);
                if v_isShared_8487_ == 0 {
                    leanh::lean_ctor_set(v___x_8486_, 1, v_snd_8480_);
                    leanh::lean_ctor_set(v___x_8486_, 0, v___x_8502_);
                    v___x_8504_ = v___x_8486_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8505_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8505_, 0, v___x_8502_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8505_, 1, v_snd_8480_);
                    v___x_8504_ = v_reuseFailAlloc_8505_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v_a_8463_ = v___x_8504_;
                state = 1;
                continue;
            }
            6 => {
                v_a_8463_ = v___x_8513_;
                state = 1;
                continue;
            }
            7 => {
                if v_isShared_8518_ == 0 {
                    v___x_8520_ = v___x_8517_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8521_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8521_, 0, v_a_8515_);
                    v___x_8520_ = v_reuseFailAlloc_8521_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8520_;
            }
            9 => {
                v___x_8527_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__10);
                v___x_8528_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8528_, 0, v___x_8526_);
                leanh::lean_ctor_set(v___x_8528_, 1, v___x_8527_);
                v___x_8529_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8529_, 0, v_fst_8479_);
                leanh::lean_ctor_set(v___x_8529_, 1, v___x_8528_);
                v___x_8530_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__12);
                v___x_8531_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8531_, 0, v___x_8529_);
                leanh::lean_ctor_set(v___x_8531_, 1, v___x_8530_);
                if v_isShared_8487_ == 0 {
                    leanh::lean_ctor_set(v___x_8486_, 1, v_snd_8480_);
                    leanh::lean_ctor_set(v___x_8486_, 0, v___x_8531_);
                    v___x_8533_ = v___x_8486_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8534_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8534_, 0, v___x_8531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8534_, 1, v_snd_8480_);
                    v___x_8533_ = v_reuseFailAlloc_8534_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                v_a_8463_ = v___x_8533_;
                state = 1;
                continue;
            }
            11 => {
                if v_isShared_8542_ == 0 {
                    v___x_8544_ = v___x_8541_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_8545_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8545_, 0, v_a_8539_);
                    v___x_8544_ = v_reuseFailAlloc_8545_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_8544_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5___boxed(
    mut v_xs_8547_: *mut leanh::LeanObject,
    mut v___x_8548_: *mut leanh::LeanObject,
    mut v_values_8549_: *mut leanh::LeanObject,
    mut v_fnNames_8550_: *mut leanh::LeanObject,
    mut v_as_8551_: *mut leanh::LeanObject,
    mut v_sz_8552_: *mut leanh::LeanObject,
    mut v_i_8553_: *mut leanh::LeanObject,
    mut v_b_8554_: *mut leanh::LeanObject,
    mut v___y_8555_: *mut leanh::LeanObject,
    mut v___y_8556_: *mut leanh::LeanObject,
    mut v___y_8557_: *mut leanh::LeanObject,
    mut v___y_8558_: *mut leanh::LeanObject,
    mut v___y_8559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8560_: usize = 0;
    let mut v_i_boxed_8561_: usize = 0;
    let mut v_res_8562_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8560_ = leanh::lean_unbox_usize(v_sz_8552_);
    leanh::lean_dec(v_sz_8552_);
    v_i_boxed_8561_ = leanh::lean_unbox_usize(v_i_8553_);
    leanh::lean_dec(v_i_8553_);
    v_res_8562_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_8547_, v___x_8548_, v_values_8549_, v_fnNames_8550_, v_as_8551_, v_sz_boxed_8560_, v_i_boxed_8561_, v_b_8554_, v___y_8555_, v___y_8556_, v___y_8557_, v___y_8558_);
    leanh::lean_dec(v___y_8558_);
    leanh::lean_dec_ref(v___y_8557_);
    leanh::lean_dec(v___y_8556_);
    leanh::lean_dec_ref(v___y_8555_);
    leanh::lean_dec_ref(v_as_8551_);
    leanh::lean_dec_ref(v_fnNames_8550_);
    leanh::lean_dec_ref(v_values_8549_);
    return v_res_8562_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_8566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8567_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8566_ = l_Lean_Elab_Structural_findRecArgCandidates___closed__1;
    v___x_8567_ = l_Lean_MessageData_ofFormat(v___x_8566_);
    return v___x_8567_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_8569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8570_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8569_ = l_Lean_Elab_Structural_findRecArgCandidates___closed__3;
    v___x_8570_ = l_Lean_stringToMessageData(v___x_8569_);
    return v___x_8570_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_8574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8574_ = l_Lean_Elab_Structural_findRecArgCandidates___closed__6;
    v___x_8575_ = l_Lean_stringToMessageData(v___x_8574_);
    return v___x_8575_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8()
-> *mut leanh::LeanObject {
    let mut v___x_8576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8577_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8576_ = leanh::lean_box(1);
    v___x_8577_ = l_Lean_MessageData_ofFormat(v___x_8576_);
    return v___x_8577_;
}
pub unsafe fn l_Lean_Elab_Structural_findRecArgCandidates(
    mut v_fnNames_8578_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_8579_: *mut leanh::LeanObject,
    mut v_xs_8580_: *mut leanh::LeanObject,
    mut v_values_8581_: *mut leanh::LeanObject,
    mut v_termMeasure_x3fs_8582_: *mut leanh::LeanObject,
    mut v_a_8583_: *mut leanh::LeanObject,
    mut v_a_8584_: *mut leanh::LeanObject,
    mut v_a_8585_: *mut leanh::LeanObject,
    mut v_a_8586_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_recArgInfoss_8589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_perms_8591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_report_8594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8596_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8602_: usize = 0;
    let mut v___x_8603_: usize = 0;
    let mut v___x_8604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_8608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8611_: u8 = 0;
    let mut v_fst_8612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8615_: u8 = 0;
    let mut v_inheritedTraceOptions_8616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_8617_: u8 = 0;
    let mut v_sz_8618_: usize = 0;
    let mut v___x_8619_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_report_8622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8623_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8629_: usize = 0;
    let mut v___x_8630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8634_: u8 = 0;
    let mut v_fst_8635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8639_: u8 = 0;
    let mut v___x_8641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8646_: u8 = 0;
    let mut v_isSharedCheck_8647_: u8 = 0;
    let mut v_a_8648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8651_: u8 = 0;
    let mut v___x_8653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8655_: u8 = 0;
    let mut v_reuseFailAlloc_8656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8664_: u8 = 0;
    let mut v___x_8665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_8677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_8678_: u8 = 0;
    let mut v_a_8679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_8681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8683_: u8 = 0;
    let mut v___x_8684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8694_: u8 = 0;
    let mut v___x_8696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8698_: u8 = 0;
    let mut v_a_8699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8702_: u8 = 0;
    let mut v___x_8704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8706_: u8 = 0;
    let mut v___y_8708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8714_: u8 = 0;
    let mut v___x_8715_: u8 = 0;
    let mut v___x_8716_: usize = 0;
    let mut v___x_8717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8718_: usize = 0;
    let mut v___x_8719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8721_: u8 = 0;
    let mut v___x_8722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8736_: u8 = 0;
    let mut v___x_8738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8740_: u8 = 0;
    let mut v___x_8741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8743_: u8 = 0;
    let mut v___x_8744_: u8 = 0;
    let mut v___x_8745_: usize = 0;
    let mut v___x_8746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8747_: usize = 0;
    let mut v___x_8748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8749_: u8 = 0;
    let mut v_unused_8750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8751_: u8 = 0;
    let mut v_unused_8752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8756_: u8 = 0;
    let mut v___x_8758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8760_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8588_ = leanh::lean_unsigned_to_nat(0);
                v_recArgInfoss_8589_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5_spec__5___closed__0;
                v___x_8590_ = lean_array_get_size(v_values_8581_);
                v_perms_8591_ = leanh::lean_ctor_get(v_fixedParamPerms_8579_, 1);
                leanh::lean_inc_ref(v_perms_8591_);
                leanh::lean_dec_ref(v_fixedParamPerms_8579_);
                leanh::lean_inc_ref(v_values_8581_);
                v___x_8592_ = l_Array_toSubarray___redArg(v_values_8581_, v___x_8588_, v___x_8590_);
                v___x_8593_ = lean_array_get_size(v_termMeasure_x3fs_8582_);
                v_report_8594_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3_once
                    ),
                    _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__3,
                );
                v___x_8595_ =
                    l_Array_toSubarray___redArg(v_termMeasure_x3fs_8582_, v___x_8588_, v___x_8593_);
                v___x_8596_ = lean_array_get_size(v_perms_8591_);
                v___x_8597_ = l_Array_toSubarray___redArg(v_perms_8591_, v___x_8588_, v___x_8596_);
                v___x_8598_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8598_, 0, v___x_8595_);
                leanh::lean_ctor_set(v___x_8598_, 1, v___x_8597_);
                v___x_8599_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8599_, 0, v___x_8592_);
                leanh::lean_ctor_set(v___x_8599_, 1, v___x_8598_);
                v___x_8600_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8600_, 0, v_recArgInfoss_8589_);
                leanh::lean_ctor_set(v___x_8600_, 1, v___x_8599_);
                v___x_8601_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8601_, 0, v_report_8594_);
                leanh::lean_ctor_set(v___x_8601_, 1, v___x_8600_);
                v_sz_8602_ = lean_array_size(v_fnNames_8578_);
                v___x_8603_ = 0usize;
                leanh::lean_inc_ref(v_xs_8580_);
                v___x_8604_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__0(v_xs_8580_, v_fnNames_8578_, v_sz_8602_, v___x_8603_, v___x_8601_, v_a_8583_, v_a_8584_, v_a_8585_, v_a_8586_);
                if leanh::lean_obj_tag(v___x_8604_) == 0 {
                    v_a_8605_ = leanh::lean_ctor_get(v___x_8604_, 0);
                    leanh::lean_inc(v_a_8605_);
                    leanh::lean_dec_ref_known(v___x_8604_, 1);
                    v_snd_8606_ = leanh::lean_ctor_get(v_a_8605_, 1);
                    leanh::lean_inc(v_snd_8606_);
                    v_options_8607_ = leanh::lean_ctor_get(v_a_8585_, 2);
                    v_fst_8608_ = leanh::lean_ctor_get(v_a_8605_, 0);
                    v_isSharedCheck_8751_ = (!leanh::lean_is_exclusive(v_a_8605_)) as u8;
                    if v_isSharedCheck_8751_ == 0 {
                        v_unused_8752_ = leanh::lean_ctor_get(v_a_8605_, 1);
                        leanh::lean_dec(v_unused_8752_);
                        v___x_8610_ = v_a_8605_;
                        v_isShared_8611_ = v_isSharedCheck_8751_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_fst_8608_);
                        leanh::lean_dec(v_a_8605_);
                        v___x_8610_ = leanh::lean_box(0);
                        v_isShared_8611_ = v_isSharedCheck_8751_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_values_8581_);
                    leanh::lean_dec_ref(v_xs_8580_);
                    v_a_8753_ = leanh::lean_ctor_get(v___x_8604_, 0);
                    v_isSharedCheck_8760_ = (!leanh::lean_is_exclusive(v___x_8604_)) as u8;
                    if v_isSharedCheck_8760_ == 0 {
                        v___x_8755_ = v___x_8604_;
                        v_isShared_8756_ = v_isSharedCheck_8760_;
                        state = 22;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8753_);
                        leanh::lean_dec(v___x_8604_);
                        v___x_8755_ = leanh::lean_box(0);
                        v_isShared_8756_ = v_isSharedCheck_8760_;
                        state = 22;
                        continue;
                    }
                }
            }
            1 => {
                v_fst_8612_ = leanh::lean_ctor_get(v_snd_8606_, 0);
                v_isSharedCheck_8749_ = (!leanh::lean_is_exclusive(v_snd_8606_)) as u8;
                if v_isSharedCheck_8749_ == 0 {
                    v_unused_8750_ = leanh::lean_ctor_get(v_snd_8606_, 1);
                    leanh::lean_dec(v_unused_8750_);
                    v___x_8614_ = v_snd_8606_;
                    v_isShared_8615_ = v_isSharedCheck_8749_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_fst_8612_);
                    leanh::lean_dec(v_snd_8606_);
                    v___x_8614_ = leanh::lean_box(0);
                    v_isShared_8615_ = v_isSharedCheck_8749_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_inheritedTraceOptions_8616_ = leanh::lean_ctor_get(v_a_8585_, 13);
                v_hasTrace_8617_ = leanh::lean_ctor_get_uint8(
                    v_options_8607_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_sz_8618_ = lean_array_size(v_fst_8612_);
                v___x_8619_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Structural_findRecArgCandidates_spec__1(v_sz_8618_, v___x_8603_, v_fst_8612_);
                v___x_8669_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9;
                if v_hasTrace_8617_ == 0 {
                    v___y_8708_ = v_a_8583_;
                    v___y_8709_ = v_a_8584_;
                    v___y_8710_ = v_a_8585_;
                    v___y_8711_ = v_a_8586_;
                    state = 18;
                    continue;
                } else {
                    v___x_8720_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12,
                    );
                    v___x_8721_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_8616_,
                        v_options_8607_,
                        v___x_8720_,
                    );
                    if v___x_8721_ == 0 {
                        v___y_8708_ = v_a_8583_;
                        v___y_8709_ = v_a_8584_;
                        v___y_8710_ = v_a_8585_;
                        v___y_8711_ = v_a_8586_;
                        state = 18;
                        continue;
                    } else {
                        v___x_8722_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_findRecArgCandidates___closed__7
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_findRecArgCandidates___closed__7_once
                            ),
                            _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__7,
                        );
                        v___x_8741_ = l_Lean_Elab_Structural_findRecArgCandidates___closed__5;
                        v___x_8742_ = lean_array_get_size(v___x_8619_);
                        v___x_8743_ = lean_nat_dec_lt(v___x_8588_, v___x_8742_);
                        if v___x_8743_ == 0 {
                            v___y_8724_ = v___x_8741_;
                            state = 19;
                            continue;
                        } else {
                            v___x_8744_ = lean_nat_dec_le(v___x_8742_, v___x_8742_);
                            if v___x_8744_ == 0 {
                                if v___x_8743_ == 0 {
                                    v___y_8724_ = v___x_8741_;
                                    state = 19;
                                    continue;
                                } else {
                                    v___x_8745_ = lean_usize_of_nat(v___x_8742_);
                                    v___x_8746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_8619_, v___x_8603_, v___x_8745_, v___x_8741_);
                                    v___y_8724_ = v___x_8746_;
                                    state = 19;
                                    continue;
                                }
                            } else {
                                v___x_8747_ = lean_usize_of_nat(v___x_8742_);
                                v___x_8748_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_8619_, v___x_8603_, v___x_8747_, v___x_8741_);
                                v___y_8724_ = v___x_8748_;
                                state = 19;
                                continue;
                            }
                        }
                    }
                }
            }
            3 => {
                if v_isShared_8615_ == 0 {
                    leanh::lean_ctor_set(v___x_8614_, 1, v_recArgInfoss_8589_);
                    leanh::lean_ctor_set(v___x_8614_, 0, v_report_8622_);
                    v___x_8628_ = v___x_8614_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8656_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8656_, 0, v_report_8622_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8656_, 1, v_recArgInfoss_8589_);
                    v___x_8628_ = v_reuseFailAlloc_8656_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_sz_8629_ = lean_array_size(v___y_8621_);
                v___x_8630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__5(v_xs_8580_, v___x_8619_, v_values_8581_, v_fnNames_8578_, v___y_8621_, v_sz_8629_, v___x_8603_, v___x_8628_, v___y_8623_, v___y_8624_, v___y_8625_, v___y_8626_);
                leanh::lean_dec_ref(v___y_8621_);
                leanh::lean_dec_ref(v_values_8581_);
                if leanh::lean_obj_tag(v___x_8630_) == 0 {
                    v_a_8631_ = leanh::lean_ctor_get(v___x_8630_, 0);
                    v_isSharedCheck_8647_ = (!leanh::lean_is_exclusive(v___x_8630_)) as u8;
                    if v_isSharedCheck_8647_ == 0 {
                        v___x_8633_ = v___x_8630_;
                        v_isShared_8634_ = v_isSharedCheck_8647_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8631_);
                        leanh::lean_dec(v___x_8630_);
                        v___x_8633_ = leanh::lean_box(0);
                        v_isShared_8634_ = v_isSharedCheck_8647_;
                        state = 5;
                        continue;
                    }
                } else {
                    v_a_8648_ = leanh::lean_ctor_get(v___x_8630_, 0);
                    v_isSharedCheck_8655_ = (!leanh::lean_is_exclusive(v___x_8630_)) as u8;
                    if v_isSharedCheck_8655_ == 0 {
                        v___x_8650_ = v___x_8630_;
                        v_isShared_8651_ = v_isSharedCheck_8655_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8648_);
                        leanh::lean_dec(v___x_8630_);
                        v___x_8650_ = leanh::lean_box(0);
                        v_isShared_8651_ = v_isSharedCheck_8655_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                v_fst_8635_ = leanh::lean_ctor_get(v_a_8631_, 0);
                v_snd_8636_ = leanh::lean_ctor_get(v_a_8631_, 1);
                v_isSharedCheck_8646_ = (!leanh::lean_is_exclusive(v_a_8631_)) as u8;
                if v_isSharedCheck_8646_ == 0 {
                    v___x_8638_ = v_a_8631_;
                    v_isShared_8639_ = v_isSharedCheck_8646_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_8636_);
                    leanh::lean_inc(v_fst_8635_);
                    leanh::lean_dec(v_a_8631_);
                    v___x_8638_ = leanh::lean_box(0);
                    v_isShared_8639_ = v_isSharedCheck_8646_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_8639_ == 0 {
                    leanh::lean_ctor_set(v___x_8638_, 1, v_fst_8635_);
                    leanh::lean_ctor_set(v___x_8638_, 0, v_snd_8636_);
                    v___x_8641_ = v___x_8638_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8645_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8645_, 0, v_snd_8636_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8645_, 1, v_fst_8635_);
                    v___x_8641_ = v_reuseFailAlloc_8645_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_8634_ == 0 {
                    leanh::lean_ctor_set(v___x_8633_, 0, v___x_8641_);
                    v___x_8643_ = v___x_8633_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_8644_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8644_, 0, v___x_8641_);
                    v___x_8643_ = v_reuseFailAlloc_8644_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_8643_;
            }
            9 => {
                if v_isShared_8651_ == 0 {
                    v___x_8653_ = v___x_8650_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_8654_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8654_, 0, v_a_8648_);
                    v___x_8653_ = v_reuseFailAlloc_8654_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_8653_;
            }
            11 => {
                v___x_8663_ = lean_array_get_size(v___y_8658_);
                v___x_8664_ = lean_nat_dec_eq(v___x_8663_, v___x_8588_);
                if v___x_8664_ == 0 {
                    leanh::lean_del_object(v___x_8610_);
                    v___y_8621_ = v___y_8658_;
                    v_report_8622_ = v_fst_8608_;
                    v___y_8623_ = v___y_8659_;
                    v___y_8624_ = v___y_8660_;
                    v___y_8625_ = v___y_8661_;
                    v___y_8626_ = v___y_8662_;
                    state = 3;
                    continue;
                } else {
                    v___x_8665_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_findRecArgCandidates___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_findRecArgCandidates___closed__2_once
                        ),
                        _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__2,
                    );
                    if v_isShared_8611_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_8610_, 7);
                        leanh::lean_ctor_set(v___x_8610_, 1, v___x_8665_);
                        v___x_8667_ = v___x_8610_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_8668_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8668_, 0, v_fst_8608_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8668_, 1, v___x_8665_);
                        v___x_8667_ = v_reuseFailAlloc_8668_;
                        state = 12;
                        continue;
                    }
                }
            }
            12 => {
                v___y_8621_ = v___y_8658_;
                v_report_8622_ = v___x_8667_;
                v___y_8623_ = v___y_8659_;
                v___y_8624_ = v___y_8660_;
                v___y_8625_ = v___y_8661_;
                v___y_8626_ = v___y_8662_;
                state = 3;
                continue;
            }
            13 => {
                v___x_8676_ = l_Lean_Elab_Structural_inductiveGroups(
                    v___y_8675_,
                    v___y_8674_,
                    v___y_8672_,
                    v___y_8673_,
                    v___y_8671_,
                );
                if leanh::lean_obj_tag(v___x_8676_) == 0 {
                    v_options_8677_ = leanh::lean_ctor_get(v___y_8673_, 2);
                    v_hasTrace_8678_ = leanh::lean_ctor_get_uint8(
                        v_options_8677_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    if v_hasTrace_8678_ == 0 {
                        v_a_8679_ = leanh::lean_ctor_get(v___x_8676_, 0);
                        leanh::lean_inc(v_a_8679_);
                        leanh::lean_dec_ref_known(v___x_8676_, 1);
                        v___y_8658_ = v_a_8679_;
                        v___y_8659_ = v___y_8674_;
                        v___y_8660_ = v___y_8672_;
                        v___y_8661_ = v___y_8673_;
                        v___y_8662_ = v___y_8671_;
                        state = 11;
                        continue;
                    } else {
                        v_a_8680_ = leanh::lean_ctor_get(v___x_8676_, 0);
                        leanh::lean_inc(v_a_8680_);
                        leanh::lean_dec_ref_known(v___x_8676_, 1);
                        v_inheritedTraceOptions_8681_ =
                            leanh::lean_ctor_get(v___y_8673_, 13);
                        v___x_8682_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once
                            ),
                            _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12,
                        );
                        v___x_8683_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_8681_,
                            v_options_8677_,
                            v___x_8682_,
                        );
                        if v___x_8683_ == 0 {
                            v___y_8658_ = v_a_8680_;
                            v___y_8659_ = v___y_8674_;
                            v___y_8660_ = v___y_8672_;
                            v___y_8661_ = v___y_8673_;
                            v___y_8662_ = v___y_8671_;
                            state = 11;
                            continue;
                        } else {
                            v___x_8684_ = leanh::lean_obj_once(
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_findRecArgCandidates___closed__4
                                ),
                                core::ptr::addr_of_mut!(
                                    l_Lean_Elab_Structural_findRecArgCandidates___closed__4_once
                                ),
                                _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__4,
                            );
                            leanh::lean_inc(v_a_8680_);
                            v___x_8685_ = lean_array_to_list(v_a_8680_);
                            v___x_8686_ = leanh::lean_box(0);
                            v___x_8687_ = l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__6(v___x_8685_, v___x_8686_);
                            v___x_8688_ = l_Lean_MessageData_ofList(v___x_8687_);
                            v___x_8689_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v___x_8689_, 0, v___x_8684_);
                            leanh::lean_ctor_set(v___x_8689_, 1, v___x_8688_);
                            v___x_8690_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(v___x_8669_, v___x_8689_, v___y_8674_, v___y_8672_, v___y_8673_, v___y_8671_);
                            if leanh::lean_obj_tag(v___x_8690_) == 0 {
                                leanh::lean_dec_ref_known(v___x_8690_, 1);
                                v___y_8658_ = v_a_8680_;
                                v___y_8659_ = v___y_8674_;
                                v___y_8660_ = v___y_8672_;
                                v___y_8661_ = v___y_8673_;
                                v___y_8662_ = v___y_8671_;
                                state = 11;
                                continue;
                            } else {
                                leanh::lean_dec(v_a_8680_);
                                leanh::lean_dec_ref(v___x_8619_);
                                leanh::lean_del_object(v___x_8614_);
                                leanh::lean_del_object(v___x_8610_);
                                leanh::lean_dec(v_fst_8608_);
                                leanh::lean_dec_ref(v_values_8581_);
                                leanh::lean_dec_ref(v_xs_8580_);
                                v_a_8691_ = leanh::lean_ctor_get(v___x_8690_, 0);
                                v_isSharedCheck_8698_ =
                                    (!leanh::lean_is_exclusive(v___x_8690_)) as u8;
                                if v_isSharedCheck_8698_ == 0 {
                                    v___x_8693_ = v___x_8690_;
                                    v_isShared_8694_ = v_isSharedCheck_8698_;
                                    state = 14;
                                    continue;
                                } else {
                                    leanh::lean_inc(v_a_8691_);
                                    leanh::lean_dec(v___x_8690_);
                                    v___x_8693_ = leanh::lean_box(0);
                                    v_isShared_8694_ = v_isSharedCheck_8698_;
                                    state = 14;
                                    continue;
                                }
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___x_8619_);
                    leanh::lean_del_object(v___x_8614_);
                    leanh::lean_del_object(v___x_8610_);
                    leanh::lean_dec(v_fst_8608_);
                    leanh::lean_dec_ref(v_values_8581_);
                    leanh::lean_dec_ref(v_xs_8580_);
                    v_a_8699_ = leanh::lean_ctor_get(v___x_8676_, 0);
                    v_isSharedCheck_8706_ = (!leanh::lean_is_exclusive(v___x_8676_)) as u8;
                    if v_isSharedCheck_8706_ == 0 {
                        v___x_8701_ = v___x_8676_;
                        v_isShared_8702_ = v_isSharedCheck_8706_;
                        state = 16;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8699_);
                        leanh::lean_dec(v___x_8676_);
                        v___x_8701_ = leanh::lean_box(0);
                        v_isShared_8702_ = v_isSharedCheck_8706_;
                        state = 16;
                        continue;
                    }
                }
            }
            14 => {
                if v_isShared_8694_ == 0 {
                    v___x_8696_ = v___x_8693_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_8697_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8697_, 0, v_a_8691_);
                    v___x_8696_ = v_reuseFailAlloc_8697_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_8696_;
            }
            16 => {
                if v_isShared_8702_ == 0 {
                    v___x_8704_ = v___x_8701_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_8705_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8705_, 0, v_a_8699_);
                    v___x_8704_ = v_reuseFailAlloc_8705_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_8704_;
            }
            18 => {
                v___x_8712_ = l_Lean_Elab_Structural_findRecArgCandidates___closed__5;
                v___x_8713_ = lean_array_get_size(v___x_8619_);
                v___x_8714_ = lean_nat_dec_lt(v___x_8588_, v___x_8713_);
                if v___x_8714_ == 0 {
                    v___y_8671_ = v___y_8711_;
                    v___y_8672_ = v___y_8709_;
                    v___y_8673_ = v___y_8710_;
                    v___y_8674_ = v___y_8708_;
                    v___y_8675_ = v___x_8712_;
                    state = 13;
                    continue;
                } else {
                    v___x_8715_ = lean_nat_dec_le(v___x_8713_, v___x_8713_);
                    if v___x_8715_ == 0 {
                        if v___x_8714_ == 0 {
                            v___y_8671_ = v___y_8711_;
                            v___y_8672_ = v___y_8709_;
                            v___y_8673_ = v___y_8710_;
                            v___y_8674_ = v___y_8708_;
                            v___y_8675_ = v___x_8712_;
                            state = 13;
                            continue;
                        } else {
                            v___x_8716_ = lean_usize_of_nat(v___x_8713_);
                            v___x_8717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_8619_, v___x_8603_, v___x_8716_, v___x_8712_);
                            v___y_8671_ = v___y_8711_;
                            v___y_8672_ = v___y_8709_;
                            v___y_8673_ = v___y_8710_;
                            v___y_8674_ = v___y_8708_;
                            v___y_8675_ = v___x_8717_;
                            state = 13;
                            continue;
                        }
                    } else {
                        v___x_8718_ = lean_usize_of_nat(v___x_8713_);
                        v___x_8719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Structural_findRecArgCandidates_spec__7(v___x_8619_, v___x_8603_, v___x_8718_, v___x_8712_);
                        v___y_8671_ = v___y_8711_;
                        v___y_8672_ = v___y_8709_;
                        v___y_8673_ = v___y_8710_;
                        v___y_8674_ = v___y_8708_;
                        v___y_8675_ = v___x_8719_;
                        state = 13;
                        continue;
                    }
                }
            }
            19 => {
                v___x_8725_ = lean_array_to_list(v___y_8724_);
                v___x_8726_ = leanh::lean_box(0);
                v___x_8727_ =
                    l_List_mapTR_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__8(
                        v___x_8725_,
                        v___x_8726_,
                    );
                v___x_8728_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_findRecArgCandidates___closed__8
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_findRecArgCandidates___closed__8_once
                    ),
                    _init_l_Lean_Elab_Structural_findRecArgCandidates___closed__8,
                );
                v___x_8729_ = l_Lean_MessageData_joinSep(v___x_8727_, v___x_8728_);
                v___x_8730_ = l_Lean_indentD(v___x_8729_);
                v___x_8731_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_8731_, 0, v___x_8722_);
                leanh::lean_ctor_set(v___x_8731_, 1, v___x_8730_);
                v___x_8732_ = l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(
                    v___x_8669_,
                    v___x_8731_,
                    v_a_8583_,
                    v_a_8584_,
                    v_a_8585_,
                    v_a_8586_,
                );
                if leanh::lean_obj_tag(v___x_8732_) == 0 {
                    leanh::lean_dec_ref_known(v___x_8732_, 1);
                    v___y_8708_ = v_a_8583_;
                    v___y_8709_ = v_a_8584_;
                    v___y_8710_ = v_a_8585_;
                    v___y_8711_ = v_a_8586_;
                    state = 18;
                    continue;
                } else {
                    leanh::lean_dec_ref(v___x_8619_);
                    leanh::lean_del_object(v___x_8614_);
                    leanh::lean_del_object(v___x_8610_);
                    leanh::lean_dec(v_fst_8608_);
                    leanh::lean_dec_ref(v_values_8581_);
                    leanh::lean_dec_ref(v_xs_8580_);
                    v_a_8733_ = leanh::lean_ctor_get(v___x_8732_, 0);
                    v_isSharedCheck_8740_ = (!leanh::lean_is_exclusive(v___x_8732_)) as u8;
                    if v_isSharedCheck_8740_ == 0 {
                        v___x_8735_ = v___x_8732_;
                        v_isShared_8736_ = v_isSharedCheck_8740_;
                        state = 20;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8733_);
                        leanh::lean_dec(v___x_8732_);
                        v___x_8735_ = leanh::lean_box(0);
                        v_isShared_8736_ = v_isSharedCheck_8740_;
                        state = 20;
                        continue;
                    }
                }
            }
            20 => {
                if v_isShared_8736_ == 0 {
                    v___x_8738_ = v___x_8735_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_8739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8739_, 0, v_a_8733_);
                    v___x_8738_ = v_reuseFailAlloc_8739_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_8738_;
            }
            22 => {
                if v_isShared_8756_ == 0 {
                    v___x_8758_ = v___x_8755_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_8759_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8759_, 0, v_a_8753_);
                    v___x_8758_ = v_reuseFailAlloc_8759_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_8758_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_findRecArgCandidates___boxed(
    mut v_fnNames_8761_: *mut leanh::LeanObject,
    mut v_fixedParamPerms_8762_: *mut leanh::LeanObject,
    mut v_xs_8763_: *mut leanh::LeanObject,
    mut v_values_8764_: *mut leanh::LeanObject,
    mut v_termMeasure_x3fs_8765_: *mut leanh::LeanObject,
    mut v_a_8766_: *mut leanh::LeanObject,
    mut v_a_8767_: *mut leanh::LeanObject,
    mut v_a_8768_: *mut leanh::LeanObject,
    mut v_a_8769_: *mut leanh::LeanObject,
    mut v_a_8770_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8771_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8771_ = l_Lean_Elab_Structural_findRecArgCandidates(
        v_fnNames_8761_,
        v_fixedParamPerms_8762_,
        v_xs_8763_,
        v_values_8764_,
        v_termMeasure_x3fs_8765_,
        v_a_8766_,
        v_a_8767_,
        v_a_8768_,
        v_a_8769_,
    );
    leanh::lean_dec(v_a_8769_);
    leanh::lean_dec_ref(v_a_8768_);
    leanh::lean_dec(v_a_8767_);
    leanh::lean_dec_ref(v_a_8766_);
    leanh::lean_dec_ref(v_fnNames_8761_);
    return v_res_8771_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(
    mut v_a_8772_: *mut leanh::LeanObject,
    mut v_as_8773_: *mut leanh::LeanObject,
    mut v_sz_8774_: usize,
    mut v_i_8775_: usize,
    mut v_b_8776_: *mut leanh::LeanObject,
    mut v___y_8777_: *mut leanh::LeanObject,
    mut v___y_8778_: *mut leanh::LeanObject,
    mut v___y_8779_: *mut leanh::LeanObject,
    mut v___y_8780_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___redArg(v_a_8772_, v_as_8773_, v_sz_8774_, v_i_8775_, v_b_8776_);
    return v___x_8782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4___boxed(
    mut v_a_8783_: *mut leanh::LeanObject,
    mut v_as_8784_: *mut leanh::LeanObject,
    mut v_sz_8785_: *mut leanh::LeanObject,
    mut v_i_8786_: *mut leanh::LeanObject,
    mut v_b_8787_: *mut leanh::LeanObject,
    mut v___y_8788_: *mut leanh::LeanObject,
    mut v___y_8789_: *mut leanh::LeanObject,
    mut v___y_8790_: *mut leanh::LeanObject,
    mut v___y_8791_: *mut leanh::LeanObject,
    mut v___y_8792_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_8793_: usize = 0;
    let mut v_i_boxed_8794_: usize = 0;
    let mut v_res_8795_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_8793_ = leanh::lean_unbox_usize(v_sz_8785_);
    leanh::lean_dec(v_sz_8785_);
    v_i_boxed_8794_ = leanh::lean_unbox_usize(v_i_8786_);
    leanh::lean_dec(v_i_8786_);
    v_res_8795_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_findRecArgCandidates_spec__4(v_a_8783_, v_as_8784_, v_sz_boxed_8793_, v_i_boxed_8794_, v_b_8787_, v___y_8788_, v___y_8789_, v___y_8790_, v___y_8791_);
    leanh::lean_dec(v___y_8791_);
    leanh::lean_dec_ref(v___y_8790_);
    leanh::lean_dec(v___y_8789_);
    leanh::lean_dec_ref(v___y_8788_);
    leanh::lean_dec_ref(v_as_8784_);
    return v_res_8795_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(
    mut v_constName_8796_: *mut leanh::LeanObject,
    mut v_skipRealize_8797_: u8,
    mut v___y_8798_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_8801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8802_: u8 = 0;
    let mut v___x_8803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8804_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8800_ = lean_st_ref_get(v___y_8798_);
    v_env_8801_ = leanh::lean_ctor_get(v___x_8800_, 0);
    leanh::lean_inc_ref(v_env_8801_);
    leanh::lean_dec(v___x_8800_);
    v___x_8802_ = l_Lean_Environment_contains(v_env_8801_, v_constName_8796_, v_skipRealize_8797_);
    v___x_8803_ = leanh::lean_box((v___x_8802_) as usize);
    v___x_8804_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_8804_, 0, v___x_8803_);
    return v___x_8804_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg___boxed(
    mut v_constName_8805_: *mut leanh::LeanObject,
    mut v_skipRealize_8806_: *mut leanh::LeanObject,
    mut v___y_8807_: *mut leanh::LeanObject,
    mut v___y_8808_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_8809_: u8 = 0;
    let mut v_res_8810_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_8809_ = (leanh::lean_unbox(v_skipRealize_8806_) as u8);
    v_res_8810_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(
        v_constName_8805_,
        v_skipRealize_boxed_8809_,
        v___y_8807_,
    );
    leanh::lean_dec(v___y_8807_);
    return v_res_8810_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(
    mut v_constName_8811_: *mut leanh::LeanObject,
    mut v_skipRealize_8812_: u8,
    mut v___y_8813_: *mut leanh::LeanObject,
    mut v___y_8814_: *mut leanh::LeanObject,
    mut v___y_8815_: *mut leanh::LeanObject,
    mut v___y_8816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8818_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8818_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(
        v_constName_8811_,
        v_skipRealize_8812_,
        v___y_8816_,
    );
    return v___x_8818_;
}
pub unsafe fn l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___boxed(
    mut v_constName_8819_: *mut leanh::LeanObject,
    mut v_skipRealize_8820_: *mut leanh::LeanObject,
    mut v___y_8821_: *mut leanh::LeanObject,
    mut v___y_8822_: *mut leanh::LeanObject,
    mut v___y_8823_: *mut leanh::LeanObject,
    mut v___y_8824_: *mut leanh::LeanObject,
    mut v___y_8825_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_skipRealize_boxed_8826_: u8 = 0;
    let mut v_res_8827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_skipRealize_boxed_8826_ = (leanh::lean_unbox(v_skipRealize_8820_) as u8);
    v_res_8827_ = l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0(
        v_constName_8819_,
        v_skipRealize_boxed_8826_,
        v___y_8821_,
        v___y_8822_,
        v___y_8823_,
        v___y_8824_,
    );
    leanh::lean_dec(v___y_8824_);
    leanh::lean_dec_ref(v___y_8823_);
    leanh::lean_dec(v___y_8822_);
    leanh::lean_dec_ref(v___y_8821_);
    return v_res_8827_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(
    mut v_x_8828_: *mut leanh::LeanObject,
    mut v___y_8829_: *mut leanh::LeanObject,
    mut v___y_8830_: *mut leanh::LeanObject,
    mut v___y_8831_: *mut leanh::LeanObject,
    mut v___y_8832_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8839_: u8 = 0;
    let mut v___x_8840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8843_: u8 = 0;
    let mut v___x_8845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8847_: u8 = 0;
    let mut v_unused_8848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8852_: u8 = 0;
    let mut v___x_8854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8856_: u8 = 0;
    let mut v___x_8857_: u8 = 0;
    let mut v___x_8858_: u8 = 0;
    let mut v_a_8859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8862_: u8 = 0;
    let mut v___x_8864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8866_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8834_ = l_Lean_Meta_saveState___redArg(v___y_8830_, v___y_8832_);
                if leanh::lean_obj_tag(v___x_8834_) == 0 {
                    v_a_8835_ = leanh::lean_ctor_get(v___x_8834_, 0);
                    leanh::lean_inc(v_a_8835_);
                    leanh::lean_dec_ref_known(v___x_8834_, 1);
                    leanh::lean_inc(v___y_8832_);
                    leanh::lean_inc_ref(v___y_8831_);
                    leanh::lean_inc(v___y_8830_);
                    leanh::lean_inc_ref(v___y_8829_);
                    v___x_8836_ = leanh::lean_apply_5(
                        v_x_8828_,
                        v___y_8829_,
                        v___y_8830_,
                        v___y_8831_,
                        v___y_8832_,
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_8836_) == 0 {
                        leanh::lean_dec(v_a_8835_);
                        return v___x_8836_;
                    } else {
                        v_a_8837_ = leanh::lean_ctor_get(v___x_8836_, 0);
                        leanh::lean_inc(v_a_8837_);
                        v___x_8857_ = l_Lean_Exception_isInterrupt(v_a_8837_);
                        if v___x_8857_ == 0 {
                            leanh::lean_inc(v_a_8837_);
                            v___x_8858_ = l_Lean_Exception_isRuntime(v_a_8837_);
                            v___y_8839_ = v___x_8858_;
                            state = 1;
                            continue;
                        } else {
                            v___y_8839_ = v___x_8857_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_x_8828_);
                    v_a_8859_ = leanh::lean_ctor_get(v___x_8834_, 0);
                    v_isSharedCheck_8866_ = (!leanh::lean_is_exclusive(v___x_8834_)) as u8;
                    if v_isSharedCheck_8866_ == 0 {
                        v___x_8861_ = v___x_8834_;
                        v_isShared_8862_ = v_isSharedCheck_8866_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8859_);
                        leanh::lean_dec(v___x_8834_);
                        v___x_8861_ = leanh::lean_box(0);
                        v_isShared_8862_ = v_isSharedCheck_8866_;
                        state = 6;
                        continue;
                    }
                }
            }
            1 => {
                if v___y_8839_ == 0 {
                    leanh::lean_dec_ref_known(v___x_8836_, 1);
                    v___x_8840_ = l_Lean_Meta_SavedState_restore___redArg(
                        v_a_8835_,
                        v___y_8830_,
                        v___y_8832_,
                    );
                    leanh::lean_dec(v_a_8835_);
                    if leanh::lean_obj_tag(v___x_8840_) == 0 {
                        v_isSharedCheck_8847_ =
                            (!leanh::lean_is_exclusive(v___x_8840_)) as u8;
                        if v_isSharedCheck_8847_ == 0 {
                            v_unused_8848_ = leanh::lean_ctor_get(v___x_8840_, 0);
                            leanh::lean_dec(v_unused_8848_);
                            v___x_8842_ = v___x_8840_;
                            v_isShared_8843_ = v_isSharedCheck_8847_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_8840_);
                            v___x_8842_ = leanh::lean_box(0);
                            v_isShared_8843_ = v_isSharedCheck_8847_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_8837_);
                        v_a_8849_ = leanh::lean_ctor_get(v___x_8840_, 0);
                        v_isSharedCheck_8856_ =
                            (!leanh::lean_is_exclusive(v___x_8840_)) as u8;
                        if v_isSharedCheck_8856_ == 0 {
                            v___x_8851_ = v___x_8840_;
                            v_isShared_8852_ = v_isSharedCheck_8856_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8849_);
                            leanh::lean_dec(v___x_8840_);
                            v___x_8851_ = leanh::lean_box(0);
                            v_isShared_8852_ = v_isSharedCheck_8856_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_a_8837_);
                    leanh::lean_dec(v_a_8835_);
                    return v___x_8836_;
                }
            }
            2 => {
                if v_isShared_8843_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_8842_, 1);
                    leanh::lean_ctor_set(v___x_8842_, 0, v_a_8837_);
                    v___x_8845_ = v___x_8842_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_8846_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8846_, 0, v_a_8837_);
                    v___x_8845_ = v_reuseFailAlloc_8846_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_8845_;
            }
            4 => {
                if v_isShared_8852_ == 0 {
                    v___x_8854_ = v___x_8851_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8855_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8855_, 0, v_a_8849_);
                    v___x_8854_ = v_reuseFailAlloc_8855_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8854_;
            }
            6 => {
                if v_isShared_8862_ == 0 {
                    v___x_8864_ = v___x_8861_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_8865_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8865_, 0, v_a_8859_);
                    v___x_8864_ = v_reuseFailAlloc_8865_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_8864_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg___boxed(
    mut v_x_8867_: *mut leanh::LeanObject,
    mut v___y_8868_: *mut leanh::LeanObject,
    mut v___y_8869_: *mut leanh::LeanObject,
    mut v___y_8870_: *mut leanh::LeanObject,
    mut v___y_8871_: *mut leanh::LeanObject,
    mut v___y_8872_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8873_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8873_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(
        v_x_8867_,
        v___y_8868_,
        v___y_8869_,
        v___y_8870_,
        v___y_8871_,
    );
    leanh::lean_dec(v___y_8871_);
    leanh::lean_dec_ref(v___y_8870_);
    leanh::lean_dec(v___y_8869_);
    leanh::lean_dec_ref(v___y_8868_);
    return v_res_8873_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(
    mut v_00_u03b1_8874_: *mut leanh::LeanObject,
    mut v_x_8875_: *mut leanh::LeanObject,
    mut v___y_8876_: *mut leanh::LeanObject,
    mut v___y_8877_: *mut leanh::LeanObject,
    mut v___y_8878_: *mut leanh::LeanObject,
    mut v___y_8879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8881_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(
        v_x_8875_,
        v___y_8876_,
        v___y_8877_,
        v___y_8878_,
        v___y_8879_,
    );
    return v___x_8881_;
}
pub unsafe fn l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___boxed(
    mut v_00_u03b1_8882_: *mut leanh::LeanObject,
    mut v_x_8883_: *mut leanh::LeanObject,
    mut v___y_8884_: *mut leanh::LeanObject,
    mut v___y_8885_: *mut leanh::LeanObject,
    mut v___y_8886_: *mut leanh::LeanObject,
    mut v___y_8887_: *mut leanh::LeanObject,
    mut v___y_8888_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8889_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1(
        v_00_u03b1_8882_,
        v_x_8883_,
        v___y_8884_,
        v___y_8885_,
        v___y_8886_,
        v___y_8887_,
    );
    leanh::lean_dec(v___y_8887_);
    leanh::lean_dec_ref(v___y_8886_);
    leanh::lean_dec(v___y_8885_);
    leanh::lean_dec_ref(v___y_8884_);
    return v_res_8889_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_8891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8892_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8891_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__0;
    v___x_8892_ = l_Lean_stringToMessageData(v___x_8891_);
    return v___x_8892_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_8894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__2;
    v___x_8895_ = l_Lean_stringToMessageData(v___x_8894_);
    return v___x_8895_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(
    mut v___x_8896_: *mut leanh::LeanObject,
    mut v___x_8897_: u8,
    mut v_group_8898_: *mut leanh::LeanObject,
    mut v_k_8899_: *mut leanh::LeanObject,
    mut v_comb_8900_: *mut leanh::LeanObject,
    mut v___y_8901_: *mut leanh::LeanObject,
    mut v___y_8902_: *mut leanh::LeanObject,
    mut v___y_8903_: *mut leanh::LeanObject,
    mut v___y_8904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8908_: u8 = 0;
    let mut v___x_8909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8919_: u8 = 0;
    let mut v___x_8921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8923_: u8 = 0;
    let mut v___x_8924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8928_: u8 = 0;
    let mut v___x_8930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8932_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8906_ =
                    l_Lean_hasConst___at___00Lean_Elab_Structural_tryCandidates_spec__0___redArg(
                        v___x_8896_,
                        v___x_8897_,
                        v___y_8904_,
                    );
                if leanh::lean_obj_tag(v___x_8906_) == 0 {
                    v_a_8907_ = leanh::lean_ctor_get(v___x_8906_, 0);
                    leanh::lean_inc(v_a_8907_);
                    leanh::lean_dec_ref_known(v___x_8906_, 1);
                    v___x_8908_ = (leanh::lean_unbox(v_a_8907_) as u8);
                    leanh::lean_dec(v_a_8907_);
                    if v___x_8908_ == 0 {
                        v___x_8909_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__1);
                        v___x_8910_ =
                            l_Lean_Elab_Structural_IndGroupInst_toMessageData(v_group_8898_);
                        v___x_8911_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_8911_, 0, v___x_8909_);
                        leanh::lean_ctor_set(v___x_8911_, 1, v___x_8910_);
                        v___x_8912_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___closed__3);
                        v___x_8913_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_8913_, 0, v___x_8911_);
                        leanh::lean_ctor_set(v___x_8913_, 1, v___x_8912_);
                        v___x_8914_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_8913_, v___y_8901_, v___y_8902_, v___y_8903_, v___y_8904_);
                        if leanh::lean_obj_tag(v___x_8914_) == 0 {
                            leanh::lean_dec_ref_known(v___x_8914_, 1);
                            v___x_8915_ = leanh::lean_apply_6(
                                v_k_8899_,
                                v_comb_8900_,
                                v___y_8901_,
                                v___y_8902_,
                                v___y_8903_,
                                v___y_8904_,
                                leanh::lean_box(0),
                            );
                            return v___x_8915_;
                        } else {
                            leanh::lean_dec(v___y_8904_);
                            leanh::lean_dec_ref(v___y_8903_);
                            leanh::lean_dec(v___y_8902_);
                            leanh::lean_dec_ref(v___y_8901_);
                            leanh::lean_dec_ref(v_comb_8900_);
                            leanh::lean_dec_ref(v_k_8899_);
                            v_a_8916_ = leanh::lean_ctor_get(v___x_8914_, 0);
                            v_isSharedCheck_8923_ =
                                (!leanh::lean_is_exclusive(v___x_8914_)) as u8;
                            if v_isSharedCheck_8923_ == 0 {
                                v___x_8918_ = v___x_8914_;
                                v_isShared_8919_ = v_isSharedCheck_8923_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_8916_);
                                leanh::lean_dec(v___x_8914_);
                                v___x_8918_ = leanh::lean_box(0);
                                v_isShared_8919_ = v_isSharedCheck_8923_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec_ref(v_group_8898_);
                        v___x_8924_ = leanh::lean_apply_6(
                            v_k_8899_,
                            v_comb_8900_,
                            v___y_8901_,
                            v___y_8902_,
                            v___y_8903_,
                            v___y_8904_,
                            leanh::lean_box(0),
                        );
                        return v___x_8924_;
                    }
                } else {
                    leanh::lean_dec(v___y_8904_);
                    leanh::lean_dec_ref(v___y_8903_);
                    leanh::lean_dec(v___y_8902_);
                    leanh::lean_dec_ref(v___y_8901_);
                    leanh::lean_dec_ref(v_comb_8900_);
                    leanh::lean_dec_ref(v_k_8899_);
                    leanh::lean_dec_ref(v_group_8898_);
                    v_a_8925_ = leanh::lean_ctor_get(v___x_8906_, 0);
                    v_isSharedCheck_8932_ = (!leanh::lean_is_exclusive(v___x_8906_)) as u8;
                    if v_isSharedCheck_8932_ == 0 {
                        v___x_8927_ = v___x_8906_;
                        v_isShared_8928_ = v_isSharedCheck_8932_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8925_);
                        leanh::lean_dec(v___x_8906_);
                        v___x_8927_ = leanh::lean_box(0);
                        v_isShared_8928_ = v_isSharedCheck_8932_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_8919_ == 0 {
                    v___x_8921_ = v___x_8918_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_8922_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8922_, 0, v_a_8916_);
                    v___x_8921_ = v_reuseFailAlloc_8922_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_8921_;
            }
            3 => {
                if v_isShared_8928_ == 0 {
                    v___x_8930_ = v___x_8927_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8931_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8931_, 0, v_a_8925_);
                    v___x_8930_ = v_reuseFailAlloc_8931_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_8930_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed(
    mut v___x_8933_: *mut leanh::LeanObject,
    mut v___x_8934_: *mut leanh::LeanObject,
    mut v_group_8935_: *mut leanh::LeanObject,
    mut v_k_8936_: *mut leanh::LeanObject,
    mut v_comb_8937_: *mut leanh::LeanObject,
    mut v___y_8938_: *mut leanh::LeanObject,
    mut v___y_8939_: *mut leanh::LeanObject,
    mut v___y_8940_: *mut leanh::LeanObject,
    mut v___y_8941_: *mut leanh::LeanObject,
    mut v___y_8942_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4418__boxed_8943_: u8 = 0;
    let mut v_res_8944_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4418__boxed_8943_ = (leanh::lean_unbox(v___x_8934_) as u8);
    v_res_8944_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0(v___x_8933_, v___x_4418__boxed_8943_, v_group_8935_, v_k_8936_, v_comb_8937_, v___y_8938_, v___y_8939_, v___y_8940_, v___y_8941_);
    return v_res_8944_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_8946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8947_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8946_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__0;
    v___x_8947_ = l_Lean_stringToMessageData(v___x_8946_);
    return v___x_8947_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_8948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8948_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__4;
    v___x_8949_ = l_Lean_stringToMessageData(v___x_8948_);
    return v___x_8949_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(
    mut v_k_8950_: *mut leanh::LeanObject,
    mut v_fnNames_8951_: *mut leanh::LeanObject,
    mut v_xs_8952_: *mut leanh::LeanObject,
    mut v_values_8953_: *mut leanh::LeanObject,
    mut v_as_8954_: *mut leanh::LeanObject,
    mut v_sz_8955_: usize,
    mut v_i_8956_: usize,
    mut v_b_8957_: *mut leanh::LeanObject,
    mut v___y_8958_: *mut leanh::LeanObject,
    mut v___y_8959_: *mut leanh::LeanObject,
    mut v___y_8960_: *mut leanh::LeanObject,
    mut v___y_8961_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8963_: u8 = 0;
    let mut v___x_8964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_8965_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8967_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8968_: u8 = 0;
    let mut v_a_8969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_group_8970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_comb_8971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8974_: u8 = 0;
    let mut v_toIndGroupInfo_8975_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_8979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8984_: u8 = 0;
    let mut v___x_8985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8992_: u8 = 0;
    let mut v_a_8993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8996_: u8 = 0;
    let mut v___x_8997_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_8999_: u8 = 0;
    let mut v___x_9000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9004_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9008_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9010_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9011_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9014_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9015_: usize = 0;
    let mut v___x_9016_: usize = 0;
    let mut v_reuseFailAlloc_9018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9023_: u8 = 0;
    let mut v___x_9025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9027_: u8 = 0;
    let mut v___x_9029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9031_: u8 = 0;
    let mut v___x_9032_: u8 = 0;
    let mut v_isSharedCheck_9033_: u8 = 0;
    let mut v_isSharedCheck_9034_: u8 = 0;
    let mut v_isSharedCheck_9035_: u8 = 0;
    let mut v_unused_9036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_8963_ = lean_usize_dec_lt(v_i_8956_, v_sz_8955_);
                if v___x_8963_ == 0 {
                    leanh::lean_dec_ref(v_values_8953_);
                    leanh::lean_dec_ref(v_xs_8952_);
                    leanh::lean_dec_ref(v_k_8950_);
                    v___x_8964_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8964_, 0, v_b_8957_);
                    return v___x_8964_;
                } else {
                    v_snd_8965_ = leanh::lean_ctor_get(v_b_8957_, 1);
                    v_isSharedCheck_9035_ = (!leanh::lean_is_exclusive(v_b_8957_)) as u8;
                    if v_isSharedCheck_9035_ == 0 {
                        v_unused_9036_ = leanh::lean_ctor_get(v_b_8957_, 0);
                        leanh::lean_dec(v_unused_9036_);
                        v___x_8967_ = v_b_8957_;
                        v_isShared_8968_ = v_isSharedCheck_9035_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_8965_);
                        leanh::lean_dec(v_b_8957_);
                        v___x_8967_ = leanh::lean_box(0);
                        v_isShared_8968_ = v_isSharedCheck_9035_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_8969_ = lean_array_uget(v_as_8954_, v_i_8956_);
                v_group_8970_ = leanh::lean_ctor_get(v_a_8969_, 0);
                v_comb_8971_ = leanh::lean_ctor_get(v_a_8969_, 1);
                v_isSharedCheck_9034_ = (!leanh::lean_is_exclusive(v_a_8969_)) as u8;
                if v_isSharedCheck_9034_ == 0 {
                    v___x_8973_ = v_a_8969_;
                    v_isShared_8974_ = v_isSharedCheck_9034_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_comb_8971_);
                    leanh::lean_inc(v_group_8970_);
                    leanh::lean_dec(v_a_8969_);
                    v___x_8973_ = leanh::lean_box(0);
                    v_isShared_8974_ = v_isSharedCheck_9034_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_toIndGroupInfo_8975_ = leanh::lean_ctor_get(v_group_8970_, 0);
                v___x_8976_ = leanh::lean_unsigned_to_nat(0);
                v___x_8977_ = l_Lean_Elab_Structural_IndGroupInfo_brecOnName(
                    v_toIndGroupInfo_8975_,
                    v___x_8976_,
                );
                v___x_8978_ = leanh::lean_box((v___x_8963_) as usize);
                leanh::lean_inc_ref(v_comb_8971_);
                leanh::lean_inc_ref(v_k_8950_);
                v___f_8979_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 10, 5);
                leanh::lean_closure_set(v___f_8979_, 0, v___x_8977_);
                leanh::lean_closure_set(v___f_8979_, 1, v___x_8978_);
                leanh::lean_closure_set(v___f_8979_, 2, v_group_8970_);
                leanh::lean_closure_set(v___f_8979_, 3, v_k_8950_);
                leanh::lean_closure_set(v___f_8979_, 4, v_comb_8971_);
                v___x_8980_ = l_Lean_commitIfNoEx___at___00Lean_Elab_Structural_tryCandidates_spec__1___redArg(v___f_8979_, v___y_8958_, v___y_8959_, v___y_8960_, v___y_8961_);
                if leanh::lean_obj_tag(v___x_8980_) == 0 {
                    leanh::lean_del_object(v___x_8973_);
                    leanh::lean_dec_ref(v_comb_8971_);
                    leanh::lean_dec_ref(v_values_8953_);
                    leanh::lean_dec_ref(v_xs_8952_);
                    leanh::lean_dec_ref(v_k_8950_);
                    v_a_8981_ = leanh::lean_ctor_get(v___x_8980_, 0);
                    v_isSharedCheck_8992_ = (!leanh::lean_is_exclusive(v___x_8980_)) as u8;
                    if v_isSharedCheck_8992_ == 0 {
                        v___x_8983_ = v___x_8980_;
                        v_isShared_8984_ = v_isSharedCheck_8992_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8981_);
                        leanh::lean_dec(v___x_8980_);
                        v___x_8983_ = leanh::lean_box(0);
                        v_isShared_8984_ = v_isSharedCheck_8992_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_8993_ = leanh::lean_ctor_get(v___x_8980_, 0);
                    v_isSharedCheck_9033_ = (!leanh::lean_is_exclusive(v___x_8980_)) as u8;
                    if v_isSharedCheck_9033_ == 0 {
                        v___x_8995_ = v___x_8980_;
                        v_isShared_8996_ = v_isSharedCheck_9033_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_8993_);
                        leanh::lean_dec(v___x_8980_);
                        v___x_8995_ = leanh::lean_box(0);
                        v_isShared_8996_ = v_isSharedCheck_9033_;
                        state = 6;
                        continue;
                    }
                }
            }
            3 => {
                v___x_8985_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_8985_, 0, v_a_8981_);
                if v_isShared_8968_ == 0 {
                    leanh::lean_ctor_set(v___x_8967_, 0, v___x_8985_);
                    v___x_8987_ = v___x_8967_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_8991_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8991_, 0, v___x_8985_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8991_, 1, v_snd_8965_);
                    v___x_8987_ = v_reuseFailAlloc_8991_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_8984_ == 0 {
                    leanh::lean_ctor_set(v___x_8983_, 0, v___x_8987_);
                    v___x_8989_ = v___x_8983_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8990_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8990_, 0, v___x_8987_);
                    v___x_8989_ = v_reuseFailAlloc_8990_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8989_;
            }
            6 => {
                v___x_8997_ = leanh::lean_box(0);
                v___x_9031_ = l_Lean_Exception_isInterrupt(v_a_8993_);
                if v___x_9031_ == 0 {
                    leanh::lean_inc(v_a_8993_);
                    v___x_9032_ = l_Lean_Exception_isRuntime(v_a_8993_);
                    v___y_8999_ = v___x_9032_;
                    state = 7;
                    continue;
                } else {
                    v___y_8999_ = v___x_9031_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v___y_8999_ == 0 {
                    leanh::lean_del_object(v___x_8995_);
                    leanh::lean_inc_ref(v_values_8953_);
                    leanh::lean_inc_ref(v_xs_8952_);
                    v___x_9000_ = l_Lean_Elab_Structural_prettyParameterSet(
                        v_fnNames_8951_,
                        v_xs_8952_,
                        v_values_8953_,
                        v_comb_8971_,
                        v___y_8958_,
                        v___y_8959_,
                        v___y_8960_,
                        v___y_8961_,
                    );
                    if leanh::lean_obj_tag(v___x_9000_) == 0 {
                        v_a_9001_ = leanh::lean_ctor_get(v___x_9000_, 0);
                        leanh::lean_inc(v_a_9001_);
                        leanh::lean_dec_ref_known(v___x_9000_, 1);
                        v___x_9002_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__1);
                        if v_isShared_8974_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_8973_, 7);
                            leanh::lean_ctor_set(v___x_8973_, 1, v_a_9001_);
                            leanh::lean_ctor_set(v___x_8973_, 0, v___x_9002_);
                            v___x_9004_ = v___x_8973_;
                            state = 8;
                            continue;
                        } else {
                            v_reuseFailAlloc_9019_ =
                                leanh::lean_alloc_ctor(7, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_9019_, 0, v___x_9002_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_9019_, 1, v_a_9001_);
                            v___x_9004_ = v_reuseFailAlloc_9019_;
                            state = 8;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_a_8993_);
                        leanh::lean_del_object(v___x_8973_);
                        leanh::lean_del_object(v___x_8967_);
                        leanh::lean_dec(v_snd_8965_);
                        leanh::lean_dec_ref(v_values_8953_);
                        leanh::lean_dec_ref(v_xs_8952_);
                        leanh::lean_dec_ref(v_k_8950_);
                        v_a_9020_ = leanh::lean_ctor_get(v___x_9000_, 0);
                        v_isSharedCheck_9027_ =
                            (!leanh::lean_is_exclusive(v___x_9000_)) as u8;
                        if v_isSharedCheck_9027_ == 0 {
                            v___x_9022_ = v___x_9000_;
                            v_isShared_9023_ = v_isSharedCheck_9027_;
                            state = 10;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_9020_);
                            leanh::lean_dec(v___x_9000_);
                            v___x_9022_ = leanh::lean_box(0);
                            v_isShared_9023_ = v_isSharedCheck_9027_;
                            state = 10;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_8973_);
                    leanh::lean_dec_ref(v_comb_8971_);
                    leanh::lean_del_object(v___x_8967_);
                    leanh::lean_dec(v_snd_8965_);
                    leanh::lean_dec_ref(v_values_8953_);
                    leanh::lean_dec_ref(v_xs_8952_);
                    leanh::lean_dec_ref(v_k_8950_);
                    if v_isShared_8996_ == 0 {
                        v___x_9029_ = v___x_8995_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_9030_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9030_, 0, v_a_8993_);
                        v___x_9029_ = v_reuseFailAlloc_9030_;
                        state = 12;
                        continue;
                    }
                }
            }
            8 => {
                v___x_9005_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Elab_Structural_getRecArgInfos_spec__1___redArg___closed__3);
                v___x_9006_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9006_, 0, v___x_9004_);
                leanh::lean_ctor_set(v___x_9006_, 1, v___x_9005_);
                v___x_9007_ = l_Lean_Exception_toMessageData(v_a_8993_);
                v___x_9008_ = l_Lean_indentD(v___x_9007_);
                v___x_9009_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9009_, 0, v___x_9006_);
                leanh::lean_ctor_set(v___x_9009_, 1, v___x_9008_);
                v___x_9010_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___closed__2);
                v___x_9011_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9011_, 0, v___x_9009_);
                leanh::lean_ctor_set(v___x_9011_, 1, v___x_9010_);
                v___x_9012_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_9012_, 0, v_snd_8965_);
                leanh::lean_ctor_set(v___x_9012_, 1, v___x_9011_);
                if v_isShared_8968_ == 0 {
                    leanh::lean_ctor_set(v___x_8967_, 1, v___x_9012_);
                    leanh::lean_ctor_set(v___x_8967_, 0, v___x_8997_);
                    v___x_9014_ = v___x_8967_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_9018_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9018_, 0, v___x_8997_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9018_, 1, v___x_9012_);
                    v___x_9014_ = v_reuseFailAlloc_9018_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_9015_ = 1usize;
                v___x_9016_ = lean_usize_add(v_i_8956_, v___x_9015_);
                v_i_8956_ = v___x_9016_;
                v_b_8957_ = v___x_9014_;
                state = 0;
                continue;
            }
            10 => {
                if v_isShared_9023_ == 0 {
                    v___x_9025_ = v___x_9022_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_9026_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9026_, 0, v_a_9020_);
                    v___x_9025_ = v_reuseFailAlloc_9026_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_9025_;
            }
            12 => {
                return v___x_9029_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg___boxed(
    mut v_k_9037_: *mut leanh::LeanObject,
    mut v_fnNames_9038_: *mut leanh::LeanObject,
    mut v_xs_9039_: *mut leanh::LeanObject,
    mut v_values_9040_: *mut leanh::LeanObject,
    mut v_as_9041_: *mut leanh::LeanObject,
    mut v_sz_9042_: *mut leanh::LeanObject,
    mut v_i_9043_: *mut leanh::LeanObject,
    mut v_b_9044_: *mut leanh::LeanObject,
    mut v___y_9045_: *mut leanh::LeanObject,
    mut v___y_9046_: *mut leanh::LeanObject,
    mut v___y_9047_: *mut leanh::LeanObject,
    mut v___y_9048_: *mut leanh::LeanObject,
    mut v___y_9049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_9050_: usize = 0;
    let mut v_i_boxed_9051_: usize = 0;
    let mut v_res_9052_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_9050_ = leanh::lean_unbox_usize(v_sz_9042_);
    leanh::lean_dec(v_sz_9042_);
    v_i_boxed_9051_ = leanh::lean_unbox_usize(v_i_9043_);
    leanh::lean_dec(v_i_9043_);
    v_res_9052_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_9037_, v_fnNames_9038_, v_xs_9039_, v_values_9040_, v_as_9041_, v_sz_boxed_9050_, v_i_boxed_9051_, v_b_9044_, v___y_9045_, v___y_9046_, v___y_9047_, v___y_9048_);
    leanh::lean_dec(v___y_9048_);
    leanh::lean_dec_ref(v___y_9047_);
    leanh::lean_dec(v___y_9046_);
    leanh::lean_dec_ref(v___y_9045_);
    leanh::lean_dec_ref(v_as_9041_);
    leanh::lean_dec_ref(v_fnNames_9038_);
    return v_res_9052_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_9054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9055_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9054_ = l_Lean_Elab_Structural_tryCandidates___redArg___closed__0;
    v___x_9055_ = l_Lean_stringToMessageData(v___x_9054_);
    return v___x_9055_;
}
pub unsafe fn _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_9057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9057_ = l_Lean_Elab_Structural_tryCandidates___redArg___closed__2;
    v___x_9058_ = l_Lean_stringToMessageData(v___x_9057_);
    return v___x_9058_;
}
pub unsafe fn l_Lean_Elab_Structural_tryCandidates___redArg(
    mut v_fnNames_9059_: *mut leanh::LeanObject,
    mut v_xs_9060_: *mut leanh::LeanObject,
    mut v_values_9061_: *mut leanh::LeanObject,
    mut v_candidates_9062_: *mut leanh::LeanObject,
    mut v_k_9063_: *mut leanh::LeanObject,
    mut v_a_9064_: *mut leanh::LeanObject,
    mut v_a_9065_: *mut leanh::LeanObject,
    mut v_a_9066_: *mut leanh::LeanObject,
    mut v_a_9067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_candidates_9069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_report_9070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9073_: u8 = 0;
    let mut v___x_9074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_9077_: usize = 0;
    let mut v___x_9078_: usize = 0;
    let mut v___x_9079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9083_: u8 = 0;
    let mut v_fst_9084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_9085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_9086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9089_: u8 = 0;
    let mut v_inheritedTraceOptions_9090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_9091_: u8 = 0;
    let mut v___x_9092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9095_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9097_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9098_: u8 = 0;
    let mut v___x_9099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_9104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9107_: u8 = 0;
    let mut v___x_9109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9111_: u8 = 0;
    let mut v_reuseFailAlloc_9112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9113_: u8 = 0;
    let mut v_unused_9114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_9115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9119_: u8 = 0;
    let mut v_a_9120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_9122_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_9123_: u8 = 0;
    let mut v___x_9125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_9126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9127_: u8 = 0;
    let mut v_reuseFailAlloc_9128_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_9129_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_candidates_9069_ = leanh::lean_ctor_get(v_candidates_9062_, 0);
                v_report_9070_ = leanh::lean_ctor_get(v_candidates_9062_, 1);
                v_isSharedCheck_9129_ =
                    (!leanh::lean_is_exclusive(v_candidates_9062_)) as u8;
                if v_isSharedCheck_9129_ == 0 {
                    v___x_9072_ = v_candidates_9062_;
                    v_isShared_9073_ = v_isSharedCheck_9129_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_report_9070_);
                    leanh::lean_inc(v_candidates_9069_);
                    leanh::lean_dec(v_candidates_9062_);
                    v___x_9072_ = leanh::lean_box(0);
                    v_isShared_9073_ = v_isSharedCheck_9129_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_9074_ = leanh::lean_box(0);
                if v_isShared_9073_ == 0 {
                    leanh::lean_ctor_set(v___x_9072_, 0, v___x_9074_);
                    v___x_9076_ = v___x_9072_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_9128_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9128_, 0, v___x_9074_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9128_, 1, v_report_9070_);
                    v___x_9076_ = v_reuseFailAlloc_9128_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_sz_9077_ = lean_array_size(v_candidates_9069_);
                v___x_9078_ = 0usize;
                v___x_9079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_9063_, v_fnNames_9059_, v_xs_9060_, v_values_9061_, v_candidates_9069_, v_sz_9077_, v___x_9078_, v___x_9076_, v_a_9064_, v_a_9065_, v_a_9066_, v_a_9067_);
                leanh::lean_dec_ref(v_candidates_9069_);
                if leanh::lean_obj_tag(v___x_9079_) == 0 {
                    v_a_9080_ = leanh::lean_ctor_get(v___x_9079_, 0);
                    v_isSharedCheck_9119_ = (!leanh::lean_is_exclusive(v___x_9079_)) as u8;
                    if v_isSharedCheck_9119_ == 0 {
                        v___x_9082_ = v___x_9079_;
                        v_isShared_9083_ = v_isSharedCheck_9119_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9080_);
                        leanh::lean_dec(v___x_9079_);
                        v___x_9082_ = leanh::lean_box(0);
                        v_isShared_9083_ = v_isSharedCheck_9119_;
                        state = 3;
                        continue;
                    }
                } else {
                    v_a_9120_ = leanh::lean_ctor_get(v___x_9079_, 0);
                    v_isSharedCheck_9127_ = (!leanh::lean_is_exclusive(v___x_9079_)) as u8;
                    if v_isSharedCheck_9127_ == 0 {
                        v___x_9122_ = v___x_9079_;
                        v_isShared_9123_ = v_isSharedCheck_9127_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_9120_);
                        leanh::lean_dec(v___x_9079_);
                        v___x_9122_ = leanh::lean_box(0);
                        v_isShared_9123_ = v_isSharedCheck_9127_;
                        state = 9;
                        continue;
                    }
                }
            }
            3 => {
                v_fst_9084_ = leanh::lean_ctor_get(v_a_9080_, 0);
                if leanh::lean_obj_tag(v_fst_9084_) == 0 {
                    leanh::lean_del_object(v___x_9082_);
                    v_options_9085_ = leanh::lean_ctor_get(v_a_9066_, 2);
                    v_snd_9086_ = leanh::lean_ctor_get(v_a_9080_, 1);
                    v_isSharedCheck_9113_ = (!leanh::lean_is_exclusive(v_a_9080_)) as u8;
                    if v_isSharedCheck_9113_ == 0 {
                        v_unused_9114_ = leanh::lean_ctor_get(v_a_9080_, 0);
                        leanh::lean_dec(v_unused_9114_);
                        v___x_9088_ = v_a_9080_;
                        v_isShared_9089_ = v_isSharedCheck_9113_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_9086_);
                        leanh::lean_dec(v_a_9080_);
                        v___x_9088_ = leanh::lean_box(0);
                        v_isShared_9089_ = v_isSharedCheck_9113_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_9084_);
                    leanh::lean_dec(v_a_9080_);
                    v_val_9115_ = leanh::lean_ctor_get(v_fst_9084_, 0);
                    leanh::lean_inc(v_val_9115_);
                    leanh::lean_dec_ref_known(v_fst_9084_, 1);
                    if v_isShared_9083_ == 0 {
                        leanh::lean_ctor_set(v___x_9082_, 0, v_val_9115_);
                        v___x_9117_ = v___x_9082_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_9118_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_9118_, 0, v_val_9115_);
                        v___x_9117_ = v_reuseFailAlloc_9118_;
                        state = 8;
                        continue;
                    }
                }
            }
            4 => {
                v_inheritedTraceOptions_9090_ = leanh::lean_ctor_get(v_a_9066_, 13);
                v_hasTrace_9091_ = leanh::lean_ctor_get_uint8(
                    v_options_9085_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v___x_9092_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_tryCandidates___redArg___closed__1
                    ),
                    core::ptr::addr_of_mut!(
                        l_Lean_Elab_Structural_tryCandidates___redArg___closed__1_once
                    ),
                    _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__1,
                );
                if v_isShared_9089_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_9088_, 7);
                    leanh::lean_ctor_set(v___x_9088_, 0, v___x_9092_);
                    v___x_9094_ = v___x_9088_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_9112_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9112_, 0, v___x_9092_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9112_, 1, v_snd_9086_);
                    v___x_9094_ = v_reuseFailAlloc_9112_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_hasTrace_9091_ == 0 {
                    v___x_9095_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_9094_, v_a_9064_, v_a_9065_, v_a_9066_, v_a_9067_);
                    return v___x_9095_;
                } else {
                    v___x_9096_ = l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__9;
                    v___x_9097_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12_once
                        ),
                        _init_l_Lean_Elab_Structural_getRecArgInfos___lam__2___closed__12,
                    );
                    v___x_9098_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                        v_inheritedTraceOptions_9090_,
                        v_options_9085_,
                        v___x_9097_,
                    );
                    if v___x_9098_ == 0 {
                        v___x_9099_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_9094_, v_a_9064_, v_a_9065_, v_a_9066_, v_a_9067_);
                        return v___x_9099_;
                    } else {
                        v___x_9100_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_tryCandidates___redArg___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Elab_Structural_tryCandidates___redArg___closed__3_once
                            ),
                            _init_l_Lean_Elab_Structural_tryCandidates___redArg___closed__3,
                        );
                        leanh::lean_inc_ref(v___x_9094_);
                        v___x_9101_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_9101_, 0, v___x_9100_);
                        leanh::lean_ctor_set(v___x_9101_, 1, v___x_9094_);
                        v___x_9102_ =
                            l_Lean_addTrace___at___00Lean_Elab_Structural_getRecArgInfos_spec__0(
                                v___x_9096_,
                                v___x_9101_,
                                v_a_9064_,
                                v_a_9065_,
                                v_a_9066_,
                                v_a_9067_,
                            );
                        if leanh::lean_obj_tag(v___x_9102_) == 0 {
                            leanh::lean_dec_ref_known(v___x_9102_, 1);
                            v___x_9103_ = l_Lean_throwError___at___00Lean_Elab_Structural_getRecArgInfo_spec__0___redArg(v___x_9094_, v_a_9064_, v_a_9065_, v_a_9066_, v_a_9067_);
                            return v___x_9103_;
                        } else {
                            leanh::lean_dec_ref(v___x_9094_);
                            v_a_9104_ = leanh::lean_ctor_get(v___x_9102_, 0);
                            v_isSharedCheck_9111_ =
                                (!leanh::lean_is_exclusive(v___x_9102_)) as u8;
                            if v_isSharedCheck_9111_ == 0 {
                                v___x_9106_ = v___x_9102_;
                                v_isShared_9107_ = v_isSharedCheck_9111_;
                                state = 6;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_9104_);
                                leanh::lean_dec(v___x_9102_);
                                v___x_9106_ = leanh::lean_box(0);
                                v_isShared_9107_ = v_isSharedCheck_9111_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                }
            }
            6 => {
                if v_isShared_9107_ == 0 {
                    v___x_9109_ = v___x_9106_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_9110_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9110_, 0, v_a_9104_);
                    v___x_9109_ = v_reuseFailAlloc_9110_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_9109_;
            }
            8 => {
                return v___x_9117_;
            }
            9 => {
                if v_isShared_9123_ == 0 {
                    v___x_9125_ = v___x_9122_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_9126_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_9126_, 0, v_a_9120_);
                    v___x_9125_ = v_reuseFailAlloc_9126_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_9125_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Elab_Structural_tryCandidates___redArg___boxed(
    mut v_fnNames_9130_: *mut leanh::LeanObject,
    mut v_xs_9131_: *mut leanh::LeanObject,
    mut v_values_9132_: *mut leanh::LeanObject,
    mut v_candidates_9133_: *mut leanh::LeanObject,
    mut v_k_9134_: *mut leanh::LeanObject,
    mut v_a_9135_: *mut leanh::LeanObject,
    mut v_a_9136_: *mut leanh::LeanObject,
    mut v_a_9137_: *mut leanh::LeanObject,
    mut v_a_9138_: *mut leanh::LeanObject,
    mut v_a_9139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9140_ = l_Lean_Elab_Structural_tryCandidates___redArg(
        v_fnNames_9130_,
        v_xs_9131_,
        v_values_9132_,
        v_candidates_9133_,
        v_k_9134_,
        v_a_9135_,
        v_a_9136_,
        v_a_9137_,
        v_a_9138_,
    );
    leanh::lean_dec(v_a_9138_);
    leanh::lean_dec_ref(v_a_9137_);
    leanh::lean_dec(v_a_9136_);
    leanh::lean_dec_ref(v_a_9135_);
    leanh::lean_dec_ref(v_fnNames_9130_);
    return v_res_9140_;
}
pub unsafe fn l_Lean_Elab_Structural_tryCandidates(
    mut v_00_u03b1_9141_: *mut leanh::LeanObject,
    mut v_fnNames_9142_: *mut leanh::LeanObject,
    mut v_xs_9143_: *mut leanh::LeanObject,
    mut v_values_9144_: *mut leanh::LeanObject,
    mut v_candidates_9145_: *mut leanh::LeanObject,
    mut v_k_9146_: *mut leanh::LeanObject,
    mut v_a_9147_: *mut leanh::LeanObject,
    mut v_a_9148_: *mut leanh::LeanObject,
    mut v_a_9149_: *mut leanh::LeanObject,
    mut v_a_9150_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9152_ = l_Lean_Elab_Structural_tryCandidates___redArg(
        v_fnNames_9142_,
        v_xs_9143_,
        v_values_9144_,
        v_candidates_9145_,
        v_k_9146_,
        v_a_9147_,
        v_a_9148_,
        v_a_9149_,
        v_a_9150_,
    );
    return v___x_9152_;
}
pub unsafe fn l_Lean_Elab_Structural_tryCandidates___boxed(
    mut v_00_u03b1_9153_: *mut leanh::LeanObject,
    mut v_fnNames_9154_: *mut leanh::LeanObject,
    mut v_xs_9155_: *mut leanh::LeanObject,
    mut v_values_9156_: *mut leanh::LeanObject,
    mut v_candidates_9157_: *mut leanh::LeanObject,
    mut v_k_9158_: *mut leanh::LeanObject,
    mut v_a_9159_: *mut leanh::LeanObject,
    mut v_a_9160_: *mut leanh::LeanObject,
    mut v_a_9161_: *mut leanh::LeanObject,
    mut v_a_9162_: *mut leanh::LeanObject,
    mut v_a_9163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_9164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_9164_ = l_Lean_Elab_Structural_tryCandidates(
        v_00_u03b1_9153_,
        v_fnNames_9154_,
        v_xs_9155_,
        v_values_9156_,
        v_candidates_9157_,
        v_k_9158_,
        v_a_9159_,
        v_a_9160_,
        v_a_9161_,
        v_a_9162_,
    );
    leanh::lean_dec(v_a_9162_);
    leanh::lean_dec_ref(v_a_9161_);
    leanh::lean_dec(v_a_9160_);
    leanh::lean_dec_ref(v_a_9159_);
    leanh::lean_dec_ref(v_fnNames_9154_);
    return v_res_9164_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(
    mut v_00_u03b1_9165_: *mut leanh::LeanObject,
    mut v_k_9166_: *mut leanh::LeanObject,
    mut v_fnNames_9167_: *mut leanh::LeanObject,
    mut v_xs_9168_: *mut leanh::LeanObject,
    mut v_values_9169_: *mut leanh::LeanObject,
    mut v_as_9170_: *mut leanh::LeanObject,
    mut v_sz_9171_: usize,
    mut v_i_9172_: usize,
    mut v_b_9173_: *mut leanh::LeanObject,
    mut v___y_9174_: *mut leanh::LeanObject,
    mut v___y_9175_: *mut leanh::LeanObject,
    mut v___y_9176_: *mut leanh::LeanObject,
    mut v___y_9177_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_9179_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_9179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___redArg(v_k_9166_, v_fnNames_9167_, v_xs_9168_, v_values_9169_, v_as_9170_, v_sz_9171_, v_i_9172_, v_b_9173_, v___y_9174_, v___y_9175_, v___y_9176_, v___y_9177_);
    return v___x_9179_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2___boxed(
    mut v_00_u03b1_9180_: *mut leanh::LeanObject,
    mut v_k_9181_: *mut leanh::LeanObject,
    mut v_fnNames_9182_: *mut leanh::LeanObject,
    mut v_xs_9183_: *mut leanh::LeanObject,
    mut v_values_9184_: *mut leanh::LeanObject,
    mut v_as_9185_: *mut leanh::LeanObject,
    mut v_sz_9186_: *mut leanh::LeanObject,
    mut v_i_9187_: *mut leanh::LeanObject,
    mut v_b_9188_: *mut leanh::LeanObject,
    mut v___y_9189_: *mut leanh::LeanObject,
    mut v___y_9190_: *mut leanh::LeanObject,
    mut v___y_9191_: *mut leanh::LeanObject,
    mut v___y_9192_: *mut leanh::LeanObject,
    mut v___y_9193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_9194_: usize = 0;
    let mut v_i_boxed_9195_: usize = 0;
    let mut v_res_9196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_9194_ = leanh::lean_unbox_usize(v_sz_9186_);
    leanh::lean_dec(v_sz_9186_);
    v_i_boxed_9195_ = leanh::lean_unbox_usize(v_i_9187_);
    leanh::lean_dec(v_i_9187_);
    v_res_9196_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Structural_tryCandidates_spec__2(v_00_u03b1_9180_, v_k_9181_, v_fnNames_9182_, v_xs_9183_, v_values_9184_, v_as_9185_, v_sz_boxed_9194_, v_i_boxed_9195_, v_b_9188_, v___y_9189_, v___y_9190_, v___y_9191_, v___y_9192_);
    leanh::lean_dec(v___y_9192_);
    leanh::lean_dec_ref(v___y_9191_);
    leanh::lean_dec(v___y_9190_);
    leanh::lean_dec_ref(v___y_9189_);
    leanh::lean_dec_ref(v_as_9185_);
    leanh::lean_dec_ref(v_fnNames_9182_);
    return v_res_9196_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Elab_Structural_maxCombinationSize = _init_l_Lean_Elab_Structural_maxCombinationSize();
    leanh::lean_mark_persistent(l_Lean_Elab_Structural_maxCombinationSize);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(
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
pub unsafe fn initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Elab_PreDefinition_Structural_RecArgInfo(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Init_Omega(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Elab_PreDefinition_Structural_FindRecArg(builtin);
}