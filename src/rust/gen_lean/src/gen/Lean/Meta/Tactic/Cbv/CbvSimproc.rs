// Lean compiler output
// Module: Lean.Meta.Tactic.Cbv.CbvSimproc
// Imports: Lean.Compiler.InitAttr Lean.ScopedEnvExtension Lean.Meta.Sym.Simp.SimpM Lean.Meta.Sym.Simp.Result Lean.Meta.Sym.Simp.App Lean.Meta.Sym.Simp.DiscrTree Lean.Meta.Sym.Pattern
use crate::ffi::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_fset, lean_array_fswap, lean_array_get,
    lean_array_get_borrowed, lean_array_get_size, lean_array_push, lean_array_set, lean_array_size,
    lean_array_uget, lean_array_uget_borrowed, lean_array_uset, lean_expr_dbg_to_string,
    lean_float_decLt, lean_float_div, lean_float_sub, lean_io_get_num_heartbeats,
    lean_io_mono_nanos_now, lean_mk_array, lean_mk_empty_array_with_capacity, lean_name_eq,
    lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
    lean_nat_shiftr, lean_nat_sub, lean_nat_to_int, lean_panic_fn_borrowed, lean_st_mk_ref,
    lean_st_ref_get, lean_st_ref_set, lean_st_ref_take, lean_string_append, lean_string_dec_eq,
    lean_uint64_of_nat, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_eq, lean_usize_dec_le, lean_usize_dec_lt, lean_usize_land,
    lean_usize_mul, lean_usize_of_nat, lean_usize_shift_left, lean_usize_shift_right,
    lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Array::Basic::{
    l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop, l_Array_eraseIdx___redArg,
};
use crate::r#gen::Init::Data::OfScientific::lean_float_of_nat;
use crate::r#gen::Init::Data::Repr::l_Repr_addAppParen;
use crate::r#gen::Init::Data::ToString::Name::{
    l_Lean_Name_toString, l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0,
};
use crate::r#gen::Init::Meta::Defs::{l_Lean_Name_replacePrefix, l_Lean_Syntax_isNone};
use crate::r#gen::Init::Prelude::{
    l_Lean_Name_append, l_Lean_Name_num___override, l_Lean_Name_str___override,
    l_Lean_Syntax_getArg, l_Lean_Syntax_getKind, l_Lean_replaceRef,
};
use crate::r#gen::Init::System::IOError::{lean_io_error_to_string, lean_mk_io_user_error};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Attributes::{
    l_Lean_ensureAttrDeclIsMeta, l_Lean_registerBuiltinAttribute,
};
use crate::r#gen::Lean::Compiler::InitAttr::{
    initialize_Lean_Compiler_InitAttr, l_Lean_declareBuiltin,
    runtime_initialize_Lean_Compiler_InitAttr,
};
use crate::r#gen::Lean::CoreM::l_Lean_Core_mkFreshUserName;
use crate::r#gen::Lean::Data::Name::l_Lean_Name_quickLt;
use crate::r#gen::Lean::Data::NameMap::Basic::l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg;
use crate::r#gen::Lean::Data::PersistentArray::{
    l_Lean_PersistentArray_append___redArg, l_Lean_PersistentArray_push___redArg,
    l_Lean_PersistentArray_toArray___redArg,
};
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_isUnaryNode___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
    l_Lean_PersistentHashMap_mkEmptyEntriesArray,
};
use crate::r#gen::Lean::Declaration::l_Lean_ConstantInfo_type;
use crate::r#gen::Lean::Environment::{
    l_Lean_Environment_evalConst___redArg, l_Lean_Environment_find_x3f,
    l_Lean_Environment_getModuleIdxFor_x3f,
    l_Lean_PersistentEnvExtension_getModuleEntries___redArg,
    l_Lean_PersistentEnvExtension_getState___redArg,
    l_Lean_PersistentEnvExtension_modifyState___redArg,
    l_Lean_registerPersistentEnvExtensionUnsafe___redArg,
};
use crate::r#gen::Lean::Exception::l_Lean_Exception_toMessageData;
use crate::r#gen::Lean::Expr::{l_Lean_mkAppN, l_Lean_mkConst};
use crate::r#gen::Lean::ImportingFlag::l_Lean_initializing;
use crate::r#gen::Lean::Message::{
    l_Lean_MessageData_ofConstName, l_Lean_MessageData_ofFormat, l_Lean_MessageData_ofName,
    l_Lean_indentExpr, l_Lean_stringToMessageData,
};
use crate::r#gen::Lean::Meta::DiscrTree::Basic::{
    l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes,
    l_Lean_Meta_DiscrTree_Key_lt, l_Lean_Meta_DiscrTree_instInhabited,
};
use crate::r#gen::Lean::Meta::DiscrTree::Types::{
    l_Lean_Meta_DiscrTree_Key_hash, l_Lean_Meta_DiscrTree_instBEqKey_beq,
};
use crate::r#gen::Lean::Meta::Sym::Pattern::{
    initialize_Lean_Meta_Sym_Pattern, runtime_initialize_Lean_Meta_Sym_Pattern,
};
use crate::r#gen::Lean::Meta::Sym::Simp::App::{
    initialize_Lean_Meta_Sym_Simp_App, l_Lean_Meta_Sym_Simp_simpOverApplied,
    runtime_initialize_Lean_Meta_Sym_Simp_App,
};
use crate::r#gen::Lean::Meta::Sym::Simp::DiscrTree::{
    initialize_Lean_Meta_Sym_Simp_DiscrTree, l_Lean_Meta_Sym_getMatchWithExtra___redArg,
    runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree,
};
use crate::r#gen::Lean::Meta::Sym::Simp::Result::{
    initialize_Lean_Meta_Sym_Simp_Result, runtime_initialize_Lean_Meta_Sym_Simp_Result,
};
use crate::r#gen::Lean::Meta::Sym::Simp::SimpM::{
    initialize_Lean_Meta_Sym_Simp_SimpM, runtime_initialize_Lean_Meta_Sym_Simp_SimpM,
};
use crate::r#gen::Lean::PrivateName::l_Lean_privateToUserName;
use crate::r#gen::Lean::ScopedEnvExtension::{
    initialize_Lean_ScopedEnvExtension, l_Lean_ScopedEnvExtension_addCore___redArg,
    l_Lean_ScopedEnvExtension_getState___redArg, l_Lean_ScopedEnvExtension_modifyState___redArg,
    l_Lean_registerScopedEnvExtensionUnsafe___redArg, runtime_initialize_Lean_ScopedEnvExtension,
};
use crate::r#gen::Lean::ToExpr::l___private_Lean_ToExpr_0__Lean_Name_toExprAux;
use crate::r#gen::Lean::Util::Trace::{
    l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go, l_Lean_TraceResult_toEmoji,
    l_Lean_trace_profiler, l_Lean_trace_profiler_threshold, l_Lean_trace_profiler_useHeartbeats,
};
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default: u8 = 0;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase: u8 = 0;
pub static l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value:
    leanh::LeanStringObject<41> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 41,
    m_capacity: 41,
    m_length: 40,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 67, 98, 118, 46,
        67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 104, 97, 115, 101, 46, 112, 114, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__0_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 67, 98, 118, 46,
        67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 104, 97, 115, 101, 46, 101, 118, 97, 108,
        0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__2_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 67, 98, 118, 46,
        67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 104, 97, 115, 101, 46, 112, 111, 115,
        116, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 1
            + 0) as u16,
        other: 1,
        tag: 3,
    },
    m_objs: [core::ptr::addr_of!(
        l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__4_value
    ) as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value:
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
    m_data: [76, 101, 97, 110, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value:
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
    m_data: [77, 101, 116, 97, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [84, 97, 99, 116, 105, 99, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [67, 98, 118, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value:
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
        67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 80, 104, 97, 115, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [112, 114, 101, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        15449383196166861506 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value
        ) as *mut leanh::LeanObject,
        15353829308266697735 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value
        ) as *mut leanh::LeanObject,
        10267394960704184689 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_4:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value
        ) as *mut leanh::LeanObject,
        5030180886731624463 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value_aux_4
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__5_value
        ) as *mut leanh::LeanObject,
        6681721167176189614 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value:
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
    m_data: [101, 118, 97, 108, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        15449383196166861506 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value
        ) as *mut leanh::LeanObject,
        15353829308266697735 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value
        ) as *mut leanh::LeanObject,
        10267394960704184689 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_4:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value
        ) as *mut leanh::LeanObject,
        5030180886731624463 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value_aux_4
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__8_value
        ) as *mut leanh::LeanObject,
        7971564759627895176 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value:
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
    m_data: [112, 111, 115, 116, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value
) as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        15449383196166861506 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value
        ) as *mut leanh::LeanObject,
        15353829308266697735 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value
        ) as *mut leanh::LeanObject,
        10267394960704184689 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_4:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value
        ) as *mut leanh::LeanObject,
        5030180886731624463 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value_aux_4
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__11_value
        ) as *mut leanh::LeanObject,
        496761162500371831 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12_value
) as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_1:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_0
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value
        ) as *mut leanh::LeanObject,
        15449383196166861506 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_1
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value
        ) as *mut leanh::LeanObject,
        15353829308266697735 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_3:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_2
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value
        ) as *mut leanh::LeanObject,
        10267394960704184689 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value_aux_3
        ) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__4_value
        ) as *mut leanh::LeanObject,
        5030180886731624463 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value:
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
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value:
    leanh::LeanCtorObject<3> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0_value
        ) as *mut leanh::LeanObject,
        2 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__1_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed
        as *const core::ffi::c_void,
    m_arity: 2,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value:
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
    m_fun: l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0 as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__0_value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0_value: leanh::LeanStringObject<26> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 26, m_capacity: 26, m_length: 25, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 66, 97, 115, 105, 99, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 68, 105, 115, 99, 114, 84, 114, 101, 101, 46, 105, 110, 115, 101, 114, 116, 75, 101, 121, 86, 97, 108, 117, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1_value) as *mut leanh::LeanObject;
pub static l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2_value: leanh::LeanStringObject<21> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 21, m_capacity: 21, m_length: 20, m_data: [105, 110, 118, 97, 108, 105, 100, 32, 107, 101, 121, 32, 115, 101, 113, 117, 101, 110, 99, 101, 0]};
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2_value) as *mut leanh::LeanObject;
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0: u64 = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0_value:
    leanh::LeanStringObject<89> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 89,
    m_capacity: 89,
    m_length: 88,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 98, 117, 105, 108, 116, 105, 110, 32, 99, 98, 118, 32,
        115, 105, 109, 112, 114, 111, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        58, 32, 73, 116, 32, 99, 97, 110, 32, 111, 110, 108, 121, 32, 98, 101, 32, 114, 101, 103,
        105, 115, 116, 101, 114, 101, 100, 32, 100, 117, 114, 105, 110, 103, 32, 105, 110, 105,
        116, 105, 97, 108, 105, 122, 97, 116, 105, 111, 110, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 98, 117, 105, 108, 116, 105, 110, 32, 99, 98, 118, 32,
        115, 105, 109, 112, 114, 111, 99, 32, 100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110,
        32, 96, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3_value:
    leanh::LeanStringObject<32> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 32,
    m_capacity: 32,
    m_length: 31,
    m_data: [
        96, 58, 32, 73, 116, 32, 104, 97, 115, 32, 97, 108, 114, 101, 97, 100, 121, 32, 98, 101,
        101, 110, 32, 100, 101, 99, 108, 97, 114, 101, 100, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value:
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
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value
) as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value:
    leanh::LeanCtorObject<2> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 2
            + 0) as u16,
        other: 2,
        tag: 0,
    },
    m_objs: [
        (((0 as usize) << 1) | 1) as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__0_value
        ) as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default:
    *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value
) as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl: *mut leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDecl_default___closed__1_value
)
    as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1:
    *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState:
    *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanArrayObject<0> = leanh::LeanArrayObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanClosureObject<1> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*1) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 3, m_num_fixed: 1, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanStringObject<18> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 18, m_capacity: 18, m_length: 17, m_data: [99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 68, 101, 99, 108, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value) as *mut leanh::LeanObject,15353829308266697735 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value) as *mut leanh::LeanObject,10267394960704184689 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject,957638054029145619 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_value:
    leanh::LeanStringObject<34> = leanh::LeanStringObject {
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
        73, 110, 118, 97, 108, 105, 100, 32, 99, 98, 118, 32, 115, 105, 109, 112, 114, 111, 99, 32,
        100, 101, 99, 108, 97, 114, 97, 116, 105, 111, 110, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_value:
    leanh::LeanStringObject<40> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 40,
    m_capacity: 40,
    m_length: 39,
    m_data: [
        96, 58, 32, 73, 116, 32, 105, 115, 32, 100, 101, 99, 108, 97, 114, 101, 100, 32, 105, 110,
        32, 97, 110, 32, 105, 109, 112, 111, 114, 116, 101, 100, 32, 109, 111, 100, 117, 108, 101,
        0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0_value:
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
        85, 110, 107, 110, 111, 119, 110, 32, 99, 111, 110, 115, 116, 97, 110, 116, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1_value:
    leanh::LeanStringObject<2> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 2,
    m_capacity: 2,
    m_length: 1,
    m_data: [96, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2_value:
    leanh::LeanStringObject<14> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 14,
    m_capacity: 14,
    m_length: 13,
    m_data: [67, 98, 118, 32, 115, 105, 109, 112, 114, 111, 99, 32, 96, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3_value:
    leanh::LeanStringObject<58> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 58,
    m_capacity: 58,
    m_length: 57,
    m_data: [
        96, 32, 104, 97, 115, 32, 97, 110, 32, 117, 110, 101, 120, 112, 101, 99, 116, 101, 100, 32,
        116, 121, 112, 101, 58, 32, 69, 120, 112, 101, 99, 116, 101, 100, 32, 96, 83, 105, 109,
        112, 114, 111, 99, 96, 44, 32, 98, 117, 116, 32, 102, 111, 117, 110, 100, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value:
    leanh::LeanStringObject<4> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [83, 121, 109, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value:
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
    m_data: [83, 105, 109, 112, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [83, 105, 109, 112, 114, 111, 99, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6_value)
        as *mut leanh::LeanObject;
pub static mut l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 1, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_ as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 2, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value: leanh::LeanStringObject<14> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 14, m_capacity: 14, m_length: 13, m_data: [99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 69, 120, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject,10798776719031711899 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static mut l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1_value:
    leanh::LeanStringObject<42> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 42,
    m_capacity: 42,
    m_length: 41,
    m_data: [
        96, 32, 100, 111, 101, 115, 32, 110, 111, 116, 32, 104, 97, 118, 101, 32, 97, 32, 91, 99,
        98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 93, 32, 97, 116, 116, 114, 105, 98, 117,
        116, 101, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0_value:
    leanh::LeanStringObject<37> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 37,
    m_capacity: 37,
    m_length: 36,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111,
        99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117, 116, 101, 58, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2_value:
    leanh::LeanStringObject<23> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 23,
    m_capacity: 23,
    m_length: 22,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 99, 98, 118, 32, 115, 105, 109, 112, 114,
        111, 99, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once:
    leanh::LeanOnceCell = leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value:
    leanh::LeanStringObject<7> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 7,
    m_capacity: 7,
    m_length: 6,
    m_data: [80, 97, 114, 115, 101, 114, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value:
    leanh::LeanStringObject<8> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 8,
    m_capacity: 8,
    m_length: 7,
    m_data: [115, 105, 109, 112, 80, 114, 101, 0],
};
static mut l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_2:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value
        ) as *mut leanh::LeanObject,
        18344149449936419494 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value_aux_2)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__1_value)
            as *mut leanh::LeanObject,
        10994783280459430853 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 69, 118, 97, 108, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value)
        as *mut leanh::LeanObject;
static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_0:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value
        ) as *mut leanh::LeanObject,
        11948124481539785030 as *mut leanh::LeanObject,
    ],
};
static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_0)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__0_value)
            as *mut leanh::LeanObject,
        8018486133748762727 as *mut leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value_aux_1)
            as *mut leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__3_value)
            as *mut leanh::LeanObject,
        9575030279827742198 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value:
    leanh::LeanStringObject<15> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 15,
    m_capacity: 15,
    m_length: 14,
    m_data: [
        99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 65, 116, 116, 114, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value:
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
        core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__0_value)
            as *mut leanh::LeanObject,
        16051190869406148755 as *mut leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value)
        as *mut leanh::LeanObject;
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5: *mut leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once: leanh::LeanOnceCell =
    leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6: *mut leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0_value:
    leanh::LeanStringObject<45> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 45,
    m_capacity: 45,
    m_length: 44,
    m_data: [
        73, 110, 118, 97, 108, 105, 100, 32, 96, 91, 98, 117, 105, 108, 116, 105, 110, 95, 99, 98,
        118, 95, 115, 105, 109, 112, 114, 111, 99, 93, 96, 32, 97, 116, 116, 114, 105, 98, 117,
        116, 101, 58, 32, 96, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0_value)
        as *mut leanh::LeanObject;
pub static l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1_value:
    leanh::LeanStringObject<31> = leanh::LeanStringObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 31,
    m_capacity: 31,
    m_length: 30,
    m_data: [
        96, 32, 105, 115, 32, 110, 111, 116, 32, 97, 32, 98, 117, 105, 108, 116, 105, 110, 32, 99,
        98, 118, 32, 115, 105, 109, 112, 114, 111, 99, 0,
    ],
};
static mut l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1:
    *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1_value)
        as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value: leanh::LeanStringObject<25> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 25, m_capacity: 25, m_length: 24, m_data: [97, 100, 100, 67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value) as *mut leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value) as *mut leanh::LeanObject,15353829308266697735 as *mut leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_3: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value) as *mut leanh::LeanObject,10267394960704184689 as *mut leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value_aux_3) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__0_value) as *mut leanh::LeanObject,6003695740450450990 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [100, 101, 99, 108, 97, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__3_value) as *mut leanh::LeanObject,13812150225987229964 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,11079354408986465895 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value) as *mut leanh::LeanObject,10352885018404983386 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,13556645696814629918 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value) as *mut leanh::LeanObject,18261494228143523011 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value) as *mut leanh::LeanObject,16489734963670585437 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanStringObject<11> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [67, 98, 118, 83, 105, 109, 112, 114, 111, 99, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,12407417592433210982 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,12892057386245800815 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value) as *mut leanh::LeanObject,15145536329247969282 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__11_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,16589845286632061270 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__12_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value) as *mut leanh::LeanObject,6043417103073948971 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__13_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value) as *mut leanh::LeanObject,17533562274006238933 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [105, 110, 105, 116, 70, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__14_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__15_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5365088781143191932 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [95, 64, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__16_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__17_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,9828581618502621557 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__18_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value) as *mut leanh::LeanObject,5101289465096299744 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__19_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,7567814071569202380 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__20_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value) as *mut leanh::LeanObject,9639771884416708745 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__21_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value) as *mut leanh::LeanObject,18216063199918047263 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__22_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,15495558869503749628 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 735115364 as usize) << 1) | 1) as *mut leanh::LeanObject,13141693454369361791 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanStringObject<8> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [95, 104, 121, 103, 67, 116, 120, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__24_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,6888186287691614996 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [95, 104, 121, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__26_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,14815927516600203072 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 2 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__28_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,((( 2 as usize) << 1) | 1) as *mut leanh::LeanObject,17305007706802526065 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanStringObject<29> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 29, m_capacity: 29, m_length: 28, m_data: [67, 98, 118, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<4> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 8) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__29_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1_value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__30_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,1 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*3 + 0) as u16, other: 3, tag: 0 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__31_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value: leanh::LeanStringObject<44> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 44, m_capacity: 44, m_length: 43, m_data: [78, 111, 116, 32, 105, 109, 112, 108, 101, 109, 101, 110, 116, 101, 100, 32, 121, 101, 116, 44, 32, 91, 45, 98, 117, 105, 108, 116, 105, 110, 95, 99, 98, 118, 95, 115, 105, 109, 112, 114, 111, 99, 93, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value: leanh::LeanClosureObject<0> = leanh::LeanClosureObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed as *const core::ffi::c_void, m_arity: 4, m_num_fixed: 0, m_objs: [] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value: leanh::LeanStringObject<22> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 22, m_capacity: 22, m_length: 21, m_data: [99, 98, 118, 83, 105, 109, 112, 114, 111, 99, 66, 117, 105, 108, 116, 105, 110, 65, 116, 116, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value) as *mut leanh::LeanObject,5413429062682062903 as *mut leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value: leanh::LeanStringObject<37> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 37, m_capacity: 37, m_length: 36, m_data: [66, 117, 105, 108, 116, 105, 110, 32, 99, 98, 118, 32, 115, 105, 109, 112, 108, 105, 102, 105, 99, 97, 116, 105, 111, 110, 32, 112, 114, 111, 99, 101, 100, 117, 114, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [32, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2: f64 = 0.0;
pub static l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_value: leanh::LeanStringObject<54> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 54, m_capacity: 54, m_length: 53, m_data: [60, 101, 120, 99, 101, 112, 116, 105, 111, 110, 32, 116, 104, 114, 111, 119, 110, 32, 119, 104, 105, 108, 101, 32, 112, 114, 111, 100, 117, 99, 105, 110, 103, 32, 116, 114, 97, 99, 101, 32, 110, 111, 100, 101, 32, 109, 101, 115, 115, 97, 103, 101, 62, 0]};
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5: f64 = 0.0;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 114, 111, 99, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2_value: leanh::LeanStringObject<3> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 3, m_capacity: 3, m_length: 2, m_data: [58, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4_value: leanh::LeanStringObject<7> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 7, m_capacity: 7, m_length: 6, m_data: [58, 32, 100, 111, 110, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6_value: leanh::LeanStringObject<12> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [58, 32, 110, 111, 32, 99, 104, 97, 110, 103, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8_value: leanh::LeanStringObject<2> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 2, m_capacity: 2, m_length: 1, m_data: [58, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10_value: leanh::LeanStringObject<5> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [10, 61, 61, 62, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4_value) as *mut leanh::LeanObject,4034176598647545331 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5_value) as *mut leanh::LeanObject,13806531830123099675 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0_value) as *mut leanh::LeanObject,11948124481539785030 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,15449383196166861506 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value) as *mut leanh::LeanObject,15353829308266697735 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__3_value) as *mut leanh::LeanObject,10267394960704184689 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value: leanh::LeanStringObject<4> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [99, 98, 118, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value: leanh::LeanStringObject<9> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [115, 105, 109, 112, 114, 111, 99, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value) as *mut leanh::LeanObject;
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_0: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1_value) as *mut leanh::LeanObject,142734480563613395 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_1: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_0) as *mut leanh::LeanObject,core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__2_value) as *mut leanh::LeanObject,15847151208953044930 as *mut leanh::LeanObject] };
static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_2: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__3_value) as *mut leanh::LeanObject,9691683737394756276 as *mut leanh::LeanObject] };
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value_aux_2) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__4_value) as *mut leanh::LeanObject,1605478173386622269 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6_value: leanh::LeanStringObject<1> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 1, m_capacity: 1, m_length: 0, m_data: [0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value: leanh::LeanStringObject<6> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 114, 97, 99, 101, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value: leanh::LeanCtorObject<3> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__7_value) as *mut leanh::LeanObject,14231257465488249300 as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10: f64 = 0.0;
pub static l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value:
    leanh::LeanCtorObject<1> = leanh::LeanCtorObject {
    m_header: leanh::LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<leanh::LeanObject>()
            + core::mem::size_of::<*mut leanh::LeanObject>() * 0
            + 8) as u16,
        other: 0,
        tag: 0,
    },
    m_objs: [0 as *mut leanh::LeanObject],
};
static mut l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0: *mut leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0_value)
        as *mut leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(
    mut v_x_4054_: u8,
) -> *mut leanh::LeanObject {
    match v_x_4054_ {
        0 => {
            let mut v___x_4055_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4055_ = leanh::lean_unsigned_to_nat(0);
            return v___x_4055_;
        }
        1 => {
            let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4056_ = leanh::lean_unsigned_to_nat(1);
            return v___x_4056_;
        }
        _ => {
            let mut v___x_4057_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4057_ = leanh::lean_unsigned_to_nat(2);
            return v___x_4057_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx___boxed(
    mut v_x_4058_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_boxed_4059_: u8 = 0;
    let mut v_res_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_boxed_4059_ = (leanh::lean_unbox(v_x_4058_) as u8);
    v_res_4060_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_boxed_4059_);
    return v_res_4060_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(
    mut v_x_4061_: u8,
) -> *mut leanh::LeanObject {
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4062_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_4061_);
    return v___x_4062_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx___boxed(
    mut v_x_4063_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_4__boxed_4064_: u8 = 0;
    let mut v_res_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_4__boxed_4064_ = (leanh::lean_unbox(v_x_4063_) as u8);
    v_res_4065_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_toCtorIdx(v_x_4__boxed_4064_);
    return v_res_4065_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(
    mut v_k_4066_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4066_);
    return v_k_4066_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg___boxed(
    mut v_k_4067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4068_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___redArg(v_k_4067_);
    leanh::lean_dec(v_k_4067_);
    return v_res_4068_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(
    mut v_motive_4069_: *mut leanh::LeanObject,
    mut v_ctorIdx_4070_: *mut leanh::LeanObject,
    mut v_t_4071_: u8,
    mut v_h_4072_: *mut leanh::LeanObject,
    mut v_k_4073_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_k_4073_);
    return v_k_4073_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim___boxed(
    mut v_motive_4074_: *mut leanh::LeanObject,
    mut v_ctorIdx_4075_: *mut leanh::LeanObject,
    mut v_t_4076_: *mut leanh::LeanObject,
    mut v_h_4077_: *mut leanh::LeanObject,
    mut v_k_4078_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4079_: u8 = 0;
    let mut v_res_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4079_ = (leanh::lean_unbox(v_t_4076_) as u8);
    v_res_4080_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorElim(
        v_motive_4074_,
        v_ctorIdx_4075_,
        v_t_boxed_4079_,
        v_h_4077_,
        v_k_4078_,
    );
    leanh::lean_dec(v_k_4078_);
    leanh::lean_dec(v_ctorIdx_4075_);
    return v_res_4080_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(
    mut v_pre_4081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_pre_4081_);
    return v_pre_4081_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg___boxed(
    mut v_pre_4082_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4083_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___redArg(v_pre_4082_);
    leanh::lean_dec(v_pre_4082_);
    return v_res_4083_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(
    mut v_motive_4084_: *mut leanh::LeanObject,
    mut v_t_4085_: u8,
    mut v_h_4086_: *mut leanh::LeanObject,
    mut v_pre_4087_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_pre_4087_);
    return v_pre_4087_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim___boxed(
    mut v_motive_4088_: *mut leanh::LeanObject,
    mut v_t_4089_: *mut leanh::LeanObject,
    mut v_h_4090_: *mut leanh::LeanObject,
    mut v_pre_4091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4092_: u8 = 0;
    let mut v_res_4093_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4092_ = (leanh::lean_unbox(v_t_4089_) as u8);
    v_res_4093_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_pre_elim(
        v_motive_4088_,
        v_t_boxed_4092_,
        v_h_4090_,
        v_pre_4091_,
    );
    leanh::lean_dec(v_pre_4091_);
    return v_res_4093_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(
    mut v_eval_4094_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_eval_4094_);
    return v_eval_4094_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg___boxed(
    mut v_eval_4095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4096_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___redArg(v_eval_4095_);
    leanh::lean_dec(v_eval_4095_);
    return v_res_4096_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(
    mut v_motive_4097_: *mut leanh::LeanObject,
    mut v_t_4098_: u8,
    mut v_h_4099_: *mut leanh::LeanObject,
    mut v_eval_4100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_eval_4100_);
    return v_eval_4100_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim___boxed(
    mut v_motive_4101_: *mut leanh::LeanObject,
    mut v_t_4102_: *mut leanh::LeanObject,
    mut v_h_4103_: *mut leanh::LeanObject,
    mut v_eval_4104_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4105_: u8 = 0;
    let mut v_res_4106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4105_ = (leanh::lean_unbox(v_t_4102_) as u8);
    v_res_4106_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_eval_elim(
        v_motive_4101_,
        v_t_boxed_4105_,
        v_h_4103_,
        v_eval_4104_,
    );
    leanh::lean_dec(v_eval_4104_);
    return v_res_4106_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(
    mut v_post_4107_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_post_4107_);
    return v_post_4107_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg___boxed(
    mut v_post_4108_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4109_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___redArg(v_post_4108_);
    leanh::lean_dec(v_post_4108_);
    return v_res_4109_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(
    mut v_motive_4110_: *mut leanh::LeanObject,
    mut v_t_4111_: u8,
    mut v_h_4112_: *mut leanh::LeanObject,
    mut v_post_4113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc(v_post_4113_);
    return v_post_4113_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim___boxed(
    mut v_motive_4114_: *mut leanh::LeanObject,
    mut v_t_4115_: *mut leanh::LeanObject,
    mut v_h_4116_: *mut leanh::LeanObject,
    mut v_post_4117_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_t_boxed_4118_: u8 = 0;
    let mut v_res_4119_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_t_boxed_4118_ = (leanh::lean_unbox(v_t_4115_) as u8);
    v_res_4119_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_post_elim(
        v_motive_4114_,
        v_t_boxed_4118_,
        v_h_4116_,
        v_post_4117_,
    );
    leanh::lean_dec(v_post_4117_);
    return v_res_4119_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default() -> u8 {
    let mut v___x_4120_: u8 = 0;
    v___x_4120_ = 0;
    return v___x_4120_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase() -> u8 {
    let mut v___x_4121_: u8 = 0;
    v___x_4121_ = 0;
    return v___x_4121_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(
    mut v_x_4122_: u8,
    mut v_y_4123_: u8,
) -> u8 {
    let mut v___x_4124_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: u8 = 0;
    v___x_4124_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_x_4122_);
    v___x_4125_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocPhase_ctorIdx(v_y_4123_);
    v___x_4126_ = lean_nat_dec_eq(v___x_4124_, v___x_4125_);
    leanh::lean_dec(v___x_4125_);
    leanh::lean_dec(v___x_4124_);
    return v___x_4126_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq___boxed(
    mut v_x_4127_: *mut leanh::LeanObject,
    mut v_y_4128_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_17__boxed_4129_: u8 = 0;
    let mut v_y_18__boxed_4130_: u8 = 0;
    let mut v_res_4131_: u8 = 0;
    let mut v_r_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_17__boxed_4129_ = (leanh::lean_unbox(v_x_4127_) as u8);
    v_y_18__boxed_4130_ = (leanh::lean_unbox(v_y_4128_) as u8);
    v_res_4131_ =
        l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocPhase_beq(v_x_17__boxed_4129_, v_y_18__boxed_4130_);
    v_r_4132_ = leanh::lean_box((v_res_4131_) as usize);
    return v_r_4132_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(mut v_x_4135_: u8) -> u64 {
    match v_x_4135_ {
        0 => {
            let mut v___x_4136_: u64 = 0;
            v___x_4136_ = 0u64;
            return v___x_4136_;
        }
        1 => {
            let mut v___x_4137_: u64 = 0;
            v___x_4137_ = 1u64;
            return v___x_4137_;
        }
        _ => {
            let mut v___x_4138_: u64 = 0;
            v___x_4138_ = 2u64;
            return v___x_4138_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash___boxed(
    mut v_x_4139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_40__boxed_4140_: u8 = 0;
    let mut v_res_4141_: u64 = 0;
    let mut v_r_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_40__boxed_4140_ = (leanh::lean_unbox(v_x_4139_) as u8);
    v_res_4141_ = l_Lean_Meta_Tactic_Cbv_instHashableCbvSimprocPhase_hash(v_x_40__boxed_4140_);
    v_r_4142_ = leanh::lean_box_uint64(v_res_4141_);
    return v_r_4142_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4154_ = leanh::lean_unsigned_to_nat(2);
    v___x_4155_ = lean_nat_to_int(v___x_4154_);
    return v___x_4155_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4156_ = leanh::lean_unsigned_to_nat(1);
    v___x_4157_ = lean_nat_to_int(v___x_4156_);
    return v___x_4157_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(
    mut v_x_4158_: u8,
    mut v_prec_4159_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4164_: u8 = 0;
    let mut v___x_4165_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4170_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: u8 = 0;
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: u8 = 0;
    let mut v___x_4179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4182_: u8 = 0;
    let mut v___x_4183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: u8 = 0;
    let mut v___x_4187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4190_: u8 = 0;
    let mut v___x_4191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => match v_x_4158_ {
                0 => {
                    v___x_4181_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4182_ = lean_nat_dec_le(v___x_4181_, v_prec_4159_);
                    if v___x_4182_ == 0 {
                        v___x_4183_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once), _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
                        v___y_4161_ = v___x_4183_;
                        state = 1;
                        continue;
                    } else {
                        v___x_4184_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once), _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
                        v___y_4161_ = v___x_4184_;
                        state = 1;
                        continue;
                    }
                }
                1 => {
                    v___x_4185_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4186_ = lean_nat_dec_le(v___x_4185_, v_prec_4159_);
                    if v___x_4186_ == 0 {
                        v___x_4187_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once), _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
                        v___y_4168_ = v___x_4187_;
                        state = 2;
                        continue;
                    } else {
                        v___x_4188_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once), _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
                        v___y_4168_ = v___x_4188_;
                        state = 2;
                        continue;
                    }
                }
                _ => {
                    v___x_4189_ = leanh::lean_unsigned_to_nat(1024);
                    v___x_4190_ = lean_nat_dec_le(v___x_4189_, v_prec_4159_);
                    if v___x_4190_ == 0 {
                        v___x_4191_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6_once), _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__6);
                        v___y_4175_ = v___x_4191_;
                        state = 3;
                        continue;
                    } else {
                        v___x_4192_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7_once), _init_l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__7);
                        v___y_4175_ = v___x_4192_;
                        state = 3;
                        continue;
                    }
                }
            },
            1 => {
                v___x_4162_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__1;
                leanh::lean_inc(v___y_4161_);
                v___x_4163_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4163_, 0, v___y_4161_);
                leanh::lean_ctor_set(v___x_4163_, 1, v___x_4162_);
                v___x_4164_ = 0;
                v___x_4165_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4165_, 0, v___x_4163_);
                leanh::lean_ctor_set_uint8(
                    v___x_4165_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4164_,
                );
                v___x_4166_ = l_Repr_addAppParen(v___x_4165_, v_prec_4159_);
                return v___x_4166_;
            }
            2 => {
                v___x_4169_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__3;
                leanh::lean_inc(v___y_4168_);
                v___x_4170_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4170_, 0, v___y_4168_);
                leanh::lean_ctor_set(v___x_4170_, 1, v___x_4169_);
                v___x_4171_ = 0;
                v___x_4172_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4172_, 0, v___x_4170_);
                leanh::lean_ctor_set_uint8(
                    v___x_4172_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4171_,
                );
                v___x_4173_ = l_Repr_addAppParen(v___x_4172_, v_prec_4159_);
                return v___x_4173_;
            }
            3 => {
                v___x_4176_ = l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___closed__5;
                leanh::lean_inc(v___y_4175_);
                v___x_4177_ = leanh::lean_alloc_ctor(4, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4177_, 0, v___y_4175_);
                leanh::lean_ctor_set(v___x_4177_, 1, v___x_4176_);
                v___x_4178_ = 0;
                v___x_4179_ = leanh::lean_alloc_ctor(6, 1, (1) as u32);
                leanh::lean_ctor_set(v___x_4179_, 0, v___x_4177_);
                leanh::lean_ctor_set_uint8(
                    v___x_4179_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    v___x_4178_,
                );
                v___x_4180_ = l_Repr_addAppParen(v___x_4179_, v_prec_4159_);
                return v___x_4180_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr___boxed(
    mut v_x_4193_: *mut leanh::LeanObject,
    mut v_prec_4194_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_177__boxed_4195_: u8 = 0;
    let mut v_res_4196_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_177__boxed_4195_ = (leanh::lean_unbox(v_x_4193_) as u8);
    v_res_4196_ =
        l_Lean_Meta_Tactic_Cbv_instReprCbvSimprocPhase_repr(v_x_177__boxed_4195_, v_prec_4194_);
    leanh::lean_dec(v_prec_4194_);
    return v_res_4196_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_4212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4213_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4212_ = leanh::lean_box(0);
    v___x_4213_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__6;
    v___x_4214_ = l_Lean_mkConst(v___x_4213_, v___x_4212_);
    return v___x_4214_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10()
-> *mut leanh::LeanObject {
    let mut v___x_4223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4223_ = leanh::lean_box(0);
    v___x_4224_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__9;
    v___x_4225_ = l_Lean_mkConst(v___x_4224_, v___x_4223_);
    return v___x_4225_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13()
-> *mut leanh::LeanObject {
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4234_ = leanh::lean_box(0);
    v___x_4235_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__12;
    v___x_4236_ = l_Lean_mkConst(v___x_4235_, v___x_4234_);
    return v___x_4236_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(
    mut v_x_4237_: u8,
) -> *mut leanh::LeanObject {
    match v_x_4237_ {
        0 => {
            let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4238_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once
                ),
                _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7,
            );
            return v___x_4238_;
        }
        1 => {
            let mut v___x_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4239_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once
                ),
                _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10,
            );
            return v___x_4239_;
        }
        _ => {
            let mut v___x_4240_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4240_ = leanh::lean_obj_once(
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13
                ),
                core::ptr::addr_of_mut!(
                    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once
                ),
                _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13,
            );
            return v___x_4240_;
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___boxed(
    mut v_x_4241_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_196__boxed_4242_: u8 = 0;
    let mut v_res_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_196__boxed_4242_ = (leanh::lean_unbox(v_x_4241_) as u8);
    v_res_4243_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0(v_x_196__boxed_4242_);
    return v_res_4243_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4251_ = leanh::lean_box(0);
    v___x_4252_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__1;
    v___x_4253_ = l_Lean_mkConst(v___x_4252_, v___x_4251_);
    return v___x_4253_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4254_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2_once),
        _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__2,
    );
    v___f_4255_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__0;
    v___x_4256_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4256_, 0, v___f_4255_);
    leanh::lean_ctor_set(v___x_4256_, 1, v___x_4254_);
    return v___x_4256_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase()
-> *mut leanh::LeanObject {
    let mut v___x_4257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4257_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3_once),
        _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___closed__3,
    );
    return v___x_4257_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(
    mut v_e_u2081_4266_: *mut leanh::LeanObject,
    mut v_e_u2082_4267_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_toCbvSimprocOLeanEntry_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCbvSimprocOLeanEntry_4269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4272_: u8 = 0;
    v_toCbvSimprocOLeanEntry_4268_ = leanh::lean_ctor_get(v_e_u2081_4266_, 0);
    v_toCbvSimprocOLeanEntry_4269_ = leanh::lean_ctor_get(v_e_u2082_4267_, 0);
    v_declName_4270_ = leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_4268_, 0);
    v_declName_4271_ = leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_4269_, 0);
    v___x_4272_ = lean_name_eq(v_declName_4270_, v_declName_4271_);
    return v___x_4272_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0___boxed(
    mut v_e_u2081_4273_: *mut leanh::LeanObject,
    mut v_e_u2082_4274_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4275_: u8 = 0;
    let mut v_r_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4275_ =
        l_Lean_Meta_Tactic_Cbv_instBEqCbvSimprocEntry___lam__0(v_e_u2081_4273_, v_e_u2082_4274_);
    leanh::lean_dec_ref(v_e_u2082_4274_);
    leanh::lean_dec_ref(v_e_u2081_4273_);
    v_r_4276_ = leanh::lean_box((v_res_4275_) as usize);
    return v_r_4276_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_instToFormatCbvSimprocEntry___lam__0(
    mut v_e_4279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toCbvSimprocOLeanEntry_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4282_: u8 = 0;
    let mut v___x_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4284_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toCbvSimprocOLeanEntry_4280_ = leanh::lean_ctor_get(v_e_4279_, 0);
    leanh::lean_inc_ref(v_toCbvSimprocOLeanEntry_4280_);
    leanh::lean_dec_ref(v_e_4279_);
    v_declName_4281_ = leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_4280_, 0);
    leanh::lean_inc(v_declName_4281_);
    leanh::lean_dec_ref(v_toCbvSimprocOLeanEntry_4280_);
    v___x_4282_ = 1;
    v___x_4283_ = l_Lean_Name_toString(v_declName_4281_, v___x_4282_);
    v___x_4284_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4284_, 0, v___x_4283_);
    return v___x_4284_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4287_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4287_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__0);
    v___x_4289_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4289_, 0, v___x_4288_);
    return v___x_4289_;
}
pub unsafe fn l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(
    mut v_00_u03b2_4290_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1_once), _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0___closed__1);
    return v___x_4291_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4292_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4292_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4292_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_4293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4293_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__0,
    );
    v___x_4294_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_4294_, 0, v___x_4293_);
    return v___x_4294_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4295_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4295_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default_spec__0(leanh::lean_box(0));
    return v___x_4295_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4298_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4296_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__2,
    );
    v___x_4297_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__1,
    );
    v___x_4298_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_4298_, 0, v___x_4297_);
    leanh::lean_ctor_set(v___x_4298_, 1, v___x_4297_);
    leanh::lean_ctor_set(v___x_4298_, 2, v___x_4297_);
    leanh::lean_ctor_set(v___x_4298_, 3, v___x_4296_);
    leanh::lean_ctor_set(v___x_4298_, 4, v___x_4296_);
    return v___x_4298_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default()
-> *mut leanh::LeanObject {
    let mut v___x_4299_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4299_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3,
    );
    return v___x_4299_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs()
-> *mut leanh::LeanObject {
    let mut v___x_4300_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4300_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
    return v___x_4300_;
}
pub unsafe fn _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4301_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4301_ = l_Lean_Meta_DiscrTree_instInhabited(leanh::lean_box(0));
    return v___x_4301_;
}
pub unsafe fn l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(
    mut v_msg_4302_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4304_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4303_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0), core::ptr::addr_of_mut!(l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0_once), _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7___closed__0);
    v___x_4304_ = lean_panic_fn_borrowed(v___x_4303_, v_msg_4302_);
    return v___x_4304_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(
    mut v_x_4305_: *mut leanh::LeanObject,
    mut v_x_4306_: *mut leanh::LeanObject,
    mut v_x_4307_: *mut leanh::LeanObject,
    mut v_x_4308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4313_: u8 = 0;
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: u8 = 0;
    let mut v___x_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: u8 = 0;
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4325_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4334_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4309_ = leanh::lean_ctor_get(v_x_4305_, 0);
                v_vs_4310_ = leanh::lean_ctor_get(v_x_4305_, 1);
                v_isSharedCheck_4334_ = (!leanh::lean_is_exclusive(v_x_4305_)) as u8;
                if v_isSharedCheck_4334_ == 0 {
                    v___x_4312_ = v_x_4305_;
                    v_isShared_4313_ = v_isSharedCheck_4334_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4310_);
                    leanh::lean_inc(v_ks_4309_);
                    leanh::lean_dec(v_x_4305_);
                    v___x_4312_ = leanh::lean_box(0);
                    v_isShared_4313_ = v_isSharedCheck_4334_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4314_ = lean_array_get_size(v_ks_4309_);
                v___x_4315_ = lean_nat_dec_lt(v_x_4306_, v___x_4314_);
                if v___x_4315_ == 0 {
                    leanh::lean_dec(v_x_4306_);
                    v___x_4316_ = lean_array_push(v_ks_4309_, v_x_4307_);
                    v___x_4317_ = lean_array_push(v_vs_4310_, v_x_4308_);
                    if v_isShared_4313_ == 0 {
                        leanh::lean_ctor_set(v___x_4312_, 1, v___x_4317_);
                        leanh::lean_ctor_set(v___x_4312_, 0, v___x_4316_);
                        v___x_4319_ = v___x_4312_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4320_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4316_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4320_, 1, v___x_4317_);
                        v___x_4319_ = v_reuseFailAlloc_4320_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4321_ = lean_array_fget_borrowed(v_ks_4309_, v_x_4306_);
                    v___x_4322_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4307_, v_k_x27_4321_);
                    if v___x_4322_ == 0 {
                        if v_isShared_4313_ == 0 {
                            v___x_4324_ = v___x_4312_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4328_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v_ks_4309_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_vs_4310_);
                            v___x_4324_ = v_reuseFailAlloc_4328_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4329_ = lean_array_fset(v_ks_4309_, v_x_4306_, v_x_4307_);
                        v___x_4330_ = lean_array_fset(v_vs_4310_, v_x_4306_, v_x_4308_);
                        leanh::lean_dec(v_x_4306_);
                        if v_isShared_4313_ == 0 {
                            leanh::lean_ctor_set(v___x_4312_, 1, v___x_4330_);
                            leanh::lean_ctor_set(v___x_4312_, 0, v___x_4329_);
                            v___x_4332_ = v___x_4312_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4333_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 0, v___x_4329_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4333_, 1, v___x_4330_);
                            v___x_4332_ = v_reuseFailAlloc_4333_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4319_;
            }
            3 => {
                v___x_4325_ = leanh::lean_unsigned_to_nat(1);
                v___x_4326_ = lean_nat_add(v_x_4306_, v___x_4325_);
                leanh::lean_dec(v_x_4306_);
                v_x_4305_ = v___x_4324_;
                v_x_4306_ = v___x_4326_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4332_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(
    mut v_n_4335_: *mut leanh::LeanObject,
    mut v_k_4336_: *mut leanh::LeanObject,
    mut v_v_4337_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4339_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4338_ = leanh::lean_unsigned_to_nat(0);
    v___x_4339_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(v_n_4335_, v___x_4338_, v_k_4336_, v_v_4337_);
    return v___x_4339_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0()
-> usize {
    let mut v___x_4340_: usize = 0;
    let mut v___x_4341_: usize = 0;
    let mut v___x_4342_: usize = 0;
    v___x_4340_ = 5usize;
    v___x_4341_ = 1usize;
    v___x_4342_ = lean_usize_shift_left(v___x_4341_, v___x_4340_);
    return v___x_4342_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1()
-> usize {
    let mut v___x_4343_: usize = 0;
    let mut v___x_4344_: usize = 0;
    let mut v___x_4345_: usize = 0;
    v___x_4343_ = 1usize;
    v___x_4344_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__0);
    v___x_4345_ = lean_usize_sub(v___x_4344_, v___x_4343_);
    return v___x_4345_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_4346_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4346_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4346_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(
    mut v_x_4347_: *mut leanh::LeanObject,
    mut v_x_4348_: usize,
    mut v_x_4349_: usize,
    mut v_x_4350_: *mut leanh::LeanObject,
    mut v_x_4351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4353_: usize = 0;
    let mut v___x_4354_: usize = 0;
    let mut v___x_4355_: usize = 0;
    let mut v___x_4356_: usize = 0;
    let mut v_j_4357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4359_: u8 = 0;
    let mut v___x_4361_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4362_: u8 = 0;
    let mut v_v_4363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4376_: u8 = 0;
    let mut v___x_4377_: u8 = 0;
    let mut v___x_4378_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4383_: u8 = 0;
    let mut v_node_4384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4387_: u8 = 0;
    let mut v___x_4388_: usize = 0;
    let mut v___x_4389_: usize = 0;
    let mut v___x_4390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4394_: u8 = 0;
    let mut v___x_4395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4396_: u8 = 0;
    let mut v_unused_4397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4402_: u8 = 0;
    let mut v___x_4404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4407_: u8 = 0;
    let mut v_ks_4408_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4413_: usize = 0;
    let mut v___x_4414_: u8 = 0;
    let mut v___x_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: u8 = 0;
    let mut v_reuseFailAlloc_4418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4419_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4347_) == 0 {
                    v_es_4352_ = leanh::lean_ctor_get(v_x_4347_, 0);
                    v___x_4353_ = 5usize;
                    v___x_4354_ = 1usize;
                    v___x_4355_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
                    v___x_4356_ = lean_usize_land(v_x_4348_, v___x_4355_);
                    v_j_4357_ = lean_usize_to_nat(v___x_4356_);
                    v___x_4358_ = lean_array_get_size(v_es_4352_);
                    v___x_4359_ = lean_nat_dec_lt(v_j_4357_, v___x_4358_);
                    if v___x_4359_ == 0 {
                        leanh::lean_dec(v_j_4357_);
                        leanh::lean_dec(v_x_4351_);
                        leanh::lean_dec(v_x_4350_);
                        return v_x_4347_;
                    } else {
                        leanh::lean_inc_ref(v_es_4352_);
                        v_isSharedCheck_4396_ = (!leanh::lean_is_exclusive(v_x_4347_)) as u8;
                        if v_isSharedCheck_4396_ == 0 {
                            v_unused_4397_ = leanh::lean_ctor_get(v_x_4347_, 0);
                            leanh::lean_dec(v_unused_4397_);
                            v___x_4361_ = v_x_4347_;
                            v_isShared_4362_ = v_isSharedCheck_4396_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4347_);
                            v___x_4361_ = leanh::lean_box(0);
                            v_isShared_4362_ = v_isSharedCheck_4396_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4398_ = leanh::lean_ctor_get(v_x_4347_, 0);
                    v_vs_4399_ = leanh::lean_ctor_get(v_x_4347_, 1);
                    v_isSharedCheck_4419_ = (!leanh::lean_is_exclusive(v_x_4347_)) as u8;
                    if v_isSharedCheck_4419_ == 0 {
                        v___x_4401_ = v_x_4347_;
                        v_isShared_4402_ = v_isSharedCheck_4419_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4399_);
                        leanh::lean_inc(v_ks_4398_);
                        leanh::lean_dec(v_x_4347_);
                        v___x_4401_ = leanh::lean_box(0);
                        v_isShared_4402_ = v_isSharedCheck_4419_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4363_ = lean_array_fget(v_es_4352_, v_j_4357_);
                v___x_4364_ = leanh::lean_box(0);
                v_xs_x27_4365_ = lean_array_fset(v_es_4352_, v_j_4357_, v___x_4364_);
                match leanh::lean_obj_tag(v_v_4363_) {
                    0 => {
                        v_key_4372_ = leanh::lean_ctor_get(v_v_4363_, 0);
                        v_val_4373_ = leanh::lean_ctor_get(v_v_4363_, 1);
                        v_isSharedCheck_4383_ = (!leanh::lean_is_exclusive(v_v_4363_)) as u8;
                        if v_isSharedCheck_4383_ == 0 {
                            v___x_4375_ = v_v_4363_;
                            v_isShared_4376_ = v_isSharedCheck_4383_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4373_);
                            leanh::lean_inc(v_key_4372_);
                            leanh::lean_dec(v_v_4363_);
                            v___x_4375_ = leanh::lean_box(0);
                            v_isShared_4376_ = v_isSharedCheck_4383_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4384_ = leanh::lean_ctor_get(v_v_4363_, 0);
                        v_isSharedCheck_4394_ = (!leanh::lean_is_exclusive(v_v_4363_)) as u8;
                        if v_isSharedCheck_4394_ == 0 {
                            v___x_4386_ = v_v_4363_;
                            v_isShared_4387_ = v_isSharedCheck_4394_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4384_);
                            leanh::lean_dec(v_v_4363_);
                            v___x_4386_ = leanh::lean_box(0);
                            v_isShared_4387_ = v_isSharedCheck_4394_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4395_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4395_, 0, v_x_4350_);
                        leanh::lean_ctor_set(v___x_4395_, 1, v_x_4351_);
                        v___y_4367_ = v___x_4395_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4368_ = lean_array_fset(v_xs_x27_4365_, v_j_4357_, v___y_4367_);
                leanh::lean_dec(v_j_4357_);
                if v_isShared_4362_ == 0 {
                    leanh::lean_ctor_set(v___x_4361_, 0, v___x_4368_);
                    v___x_4370_ = v___x_4361_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4371_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4371_, 0, v___x_4368_);
                    v___x_4370_ = v_reuseFailAlloc_4371_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4370_;
            }
            4 => {
                v___x_4377_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4350_, v_key_4372_);
                if v___x_4377_ == 0 {
                    leanh::lean_del_object(v___x_4375_);
                    v___x_4378_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4372_,
                        v_val_4373_,
                        v_x_4350_,
                        v_x_4351_,
                    );
                    v___x_4379_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4379_, 0, v___x_4378_);
                    v___y_4367_ = v___x_4379_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4373_);
                    leanh::lean_dec(v_key_4372_);
                    if v_isShared_4376_ == 0 {
                        leanh::lean_ctor_set(v___x_4375_, 1, v_x_4351_);
                        leanh::lean_ctor_set(v___x_4375_, 0, v_x_4350_);
                        v___x_4381_ = v___x_4375_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4382_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_x_4350_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4382_, 1, v_x_4351_);
                        v___x_4381_ = v_reuseFailAlloc_4382_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4367_ = v___x_4381_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4388_ = lean_usize_shift_right(v_x_4348_, v___x_4353_);
                v___x_4389_ = lean_usize_add(v_x_4349_, v___x_4354_);
                v___x_4390_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_node_4384_, v___x_4388_, v___x_4389_, v_x_4350_, v_x_4351_);
                if v_isShared_4387_ == 0 {
                    leanh::lean_ctor_set(v___x_4386_, 0, v___x_4390_);
                    v___x_4392_ = v___x_4386_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4393_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4393_, 0, v___x_4390_);
                    v___x_4392_ = v_reuseFailAlloc_4393_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4367_ = v___x_4392_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4402_ == 0 {
                    v___x_4404_ = v___x_4401_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4418_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 0, v_ks_4398_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4418_, 1, v_vs_4399_);
                    v___x_4404_ = v_reuseFailAlloc_4418_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4405_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(v___x_4404_, v_x_4350_, v_x_4351_);
                v___x_4413_ = 7usize;
                v___x_4414_ = lean_usize_dec_le(v___x_4413_, v_x_4349_);
                if v___x_4414_ == 0 {
                    v___x_4415_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4405_);
                    v___x_4416_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4417_ = lean_nat_dec_lt(v___x_4415_, v___x_4416_);
                    leanh::lean_dec(v___x_4415_);
                    v___y_4407_ = v___x_4417_;
                    state = 10;
                    continue;
                } else {
                    v___y_4407_ = v___x_4414_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4407_ == 0 {
                    v_ks_4408_ = leanh::lean_ctor_get(v_newNode_4405_, 0);
                    leanh::lean_inc_ref(v_ks_4408_);
                    v_vs_4409_ = leanh::lean_ctor_get(v_newNode_4405_, 1);
                    leanh::lean_inc_ref(v_vs_4409_);
                    leanh::lean_dec_ref(v_newNode_4405_);
                    v___x_4410_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4411_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__2);
                    v___x_4412_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_x_4349_, v_ks_4408_, v_vs_4409_, v___x_4410_, v___x_4411_);
                    leanh::lean_dec_ref(v_vs_4409_);
                    leanh::lean_dec_ref(v_ks_4408_);
                    return v___x_4412_;
                } else {
                    return v_newNode_4405_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(
    mut v_depth_4420_: usize,
    mut v_keys_4421_: *mut leanh::LeanObject,
    mut v_vals_4422_: *mut leanh::LeanObject,
    mut v_i_4423_: *mut leanh::LeanObject,
    mut v_entries_4424_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4426_: u8 = 0;
    let mut v_k_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4429_: u64 = 0;
    let mut v_h_4430_: usize = 0;
    let mut v___x_4431_: usize = 0;
    let mut v___x_4432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4433_: usize = 0;
    let mut v___x_4434_: usize = 0;
    let mut v___x_4435_: usize = 0;
    let mut v_h_4436_: usize = 0;
    let mut v___x_4437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4425_ = lean_array_get_size(v_keys_4421_);
                v___x_4426_ = lean_nat_dec_lt(v_i_4423_, v___x_4425_);
                if v___x_4426_ == 0 {
                    leanh::lean_dec(v_i_4423_);
                    return v_entries_4424_;
                } else {
                    v_k_4427_ = lean_array_fget_borrowed(v_keys_4421_, v_i_4423_);
                    v_v_4428_ = lean_array_fget_borrowed(v_vals_4422_, v_i_4423_);
                    v___x_4429_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_4427_);
                    v_h_4430_ = lean_uint64_to_usize(v___x_4429_);
                    v___x_4431_ = 5usize;
                    v___x_4432_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4433_ = 1usize;
                    v___x_4434_ = lean_usize_sub(v_depth_4420_, v___x_4433_);
                    v___x_4435_ = lean_usize_mul(v___x_4431_, v___x_4434_);
                    v_h_4436_ = lean_usize_shift_right(v_h_4430_, v___x_4435_);
                    v___x_4437_ = lean_nat_add(v_i_4423_, v___x_4432_);
                    leanh::lean_dec(v_i_4423_);
                    leanh::lean_inc(v_v_4428_);
                    leanh::lean_inc(v_k_4427_);
                    v___x_4438_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_entries_4424_, v_h_4436_, v_depth_4420_, v_k_4427_, v_v_4428_);
                    v_i_4423_ = v___x_4437_;
                    v_entries_4424_ = v___x_4438_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg___boxed(
    mut v_depth_4440_: *mut leanh::LeanObject,
    mut v_keys_4441_: *mut leanh::LeanObject,
    mut v_vals_4442_: *mut leanh::LeanObject,
    mut v_i_4443_: *mut leanh::LeanObject,
    mut v_entries_4444_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4445_: usize = 0;
    let mut v_res_4446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4445_ = leanh::lean_unbox_usize(v_depth_4440_);
    leanh::lean_dec(v_depth_4440_);
    v_res_4446_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_depth_boxed_4445_, v_keys_4441_, v_vals_4442_, v_i_4443_, v_entries_4444_);
    leanh::lean_dec_ref(v_vals_4442_);
    leanh::lean_dec_ref(v_keys_4441_);
    return v_res_4446_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___boxed(
    mut v_x_4447_: *mut leanh::LeanObject,
    mut v_x_4448_: *mut leanh::LeanObject,
    mut v_x_4449_: *mut leanh::LeanObject,
    mut v_x_4450_: *mut leanh::LeanObject,
    mut v_x_4451_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2100__boxed_4452_: usize = 0;
    let mut v_x_2101__boxed_4453_: usize = 0;
    let mut v_res_4454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2100__boxed_4452_ = leanh::lean_unbox_usize(v_x_4448_);
    leanh::lean_dec(v_x_4448_);
    v_x_2101__boxed_4453_ = leanh::lean_unbox_usize(v_x_4449_);
    leanh::lean_dec(v_x_4449_);
    v_res_4454_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_4447_, v_x_2100__boxed_4452_, v_x_2101__boxed_4453_, v_x_4450_, v_x_4451_);
    return v_res_4454_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(
    mut v_x_4455_: *mut leanh::LeanObject,
    mut v_x_4456_: *mut leanh::LeanObject,
    mut v_x_4457_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4458_: u64 = 0;
    let mut v___x_4459_: usize = 0;
    let mut v___x_4460_: usize = 0;
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4458_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4456_);
    v___x_4459_ = lean_uint64_to_usize(v___x_4458_);
    v___x_4460_ = 1usize;
    v___x_4461_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_4455_, v___x_4459_, v___x_4460_, v_x_4456_, v_x_4457_);
    return v___x_4461_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(
    mut v_x_4462_: *mut leanh::LeanObject,
    mut v_keys_4463_: *mut leanh::LeanObject,
    mut v_v_4464_: *mut leanh::LeanObject,
    mut v_k_4465_: *mut leanh::LeanObject,
    mut v_x_4466_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4470_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4467_ = leanh::lean_unsigned_to_nat(1);
    v___x_4468_ = lean_nat_add(v_x_4462_, v___x_4467_);
    v_c_4469_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
        leanh::lean_box(0),
        v_keys_4463_,
        v_v_4464_,
        v___x_4468_,
    );
    leanh::lean_dec(v___x_4468_);
    v___x_4470_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_4470_, 0, v_k_4465_);
    leanh::lean_ctor_set(v___x_4470_, 1, v_c_4469_);
    return v___x_4470_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0___boxed(
    mut v_x_4471_: *mut leanh::LeanObject,
    mut v_keys_4472_: *mut leanh::LeanObject,
    mut v_v_4473_: *mut leanh::LeanObject,
    mut v_k_4474_: *mut leanh::LeanObject,
    mut v_x_4475_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4476_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_4471_, v_keys_4472_, v_v_4473_, v_k_4474_, v_x_4475_);
    leanh::lean_dec_ref(v_keys_4472_);
    leanh::lean_dec(v_x_4471_);
    return v_res_4476_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(
    mut v_a_4477_: *mut leanh::LeanObject,
    mut v_b_4478_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_fst_4479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4481_: u8 = 0;
    v_fst_4479_ = leanh::lean_ctor_get(v_a_4477_, 0);
    v_fst_4480_ = leanh::lean_ctor_get(v_b_4478_, 0);
    v___x_4481_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_4479_, v_fst_4480_);
    return v___x_4481_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1___boxed(
    mut v_a_4482_: *mut leanh::LeanObject,
    mut v_b_4483_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4484_: u8 = 0;
    let mut v_r_4485_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4484_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_a_4482_, v_b_4483_);
    leanh::lean_dec_ref(v_b_4483_);
    leanh::lean_dec_ref(v_a_4482_);
    v_r_4485_ = leanh::lean_box((v_res_4484_) as usize);
    return v_r_4485_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(
    mut v_vs_4486_: *mut leanh::LeanObject,
    mut v_v_4487_: *mut leanh::LeanObject,
    mut v_i_4488_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4490_: u8 = 0;
    let mut v___x_4491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCbvSimprocOLeanEntry_4492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCbvSimprocOLeanEntry_4495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_4496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4497_: u8 = 0;
    let mut v___x_4498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4489_ = lean_array_get_size(v_vs_4486_);
                v___x_4490_ = lean_nat_dec_lt(v_i_4488_, v___x_4489_);
                if v___x_4490_ == 0 {
                    leanh::lean_dec(v_i_4488_);
                    v___x_4491_ = lean_array_push(v_vs_4486_, v_v_4487_);
                    return v___x_4491_;
                } else {
                    v_toCbvSimprocOLeanEntry_4492_ = leanh::lean_ctor_get(v_v_4487_, 0);
                    v_declName_4493_ =
                        leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_4492_, 0);
                    v___x_4494_ = lean_array_fget_borrowed(v_vs_4486_, v_i_4488_);
                    v_toCbvSimprocOLeanEntry_4495_ = leanh::lean_ctor_get(v___x_4494_, 0);
                    v_declName_4496_ =
                        leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_4495_, 0);
                    v___x_4497_ = lean_name_eq(v_declName_4493_, v_declName_4496_);
                    if v___x_4497_ == 0 {
                        v___x_4498_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4499_ = lean_nat_add(v_i_4488_, v___x_4498_);
                        leanh::lean_dec(v_i_4488_);
                        v_i_4488_ = v___x_4499_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4501_ = lean_array_fset(v_vs_4486_, v_i_4488_, v_v_4487_);
                        leanh::lean_dec(v_i_4488_);
                        return v___x_4501_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(
    mut v_vs_4502_: *mut leanh::LeanObject,
    mut v_v_4503_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4505_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4504_ = leanh::lean_unsigned_to_nat(0);
    v___x_4505_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12_spec__19(v_vs_4502_, v_v_4503_, v___x_4504_);
    return v___x_4505_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(
    mut v_x_4510_: *mut leanh::LeanObject,
    mut v_keys_4511_: *mut leanh::LeanObject,
    mut v_v_4512_: *mut leanh::LeanObject,
    mut v_k_4513_: *mut leanh::LeanObject,
    mut v_as_4514_: *mut leanh::LeanObject,
    mut v_k_4515_: *mut leanh::LeanObject,
    mut v_x_4516_: *mut leanh::LeanObject,
    mut v_x_4517_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_4520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_midVal_4521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4522_: u8 = 0;
    let mut v___x_4523_: u8 = 0;
    let mut v___x_4524_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: u8 = 0;
    let mut v_snd_4526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4529_: u8 = 0;
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4538_: u8 = 0;
    let mut v_unused_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: u8 = 0;
    let mut v___x_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_j_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_as_4548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4518_ = lean_nat_add(v_x_4516_, v_x_4517_);
                v___x_4519_ = leanh::lean_unsigned_to_nat(1);
                v_mid_4520_ = lean_nat_shiftr(v___x_4518_, v___x_4519_);
                leanh::lean_dec(v___x_4518_);
                v_midVal_4521_ = lean_array_fget(v_as_4514_, v_mid_4520_);
                v___x_4522_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_midVal_4521_, v_k_4515_);
                if v___x_4522_ == 0 {
                    leanh::lean_dec(v_x_4517_);
                    v___x_4523_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_4515_, v_midVal_4521_);
                    if v___x_4523_ == 0 {
                        leanh::lean_dec(v_x_4516_);
                        v___x_4524_ = lean_array_get_size(v_as_4514_);
                        v___x_4525_ = lean_nat_dec_lt(v_mid_4520_, v___x_4524_);
                        if v___x_4525_ == 0 {
                            leanh::lean_dec(v_midVal_4521_);
                            leanh::lean_dec(v_mid_4520_);
                            leanh::lean_dec(v_k_4513_);
                            leanh::lean_dec_ref(v_v_4512_);
                            return v_as_4514_;
                        } else {
                            v_snd_4526_ = leanh::lean_ctor_get(v_midVal_4521_, 1);
                            v_isSharedCheck_4538_ =
                                (!leanh::lean_is_exclusive(v_midVal_4521_)) as u8;
                            if v_isSharedCheck_4538_ == 0 {
                                v_unused_4539_ = leanh::lean_ctor_get(v_midVal_4521_, 0);
                                leanh::lean_dec(v_unused_4539_);
                                v___x_4528_ = v_midVal_4521_;
                                v_isShared_4529_ = v_isSharedCheck_4538_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_inc(v_snd_4526_);
                                leanh::lean_dec(v_midVal_4521_);
                                v___x_4528_ = leanh::lean_box(0);
                                v_isShared_4529_ = v_isSharedCheck_4538_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        leanh::lean_dec(v_midVal_4521_);
                        v_x_4517_ = v_mid_4520_;
                        state = 0;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_midVal_4521_);
                    v___x_4541_ = lean_nat_dec_eq(v_mid_4520_, v_x_4516_);
                    if v___x_4541_ == 0 {
                        leanh::lean_dec(v_x_4516_);
                        v_x_4516_ = v_mid_4520_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_mid_4520_);
                        leanh::lean_dec(v_x_4517_);
                        v___x_4543_ = lean_nat_add(v_x_4510_, v___x_4519_);
                        v_c_4544_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(leanh::lean_box(0), v_keys_4511_, v_v_4512_, v___x_4543_);
                        leanh::lean_dec(v___x_4543_);
                        v___x_4545_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4545_, 0, v_k_4513_);
                        leanh::lean_ctor_set(v___x_4545_, 1, v_c_4544_);
                        v___x_4546_ = lean_nat_add(v_x_4516_, v___x_4519_);
                        leanh::lean_dec(v_x_4516_);
                        v_j_4547_ = lean_array_get_size(v_as_4514_);
                        v_as_4548_ = lean_array_push(v_as_4514_, v___x_4545_);
                        v___x_4549_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                            leanh::lean_box(0),
                            v___x_4546_,
                            v_as_4548_,
                            v_j_4547_,
                        );
                        leanh::lean_dec(v___x_4546_);
                        return v___x_4549_;
                    }
                }
            }
            1 => {
                v___x_4530_ = leanh::lean_box(0);
                v_xs_x27_4531_ = lean_array_fset(v_as_4514_, v_mid_4520_, v___x_4530_);
                v___x_4532_ = lean_nat_add(v_x_4510_, v___x_4519_);
                v_c_4533_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_4511_, v_v_4512_, v___x_4532_, v_snd_4526_);
                leanh::lean_dec(v___x_4532_);
                if v_isShared_4529_ == 0 {
                    leanh::lean_ctor_set(v___x_4528_, 1, v_c_4533_);
                    leanh::lean_ctor_set(v___x_4528_, 0, v_k_4513_);
                    v___x_4535_ = v___x_4528_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4537_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 0, v_k_4513_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4537_, 1, v_c_4533_);
                    v___x_4535_ = v_reuseFailAlloc_4537_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_4536_ = lean_array_fset(v_xs_x27_4531_, v_mid_4520_, v___x_4535_);
                leanh::lean_dec(v_mid_4520_);
                return v___x_4536_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(
    mut v_x_4550_: *mut leanh::LeanObject,
    mut v_keys_4551_: *mut leanh::LeanObject,
    mut v_v_4552_: *mut leanh::LeanObject,
    mut v_k_4553_: *mut leanh::LeanObject,
    mut v_as_4554_: *mut leanh::LeanObject,
    mut v_k_4555_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4558_: u8 = 0;
    v___x_4556_ = lean_array_get_size(v_as_4554_);
    v___x_4557_ = leanh::lean_unsigned_to_nat(0);
    v___x_4558_ = lean_nat_dec_eq(v___x_4556_, v___x_4557_);
    if v___x_4558_ == 0 {
        let mut v___x_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4560_: u8 = 0;
        v___x_4559_ = lean_array_fget_borrowed(v_as_4554_, v___x_4557_);
        v___x_4560_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_4555_, v___x_4559_);
        if v___x_4560_ == 0 {
            let mut v___x_4561_: u8 = 0;
            v___x_4561_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v___x_4559_, v_k_4555_);
            if v___x_4561_ == 0 {
                let mut v___x_4562_: u8 = 0;
                v___x_4562_ = lean_nat_dec_lt(v___x_4557_, v___x_4556_);
                if v___x_4562_ == 0 {
                    leanh::lean_dec(v_k_4553_);
                    leanh::lean_dec_ref(v_v_4552_);
                    return v_as_4554_;
                } else {
                    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v_xs_x27_4564_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4565_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_inc(v___x_4559_);
                    v___x_4563_ = leanh::lean_box(0);
                    v_xs_x27_4564_ = lean_array_fset(v_as_4554_, v___x_4557_, v___x_4563_);
                    v___x_4565_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_4550_, v_keys_4551_, v_v_4552_, v_k_4553_, v___x_4559_);
                    v___x_4566_ = lean_array_fset(v_xs_x27_4564_, v___x_4557_, v___x_4565_);
                    return v___x_4566_;
                }
            } else {
                let mut v___x_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4568_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4569_: *mut leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_4570_: u8 = 0;
                v___x_4567_ = leanh::lean_unsigned_to_nat(1);
                v___x_4568_ = lean_nat_sub(v___x_4556_, v___x_4567_);
                v___x_4569_ = lean_array_fget_borrowed(v_as_4554_, v___x_4568_);
                v___x_4570_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v___x_4569_, v_k_4555_);
                if v___x_4570_ == 0 {
                    let mut v___x_4571_: u8 = 0;
                    v___x_4571_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__1(v_k_4555_, v___x_4569_);
                    if v___x_4571_ == 0 {
                        let mut v___x_4572_: u8 = 0;
                        v___x_4572_ = lean_nat_dec_lt(v___x_4568_, v___x_4556_);
                        if v___x_4572_ == 0 {
                            leanh::lean_dec(v___x_4568_);
                            leanh::lean_dec(v_k_4553_);
                            leanh::lean_dec_ref(v_v_4552_);
                            return v_as_4554_;
                        } else {
                            let mut v___x_4573_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v_xs_x27_4574_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4575_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            let mut v___x_4576_: *mut leanh::LeanObject =
                                core::ptr::null_mut();
                            leanh::lean_inc(v___x_4569_);
                            v___x_4573_ = leanh::lean_box(0);
                            v_xs_x27_4574_ = lean_array_fset(v_as_4554_, v___x_4568_, v___x_4573_);
                            v___x_4575_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_4550_, v_keys_4551_, v_v_4552_, v_k_4553_, v___x_4569_);
                            v___x_4576_ = lean_array_fset(v_xs_x27_4574_, v___x_4568_, v___x_4575_);
                            leanh::lean_dec(v___x_4568_);
                            return v___x_4576_;
                        }
                    } else {
                        let mut v___x_4577_: *mut leanh::LeanObject = core::ptr::null_mut();
                        v___x_4577_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_4550_, v_keys_4551_, v_v_4552_, v_k_4553_, v_as_4554_, v_k_4555_, v___x_4557_, v___x_4568_);
                        return v___x_4577_;
                    }
                } else {
                    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4579_: *mut leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_4580_: *mut leanh::LeanObject = core::ptr::null_mut();
                    leanh::lean_dec(v___x_4568_);
                    v___x_4578_ = leanh::lean_box(0);
                    v___x_4579_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_4550_, v_keys_4551_, v_v_4552_, v_k_4553_, v___x_4578_);
                    v___x_4580_ = lean_array_push(v_as_4554_, v___x_4579_);
                    return v___x_4580_;
                }
            }
        } else {
            let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_as_4583_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4581_ = leanh::lean_box(0);
            v___x_4582_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_4550_, v_keys_4551_, v_v_4552_, v_k_4553_, v___x_4581_);
            v_as_4583_ = lean_array_push(v_as_4554_, v___x_4582_);
            v___x_4584_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(
                leanh::lean_box(0),
                v___x_4557_,
                v_as_4583_,
                v___x_4556_,
            );
            return v___x_4584_;
        }
    } else {
        let mut v___x_4585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4587_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4585_ = leanh::lean_box(0);
        v___x_4586_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__0(v_x_4550_, v_keys_4551_, v_v_4552_, v_k_4553_, v___x_4585_);
        v___x_4587_ = lean_array_push(v_as_4554_, v___x_4586_);
        return v___x_4587_;
    }
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(
    mut v_keys_4588_: *mut leanh::LeanObject,
    mut v_v_4589_: *mut leanh::LeanObject,
    mut v_x_4590_: *mut leanh::LeanObject,
    mut v_x_4591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_vs_4592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_children_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4596_: u8 = 0;
    let mut v___x_4597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4598_: u8 = 0;
    let mut v___x_4599_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_4603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4605_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4610_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_vs_4592_ = leanh::lean_ctor_get(v_x_4591_, 0);
                v_children_4593_ = leanh::lean_ctor_get(v_x_4591_, 1);
                v_isSharedCheck_4610_ = (!leanh::lean_is_exclusive(v_x_4591_)) as u8;
                if v_isSharedCheck_4610_ == 0 {
                    v___x_4595_ = v_x_4591_;
                    v_isShared_4596_ = v_isSharedCheck_4610_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_children_4593_);
                    leanh::lean_inc(v_vs_4592_);
                    leanh::lean_dec(v_x_4591_);
                    v___x_4595_ = leanh::lean_box(0);
                    v_isShared_4596_ = v_isSharedCheck_4610_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4597_ = lean_array_get_size(v_keys_4588_);
                v___x_4598_ = lean_nat_dec_lt(v_x_4590_, v___x_4597_);
                if v___x_4598_ == 0 {
                    v___x_4599_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__12(v_vs_4592_, v_v_4589_);
                    if v_isShared_4596_ == 0 {
                        leanh::lean_ctor_set(v___x_4595_, 0, v___x_4599_);
                        v___x_4601_ = v___x_4595_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4602_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4599_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_children_4593_);
                        v___x_4601_ = v_reuseFailAlloc_4602_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_4603_ = lean_array_fget_borrowed(v_keys_4588_, v_x_4590_);
                    v___x_4604_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___closed__1;
                    leanh::lean_inc_n(v_k_4603_, 2);
                    v___x_4605_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4605_, 0, v_k_4603_);
                    leanh::lean_ctor_set(v___x_4605_, 1, v___x_4604_);
                    v_c_4606_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(v_x_4590_, v_keys_4588_, v_v_4589_, v_k_4603_, v_children_4593_, v___x_4605_);
                    leanh::lean_dec_ref_known(v___x_4605_, 2);
                    if v_isShared_4596_ == 0 {
                        leanh::lean_ctor_set(v___x_4595_, 1, v_c_4606_);
                        v___x_4608_ = v___x_4595_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4609_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 0, v_vs_4592_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4609_, 1, v_c_4606_);
                        v___x_4608_ = v_reuseFailAlloc_4609_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4601_;
            }
            3 => {
                return v___x_4608_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(
    mut v_x_4611_: *mut leanh::LeanObject,
    mut v_keys_4612_: *mut leanh::LeanObject,
    mut v_v_4613_: *mut leanh::LeanObject,
    mut v_k_4614_: *mut leanh::LeanObject,
    mut v_x_4615_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_snd_4616_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4618_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4619_: u8 = 0;
    let mut v___x_4620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4621_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_c_4622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4625_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4626_: u8 = 0;
    let mut v_unused_4627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_snd_4616_ = leanh::lean_ctor_get(v_x_4615_, 1);
                v_isSharedCheck_4626_ = (!leanh::lean_is_exclusive(v_x_4615_)) as u8;
                if v_isSharedCheck_4626_ == 0 {
                    v_unused_4627_ = leanh::lean_ctor_get(v_x_4615_, 0);
                    leanh::lean_dec(v_unused_4627_);
                    v___x_4618_ = v_x_4615_;
                    v_isShared_4619_ = v_isSharedCheck_4626_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_4616_);
                    leanh::lean_dec(v_x_4615_);
                    v___x_4618_ = leanh::lean_box(0);
                    v_isShared_4619_ = v_isSharedCheck_4626_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4620_ = leanh::lean_unsigned_to_nat(1);
                v___x_4621_ = lean_nat_add(v_x_4611_, v___x_4620_);
                v_c_4622_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_4612_, v_v_4613_, v___x_4621_, v_snd_4616_);
                leanh::lean_dec(v___x_4621_);
                if v_isShared_4619_ == 0 {
                    leanh::lean_ctor_set(v___x_4618_, 1, v_c_4622_);
                    leanh::lean_ctor_set(v___x_4618_, 0, v_k_4614_);
                    v___x_4624_ = v___x_4618_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4625_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 0, v_k_4614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4625_, 1, v_c_4622_);
                    v___x_4624_ = v_reuseFailAlloc_4625_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4624_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2___boxed(
    mut v_x_4628_: *mut leanh::LeanObject,
    mut v_keys_4629_: *mut leanh::LeanObject,
    mut v_v_4630_: *mut leanh::LeanObject,
    mut v_k_4631_: *mut leanh::LeanObject,
    mut v_x_4632_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4633_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___lam__2(v_x_4628_, v_keys_4629_, v_v_4630_, v_k_4631_, v_x_4632_);
    leanh::lean_dec_ref(v_keys_4629_);
    leanh::lean_dec(v_x_4628_);
    return v_res_4633_;
}
pub unsafe fn l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6___boxed(
    mut v_keys_4634_: *mut leanh::LeanObject,
    mut v_v_4635_: *mut leanh::LeanObject,
    mut v_x_4636_: *mut leanh::LeanObject,
    mut v_x_4637_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4638_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_4634_, v_v_4635_, v_x_4636_, v_x_4637_);
    leanh::lean_dec(v_x_4636_);
    leanh::lean_dec_ref(v_keys_4634_);
    return v_res_4638_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg___boxed(
    mut v_x_4639_: *mut leanh::LeanObject,
    mut v_keys_4640_: *mut leanh::LeanObject,
    mut v_v_4641_: *mut leanh::LeanObject,
    mut v_k_4642_: *mut leanh::LeanObject,
    mut v_as_4643_: *mut leanh::LeanObject,
    mut v_k_4644_: *mut leanh::LeanObject,
    mut v_x_4645_: *mut leanh::LeanObject,
    mut v_x_4646_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4647_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4647_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_4639_, v_keys_4640_, v_v_4641_, v_k_4642_, v_as_4643_, v_k_4644_, v_x_4645_, v_x_4646_);
    leanh::lean_dec_ref(v_k_4644_);
    leanh::lean_dec_ref(v_keys_4640_);
    leanh::lean_dec(v_x_4639_);
    return v_res_4647_;
}
pub unsafe fn l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13___boxed(
    mut v_x_4648_: *mut leanh::LeanObject,
    mut v_keys_4649_: *mut leanh::LeanObject,
    mut v_v_4650_: *mut leanh::LeanObject,
    mut v_k_4651_: *mut leanh::LeanObject,
    mut v_as_4652_: *mut leanh::LeanObject,
    mut v_k_4653_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4654_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13(v_x_4648_, v_keys_4649_, v_v_4650_, v_k_4651_, v_as_4652_, v_k_4653_);
    leanh::lean_dec_ref(v_k_4653_);
    leanh::lean_dec_ref(v_keys_4649_);
    leanh::lean_dec(v_x_4648_);
    return v_res_4654_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(
    mut v_keys_4655_: *mut leanh::LeanObject,
    mut v_vals_4656_: *mut leanh::LeanObject,
    mut v_i_4657_: *mut leanh::LeanObject,
    mut v_k_4658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4659_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: u8 = 0;
    let mut v___x_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4662_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4663_: u8 = 0;
    let mut v___x_4664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4659_ = lean_array_get_size(v_keys_4655_);
                v___x_4660_ = lean_nat_dec_lt(v_i_4657_, v___x_4659_);
                if v___x_4660_ == 0 {
                    leanh::lean_dec(v_i_4657_);
                    v___x_4661_ = leanh::lean_box(0);
                    return v___x_4661_;
                } else {
                    v_k_x27_4662_ = lean_array_fget_borrowed(v_keys_4655_, v_i_4657_);
                    v___x_4663_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_k_4658_, v_k_x27_4662_);
                    if v___x_4663_ == 0 {
                        v___x_4664_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4665_ = lean_nat_add(v_i_4657_, v___x_4664_);
                        leanh::lean_dec(v_i_4657_);
                        v_i_4657_ = v___x_4665_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4667_ = lean_array_fget_borrowed(v_vals_4656_, v_i_4657_);
                        leanh::lean_dec(v_i_4657_);
                        leanh::lean_inc(v___x_4667_);
                        v___x_4668_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4668_, 0, v___x_4667_);
                        return v___x_4668_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg___boxed(
    mut v_keys_4669_: *mut leanh::LeanObject,
    mut v_vals_4670_: *mut leanh::LeanObject,
    mut v_i_4671_: *mut leanh::LeanObject,
    mut v_k_4672_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4673_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_keys_4669_, v_vals_4670_, v_i_4671_, v_k_4672_);
    leanh::lean_dec(v_k_4672_);
    leanh::lean_dec_ref(v_vals_4670_);
    leanh::lean_dec_ref(v_keys_4669_);
    return v_res_4673_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(
    mut v_x_4674_: *mut leanh::LeanObject,
    mut v_x_4675_: usize,
    mut v_x_4676_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4679_: usize = 0;
    let mut v___x_4680_: usize = 0;
    let mut v___x_4681_: usize = 0;
    let mut v_j_4682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4686_: u8 = 0;
    let mut v___x_4687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_4689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4690_: usize = 0;
    let mut v___x_4692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4695_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4674_) == 0 {
                    v_es_4677_ = leanh::lean_ctor_get(v_x_4674_, 0);
                    v___x_4678_ = leanh::lean_box(2);
                    v___x_4679_ = 5usize;
                    v___x_4680_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
                    v___x_4681_ = lean_usize_land(v_x_4675_, v___x_4680_);
                    v_j_4682_ = lean_usize_to_nat(v___x_4681_);
                    v___x_4683_ = lean_array_get_borrowed(v___x_4678_, v_es_4677_, v_j_4682_);
                    leanh::lean_dec(v_j_4682_);
                    match leanh::lean_obj_tag(v___x_4683_) {
                        0 => {
                            v_key_4684_ = leanh::lean_ctor_get(v___x_4683_, 0);
                            v_val_4685_ = leanh::lean_ctor_get(v___x_4683_, 1);
                            v___x_4686_ =
                                l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_4676_, v_key_4684_);
                            if v___x_4686_ == 0 {
                                v___x_4687_ = leanh::lean_box(0);
                                return v___x_4687_;
                            } else {
                                leanh::lean_inc(v_val_4685_);
                                v___x_4688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_4688_, 0, v_val_4685_);
                                return v___x_4688_;
                            }
                        }
                        1 => {
                            v_node_4689_ = leanh::lean_ctor_get(v___x_4683_, 0);
                            v___x_4690_ = lean_usize_shift_right(v_x_4675_, v___x_4679_);
                            v_x_4674_ = v_node_4689_;
                            v_x_4675_ = v___x_4690_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_4692_ = leanh::lean_box(0);
                            return v___x_4692_;
                        }
                    }
                } else {
                    v_ks_4693_ = leanh::lean_ctor_get(v_x_4674_, 0);
                    v_vs_4694_ = leanh::lean_ctor_get(v_x_4674_, 1);
                    v___x_4695_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4696_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_ks_4693_, v_vs_4694_, v___x_4695_, v_x_4676_);
                    return v___x_4696_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg___boxed(
    mut v_x_4697_: *mut leanh::LeanObject,
    mut v_x_4698_: *mut leanh::LeanObject,
    mut v_x_4699_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2540__boxed_4700_: usize = 0;
    let mut v_res_4701_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2540__boxed_4700_ = leanh::lean_unbox_usize(v_x_4698_);
    leanh::lean_dec(v_x_4698_);
    v_res_4701_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_4697_, v_x_2540__boxed_4700_, v_x_4699_);
    leanh::lean_dec(v_x_4699_);
    leanh::lean_dec_ref(v_x_4697_);
    return v_res_4701_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(
    mut v_x_4702_: *mut leanh::LeanObject,
    mut v_x_4703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4704_: u64 = 0;
    let mut v___x_4705_: usize = 0;
    let mut v___x_4706_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4704_ = l_Lean_Meta_DiscrTree_Key_hash(v_x_4703_);
    v___x_4705_ = lean_uint64_to_usize(v___x_4704_);
    v___x_4706_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_4702_, v___x_4705_, v_x_4703_);
    return v___x_4706_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg___boxed(
    mut v_x_4707_: *mut leanh::LeanObject,
    mut v_x_4708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4709_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_x_4707_, v_x_4708_);
    leanh::lean_dec(v_x_4708_);
    leanh::lean_dec_ref(v_x_4707_);
    return v_res_4709_;
}
pub unsafe fn _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_4713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4718_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4713_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__2;
    v___x_4714_ = leanh::lean_unsigned_to_nat(23);
    v___x_4715_ = leanh::lean_unsigned_to_nat(166);
    v___x_4716_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__1;
    v___x_4717_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__0;
    v___x_4718_ = l_mkPanicMessageWithDecl(
        v___x_4717_,
        v___x_4716_,
        v___x_4715_,
        v___x_4714_,
        v___x_4713_,
    );
    return v___x_4718_;
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(
    mut v_d_4719_: *mut leanh::LeanObject,
    mut v_keys_4720_: *mut leanh::LeanObject,
    mut v_v_4721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: u8 = 0;
    v___x_4722_ = lean_array_get_size(v_keys_4720_);
    v___x_4723_ = leanh::lean_unsigned_to_nat(0);
    v___x_4724_ = lean_nat_dec_eq(v___x_4722_, v___x_4723_);
    if v___x_4724_ == 0 {
        let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_k_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4727_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_4725_ = leanh::lean_box(0);
        v_k_4726_ = lean_array_get_borrowed(v___x_4725_, v_keys_4720_, v___x_4723_);
        v___x_4727_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_d_4719_, v_k_4726_);
        if leanh::lean_obj_tag(v___x_4727_) == 0 {
            let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4729_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4730_: *mut leanh::LeanObject = core::ptr::null_mut();
            v___x_4728_ = leanh::lean_unsigned_to_nat(1);
            v_c_4729_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(
                leanh::lean_box(0),
                v_keys_4720_,
                v_v_4721_,
                v___x_4728_,
            );
            leanh::lean_inc(v_k_4726_);
            v___x_4730_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_d_4719_, v_k_4726_, v_c_4729_);
            return v___x_4730_;
        } else {
            let mut v_val_4731_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v_c_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_4734_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_val_4731_ = leanh::lean_ctor_get(v___x_4727_, 0);
            leanh::lean_inc(v_val_4731_);
            leanh::lean_dec_ref_known(v___x_4727_, 1);
            v___x_4732_ = leanh::lean_unsigned_to_nat(1);
            v_c_4733_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6(v_keys_4720_, v_v_4721_, v___x_4732_, v_val_4731_);
            leanh::lean_inc(v_k_4726_);
            v___x_4734_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_d_4719_, v_k_4726_, v_c_4733_);
            return v___x_4734_;
        }
    } else {
        let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_4736_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref(v_v_4721_);
        leanh::lean_dec_ref(v_d_4719_);
        v___x_4735_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3), core::ptr::addr_of_mut!(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3_once), _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___closed__3);
        v___x_4736_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__7(v___x_4735_);
        return v___x_4736_;
    }
}
pub unsafe fn l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2___boxed(
    mut v_d_4737_: *mut leanh::LeanObject,
    mut v_keys_4738_: *mut leanh::LeanObject,
    mut v_v_4739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4740_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4740_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_d_4737_, v_keys_4738_, v_v_4739_);
    leanh::lean_dec_ref(v_keys_4738_);
    return v_res_4740_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(
    mut v_x_4741_: *mut leanh::LeanObject,
    mut v_x_4742_: *mut leanh::LeanObject,
    mut v_x_4743_: *mut leanh::LeanObject,
    mut v_x_4744_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ks_4745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4749_: u8 = 0;
    let mut v___x_4750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4751_: u8 = 0;
    let mut v___x_4752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_4757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4758_: u8 = 0;
    let mut v___x_4760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4762_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4764_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4765_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4766_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4768_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_4745_ = leanh::lean_ctor_get(v_x_4741_, 0);
                v_vs_4746_ = leanh::lean_ctor_get(v_x_4741_, 1);
                v_isSharedCheck_4770_ = (!leanh::lean_is_exclusive(v_x_4741_)) as u8;
                if v_isSharedCheck_4770_ == 0 {
                    v___x_4748_ = v_x_4741_;
                    v_isShared_4749_ = v_isSharedCheck_4770_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_vs_4746_);
                    leanh::lean_inc(v_ks_4745_);
                    leanh::lean_dec(v_x_4741_);
                    v___x_4748_ = leanh::lean_box(0);
                    v_isShared_4749_ = v_isSharedCheck_4770_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4750_ = lean_array_get_size(v_ks_4745_);
                v___x_4751_ = lean_nat_dec_lt(v_x_4742_, v___x_4750_);
                if v___x_4751_ == 0 {
                    leanh::lean_dec(v_x_4742_);
                    v___x_4752_ = lean_array_push(v_ks_4745_, v_x_4743_);
                    v___x_4753_ = lean_array_push(v_vs_4746_, v_x_4744_);
                    if v_isShared_4749_ == 0 {
                        leanh::lean_ctor_set(v___x_4748_, 1, v___x_4753_);
                        leanh::lean_ctor_set(v___x_4748_, 0, v___x_4752_);
                        v___x_4755_ = v___x_4748_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4756_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4756_, 0, v___x_4752_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4756_, 1, v___x_4753_);
                        v___x_4755_ = v_reuseFailAlloc_4756_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_4757_ = lean_array_fget_borrowed(v_ks_4745_, v_x_4742_);
                    v___x_4758_ = lean_name_eq(v_x_4743_, v_k_x27_4757_);
                    if v___x_4758_ == 0 {
                        if v_isShared_4749_ == 0 {
                            v___x_4760_ = v___x_4748_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_4764_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 0, v_ks_4745_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4764_, 1, v_vs_4746_);
                            v___x_4760_ = v_reuseFailAlloc_4764_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_4765_ = lean_array_fset(v_ks_4745_, v_x_4742_, v_x_4743_);
                        v___x_4766_ = lean_array_fset(v_vs_4746_, v_x_4742_, v_x_4744_);
                        leanh::lean_dec(v_x_4742_);
                        if v_isShared_4749_ == 0 {
                            leanh::lean_ctor_set(v___x_4748_, 1, v___x_4766_);
                            leanh::lean_ctor_set(v___x_4748_, 0, v___x_4765_);
                            v___x_4768_ = v___x_4748_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_4769_ =
                                leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 0, v___x_4765_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_4769_, 1, v___x_4766_);
                            v___x_4768_ = v_reuseFailAlloc_4769_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4755_;
            }
            3 => {
                v___x_4761_ = leanh::lean_unsigned_to_nat(1);
                v___x_4762_ = lean_nat_add(v_x_4742_, v___x_4761_);
                leanh::lean_dec(v_x_4742_);
                v_x_4741_ = v___x_4760_;
                v_x_4742_ = v___x_4762_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_4768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(
    mut v_n_4771_: *mut leanh::LeanObject,
    mut v_k_4772_: *mut leanh::LeanObject,
    mut v_v_4773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4774_ = leanh::lean_unsigned_to_nat(0);
    v___x_4775_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_n_4771_, v___x_4774_, v_k_4772_, v_v_4773_);
    return v___x_4775_;
}
pub unsafe fn _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0()
-> u64 {
    let mut v___x_4776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4777_: u64 = 0;
    v___x_4776_ = leanh::lean_unsigned_to_nat(1723);
    v___x_4777_ = lean_uint64_of_nat(v___x_4776_);
    return v___x_4777_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_4778_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4778_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_4778_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(
    mut v_x_4779_: *mut leanh::LeanObject,
    mut v_x_4780_: usize,
    mut v_x_4781_: usize,
    mut v_x_4782_: *mut leanh::LeanObject,
    mut v_x_4783_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: usize = 0;
    let mut v___x_4786_: usize = 0;
    let mut v___x_4787_: usize = 0;
    let mut v___x_4788_: usize = 0;
    let mut v_j_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: u8 = 0;
    let mut v___x_4793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4794_: u8 = 0;
    let mut v_v_4795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4803_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4808_: u8 = 0;
    let mut v___x_4809_: u8 = 0;
    let mut v___x_4810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4815_: u8 = 0;
    let mut v_node_4816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4818_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4819_: u8 = 0;
    let mut v___x_4820_: usize = 0;
    let mut v___x_4821_: usize = 0;
    let mut v___x_4822_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4826_: u8 = 0;
    let mut v___x_4827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4828_: u8 = 0;
    let mut v_unused_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4833_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4834_: u8 = 0;
    let mut v___x_4836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_4837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4839_: u8 = 0;
    let mut v_ks_4840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4845_: usize = 0;
    let mut v___x_4846_: u8 = 0;
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4849_: u8 = 0;
    let mut v_reuseFailAlloc_4850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4851_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4779_) == 0 {
                    v_es_4784_ = leanh::lean_ctor_get(v_x_4779_, 0);
                    v___x_4785_ = 5usize;
                    v___x_4786_ = 1usize;
                    v___x_4787_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
                    v___x_4788_ = lean_usize_land(v_x_4780_, v___x_4787_);
                    v_j_4789_ = lean_usize_to_nat(v___x_4788_);
                    v___x_4790_ = lean_array_get_size(v_es_4784_);
                    v___x_4791_ = lean_nat_dec_lt(v_j_4789_, v___x_4790_);
                    if v___x_4791_ == 0 {
                        leanh::lean_dec(v_j_4789_);
                        leanh::lean_dec(v_x_4783_);
                        leanh::lean_dec(v_x_4782_);
                        return v_x_4779_;
                    } else {
                        leanh::lean_inc_ref(v_es_4784_);
                        v_isSharedCheck_4828_ = (!leanh::lean_is_exclusive(v_x_4779_)) as u8;
                        if v_isSharedCheck_4828_ == 0 {
                            v_unused_4829_ = leanh::lean_ctor_get(v_x_4779_, 0);
                            leanh::lean_dec(v_unused_4829_);
                            v___x_4793_ = v_x_4779_;
                            v_isShared_4794_ = v_isSharedCheck_4828_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v_x_4779_);
                            v___x_4793_ = leanh::lean_box(0);
                            v_isShared_4794_ = v_isSharedCheck_4828_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_4830_ = leanh::lean_ctor_get(v_x_4779_, 0);
                    v_vs_4831_ = leanh::lean_ctor_get(v_x_4779_, 1);
                    v_isSharedCheck_4851_ = (!leanh::lean_is_exclusive(v_x_4779_)) as u8;
                    if v_isSharedCheck_4851_ == 0 {
                        v___x_4833_ = v_x_4779_;
                        v_isShared_4834_ = v_isSharedCheck_4851_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4831_);
                        leanh::lean_inc(v_ks_4830_);
                        leanh::lean_dec(v_x_4779_);
                        v___x_4833_ = leanh::lean_box(0);
                        v_isShared_4834_ = v_isSharedCheck_4851_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_4795_ = lean_array_fget(v_es_4784_, v_j_4789_);
                v___x_4796_ = leanh::lean_box(0);
                v_xs_x27_4797_ = lean_array_fset(v_es_4784_, v_j_4789_, v___x_4796_);
                match leanh::lean_obj_tag(v_v_4795_) {
                    0 => {
                        v_key_4804_ = leanh::lean_ctor_get(v_v_4795_, 0);
                        v_val_4805_ = leanh::lean_ctor_get(v_v_4795_, 1);
                        v_isSharedCheck_4815_ = (!leanh::lean_is_exclusive(v_v_4795_)) as u8;
                        if v_isSharedCheck_4815_ == 0 {
                            v___x_4807_ = v_v_4795_;
                            v_isShared_4808_ = v_isSharedCheck_4815_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_4805_);
                            leanh::lean_inc(v_key_4804_);
                            leanh::lean_dec(v_v_4795_);
                            v___x_4807_ = leanh::lean_box(0);
                            v_isShared_4808_ = v_isSharedCheck_4815_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_4816_ = leanh::lean_ctor_get(v_v_4795_, 0);
                        v_isSharedCheck_4826_ = (!leanh::lean_is_exclusive(v_v_4795_)) as u8;
                        if v_isSharedCheck_4826_ == 0 {
                            v___x_4818_ = v_v_4795_;
                            v_isShared_4819_ = v_isSharedCheck_4826_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_node_4816_);
                            leanh::lean_dec(v_v_4795_);
                            v___x_4818_ = leanh::lean_box(0);
                            v_isShared_4819_ = v_isSharedCheck_4826_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_4827_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_4827_, 0, v_x_4782_);
                        leanh::lean_ctor_set(v___x_4827_, 1, v_x_4783_);
                        v___y_4799_ = v___x_4827_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4800_ = lean_array_fset(v_xs_x27_4797_, v_j_4789_, v___y_4799_);
                leanh::lean_dec(v_j_4789_);
                if v_isShared_4794_ == 0 {
                    leanh::lean_ctor_set(v___x_4793_, 0, v___x_4800_);
                    v___x_4802_ = v___x_4793_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4803_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4803_, 0, v___x_4800_);
                    v___x_4802_ = v_reuseFailAlloc_4803_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4802_;
            }
            4 => {
                v___x_4809_ = lean_name_eq(v_x_4782_, v_key_4804_);
                if v___x_4809_ == 0 {
                    leanh::lean_del_object(v___x_4807_);
                    v___x_4810_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_4804_,
                        v_val_4805_,
                        v_x_4782_,
                        v_x_4783_,
                    );
                    v___x_4811_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4811_, 0, v___x_4810_);
                    v___y_4799_ = v___x_4811_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_val_4805_);
                    leanh::lean_dec(v_key_4804_);
                    if v_isShared_4808_ == 0 {
                        leanh::lean_ctor_set(v___x_4807_, 1, v_x_4783_);
                        leanh::lean_ctor_set(v___x_4807_, 0, v_x_4782_);
                        v___x_4813_ = v___x_4807_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4814_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 0, v_x_4782_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_x_4783_);
                        v___x_4813_ = v_reuseFailAlloc_4814_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_4799_ = v___x_4813_;
                state = 2;
                continue;
            }
            6 => {
                v___x_4820_ = lean_usize_shift_right(v_x_4780_, v___x_4785_);
                v___x_4821_ = lean_usize_add(v_x_4781_, v___x_4786_);
                v___x_4822_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_node_4816_, v___x_4820_, v___x_4821_, v_x_4782_, v_x_4783_);
                if v_isShared_4819_ == 0 {
                    leanh::lean_ctor_set(v___x_4818_, 0, v___x_4822_);
                    v___x_4824_ = v___x_4818_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4825_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4825_, 0, v___x_4822_);
                    v___x_4824_ = v_reuseFailAlloc_4825_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_4799_ = v___x_4824_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_4834_ == 0 {
                    v___x_4836_ = v___x_4833_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4850_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 0, v_ks_4830_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4850_, 1, v_vs_4831_);
                    v___x_4836_ = v_reuseFailAlloc_4850_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_4837_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v___x_4836_, v_x_4782_, v_x_4783_);
                v___x_4845_ = 7usize;
                v___x_4846_ = lean_usize_dec_le(v___x_4845_, v_x_4781_);
                if v___x_4846_ == 0 {
                    v___x_4847_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_4837_);
                    v___x_4848_ = leanh::lean_unsigned_to_nat(4);
                    v___x_4849_ = lean_nat_dec_lt(v___x_4847_, v___x_4848_);
                    leanh::lean_dec(v___x_4847_);
                    v___y_4839_ = v___x_4849_;
                    state = 10;
                    continue;
                } else {
                    v___y_4839_ = v___x_4846_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_4839_ == 0 {
                    v_ks_4840_ = leanh::lean_ctor_get(v_newNode_4837_, 0);
                    leanh::lean_inc_ref(v_ks_4840_);
                    v_vs_4841_ = leanh::lean_ctor_get(v_newNode_4837_, 1);
                    leanh::lean_inc_ref(v_vs_4841_);
                    leanh::lean_dec_ref(v_newNode_4837_);
                    v___x_4842_ = leanh::lean_unsigned_to_nat(0);
                    v___x_4843_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___closed__0);
                    v___x_4844_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_x_4781_, v_ks_4840_, v_vs_4841_, v___x_4842_, v___x_4843_);
                    leanh::lean_dec_ref(v_vs_4841_);
                    leanh::lean_dec_ref(v_ks_4840_);
                    return v___x_4844_;
                } else {
                    return v_newNode_4837_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(
    mut v_depth_4852_: usize,
    mut v_keys_4853_: *mut leanh::LeanObject,
    mut v_vals_4854_: *mut leanh::LeanObject,
    mut v_i_4855_: *mut leanh::LeanObject,
    mut v_entries_4856_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: u8 = 0;
    let mut v_k_4859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4862_: u64 = 0;
    let mut v_h_4863_: usize = 0;
    let mut v___x_4864_: usize = 0;
    let mut v___x_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4866_: usize = 0;
    let mut v___x_4867_: usize = 0;
    let mut v___x_4868_: usize = 0;
    let mut v_h_4869_: usize = 0;
    let mut v___x_4870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4873_: u64 = 0;
    let mut v_hash_4874_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4857_ = lean_array_get_size(v_keys_4853_);
                v___x_4858_ = lean_nat_dec_lt(v_i_4855_, v___x_4857_);
                if v___x_4858_ == 0 {
                    leanh::lean_dec(v_i_4855_);
                    return v_entries_4856_;
                } else {
                    v_k_4859_ = lean_array_fget_borrowed(v_keys_4853_, v_i_4855_);
                    v_v_4860_ = lean_array_fget_borrowed(v_vals_4854_, v_i_4855_);
                    if leanh::lean_obj_tag(v_k_4859_) == 0 {
                        v___x_4873_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                        v___y_4862_ = v___x_4873_;
                        state = 1;
                        continue;
                    } else {
                        v_hash_4874_ = leanh::lean_ctor_get_uint64(
                            v_k_4859_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                        );
                        v___y_4862_ = v_hash_4874_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_h_4863_ = lean_uint64_to_usize(v___y_4862_);
                v___x_4864_ = 5usize;
                v___x_4865_ = leanh::lean_unsigned_to_nat(1);
                v___x_4866_ = 1usize;
                v___x_4867_ = lean_usize_sub(v_depth_4852_, v___x_4866_);
                v___x_4868_ = lean_usize_mul(v___x_4864_, v___x_4867_);
                v_h_4869_ = lean_usize_shift_right(v_h_4863_, v___x_4868_);
                v___x_4870_ = lean_nat_add(v_i_4855_, v___x_4865_);
                leanh::lean_dec(v_i_4855_);
                leanh::lean_inc(v_v_4860_);
                leanh::lean_inc(v_k_4859_);
                v___x_4871_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_entries_4856_, v_h_4869_, v_depth_4852_, v_k_4859_, v_v_4860_);
                v_i_4855_ = v___x_4870_;
                v_entries_4856_ = v___x_4871_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_4875_: *mut leanh::LeanObject,
    mut v_keys_4876_: *mut leanh::LeanObject,
    mut v_vals_4877_: *mut leanh::LeanObject,
    mut v_i_4878_: *mut leanh::LeanObject,
    mut v_entries_4879_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_4880_: usize = 0;
    let mut v_res_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_4880_ = leanh::lean_unbox_usize(v_depth_4875_);
    leanh::lean_dec(v_depth_4875_);
    v_res_4881_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_boxed_4880_, v_keys_4876_, v_vals_4877_, v_i_4878_, v_entries_4879_);
    leanh::lean_dec_ref(v_vals_4877_);
    leanh::lean_dec_ref(v_keys_4876_);
    return v_res_4881_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg___boxed(
    mut v_x_4882_: *mut leanh::LeanObject,
    mut v_x_4883_: *mut leanh::LeanObject,
    mut v_x_4884_: *mut leanh::LeanObject,
    mut v_x_4885_: *mut leanh::LeanObject,
    mut v_x_4886_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2740__boxed_4887_: usize = 0;
    let mut v_x_2741__boxed_4888_: usize = 0;
    let mut v_res_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2740__boxed_4887_ = leanh::lean_unbox_usize(v_x_4883_);
    leanh::lean_dec(v_x_4883_);
    v_x_2741__boxed_4888_ = leanh::lean_unbox_usize(v_x_4884_);
    leanh::lean_dec(v_x_4884_);
    v_res_4889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_4882_, v_x_2740__boxed_4887_, v_x_2741__boxed_4888_, v_x_4885_, v_x_4886_);
    return v_res_4889_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(
    mut v_x_4890_: *mut leanh::LeanObject,
    mut v_x_4891_: *mut leanh::LeanObject,
    mut v_x_4892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_4894_: u64 = 0;
    let mut v___x_4895_: usize = 0;
    let mut v___x_4896_: usize = 0;
    let mut v___x_4897_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: u64 = 0;
    let mut v_hash_4899_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4891_) == 0 {
                    v___x_4898_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_4894_ = v___x_4898_;
                    state = 1;
                    continue;
                } else {
                    v_hash_4899_ = leanh::lean_ctor_get_uint64(
                        v_x_4891_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_4894_ = v_hash_4899_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_4895_ = lean_uint64_to_usize(v___y_4894_);
                v___x_4896_ = 1usize;
                v___x_4897_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_4890_, v___x_4895_, v___x_4896_, v_x_4891_, v_x_4892_);
                return v___x_4897_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(
    mut v_xs_4900_: *mut leanh::LeanObject,
    mut v_v_4901_: *mut leanh::LeanObject,
    mut v_i_4902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4903_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4904_: u8 = 0;
    let mut v___x_4905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4907_: u8 = 0;
    let mut v___x_4908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4903_ = lean_array_get_size(v_xs_4900_);
                v___x_4904_ = lean_nat_dec_lt(v_i_4902_, v___x_4903_);
                if v___x_4904_ == 0 {
                    leanh::lean_dec(v_i_4902_);
                    v___x_4905_ = leanh::lean_box(0);
                    return v___x_4905_;
                } else {
                    v___x_4906_ = lean_array_fget_borrowed(v_xs_4900_, v_i_4902_);
                    v___x_4907_ = lean_name_eq(v___x_4906_, v_v_4901_);
                    if v___x_4907_ == 0 {
                        v___x_4908_ = leanh::lean_unsigned_to_nat(1);
                        v___x_4909_ = lean_nat_add(v_i_4902_, v___x_4908_);
                        leanh::lean_dec(v_i_4902_);
                        v_i_4902_ = v___x_4909_;
                        state = 0;
                        continue;
                    } else {
                        v___x_4911_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_4911_, 0, v_i_4902_);
                        return v___x_4911_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9___boxed(
    mut v_xs_4912_: *mut leanh::LeanObject,
    mut v_v_4913_: *mut leanh::LeanObject,
    mut v_i_4914_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4915_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4915_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_4912_, v_v_4913_, v_i_4914_);
    leanh::lean_dec(v_v_4913_);
    leanh::lean_dec_ref(v_xs_4912_);
    return v_res_4915_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(
    mut v_xs_4916_: *mut leanh::LeanObject,
    mut v_v_4917_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4919_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_4918_ = leanh::lean_unsigned_to_nat(0);
    v___x_4919_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5_spec__9(v_xs_4916_, v_v_4917_, v___x_4918_);
    return v___x_4919_;
}
pub unsafe fn l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5___boxed(
    mut v_xs_4920_: *mut leanh::LeanObject,
    mut v_v_4921_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_4922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_4922_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_xs_4920_, v_v_4921_);
    leanh::lean_dec(v_v_4921_);
    leanh::lean_dec_ref(v_xs_4920_);
    return v_res_4922_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(
    mut v_x_4923_: *mut leanh::LeanObject,
    mut v_x_4924_: usize,
    mut v_x_4925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4928_: usize = 0;
    let mut v___x_4929_: usize = 0;
    let mut v___x_4930_: usize = 0;
    let mut v_j_4931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_4933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4934_: u8 = 0;
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4937_: u8 = 0;
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4942_: u8 = 0;
    let mut v_unused_4943_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4946_: u8 = 0;
    let mut v_node_4947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4950_: u8 = 0;
    let mut v_entries_4951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: usize = 0;
    let mut v_newNode_4953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4960_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_4963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4967_: u8 = 0;
    let mut v___x_4969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4975_: u8 = 0;
    let mut v_isSharedCheck_4976_: u8 = 0;
    let mut v_isSharedCheck_4977_: u8 = 0;
    let mut v_unused_4978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_4979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_4980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4983_: u8 = 0;
    let mut v___x_4984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_x27_4989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vals_x27_4990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4994_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_4923_) == 0 {
                    v_es_4926_ = leanh::lean_ctor_get(v_x_4923_, 0);
                    v___x_4927_ = leanh::lean_box(2);
                    v___x_4928_ = 5usize;
                    v___x_4929_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
                    v___x_4930_ = lean_usize_land(v_x_4924_, v___x_4929_);
                    v_j_4931_ = lean_usize_to_nat(v___x_4930_);
                    v_entry_4932_ = lean_array_get(v___x_4927_, v_es_4926_, v_j_4931_);
                    match leanh::lean_obj_tag(v_entry_4932_) {
                        0 => {
                            v_key_4933_ = leanh::lean_ctor_get(v_entry_4932_, 0);
                            leanh::lean_inc(v_key_4933_);
                            leanh::lean_dec_ref_known(v_entry_4932_, 2);
                            v___x_4934_ = lean_name_eq(v_x_4925_, v_key_4933_);
                            leanh::lean_dec(v_key_4933_);
                            if v___x_4934_ == 0 {
                                leanh::lean_dec(v_j_4931_);
                                return v_x_4923_;
                            } else {
                                leanh::lean_inc_ref(v_es_4926_);
                                v_isSharedCheck_4942_ =
                                    (!leanh::lean_is_exclusive(v_x_4923_)) as u8;
                                if v_isSharedCheck_4942_ == 0 {
                                    v_unused_4943_ = leanh::lean_ctor_get(v_x_4923_, 0);
                                    leanh::lean_dec(v_unused_4943_);
                                    v___x_4936_ = v_x_4923_;
                                    v_isShared_4937_ = v_isSharedCheck_4942_;
                                    state = 1;
                                    continue;
                                } else {
                                    leanh::lean_dec(v_x_4923_);
                                    v___x_4936_ = leanh::lean_box(0);
                                    v_isShared_4937_ = v_isSharedCheck_4942_;
                                    state = 1;
                                    continue;
                                }
                            }
                        }
                        1 => {
                            leanh::lean_inc_ref(v_es_4926_);
                            v_isSharedCheck_4977_ =
                                (!leanh::lean_is_exclusive(v_x_4923_)) as u8;
                            if v_isSharedCheck_4977_ == 0 {
                                v_unused_4978_ = leanh::lean_ctor_get(v_x_4923_, 0);
                                leanh::lean_dec(v_unused_4978_);
                                v___x_4945_ = v_x_4923_;
                                v_isShared_4946_ = v_isSharedCheck_4977_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_dec(v_x_4923_);
                                v___x_4945_ = leanh::lean_box(0);
                                v_isShared_4946_ = v_isSharedCheck_4977_;
                                state = 3;
                                continue;
                            }
                        }
                        _ => {
                            leanh::lean_dec(v_j_4931_);
                            return v_x_4923_;
                        }
                    }
                } else {
                    v_ks_4979_ = leanh::lean_ctor_get(v_x_4923_, 0);
                    v_vs_4980_ = leanh::lean_ctor_get(v_x_4923_, 1);
                    v_isSharedCheck_4994_ = (!leanh::lean_is_exclusive(v_x_4923_)) as u8;
                    if v_isSharedCheck_4994_ == 0 {
                        v___x_4982_ = v_x_4923_;
                        v_isShared_4983_ = v_isSharedCheck_4994_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_vs_4980_);
                        leanh::lean_inc(v_ks_4979_);
                        leanh::lean_dec(v_x_4923_);
                        v___x_4982_ = leanh::lean_box(0);
                        v_isShared_4983_ = v_isSharedCheck_4994_;
                        state = 10;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4938_ = lean_array_set(v_es_4926_, v_j_4931_, v___x_4927_);
                leanh::lean_dec(v_j_4931_);
                if v_isShared_4937_ == 0 {
                    leanh::lean_ctor_set(v___x_4936_, 0, v___x_4938_);
                    v___x_4940_ = v___x_4936_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4941_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4938_);
                    v___x_4940_ = v_reuseFailAlloc_4941_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4940_;
            }
            3 => {
                v_node_4947_ = leanh::lean_ctor_get(v_entry_4932_, 0);
                v_isSharedCheck_4976_ = (!leanh::lean_is_exclusive(v_entry_4932_)) as u8;
                if v_isSharedCheck_4976_ == 0 {
                    v___x_4949_ = v_entry_4932_;
                    v_isShared_4950_ = v_isSharedCheck_4976_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_inc(v_node_4947_);
                    leanh::lean_dec(v_entry_4932_);
                    v___x_4949_ = leanh::lean_box(0);
                    v_isShared_4950_ = v_isSharedCheck_4976_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_entries_4951_ = lean_array_set(v_es_4926_, v_j_4931_, v___x_4927_);
                v___x_4952_ = lean_usize_shift_right(v_x_4924_, v___x_4928_);
                v_newNode_4953_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_node_4947_, v___x_4952_, v_x_4925_);
                leanh::lean_inc_ref(v_newNode_4953_);
                v___x_4954_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_4953_);
                if leanh::lean_obj_tag(v___x_4954_) == 0 {
                    if v_isShared_4950_ == 0 {
                        leanh::lean_ctor_set(v___x_4949_, 0, v_newNode_4953_);
                        v___x_4956_ = v___x_4949_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4961_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4961_, 0, v_newNode_4953_);
                        v___x_4956_ = v_reuseFailAlloc_4961_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_newNode_4953_);
                    leanh::lean_del_object(v___x_4949_);
                    v_val_4962_ = leanh::lean_ctor_get(v___x_4954_, 0);
                    leanh::lean_inc(v_val_4962_);
                    leanh::lean_dec_ref_known(v___x_4954_, 1);
                    v_fst_4963_ = leanh::lean_ctor_get(v_val_4962_, 0);
                    v_snd_4964_ = leanh::lean_ctor_get(v_val_4962_, 1);
                    v_isSharedCheck_4975_ = (!leanh::lean_is_exclusive(v_val_4962_)) as u8;
                    if v_isSharedCheck_4975_ == 0 {
                        v___x_4966_ = v_val_4962_;
                        v_isShared_4967_ = v_isSharedCheck_4975_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4964_);
                        leanh::lean_inc(v_fst_4963_);
                        leanh::lean_dec(v_val_4962_);
                        v___x_4966_ = leanh::lean_box(0);
                        v_isShared_4967_ = v_isSharedCheck_4975_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                v___x_4957_ = lean_array_set(v_entries_4951_, v_j_4931_, v___x_4956_);
                leanh::lean_dec(v_j_4931_);
                if v_isShared_4946_ == 0 {
                    leanh::lean_ctor_set(v___x_4945_, 0, v___x_4957_);
                    v___x_4959_ = v___x_4945_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4960_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4960_, 0, v___x_4957_);
                    v___x_4959_ = v_reuseFailAlloc_4960_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4959_;
            }
            7 => {
                if v_isShared_4967_ == 0 {
                    v___x_4969_ = v___x_4966_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4974_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 0, v_fst_4963_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4974_, 1, v_snd_4964_);
                    v___x_4969_ = v_reuseFailAlloc_4974_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_4970_ = lean_array_set(v_entries_4951_, v_j_4931_, v___x_4969_);
                leanh::lean_dec(v_j_4931_);
                if v_isShared_4946_ == 0 {
                    leanh::lean_ctor_set(v___x_4945_, 0, v___x_4970_);
                    v___x_4972_ = v___x_4945_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4973_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4973_, 0, v___x_4970_);
                    v___x_4972_ = v_reuseFailAlloc_4973_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4972_;
            }
            10 => {
                v___x_4984_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2_spec__5(v_ks_4979_, v_x_4925_);
                if leanh::lean_obj_tag(v___x_4984_) == 0 {
                    if v_isShared_4983_ == 0 {
                        v___x_4986_ = v___x_4982_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_4987_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 0, v_ks_4979_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4987_, 1, v_vs_4980_);
                        v___x_4986_ = v_reuseFailAlloc_4987_;
                        state = 11;
                        continue;
                    }
                } else {
                    v_val_4988_ = leanh::lean_ctor_get(v___x_4984_, 0);
                    leanh::lean_inc_n(v_val_4988_, 2);
                    leanh::lean_dec_ref_known(v___x_4984_, 1);
                    v_keys_x27_4989_ = l_Array_eraseIdx___redArg(v_ks_4979_, v_val_4988_);
                    v_vals_x27_4990_ = l_Array_eraseIdx___redArg(v_vs_4980_, v_val_4988_);
                    if v_isShared_4983_ == 0 {
                        leanh::lean_ctor_set(v___x_4982_, 1, v_vals_x27_4990_);
                        leanh::lean_ctor_set(v___x_4982_, 0, v_keys_x27_4989_);
                        v___x_4992_ = v___x_4982_;
                        state = 12;
                        continue;
                    } else {
                        v_reuseFailAlloc_4993_ = leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 0, v_keys_x27_4989_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4993_, 1, v_vals_x27_4990_);
                        v___x_4992_ = v_reuseFailAlloc_4993_;
                        state = 12;
                        continue;
                    }
                }
            }
            11 => {
                return v___x_4986_;
            }
            12 => {
                return v___x_4992_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg___boxed(
    mut v_x_4995_: *mut leanh::LeanObject,
    mut v_x_4996_: *mut leanh::LeanObject,
    mut v_x_4997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_2949__boxed_4998_: usize = 0;
    let mut v_res_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_2949__boxed_4998_ = leanh::lean_unbox_usize(v_x_4996_);
    leanh::lean_dec(v_x_4996_);
    v_res_4999_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_4995_, v_x_2949__boxed_4998_, v_x_4997_);
    leanh::lean_dec(v_x_4997_);
    return v_res_4999_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(
    mut v_x_5000_: *mut leanh::LeanObject,
    mut v_x_5001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5003_: u64 = 0;
    let mut v_h_5004_: usize = 0;
    let mut v___x_5005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5006_: u64 = 0;
    let mut v_hash_5007_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5001_) == 0 {
                    v___x_5006_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_5003_ = v___x_5006_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5007_ = leanh::lean_ctor_get_uint64(
                        v_x_5001_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5003_ = v_hash_5007_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_h_5004_ = lean_uint64_to_usize(v___y_5003_);
                v___x_5005_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_5000_, v_h_5004_, v_x_5001_);
                return v___x_5005_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg___boxed(
    mut v_x_5008_: *mut leanh::LeanObject,
    mut v_x_5009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5010_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_5008_, v_x_5009_);
    leanh::lean_dec(v_x_5009_);
    return v_res_5010_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(
    mut v_s_5011_: *mut leanh::LeanObject,
    mut v_keys_5012_: *mut leanh::LeanObject,
    mut v_declName_5013_: *mut leanh::LeanObject,
    mut v_phase_5014_: u8,
    mut v_proc_5015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_5016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eval_5017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocNames_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_5020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5023_: u8 = 0;
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_entry_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5041_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pre_5016_ = leanh::lean_ctor_get(v_s_5011_, 0);
                v_eval_5017_ = leanh::lean_ctor_get(v_s_5011_, 1);
                v_post_5018_ = leanh::lean_ctor_get(v_s_5011_, 2);
                v_simprocNames_5019_ = leanh::lean_ctor_get(v_s_5011_, 3);
                v_erased_5020_ = leanh::lean_ctor_get(v_s_5011_, 4);
                v_isSharedCheck_5041_ = (!leanh::lean_is_exclusive(v_s_5011_)) as u8;
                if v_isSharedCheck_5041_ == 0 {
                    v___x_5022_ = v_s_5011_;
                    v_isShared_5023_ = v_isSharedCheck_5041_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_erased_5020_);
                    leanh::lean_inc(v_simprocNames_5019_);
                    leanh::lean_inc(v_post_5018_);
                    leanh::lean_inc(v_eval_5017_);
                    leanh::lean_inc(v_pre_5016_);
                    leanh::lean_dec(v_s_5011_);
                    v___x_5022_ = leanh::lean_box(0);
                    v_isShared_5023_ = v_isSharedCheck_5041_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc_ref(v_keys_5012_);
                leanh::lean_inc_n(v_declName_5013_, 2);
                v___x_5024_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                leanh::lean_ctor_set(v___x_5024_, 0, v_declName_5013_);
                leanh::lean_ctor_set(v___x_5024_, 1, v_keys_5012_);
                leanh::lean_ctor_set_uint8(
                    v___x_5024_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    v_phase_5014_,
                );
                v_entry_5025_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v_entry_5025_, 0, v___x_5024_);
                leanh::lean_ctor_set(v_entry_5025_, 1, v_proc_5015_);
                v___x_5026_ = leanh::lean_box(0);
                v___x_5027_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_simprocNames_5019_, v_declName_5013_, v___x_5026_);
                v___x_5028_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_erased_5020_, v_declName_5013_);
                leanh::lean_dec(v_declName_5013_);
                match v_phase_5014_ {
                    0 => {
                        v___x_5029_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_pre_5016_, v_keys_5012_, v_entry_5025_);
                        leanh::lean_dec_ref(v_keys_5012_);
                        if v_isShared_5023_ == 0 {
                            leanh::lean_ctor_set(v___x_5022_, 4, v___x_5028_);
                            leanh::lean_ctor_set(v___x_5022_, 3, v___x_5027_);
                            leanh::lean_ctor_set(v___x_5022_, 0, v___x_5029_);
                            v___x_5031_ = v___x_5022_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_5032_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 0, v___x_5029_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 1, v_eval_5017_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 2, v_post_5018_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 3, v___x_5027_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5032_, 4, v___x_5028_);
                            v___x_5031_ = v_reuseFailAlloc_5032_;
                            state = 2;
                            continue;
                        }
                    }
                    1 => {
                        v___x_5033_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_eval_5017_, v_keys_5012_, v_entry_5025_);
                        leanh::lean_dec_ref(v_keys_5012_);
                        if v_isShared_5023_ == 0 {
                            leanh::lean_ctor_set(v___x_5022_, 4, v___x_5028_);
                            leanh::lean_ctor_set(v___x_5022_, 3, v___x_5027_);
                            leanh::lean_ctor_set(v___x_5022_, 1, v___x_5033_);
                            v___x_5035_ = v___x_5022_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5036_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 0, v_pre_5016_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 1, v___x_5033_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 2, v_post_5018_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 3, v___x_5027_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5036_, 4, v___x_5028_);
                            v___x_5035_ = v_reuseFailAlloc_5036_;
                            state = 3;
                            continue;
                        }
                    }
                    _ => {
                        v___x_5037_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2(v_post_5018_, v_keys_5012_, v_entry_5025_);
                        leanh::lean_dec_ref(v_keys_5012_);
                        if v_isShared_5023_ == 0 {
                            leanh::lean_ctor_set(v___x_5022_, 4, v___x_5028_);
                            leanh::lean_ctor_set(v___x_5022_, 3, v___x_5027_);
                            leanh::lean_ctor_set(v___x_5022_, 2, v___x_5037_);
                            v___x_5039_ = v___x_5022_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5040_ =
                                leanh::lean_alloc_ctor(0, 5, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 0, v_pre_5016_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 1, v_eval_5017_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 2, v___x_5037_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 3, v___x_5027_);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5040_, 4, v___x_5028_);
                            v___x_5039_ = v_reuseFailAlloc_5040_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5031_;
            }
            3 => {
                return v___x_5035_;
            }
            4 => {
                return v___x_5039_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore___boxed(
    mut v_s_5042_: *mut leanh::LeanObject,
    mut v_keys_5043_: *mut leanh::LeanObject,
    mut v_declName_5044_: *mut leanh::LeanObject,
    mut v_phase_5045_: *mut leanh::LeanObject,
    mut v_proc_5046_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_5047_: u8 = 0;
    let mut v_res_5048_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_5047_ = (leanh::lean_unbox(v_phase_5045_) as u8);
    v_res_5048_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(
        v_s_5042_,
        v_keys_5043_,
        v_declName_5044_,
        v_phase_boxed_5047_,
        v_proc_5046_,
    );
    return v_res_5048_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0(
    mut v_00_u03b2_5049_: *mut leanh::LeanObject,
    mut v_x_5050_: *mut leanh::LeanObject,
    mut v_x_5051_: *mut leanh::LeanObject,
    mut v_x_5052_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5053_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5053_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_x_5050_, v_x_5051_, v_x_5052_);
    return v___x_5053_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(
    mut v_00_u03b2_5054_: *mut leanh::LeanObject,
    mut v_x_5055_: *mut leanh::LeanObject,
    mut v_x_5056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5057_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5057_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_x_5055_, v_x_5056_);
    return v___x_5057_;
}
pub unsafe fn l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___boxed(
    mut v_00_u03b2_5058_: *mut leanh::LeanObject,
    mut v_x_5059_: *mut leanh::LeanObject,
    mut v_x_5060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5061_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5061_ =
        l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1(
            v_00_u03b2_5058_,
            v_x_5059_,
            v_x_5060_,
        );
    leanh::lean_dec(v_x_5060_);
    return v_res_5061_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(
    mut v_00_u03b2_5062_: *mut leanh::LeanObject,
    mut v_x_5063_: *mut leanh::LeanObject,
    mut v_x_5064_: usize,
    mut v_x_5065_: usize,
    mut v_x_5066_: *mut leanh::LeanObject,
    mut v_x_5067_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5068_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5068_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___redArg(v_x_5063_, v_x_5064_, v_x_5065_, v_x_5066_, v_x_5067_);
    return v___x_5068_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0___boxed(
    mut v_00_u03b2_5069_: *mut leanh::LeanObject,
    mut v_x_5070_: *mut leanh::LeanObject,
    mut v_x_5071_: *mut leanh::LeanObject,
    mut v_x_5072_: *mut leanh::LeanObject,
    mut v_x_5073_: *mut leanh::LeanObject,
    mut v_x_5074_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3160__boxed_5075_: usize = 0;
    let mut v_x_3161__boxed_5076_: usize = 0;
    let mut v_res_5077_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3160__boxed_5075_ = leanh::lean_unbox_usize(v_x_5071_);
    leanh::lean_dec(v_x_5071_);
    v_x_3161__boxed_5076_ = leanh::lean_unbox_usize(v_x_5072_);
    leanh::lean_dec(v_x_5072_);
    v_res_5077_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0(v_00_u03b2_5069_, v_x_5070_, v_x_3160__boxed_5075_, v_x_3161__boxed_5076_, v_x_5073_, v_x_5074_);
    return v_res_5077_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(
    mut v_00_u03b2_5078_: *mut leanh::LeanObject,
    mut v_x_5079_: *mut leanh::LeanObject,
    mut v_x_5080_: usize,
    mut v_x_5081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5082_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5082_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___redArg(v_x_5079_, v_x_5080_, v_x_5081_);
    return v___x_5082_;
}
pub unsafe fn l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2___boxed(
    mut v_00_u03b2_5083_: *mut leanh::LeanObject,
    mut v_x_5084_: *mut leanh::LeanObject,
    mut v_x_5085_: *mut leanh::LeanObject,
    mut v_x_5086_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3177__boxed_5087_: usize = 0;
    let mut v_res_5088_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3177__boxed_5087_ = leanh::lean_unbox_usize(v_x_5085_);
    leanh::lean_dec(v_x_5085_);
    v_res_5088_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1_spec__2(v_00_u03b2_5083_, v_x_5084_, v_x_3177__boxed_5087_, v_x_5086_);
    leanh::lean_dec(v_x_5086_);
    return v_res_5088_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(
    mut v_00_u03b2_5089_: *mut leanh::LeanObject,
    mut v_x_5090_: *mut leanh::LeanObject,
    mut v_x_5091_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5092_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___redArg(v_x_5090_, v_x_5091_);
    return v___x_5092_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4___boxed(
    mut v_00_u03b2_5093_: *mut leanh::LeanObject,
    mut v_x_5094_: *mut leanh::LeanObject,
    mut v_x_5095_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5096_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4(v_00_u03b2_5093_, v_x_5094_, v_x_5095_);
    leanh::lean_dec(v_x_5095_);
    leanh::lean_dec_ref(v_x_5094_);
    return v_res_5096_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5(
    mut v_00_u03b2_5097_: *mut leanh::LeanObject,
    mut v_x_5098_: *mut leanh::LeanObject,
    mut v_x_5099_: *mut leanh::LeanObject,
    mut v_x_5100_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5101_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5___redArg(v_x_5098_, v_x_5099_, v_x_5100_);
    return v___x_5101_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1(
    mut v_00_u03b2_5102_: *mut leanh::LeanObject,
    mut v_n_5103_: *mut leanh::LeanObject,
    mut v_k_5104_: *mut leanh::LeanObject,
    mut v_v_5105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5106_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1___redArg(v_n_5103_, v_k_5104_, v_v_5105_);
    return v___x_5106_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(
    mut v_00_u03b2_5107_: *mut leanh::LeanObject,
    mut v_depth_5108_: usize,
    mut v_keys_5109_: *mut leanh::LeanObject,
    mut v_vals_5110_: *mut leanh::LeanObject,
    mut v_heq_5111_: *mut leanh::LeanObject,
    mut v_i_5112_: *mut leanh::LeanObject,
    mut v_entries_5113_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5114_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5114_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg(v_depth_5108_, v_keys_5109_, v_vals_5110_, v_i_5112_, v_entries_5113_);
    return v___x_5114_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_5115_: *mut leanh::LeanObject,
    mut v_depth_5116_: *mut leanh::LeanObject,
    mut v_keys_5117_: *mut leanh::LeanObject,
    mut v_vals_5118_: *mut leanh::LeanObject,
    mut v_heq_5119_: *mut leanh::LeanObject,
    mut v_i_5120_: *mut leanh::LeanObject,
    mut v_entries_5121_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5122_: usize = 0;
    let mut v_res_5123_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5122_ = leanh::lean_unbox_usize(v_depth_5116_);
    leanh::lean_dec(v_depth_5116_);
    v_res_5123_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2(v_00_u03b2_5115_, v_depth_boxed_5122_, v_keys_5117_, v_vals_5118_, v_heq_5119_, v_i_5120_, v_entries_5121_);
    leanh::lean_dec_ref(v_vals_5118_);
    leanh::lean_dec_ref(v_keys_5117_);
    return v_res_5123_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(
    mut v_00_u03b2_5124_: *mut leanh::LeanObject,
    mut v_x_5125_: *mut leanh::LeanObject,
    mut v_x_5126_: usize,
    mut v_x_5127_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5128_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5128_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___redArg(v_x_5125_, v_x_5126_, v_x_5127_);
    return v___x_5128_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8___boxed(
    mut v_00_u03b2_5129_: *mut leanh::LeanObject,
    mut v_x_5130_: *mut leanh::LeanObject,
    mut v_x_5131_: *mut leanh::LeanObject,
    mut v_x_5132_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3208__boxed_5133_: usize = 0;
    let mut v_res_5134_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3208__boxed_5133_ = leanh::lean_unbox_usize(v_x_5131_);
    leanh::lean_dec(v_x_5131_);
    v_res_5134_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8(v_00_u03b2_5129_, v_x_5130_, v_x_3208__boxed_5133_, v_x_5132_);
    leanh::lean_dec(v_x_5132_);
    leanh::lean_dec_ref(v_x_5130_);
    return v_res_5134_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(
    mut v_00_u03b2_5135_: *mut leanh::LeanObject,
    mut v_x_5136_: *mut leanh::LeanObject,
    mut v_x_5137_: usize,
    mut v_x_5138_: usize,
    mut v_x_5139_: *mut leanh::LeanObject,
    mut v_x_5140_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5141_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5141_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg(v_x_5136_, v_x_5137_, v_x_5138_, v_x_5139_, v_x_5140_);
    return v___x_5141_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___boxed(
    mut v_00_u03b2_5142_: *mut leanh::LeanObject,
    mut v_x_5143_: *mut leanh::LeanObject,
    mut v_x_5144_: *mut leanh::LeanObject,
    mut v_x_5145_: *mut leanh::LeanObject,
    mut v_x_5146_: *mut leanh::LeanObject,
    mut v_x_5147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_3219__boxed_5148_: usize = 0;
    let mut v_x_3220__boxed_5149_: usize = 0;
    let mut v_res_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_3219__boxed_5148_ = leanh::lean_unbox_usize(v_x_5144_);
    leanh::lean_dec(v_x_5144_);
    v_x_3220__boxed_5149_ = leanh::lean_unbox_usize(v_x_5145_);
    leanh::lean_dec(v_x_5145_);
    v_res_5150_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10(v_00_u03b2_5142_, v_x_5143_, v_x_3219__boxed_5148_, v_x_3220__boxed_5149_, v_x_5146_, v_x_5147_);
    return v_res_5150_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5(
    mut v_00_u03b2_5151_: *mut leanh::LeanObject,
    mut v_x_5152_: *mut leanh::LeanObject,
    mut v_x_5153_: *mut leanh::LeanObject,
    mut v_x_5154_: *mut leanh::LeanObject,
    mut v_x_5155_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5156_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__1_spec__5___redArg(v_x_5152_, v_x_5153_, v_x_5154_, v_x_5155_);
    return v___x_5156_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(
    mut v_00_u03b2_5157_: *mut leanh::LeanObject,
    mut v_keys_5158_: *mut leanh::LeanObject,
    mut v_vals_5159_: *mut leanh::LeanObject,
    mut v_heq_5160_: *mut leanh::LeanObject,
    mut v_i_5161_: *mut leanh::LeanObject,
    mut v_k_5162_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5163_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___redArg(v_keys_5158_, v_vals_5159_, v_i_5161_, v_k_5162_);
    return v___x_5163_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12___boxed(
    mut v_00_u03b2_5164_: *mut leanh::LeanObject,
    mut v_keys_5165_: *mut leanh::LeanObject,
    mut v_vals_5166_: *mut leanh::LeanObject,
    mut v_heq_5167_: *mut leanh::LeanObject,
    mut v_i_5168_: *mut leanh::LeanObject,
    mut v_k_5169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5170_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5170_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__4_spec__8_spec__12(v_00_u03b2_5164_, v_keys_5165_, v_vals_5166_, v_heq_5167_, v_i_5168_, v_k_5169_);
    leanh::lean_dec(v_k_5169_);
    leanh::lean_dec_ref(v_vals_5166_);
    leanh::lean_dec_ref(v_keys_5165_);
    return v_res_5170_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15(
    mut v_00_u03b2_5171_: *mut leanh::LeanObject,
    mut v_n_5172_: *mut leanh::LeanObject,
    mut v_k_5173_: *mut leanh::LeanObject,
    mut v_v_5174_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5175_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15___redArg(v_n_5172_, v_k_5173_, v_v_5174_);
    return v___x_5175_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(
    mut v_00_u03b2_5176_: *mut leanh::LeanObject,
    mut v_depth_5177_: usize,
    mut v_keys_5178_: *mut leanh::LeanObject,
    mut v_vals_5179_: *mut leanh::LeanObject,
    mut v_heq_5180_: *mut leanh::LeanObject,
    mut v_i_5181_: *mut leanh::LeanObject,
    mut v_entries_5182_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5183_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___redArg(v_depth_5177_, v_keys_5178_, v_vals_5179_, v_i_5181_, v_entries_5182_);
    return v___x_5183_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16___boxed(
    mut v_00_u03b2_5184_: *mut leanh::LeanObject,
    mut v_depth_5185_: *mut leanh::LeanObject,
    mut v_keys_5186_: *mut leanh::LeanObject,
    mut v_vals_5187_: *mut leanh::LeanObject,
    mut v_heq_5188_: *mut leanh::LeanObject,
    mut v_i_5189_: *mut leanh::LeanObject,
    mut v_entries_5190_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_depth_boxed_5191_: usize = 0;
    let mut v_res_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_5191_ = leanh::lean_unbox_usize(v_depth_5185_);
    leanh::lean_dec(v_depth_5185_);
    v_res_5192_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__16(v_00_u03b2_5184_, v_depth_boxed_5191_, v_keys_5186_, v_vals_5187_, v_heq_5188_, v_i_5189_, v_entries_5190_);
    leanh::lean_dec_ref(v_vals_5187_);
    leanh::lean_dec_ref(v_keys_5186_);
    return v_res_5192_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(
    mut v_x_5193_: *mut leanh::LeanObject,
    mut v_keys_5194_: *mut leanh::LeanObject,
    mut v_v_5195_: *mut leanh::LeanObject,
    mut v_k_5196_: *mut leanh::LeanObject,
    mut v_as_5197_: *mut leanh::LeanObject,
    mut v_k_5198_: *mut leanh::LeanObject,
    mut v_x_5199_: *mut leanh::LeanObject,
    mut v_x_5200_: *mut leanh::LeanObject,
    mut v_x_5201_: *mut leanh::LeanObject,
    mut v_x_5202_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5203_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5203_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___redArg(v_x_5193_, v_keys_5194_, v_v_5195_, v_k_5196_, v_as_5197_, v_k_5198_, v_x_5199_, v_x_5200_);
    return v___x_5203_;
}
pub unsafe fn l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21___boxed(
    mut v_x_5204_: *mut leanh::LeanObject,
    mut v_keys_5205_: *mut leanh::LeanObject,
    mut v_v_5206_: *mut leanh::LeanObject,
    mut v_k_5207_: *mut leanh::LeanObject,
    mut v_as_5208_: *mut leanh::LeanObject,
    mut v_k_5209_: *mut leanh::LeanObject,
    mut v_x_5210_: *mut leanh::LeanObject,
    mut v_x_5211_: *mut leanh::LeanObject,
    mut v_x_5212_: *mut leanh::LeanObject,
    mut v_x_5213_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5214_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5214_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__6_spec__13_spec__21(v_x_5204_, v_keys_5205_, v_v_5206_, v_k_5207_, v_as_5208_, v_k_5209_, v_x_5210_, v_x_5211_, v_x_5212_, v_x_5213_);
    leanh::lean_dec_ref(v_k_5209_);
    leanh::lean_dec_ref(v_keys_5205_);
    leanh::lean_dec(v_x_5204_);
    return v_res_5214_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17(
    mut v_00_u03b2_5215_: *mut leanh::LeanObject,
    mut v_x_5216_: *mut leanh::LeanObject,
    mut v_x_5217_: *mut leanh::LeanObject,
    mut v_x_5218_: *mut leanh::LeanObject,
    mut v_x_5219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5220_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10_spec__15_spec__17___redArg(v_x_5216_, v_x_5217_, v_x_5218_, v_x_5219_);
    return v___x_5220_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(
    mut v_s_5221_: *mut leanh::LeanObject,
    mut v_declName_5222_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_pre_5223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_eval_5224_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_post_5225_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocNames_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_erased_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5237_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_pre_5223_ = leanh::lean_ctor_get(v_s_5221_, 0);
                v_eval_5224_ = leanh::lean_ctor_get(v_s_5221_, 1);
                v_post_5225_ = leanh::lean_ctor_get(v_s_5221_, 2);
                v_simprocNames_5226_ = leanh::lean_ctor_get(v_s_5221_, 3);
                v_erased_5227_ = leanh::lean_ctor_get(v_s_5221_, 4);
                v_isSharedCheck_5237_ = (!leanh::lean_is_exclusive(v_s_5221_)) as u8;
                if v_isSharedCheck_5237_ == 0 {
                    v___x_5229_ = v_s_5221_;
                    v_isShared_5230_ = v_isSharedCheck_5237_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_erased_5227_);
                    leanh::lean_inc(v_simprocNames_5226_);
                    leanh::lean_inc(v_post_5225_);
                    leanh::lean_inc(v_eval_5224_);
                    leanh::lean_inc(v_pre_5223_);
                    leanh::lean_dec(v_s_5221_);
                    v___x_5229_ = leanh::lean_box(0);
                    v_isShared_5230_ = v_isSharedCheck_5237_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5231_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__1___redArg(v_simprocNames_5226_, v_declName_5222_);
                v___x_5232_ = leanh::lean_box(0);
                v___x_5233_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_erased_5227_, v_declName_5222_, v___x_5232_);
                if v_isShared_5230_ == 0 {
                    leanh::lean_ctor_set(v___x_5229_, 4, v___x_5233_);
                    leanh::lean_ctor_set(v___x_5229_, 3, v___x_5231_);
                    v___x_5235_ = v___x_5229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5236_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 0, v_pre_5223_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 1, v_eval_5224_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 2, v_post_5225_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 3, v___x_5231_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5236_, 4, v___x_5233_);
                    v___x_5235_ = v_reuseFailAlloc_5236_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5235_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5238_ = leanh::lean_box(0);
    v___x_5239_ = leanh::lean_unsigned_to_nat(16);
    v___x_5240_ = lean_mk_array(v___x_5239_, v___x_5238_);
    return v___x_5240_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5241_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__0,
    );
    v___x_5242_ = leanh::lean_unsigned_to_nat(0);
    v___x_5243_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5243_, 0, v___x_5242_);
    leanh::lean_ctor_set(v___x_5243_, 1, v___x_5241_);
    return v___x_5243_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5244_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1,
    );
    v___x_5245_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5245_, 0, v___x_5244_);
    leanh::lean_ctor_set(v___x_5245_, 1, v___x_5244_);
    return v___x_5245_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default()
-> *mut leanh::LeanObject {
    let mut v___x_5246_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5246_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2,
    );
    return v___x_5246_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs()
-> *mut leanh::LeanObject {
    let mut v___x_5247_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5247_ = l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default;
    return v___x_5247_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5249_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__2,
    );
    v___x_5250_ = lean_st_mk_ref(v___x_5249_);
    v___x_5251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5251_, 0, v___x_5250_);
    return v___x_5251_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2____boxed(
    mut v_a_5252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5253_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5253_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
    return v_res_5253_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(
    mut v_a_5254_: *mut leanh::LeanObject,
    mut v_x_5255_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5256_: u8 = 0;
    let mut v_key_5257_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5258_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5259_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5255_) == 0 {
                    v___x_5256_ = 0;
                    return v___x_5256_;
                } else {
                    v_key_5257_ = leanh::lean_ctor_get(v_x_5255_, 0);
                    v_tail_5258_ = leanh::lean_ctor_get(v_x_5255_, 2);
                    v___x_5259_ = lean_name_eq(v_key_5257_, v_a_5254_);
                    if v___x_5259_ == 0 {
                        v_x_5255_ = v_tail_5258_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_5259_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg___boxed(
    mut v_a_5261_: *mut leanh::LeanObject,
    mut v_x_5262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5263_: u8 = 0;
    let mut v_r_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5263_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_5261_, v_x_5262_);
    leanh::lean_dec(v_x_5262_);
    leanh::lean_dec(v_a_5261_);
    v_r_5264_ = leanh::lean_box((v_res_5263_) as usize);
    return v_r_5264_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(
    mut v_m_5265_: *mut leanh::LeanObject,
    mut v_a_5266_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_buckets_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5270_: u64 = 0;
    let mut v___x_5271_: u64 = 0;
    let mut v___x_5272_: u64 = 0;
    let mut v_fold_5273_: u64 = 0;
    let mut v___x_5274_: u64 = 0;
    let mut v___x_5275_: u64 = 0;
    let mut v___x_5276_: u64 = 0;
    let mut v___x_5277_: usize = 0;
    let mut v___x_5278_: usize = 0;
    let mut v___x_5279_: usize = 0;
    let mut v___x_5280_: usize = 0;
    let mut v___x_5281_: usize = 0;
    let mut v___x_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5283_: u8 = 0;
    let mut v___x_5284_: u64 = 0;
    let mut v_hash_5285_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5267_ = leanh::lean_ctor_get(v_m_5265_, 1);
                v___x_5268_ = lean_array_get_size(v_buckets_5267_);
                if leanh::lean_obj_tag(v_a_5266_) == 0 {
                    v___x_5284_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_5270_ = v___x_5284_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5285_ = leanh::lean_ctor_get_uint64(
                        v_a_5266_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5270_ = v_hash_5285_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5271_ = 32u64;
                v___x_5272_ = lean_uint64_shift_right(v___y_5270_, v___x_5271_);
                v_fold_5273_ = lean_uint64_xor(v___y_5270_, v___x_5272_);
                v___x_5274_ = 16u64;
                v___x_5275_ = lean_uint64_shift_right(v_fold_5273_, v___x_5274_);
                v___x_5276_ = lean_uint64_xor(v_fold_5273_, v___x_5275_);
                v___x_5277_ = lean_uint64_to_usize(v___x_5276_);
                v___x_5278_ = lean_usize_of_nat(v___x_5268_);
                v___x_5279_ = 1usize;
                v___x_5280_ = lean_usize_sub(v___x_5278_, v___x_5279_);
                v___x_5281_ = lean_usize_land(v___x_5277_, v___x_5280_);
                v___x_5282_ = lean_array_uget_borrowed(v_buckets_5267_, v___x_5281_);
                v___x_5283_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_5266_, v___x_5282_);
                return v___x_5283_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg___boxed(
    mut v_m_5286_: *mut leanh::LeanObject,
    mut v_a_5287_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5288_: u8 = 0;
    let mut v_r_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5288_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_5286_, v_a_5287_);
    leanh::lean_dec(v_a_5287_);
    leanh::lean_dec_ref(v_m_5286_);
    v_r_5289_ = leanh::lean_box((v_res_5288_) as usize);
    return v_r_5289_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(
    mut v_a_5290_: *mut leanh::LeanObject,
    mut v_b_5291_: *mut leanh::LeanObject,
    mut v_x_5292_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5295_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5298_: u8 = 0;
    let mut v___x_5299_: u8 = 0;
    let mut v___x_5300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5306_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5307_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5292_) == 0 {
                    leanh::lean_dec(v_b_5291_);
                    leanh::lean_dec(v_a_5290_);
                    return v_x_5292_;
                } else {
                    v_key_5293_ = leanh::lean_ctor_get(v_x_5292_, 0);
                    v_value_5294_ = leanh::lean_ctor_get(v_x_5292_, 1);
                    v_tail_5295_ = leanh::lean_ctor_get(v_x_5292_, 2);
                    v_isSharedCheck_5307_ = (!leanh::lean_is_exclusive(v_x_5292_)) as u8;
                    if v_isSharedCheck_5307_ == 0 {
                        v___x_5297_ = v_x_5292_;
                        v_isShared_5298_ = v_isSharedCheck_5307_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5295_);
                        leanh::lean_inc(v_value_5294_);
                        leanh::lean_inc(v_key_5293_);
                        leanh::lean_dec(v_x_5292_);
                        v___x_5297_ = leanh::lean_box(0);
                        v_isShared_5298_ = v_isSharedCheck_5307_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5299_ = lean_name_eq(v_key_5293_, v_a_5290_);
                if v___x_5299_ == 0 {
                    v___x_5300_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_5290_, v_b_5291_, v_tail_5295_);
                    if v_isShared_5298_ == 0 {
                        leanh::lean_ctor_set(v___x_5297_, 2, v___x_5300_);
                        v___x_5302_ = v___x_5297_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5303_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 0, v_key_5293_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 1, v_value_5294_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5303_, 2, v___x_5300_);
                        v___x_5302_ = v_reuseFailAlloc_5303_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v_value_5294_);
                    leanh::lean_dec(v_key_5293_);
                    if v_isShared_5298_ == 0 {
                        leanh::lean_ctor_set(v___x_5297_, 1, v_b_5291_);
                        leanh::lean_ctor_set(v___x_5297_, 0, v_a_5290_);
                        v___x_5305_ = v___x_5297_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5306_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 0, v_a_5290_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 1, v_b_5291_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5306_, 2, v_tail_5295_);
                        v___x_5305_ = v_reuseFailAlloc_5306_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5302_;
            }
            3 => {
                return v___x_5305_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(
    mut v_x_5308_: *mut leanh::LeanObject,
    mut v_x_5309_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_key_5310_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5315_: u8 = 0;
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5318_: u64 = 0;
    let mut v___x_5319_: u64 = 0;
    let mut v___x_5320_: u64 = 0;
    let mut v_fold_5321_: u64 = 0;
    let mut v___x_5322_: u64 = 0;
    let mut v___x_5323_: u64 = 0;
    let mut v___x_5324_: u64 = 0;
    let mut v___x_5325_: usize = 0;
    let mut v___x_5326_: usize = 0;
    let mut v___x_5327_: usize = 0;
    let mut v___x_5328_: usize = 0;
    let mut v___x_5329_: usize = 0;
    let mut v___x_5330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5336_: u64 = 0;
    let mut v_hash_5337_: u64 = 0;
    let mut v_isSharedCheck_5338_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5309_) == 0 {
                    return v_x_5308_;
                } else {
                    v_key_5310_ = leanh::lean_ctor_get(v_x_5309_, 0);
                    v_value_5311_ = leanh::lean_ctor_get(v_x_5309_, 1);
                    v_tail_5312_ = leanh::lean_ctor_get(v_x_5309_, 2);
                    v_isSharedCheck_5338_ = (!leanh::lean_is_exclusive(v_x_5309_)) as u8;
                    if v_isSharedCheck_5338_ == 0 {
                        v___x_5314_ = v_x_5309_;
                        v_isShared_5315_ = v_isSharedCheck_5338_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_tail_5312_);
                        leanh::lean_inc(v_value_5311_);
                        leanh::lean_inc(v_key_5310_);
                        leanh::lean_dec(v_x_5309_);
                        v___x_5314_ = leanh::lean_box(0);
                        v_isShared_5315_ = v_isSharedCheck_5338_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5316_ = lean_array_get_size(v_x_5308_);
                if leanh::lean_obj_tag(v_key_5310_) == 0 {
                    v___x_5336_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_5318_ = v___x_5336_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5337_ = leanh::lean_ctor_get_uint64(
                        v_key_5310_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5318_ = v_hash_5337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5319_ = 32u64;
                v___x_5320_ = lean_uint64_shift_right(v___y_5318_, v___x_5319_);
                v_fold_5321_ = lean_uint64_xor(v___y_5318_, v___x_5320_);
                v___x_5322_ = 16u64;
                v___x_5323_ = lean_uint64_shift_right(v_fold_5321_, v___x_5322_);
                v___x_5324_ = lean_uint64_xor(v_fold_5321_, v___x_5323_);
                v___x_5325_ = lean_uint64_to_usize(v___x_5324_);
                v___x_5326_ = lean_usize_of_nat(v___x_5316_);
                v___x_5327_ = 1usize;
                v___x_5328_ = lean_usize_sub(v___x_5326_, v___x_5327_);
                v___x_5329_ = lean_usize_land(v___x_5325_, v___x_5328_);
                v___x_5330_ = lean_array_uget_borrowed(v_x_5308_, v___x_5329_);
                leanh::lean_inc(v___x_5330_);
                if v_isShared_5315_ == 0 {
                    leanh::lean_ctor_set(v___x_5314_, 2, v___x_5330_);
                    v___x_5332_ = v___x_5314_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_5335_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 0, v_key_5310_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 1, v_value_5311_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5335_, 2, v___x_5330_);
                    v___x_5332_ = v_reuseFailAlloc_5335_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_5333_ = lean_array_uset(v_x_5308_, v___x_5329_, v___x_5332_);
                v_x_5308_ = v___x_5333_;
                v_x_5309_ = v_tail_5312_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(
    mut v_i_5339_: *mut leanh::LeanObject,
    mut v_source_5340_: *mut leanh::LeanObject,
    mut v_target_5341_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5343_: u8 = 0;
    let mut v_es_5344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_5346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_5347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5342_ = lean_array_get_size(v_source_5340_);
                v___x_5343_ = lean_nat_dec_lt(v_i_5339_, v___x_5342_);
                if v___x_5343_ == 0 {
                    leanh::lean_dec_ref(v_source_5340_);
                    leanh::lean_dec(v_i_5339_);
                    return v_target_5341_;
                } else {
                    v_es_5344_ = lean_array_fget(v_source_5340_, v_i_5339_);
                    v___x_5345_ = leanh::lean_box(0);
                    v_source_5346_ = lean_array_fset(v_source_5340_, v_i_5339_, v___x_5345_);
                    v_target_5347_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_target_5341_, v_es_5344_);
                    v___x_5348_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5349_ = lean_nat_add(v_i_5339_, v___x_5348_);
                    leanh::lean_dec(v_i_5339_);
                    v_i_5339_ = v___x_5349_;
                    v_source_5340_ = v_source_5346_;
                    v_target_5341_ = v_target_5347_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(
    mut v_data_5351_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_5354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5358_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5352_ = lean_array_get_size(v_data_5351_);
    v___x_5353_ = leanh::lean_unsigned_to_nat(2);
    v_nbuckets_5354_ = lean_nat_mul(v___x_5352_, v___x_5353_);
    v___x_5355_ = leanh::lean_unsigned_to_nat(0);
    v___x_5356_ = leanh::lean_box(0);
    v___x_5357_ = lean_mk_array(v_nbuckets_5354_, v___x_5356_);
    v___x_5358_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v___x_5355_, v_data_5351_, v___x_5357_);
    return v___x_5358_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(
    mut v_m_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_b_5361_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_size_5362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5366_: u8 = 0;
    let mut v___x_5367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5369_: u64 = 0;
    let mut v___x_5370_: u64 = 0;
    let mut v___x_5371_: u64 = 0;
    let mut v_fold_5372_: u64 = 0;
    let mut v___x_5373_: u64 = 0;
    let mut v___x_5374_: u64 = 0;
    let mut v___x_5375_: u64 = 0;
    let mut v___x_5376_: usize = 0;
    let mut v___x_5377_: usize = 0;
    let mut v___x_5378_: usize = 0;
    let mut v___x_5379_: usize = 0;
    let mut v___x_5380_: usize = 0;
    let mut v_bkt_5381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5382_: u8 = 0;
    let mut v___x_5383_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_5384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5392_: u8 = 0;
    let mut v_val_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5400_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_5401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5407_: u64 = 0;
    let mut v_hash_5408_: u64 = 0;
    let mut v_isSharedCheck_5409_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_5362_ = leanh::lean_ctor_get(v_m_5359_, 0);
                v_buckets_5363_ = leanh::lean_ctor_get(v_m_5359_, 1);
                v_isSharedCheck_5409_ = (!leanh::lean_is_exclusive(v_m_5359_)) as u8;
                if v_isSharedCheck_5409_ == 0 {
                    v___x_5365_ = v_m_5359_;
                    v_isShared_5366_ = v_isSharedCheck_5409_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_buckets_5363_);
                    leanh::lean_inc(v_size_5362_);
                    leanh::lean_dec(v_m_5359_);
                    v___x_5365_ = leanh::lean_box(0);
                    v_isShared_5366_ = v_isSharedCheck_5409_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5367_ = lean_array_get_size(v_buckets_5363_);
                if leanh::lean_obj_tag(v_a_5360_) == 0 {
                    v___x_5407_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_5369_ = v___x_5407_;
                    state = 2;
                    continue;
                } else {
                    v_hash_5408_ = leanh::lean_ctor_get_uint64(
                        v_a_5360_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5369_ = v_hash_5408_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5370_ = 32u64;
                v___x_5371_ = lean_uint64_shift_right(v___y_5369_, v___x_5370_);
                v_fold_5372_ = lean_uint64_xor(v___y_5369_, v___x_5371_);
                v___x_5373_ = 16u64;
                v___x_5374_ = lean_uint64_shift_right(v_fold_5372_, v___x_5373_);
                v___x_5375_ = lean_uint64_xor(v_fold_5372_, v___x_5374_);
                v___x_5376_ = lean_uint64_to_usize(v___x_5375_);
                v___x_5377_ = lean_usize_of_nat(v___x_5367_);
                v___x_5378_ = 1usize;
                v___x_5379_ = lean_usize_sub(v___x_5377_, v___x_5378_);
                v___x_5380_ = lean_usize_land(v___x_5376_, v___x_5379_);
                v_bkt_5381_ = lean_array_uget_borrowed(v_buckets_5363_, v___x_5380_);
                v___x_5382_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_5360_, v_bkt_5381_);
                if v___x_5382_ == 0 {
                    v___x_5383_ = leanh::lean_unsigned_to_nat(1);
                    v_size_x27_5384_ = lean_nat_add(v_size_5362_, v___x_5383_);
                    leanh::lean_dec(v_size_5362_);
                    leanh::lean_inc(v_bkt_5381_);
                    v___x_5385_ = leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5385_, 0, v_a_5360_);
                    leanh::lean_ctor_set(v___x_5385_, 1, v_b_5361_);
                    leanh::lean_ctor_set(v___x_5385_, 2, v_bkt_5381_);
                    v_buckets_x27_5386_ =
                        lean_array_uset(v_buckets_5363_, v___x_5380_, v___x_5385_);
                    v___x_5387_ = leanh::lean_unsigned_to_nat(4);
                    v___x_5388_ = lean_nat_mul(v_size_x27_5384_, v___x_5387_);
                    v___x_5389_ = leanh::lean_unsigned_to_nat(3);
                    v___x_5390_ = lean_nat_div(v___x_5388_, v___x_5389_);
                    leanh::lean_dec(v___x_5388_);
                    v___x_5391_ = lean_array_get_size(v_buckets_x27_5386_);
                    v___x_5392_ = lean_nat_dec_le(v___x_5390_, v___x_5391_);
                    leanh::lean_dec(v___x_5390_);
                    if v___x_5392_ == 0 {
                        v_val_5393_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_buckets_x27_5386_);
                        if v_isShared_5366_ == 0 {
                            leanh::lean_ctor_set(v___x_5365_, 1, v_val_5393_);
                            leanh::lean_ctor_set(v___x_5365_, 0, v_size_x27_5384_);
                            v___x_5395_ = v___x_5365_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_5396_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5396_,
                                0,
                                v_size_x27_5384_,
                            );
                            leanh::lean_ctor_set(v_reuseFailAlloc_5396_, 1, v_val_5393_);
                            v___x_5395_ = v_reuseFailAlloc_5396_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_5366_ == 0 {
                            leanh::lean_ctor_set(v___x_5365_, 1, v_buckets_x27_5386_);
                            leanh::lean_ctor_set(v___x_5365_, 0, v_size_x27_5384_);
                            v___x_5398_ = v___x_5365_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_5399_ =
                                leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5399_,
                                0,
                                v_size_x27_5384_,
                            );
                            leanh::lean_ctor_set(
                                v_reuseFailAlloc_5399_,
                                1,
                                v_buckets_x27_5386_,
                            );
                            v___x_5398_ = v_reuseFailAlloc_5399_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_inc(v_bkt_5381_);
                    v___x_5400_ = leanh::lean_box(0);
                    v_buckets_x27_5401_ =
                        lean_array_uset(v_buckets_5363_, v___x_5380_, v___x_5400_);
                    v___x_5402_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_5360_, v_b_5361_, v_bkt_5381_);
                    v___x_5403_ = lean_array_uset(v_buckets_x27_5401_, v___x_5380_, v___x_5402_);
                    if v_isShared_5366_ == 0 {
                        leanh::lean_ctor_set(v___x_5365_, 1, v___x_5403_);
                        v___x_5405_ = v___x_5365_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5406_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 0, v_size_5362_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5406_, 1, v___x_5403_);
                        v___x_5405_ = v_reuseFailAlloc_5406_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_5395_;
            }
            4 => {
                return v___x_5398_;
            }
            5 => {
                return v___x_5405_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5411_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__0;
    v___x_5412_ = lean_mk_io_user_error(v___x_5411_);
    return v___x_5412_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(
    mut v_declName_5415_: *mut leanh::LeanObject,
    mut v_keys_5416_: *mut leanh::LeanObject,
    mut v_proc_5417_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5423_: u8 = 0;
    let mut v___x_5424_: u8 = 0;
    let mut v___x_5425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_5431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5432_: u8 = 0;
    let mut v___x_5433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_5434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_procs_5435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5438_: u8 = 0;
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5448_: u8 = 0;
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5459_: u8 = 0;
    let mut v_a_5460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5463_: u8 = 0;
    let mut v___x_5465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5467_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5419_ = l_Lean_initializing();
                if leanh::lean_obj_tag(v___x_5419_) == 0 {
                    v_a_5420_ = leanh::lean_ctor_get(v___x_5419_, 0);
                    v_isSharedCheck_5459_ = (!leanh::lean_is_exclusive(v___x_5419_)) as u8;
                    if v_isSharedCheck_5459_ == 0 {
                        v___x_5422_ = v___x_5419_;
                        v_isShared_5423_ = v_isSharedCheck_5459_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5420_);
                        leanh::lean_dec(v___x_5419_);
                        v___x_5422_ = leanh::lean_box(0);
                        v_isShared_5423_ = v_isSharedCheck_5459_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_proc_5417_);
                    leanh::lean_dec_ref(v_keys_5416_);
                    leanh::lean_dec(v_declName_5415_);
                    v_a_5460_ = leanh::lean_ctor_get(v___x_5419_, 0);
                    v_isSharedCheck_5467_ = (!leanh::lean_is_exclusive(v___x_5419_)) as u8;
                    if v_isSharedCheck_5467_ == 0 {
                        v___x_5462_ = v___x_5419_;
                        v_isShared_5463_ = v_isSharedCheck_5467_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5460_);
                        leanh::lean_dec(v___x_5419_);
                        v___x_5462_ = leanh::lean_box(0);
                        v_isShared_5463_ = v_isSharedCheck_5467_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5424_ = (leanh::lean_unbox(v_a_5420_) as u8);
                leanh::lean_dec(v_a_5420_);
                if v___x_5424_ == 0 {
                    leanh::lean_dec_ref(v_proc_5417_);
                    leanh::lean_dec_ref(v_keys_5416_);
                    leanh::lean_dec(v_declName_5415_);
                    v___x_5425_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__1,
                    );
                    if v_isShared_5423_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_5422_, 1);
                        leanh::lean_ctor_set(v___x_5422_, 0, v___x_5425_);
                        v___x_5427_ = v___x_5422_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5428_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5425_);
                        v___x_5427_ = v_reuseFailAlloc_5428_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_5429_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
                    v___x_5430_ = lean_st_ref_get(v___x_5429_);
                    v_keys_5431_ = leanh::lean_ctor_get(v___x_5430_, 0);
                    leanh::lean_inc_ref(v_keys_5431_);
                    leanh::lean_dec(v___x_5430_);
                    v___x_5432_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_keys_5431_, v_declName_5415_);
                    leanh::lean_dec_ref(v_keys_5431_);
                    if v___x_5432_ == 0 {
                        v___x_5433_ = lean_st_ref_take(v___x_5429_);
                        v_keys_5434_ = leanh::lean_ctor_get(v___x_5433_, 0);
                        v_procs_5435_ = leanh::lean_ctor_get(v___x_5433_, 1);
                        v_isSharedCheck_5448_ =
                            (!leanh::lean_is_exclusive(v___x_5433_)) as u8;
                        if v_isSharedCheck_5448_ == 0 {
                            v___x_5437_ = v___x_5433_;
                            v_isShared_5438_ = v_isSharedCheck_5448_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_procs_5435_);
                            leanh::lean_inc(v_keys_5434_);
                            leanh::lean_dec(v___x_5433_);
                            v___x_5437_ = leanh::lean_box(0);
                            v_isShared_5438_ = v_isSharedCheck_5448_;
                            state = 3;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_proc_5417_);
                        leanh::lean_dec_ref(v_keys_5416_);
                        v___x_5449_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__2;
                        v___x_5450_ = l_Lean_privateToUserName(v_declName_5415_);
                        v___x_5451_ =
                            l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                                v___x_5450_,
                                v___x_5432_,
                            );
                        v___x_5452_ = lean_string_append(v___x_5449_, v___x_5451_);
                        leanh::lean_dec_ref(v___x_5451_);
                        v___x_5453_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3;
                        v___x_5454_ = lean_string_append(v___x_5452_, v___x_5453_);
                        v___x_5455_ = lean_mk_io_user_error(v___x_5454_);
                        if v_isShared_5423_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_5422_, 1);
                            leanh::lean_ctor_set(v___x_5422_, 0, v___x_5455_);
                            v___x_5457_ = v___x_5422_;
                            state = 6;
                            continue;
                        } else {
                            v_reuseFailAlloc_5458_ =
                                leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_5458_, 0, v___x_5455_);
                            v___x_5457_ = v_reuseFailAlloc_5458_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5427_;
            }
            3 => {
                leanh::lean_inc(v_declName_5415_);
                v___x_5439_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_keys_5434_, v_declName_5415_, v_keys_5416_);
                v___x_5440_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_procs_5435_, v_declName_5415_, v_proc_5417_);
                if v_isShared_5438_ == 0 {
                    leanh::lean_ctor_set(v___x_5437_, 1, v___x_5440_);
                    leanh::lean_ctor_set(v___x_5437_, 0, v___x_5439_);
                    v___x_5442_ = v___x_5437_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5447_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5447_, 0, v___x_5439_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5447_, 1, v___x_5440_);
                    v___x_5442_ = v_reuseFailAlloc_5447_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_5443_ = lean_st_ref_set(v___x_5429_, v___x_5442_);
                if v_isShared_5423_ == 0 {
                    leanh::lean_ctor_set(v___x_5422_, 0, v___x_5443_);
                    v___x_5445_ = v___x_5422_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5446_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5443_);
                    v___x_5445_ = v_reuseFailAlloc_5446_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5445_;
            }
            6 => {
                return v___x_5457_;
            }
            7 => {
                if v_isShared_5463_ == 0 {
                    v___x_5465_ = v___x_5462_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_5466_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5466_, 0, v_a_5460_);
                    v___x_5465_ = v_reuseFailAlloc_5466_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_5465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___boxed(
    mut v_declName_5468_: *mut leanh::LeanObject,
    mut v_keys_5469_: *mut leanh::LeanObject,
    mut v_proc_5470_: *mut leanh::LeanObject,
    mut v_a_5471_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5472_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5472_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc(
        v_declName_5468_,
        v_keys_5469_,
        v_proc_5470_,
    );
    return v_res_5472_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(
    mut v_00_u03b2_5473_: *mut leanh::LeanObject,
    mut v_m_5474_: *mut leanh::LeanObject,
    mut v_a_5475_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5476_: u8 = 0;
    v___x_5476_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_m_5474_, v_a_5475_);
    return v___x_5476_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___boxed(
    mut v_00_u03b2_5477_: *mut leanh::LeanObject,
    mut v_m_5478_: *mut leanh::LeanObject,
    mut v_a_5479_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5480_: u8 = 0;
    let mut v_r_5481_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5480_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0(v_00_u03b2_5477_, v_m_5478_, v_a_5479_);
    leanh::lean_dec(v_a_5479_);
    leanh::lean_dec_ref(v_m_5478_);
    v_r_5481_ = leanh::lean_box((v_res_5480_) as usize);
    return v_r_5481_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1(
    mut v_00_u03b2_5482_: *mut leanh::LeanObject,
    mut v_m_5483_: *mut leanh::LeanObject,
    mut v_a_5484_: *mut leanh::LeanObject,
    mut v_b_5485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5486_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1___redArg(v_m_5483_, v_a_5484_, v_b_5485_);
    return v___x_5486_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(
    mut v_00_u03b2_5487_: *mut leanh::LeanObject,
    mut v_a_5488_: *mut leanh::LeanObject,
    mut v_x_5489_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_5490_: u8 = 0;
    v___x_5490_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___redArg(v_a_5488_, v_x_5489_);
    return v___x_5490_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0___boxed(
    mut v_00_u03b2_5491_: *mut leanh::LeanObject,
    mut v_a_5492_: *mut leanh::LeanObject,
    mut v_x_5493_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5494_: u8 = 0;
    let mut v_r_5495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5494_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0_spec__0(v_00_u03b2_5491_, v_a_5492_, v_x_5493_);
    leanh::lean_dec(v_x_5493_);
    leanh::lean_dec(v_a_5492_);
    v_r_5495_ = leanh::lean_box((v_res_5494_) as usize);
    return v_r_5495_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2(
    mut v_00_u03b2_5496_: *mut leanh::LeanObject,
    mut v_data_5497_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5498_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2___redArg(v_data_5497_);
    return v___x_5498_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3(
    mut v_00_u03b2_5499_: *mut leanh::LeanObject,
    mut v_a_5500_: *mut leanh::LeanObject,
    mut v_b_5501_: *mut leanh::LeanObject,
    mut v_x_5502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5503_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__3___redArg(v_a_5500_, v_b_5501_, v_x_5502_);
    return v___x_5503_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3(
    mut v_00_u03b2_5504_: *mut leanh::LeanObject,
    mut v_i_5505_: *mut leanh::LeanObject,
    mut v_source_5506_: *mut leanh::LeanObject,
    mut v_target_5507_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5508_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5508_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3___redArg(v_i_5505_, v_source_5506_, v_target_5507_);
    return v___x_5508_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4(
    mut v_00_u03b2_5509_: *mut leanh::LeanObject,
    mut v_x_5510_: *mut leanh::LeanObject,
    mut v_x_5511_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5512_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__1_spec__2_spec__3_spec__4___redArg(v_x_5510_, v_x_5511_);
    return v___x_5512_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(
    mut v_d_u2081_5520_: *mut leanh::LeanObject,
    mut v_d_u2082_5521_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_declName_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_5523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5524_: u8 = 0;
    v_declName_5522_ = leanh::lean_ctor_get(v_d_u2081_5520_, 0);
    v_declName_5523_ = leanh::lean_ctor_get(v_d_u2082_5521_, 0);
    v___x_5524_ = l_Lean_Name_quickLt(v_declName_5522_, v_declName_5523_);
    return v___x_5524_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt___boxed(
    mut v_d_u2081_5525_: *mut leanh::LeanObject,
    mut v_d_u2082_5526_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5527_: u8 = 0;
    let mut v_r_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5527_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_d_u2081_5525_, v_d_u2082_5526_);
    leanh::lean_dec_ref(v_d_u2082_5526_);
    leanh::lean_dec_ref(v_d_u2081_5525_);
    v_r_5528_ = leanh::lean_box((v_res_5527_) as usize);
    return v_r_5528_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_5529_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5529_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_5529_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5530_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__0,
    );
    v___x_5531_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_5531_, 0, v___x_5530_);
    return v___x_5531_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5532_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1,
    );
    v___x_5533_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default___closed__1,
    );
    v___x_5534_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5534_, 0, v___x_5533_);
    leanh::lean_ctor_set(v___x_5534_, 1, v___x_5532_);
    return v___x_5534_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default()
-> *mut leanh::LeanObject {
    let mut v___x_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5535_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__2,
    );
    return v___x_5535_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState()
-> *mut leanh::LeanObject {
    let mut v___x_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5536_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
    return v___x_5536_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(
    mut v_s_5537_: *mut leanh::LeanObject,
    mut v_d_5538_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_5540_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5543_: u8 = 0;
    let mut v_declName_5544_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_5545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5548_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5550_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_builtin_5539_ = leanh::lean_ctor_get(v_s_5537_, 0);
                v_newEntries_5540_ = leanh::lean_ctor_get(v_s_5537_, 1);
                v_isSharedCheck_5550_ = (!leanh::lean_is_exclusive(v_s_5537_)) as u8;
                if v_isSharedCheck_5550_ == 0 {
                    v___x_5542_ = v_s_5537_;
                    v_isShared_5543_ = v_isSharedCheck_5550_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_newEntries_5540_);
                    leanh::lean_inc(v_builtin_5539_);
                    leanh::lean_dec(v_s_5537_);
                    v___x_5542_ = leanh::lean_box(0);
                    v_isShared_5543_ = v_isSharedCheck_5550_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_declName_5544_ = leanh::lean_ctor_get(v_d_5538_, 0);
                leanh::lean_inc(v_declName_5544_);
                v_keys_5545_ = leanh::lean_ctor_get(v_d_5538_, 1);
                leanh::lean_inc_ref(v_keys_5545_);
                leanh::lean_dec_ref(v_d_5538_);
                v___x_5546_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_5540_, v_declName_5544_, v_keys_5545_);
                if v_isShared_5543_ == 0 {
                    leanh::lean_ctor_set(v___x_5542_, 1, v___x_5546_);
                    v___x_5548_ = v___x_5542_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5549_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5549_, 0, v_builtin_5539_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5549_, 1, v___x_5546_);
                    v___x_5548_ = v_reuseFailAlloc_5549_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5548_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(
    mut v_result_5551_: *mut leanh::LeanObject,
    mut v_declName_5552_: *mut leanh::LeanObject,
    mut v_keys_5553_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5555_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5554_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5554_, 0, v_declName_5552_);
    leanh::lean_ctor_set(v___x_5554_, 1, v_keys_5553_);
    v___x_5555_ = lean_array_push(v_result_5551_, v___x_5554_);
    return v___x_5555_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0(
    mut v_f_5556_: *mut leanh::LeanObject,
    mut v_x1_5557_: *mut leanh::LeanObject,
    mut v_x2_5558_: *mut leanh::LeanObject,
    mut v_x3_5559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5560_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5560_ = leanh::lean_apply_3(v_f_5556_, v_x1_5557_, v_x2_5558_, v_x3_5559_);
    return v___x_5560_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(
    mut v_f_5561_: *mut leanh::LeanObject,
    mut v_keys_5562_: *mut leanh::LeanObject,
    mut v_vals_5563_: *mut leanh::LeanObject,
    mut v_i_5564_: *mut leanh::LeanObject,
    mut v_acc_5565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5567_: u8 = 0;
    let mut v_k_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5566_ = lean_array_get_size(v_keys_5562_);
                v___x_5567_ = lean_nat_dec_lt(v_i_5564_, v___x_5566_);
                if v___x_5567_ == 0 {
                    leanh::lean_dec(v_i_5564_);
                    leanh::lean_dec(v_f_5561_);
                    return v_acc_5565_;
                } else {
                    v_k_5568_ = lean_array_fget_borrowed(v_keys_5562_, v_i_5564_);
                    v_v_5569_ = lean_array_fget_borrowed(v_vals_5563_, v_i_5564_);
                    leanh::lean_inc(v_f_5561_);
                    leanh::lean_inc(v_v_5569_);
                    leanh::lean_inc(v_k_5568_);
                    v___x_5570_ =
                        leanh::lean_apply_3(v_f_5561_, v_acc_5565_, v_k_5568_, v_v_5569_);
                    v___x_5571_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5572_ = lean_nat_add(v_i_5564_, v___x_5571_);
                    leanh::lean_dec(v_i_5564_);
                    v_i_5564_ = v___x_5572_;
                    v_acc_5565_ = v___x_5570_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg___boxed(
    mut v_f_5574_: *mut leanh::LeanObject,
    mut v_keys_5575_: *mut leanh::LeanObject,
    mut v_vals_5576_: *mut leanh::LeanObject,
    mut v_i_5577_: *mut leanh::LeanObject,
    mut v_acc_5578_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5579_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_5574_, v_keys_5575_, v_vals_5576_, v_i_5577_, v_acc_5578_);
    leanh::lean_dec_ref(v_vals_5576_);
    leanh::lean_dec_ref(v_keys_5575_);
    return v_res_5579_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(
    mut v_f_5580_: *mut leanh::LeanObject,
    mut v_x_5581_: *mut leanh::LeanObject,
    mut v_x_5582_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_x_5581_) == 0 {
        let mut v_es_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5586_: u8 = 0;
        v_es_5583_ = leanh::lean_ctor_get(v_x_5581_, 0);
        v___x_5584_ = leanh::lean_unsigned_to_nat(0);
        v___x_5585_ = lean_array_get_size(v_es_5583_);
        v___x_5586_ = lean_nat_dec_lt(v___x_5584_, v___x_5585_);
        if v___x_5586_ == 0 {
            leanh::lean_dec(v_f_5580_);
            return v_x_5582_;
        } else {
            let mut v___x_5587_: u8 = 0;
            v___x_5587_ = lean_nat_dec_le(v___x_5585_, v___x_5585_);
            if v___x_5587_ == 0 {
                if v___x_5586_ == 0 {
                    leanh::lean_dec(v_f_5580_);
                    return v_x_5582_;
                } else {
                    let mut v___x_5588_: usize = 0;
                    let mut v___x_5589_: usize = 0;
                    let mut v___x_5590_: *mut leanh::LeanObject = core::ptr::null_mut();
                    v___x_5588_ = 0usize;
                    v___x_5589_ = lean_usize_of_nat(v___x_5585_);
                    v___x_5590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_5580_, v_es_5583_, v___x_5588_, v___x_5589_, v_x_5582_);
                    return v___x_5590_;
                }
            } else {
                let mut v___x_5591_: usize = 0;
                let mut v___x_5592_: usize = 0;
                let mut v___x_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
                v___x_5591_ = 0usize;
                v___x_5592_ = lean_usize_of_nat(v___x_5585_);
                v___x_5593_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_5580_, v_es_5583_, v___x_5591_, v___x_5592_, v_x_5582_);
                return v___x_5593_;
            }
        }
    } else {
        let mut v_ks_5594_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_vs_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5596_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_ks_5594_ = leanh::lean_ctor_get(v_x_5581_, 0);
        v_vs_5595_ = leanh::lean_ctor_get(v_x_5581_, 1);
        v___x_5596_ = leanh::lean_unsigned_to_nat(0);
        v___x_5597_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_5580_, v_ks_5594_, v_vs_5595_, v___x_5596_, v_x_5582_);
        return v___x_5597_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(
    mut v_f_5598_: *mut leanh::LeanObject,
    mut v_as_5599_: *mut leanh::LeanObject,
    mut v_i_5600_: usize,
    mut v_stop_5601_: usize,
    mut v_b_5602_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5605_: usize = 0;
    let mut v___x_5606_: usize = 0;
    let mut v___x_5608_: u8 = 0;
    let mut v___x_5609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_5613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5608_ = lean_usize_dec_eq(v_i_5600_, v_stop_5601_);
                if v___x_5608_ == 0 {
                    v___x_5609_ = lean_array_uget_borrowed(v_as_5599_, v_i_5600_);
                    match leanh::lean_obj_tag(v___x_5609_) {
                        0 => {
                            v_key_5610_ = leanh::lean_ctor_get(v___x_5609_, 0);
                            v_val_5611_ = leanh::lean_ctor_get(v___x_5609_, 1);
                            leanh::lean_inc(v_f_5598_);
                            leanh::lean_inc(v_val_5611_);
                            leanh::lean_inc(v_key_5610_);
                            v___x_5612_ = leanh::lean_apply_3(
                                v_f_5598_,
                                v_b_5602_,
                                v_key_5610_,
                                v_val_5611_,
                            );
                            v___y_5604_ = v___x_5612_;
                            state = 1;
                            continue;
                        }
                        1 => {
                            v_node_5613_ = leanh::lean_ctor_get(v___x_5609_, 0);
                            leanh::lean_inc(v_f_5598_);
                            v___x_5614_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_5598_, v_node_5613_, v_b_5602_);
                            v___y_5604_ = v___x_5614_;
                            state = 1;
                            continue;
                        }
                        _ => {
                            v___y_5604_ = v_b_5602_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_f_5598_);
                    return v_b_5602_;
                }
            }
            1 => {
                v___x_5605_ = 1usize;
                v___x_5606_ = lean_usize_add(v_i_5600_, v___x_5605_);
                v_i_5600_ = v___x_5606_;
                v_b_5602_ = v___y_5604_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg___boxed(
    mut v_f_5615_: *mut leanh::LeanObject,
    mut v_as_5616_: *mut leanh::LeanObject,
    mut v_i_5617_: *mut leanh::LeanObject,
    mut v_stop_5618_: *mut leanh::LeanObject,
    mut v_b_5619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5620_: usize = 0;
    let mut v_stop_boxed_5621_: usize = 0;
    let mut v_res_5622_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5620_ = leanh::lean_unbox_usize(v_i_5617_);
    leanh::lean_dec(v_i_5617_);
    v_stop_boxed_5621_ = leanh::lean_unbox_usize(v_stop_5618_);
    leanh::lean_dec(v_stop_5618_);
    v_res_5622_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_5615_, v_as_5616_, v_i_boxed_5620_, v_stop_boxed_5621_, v_b_5619_);
    leanh::lean_dec_ref(v_as_5616_);
    return v_res_5622_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(
    mut v_f_5623_: *mut leanh::LeanObject,
    mut v_x_5624_: *mut leanh::LeanObject,
    mut v_x_5625_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5626_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5626_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_5623_, v_x_5624_, v_x_5625_);
    leanh::lean_dec_ref(v_x_5624_);
    return v_res_5626_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(
    mut v_map_5627_: *mut leanh::LeanObject,
    mut v_f_5628_: *mut leanh::LeanObject,
    mut v_init_5629_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_5630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5631_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5630_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___lam__0 as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_5630_, 0, v_f_5628_);
    v___x_5631_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v___f_5630_, v_map_5627_, v_init_5629_);
    return v___x_5631_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg___boxed(
    mut v_map_5632_: *mut leanh::LeanObject,
    mut v_f_5633_: *mut leanh::LeanObject,
    mut v_init_5634_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5635_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5635_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_5632_, v_f_5633_, v_init_5634_);
    leanh::lean_dec_ref(v_map_5632_);
    return v_res_5635_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(
    mut v_hi_5636_: *mut leanh::LeanObject,
    mut v_pivot_5637_: *mut leanh::LeanObject,
    mut v_as_5638_: *mut leanh::LeanObject,
    mut v_i_5639_: *mut leanh::LeanObject,
    mut v_k_5640_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5641_: u8 = 0;
    let mut v___x_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5645_: u8 = 0;
    let mut v___x_5646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5650_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5641_ = lean_nat_dec_lt(v_k_5640_, v_hi_5636_);
                if v___x_5641_ == 0 {
                    leanh::lean_dec(v_k_5640_);
                    v___x_5642_ = lean_array_fswap(v_as_5638_, v_i_5639_, v_hi_5636_);
                    v___x_5643_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5643_, 0, v_i_5639_);
                    leanh::lean_ctor_set(v___x_5643_, 1, v___x_5642_);
                    return v___x_5643_;
                } else {
                    v___x_5644_ = lean_array_fget_borrowed(v_as_5638_, v_k_5640_);
                    v___x_5645_ =
                        l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_5644_, v_pivot_5637_);
                    if v___x_5645_ == 0 {
                        v___x_5646_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5647_ = lean_nat_add(v_k_5640_, v___x_5646_);
                        leanh::lean_dec(v_k_5640_);
                        v_k_5640_ = v___x_5647_;
                        state = 0;
                        continue;
                    } else {
                        v___x_5649_ = lean_array_fswap(v_as_5638_, v_i_5639_, v_k_5640_);
                        v___x_5650_ = leanh::lean_unsigned_to_nat(1);
                        v___x_5651_ = lean_nat_add(v_i_5639_, v___x_5650_);
                        leanh::lean_dec(v_i_5639_);
                        v___x_5652_ = lean_nat_add(v_k_5640_, v___x_5650_);
                        leanh::lean_dec(v_k_5640_);
                        v_as_5638_ = v___x_5649_;
                        v_i_5639_ = v___x_5651_;
                        v_k_5640_ = v___x_5652_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(
    mut v_hi_5654_: *mut leanh::LeanObject,
    mut v_pivot_5655_: *mut leanh::LeanObject,
    mut v_as_5656_: *mut leanh::LeanObject,
    mut v_i_5657_: *mut leanh::LeanObject,
    mut v_k_5658_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5659_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5659_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_5654_, v_pivot_5655_, v_as_5656_, v_i_5657_, v_k_5658_);
    leanh::lean_dec_ref(v_pivot_5655_);
    leanh::lean_dec(v_hi_5654_);
    return v_res_5659_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(
    mut v_n_5660_: *mut leanh::LeanObject,
    mut v_as_5661_: *mut leanh::LeanObject,
    mut v_lo_5662_: *mut leanh::LeanObject,
    mut v_hi_5663_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pivot_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5670_: u8 = 0;
    let mut v___x_5671_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5675_: u8 = 0;
    let mut v___x_5676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mid_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5683_: u8 = 0;
    let mut v___x_5684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5689_: u8 = 0;
    let mut v___x_5690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5693_: u8 = 0;
    let mut v___x_5694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5675_ = lean_nat_dec_lt(v_lo_5662_, v_hi_5663_);
                if v___x_5675_ == 0 {
                    leanh::lean_dec(v_lo_5662_);
                    return v_as_5661_;
                } else {
                    v___x_5676_ = lean_nat_add(v_lo_5662_, v_hi_5663_);
                    v___x_5677_ = leanh::lean_unsigned_to_nat(1);
                    v_mid_5678_ = lean_nat_shiftr(v___x_5676_, v___x_5677_);
                    leanh::lean_dec(v___x_5676_);
                    v___x_5691_ = lean_array_fget_borrowed(v_as_5661_, v_mid_5678_);
                    v___x_5692_ = lean_array_fget_borrowed(v_as_5661_, v_lo_5662_);
                    v___x_5693_ =
                        l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_5691_, v___x_5692_);
                    if v___x_5693_ == 0 {
                        v___y_5686_ = v_as_5661_;
                        state = 3;
                        continue;
                    } else {
                        v___x_5694_ = lean_array_fswap(v_as_5661_, v_lo_5662_, v_mid_5678_);
                        v___y_5686_ = v___x_5694_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_pivot_5666_ = lean_array_fget(v___y_5665_, v_hi_5663_);
                leanh::lean_inc_n(v_lo_5662_, 2);
                v___x_5667_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_5663_, v_pivot_5666_, v___y_5665_, v_lo_5662_, v_lo_5662_);
                leanh::lean_dec(v_pivot_5666_);
                v_fst_5668_ = leanh::lean_ctor_get(v___x_5667_, 0);
                leanh::lean_inc(v_fst_5668_);
                v_snd_5669_ = leanh::lean_ctor_get(v___x_5667_, 1);
                leanh::lean_inc(v_snd_5669_);
                leanh::lean_dec_ref(v___x_5667_);
                v___x_5670_ = lean_nat_dec_le(v_hi_5663_, v_fst_5668_);
                if v___x_5670_ == 0 {
                    v___x_5671_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_5660_, v_snd_5669_, v_lo_5662_, v_fst_5668_);
                    v___x_5672_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5673_ = lean_nat_add(v_fst_5668_, v___x_5672_);
                    leanh::lean_dec(v_fst_5668_);
                    v_as_5661_ = v___x_5671_;
                    v_lo_5662_ = v___x_5673_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_fst_5668_);
                    leanh::lean_dec(v_lo_5662_);
                    return v_snd_5669_;
                }
            }
            2 => {
                v___x_5681_ = lean_array_fget_borrowed(v___y_5680_, v_mid_5678_);
                v___x_5682_ = lean_array_fget_borrowed(v___y_5680_, v_hi_5663_);
                v___x_5683_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_5681_, v___x_5682_);
                if v___x_5683_ == 0 {
                    leanh::lean_dec(v_mid_5678_);
                    v___y_5665_ = v___y_5680_;
                    state = 1;
                    continue;
                } else {
                    v___x_5684_ = lean_array_fswap(v___y_5680_, v_mid_5678_, v_hi_5663_);
                    leanh::lean_dec(v_mid_5678_);
                    v___y_5665_ = v___x_5684_;
                    state = 1;
                    continue;
                }
            }
            3 => {
                v___x_5687_ = lean_array_fget_borrowed(v___y_5686_, v_hi_5663_);
                v___x_5688_ = lean_array_fget_borrowed(v___y_5686_, v_lo_5662_);
                v___x_5689_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v___x_5687_, v___x_5688_);
                if v___x_5689_ == 0 {
                    v___y_5680_ = v___y_5686_;
                    state = 2;
                    continue;
                } else {
                    v___x_5690_ = lean_array_fswap(v___y_5686_, v_lo_5662_, v_hi_5663_);
                    v___y_5680_ = v___x_5690_;
                    state = 2;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg___boxed(
    mut v_n_5695_: *mut leanh::LeanObject,
    mut v_as_5696_: *mut leanh::LeanObject,
    mut v_lo_5697_: *mut leanh::LeanObject,
    mut v_hi_5698_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5699_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_5695_, v_as_5696_, v_lo_5697_, v_hi_5698_);
    leanh::lean_dec(v_hi_5698_);
    leanh::lean_dec(v_n_5695_);
    return v_res_5699_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(
    mut v___f_5702_: *mut leanh::LeanObject,
    mut v_s_5703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_newEntries_5704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5706_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5708_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5709_: u8 = 0;
    let mut v___x_5710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5714_: u8 = 0;
    let mut v___x_5715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5717_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_newEntries_5704_ = leanh::lean_ctor_get(v_s_5703_, 1);
                v___x_5705_ = leanh::lean_unsigned_to_nat(0);
                v___x_5706_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
                v_result_5707_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_5704_, v___f_5702_, v___x_5706_);
                v___x_5708_ = lean_array_get_size(v_result_5707_);
                v___x_5709_ = lean_nat_dec_eq(v___x_5708_, v___x_5705_);
                if v___x_5709_ == 0 {
                    v___x_5710_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5711_ = lean_nat_sub(v___x_5708_, v___x_5710_);
                    v___x_5717_ = lean_nat_dec_le(v___x_5705_, v___x_5711_);
                    if v___x_5717_ == 0 {
                        leanh::lean_inc(v___x_5711_);
                        v___y_5713_ = v___x_5711_;
                        state = 1;
                        continue;
                    } else {
                        v___y_5713_ = v___x_5705_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v_result_5707_;
                }
            }
            1 => {
                v___x_5714_ = lean_nat_dec_le(v___y_5713_, v___x_5711_);
                if v___x_5714_ == 0 {
                    leanh::lean_dec(v___x_5711_);
                    leanh::lean_inc(v___y_5713_);
                    v___x_5715_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_5708_, v_result_5707_, v___y_5713_, v___y_5713_);
                    leanh::lean_dec(v___y_5713_);
                    return v___x_5715_;
                } else {
                    v___x_5716_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_5708_, v_result_5707_, v___y_5713_, v___x_5711_);
                    leanh::lean_dec(v___x_5711_);
                    return v___x_5716_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(
    mut v___f_5718_: *mut leanh::LeanObject,
    mut v_s_5719_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5720_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_5718_, v_s_5719_);
    leanh::lean_dec_ref(v_s_5719_);
    return v_res_5720_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(
    mut v_x_5721_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5722_ = leanh::lean_box(0);
    return v___x_5722_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(
    mut v_x_5723_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5724_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5724_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v_x_5723_);
    leanh::lean_dec_ref(v_x_5723_);
    return v_res_5724_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(
    mut v___f_5725_: *mut leanh::LeanObject,
    mut v_x_5726_: *mut leanh::LeanObject,
    mut v_s_5727_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_newEntries_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5738_: u8 = 0;
    let mut v___x_5739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5743_: u8 = 0;
    let mut v___x_5744_: u8 = 0;
    let mut v___x_5745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_newEntries_5728_ = leanh::lean_ctor_get(v_s_5727_, 1);
                v___x_5729_ = leanh::lean_unsigned_to_nat(0);
                v___x_5730_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
                v_result_5731_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_newEntries_5728_, v___f_5725_, v___x_5730_);
                v___x_5732_ = lean_array_get_size(v_result_5731_);
                v___x_5738_ = lean_nat_dec_eq(v___x_5732_, v___x_5729_);
                if v___x_5738_ == 0 {
                    v___x_5739_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5740_ = lean_nat_sub(v___x_5732_, v___x_5739_);
                    v___x_5744_ = lean_nat_dec_le(v___x_5729_, v___x_5740_);
                    if v___x_5744_ == 0 {
                        leanh::lean_inc(v___x_5740_);
                        v___y_5742_ = v___x_5740_;
                        state = 2;
                        continue;
                    } else {
                        v___y_5742_ = v___x_5729_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_n(v_result_5731_, 2);
                    v___x_5745_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                    leanh::lean_ctor_set(v___x_5745_, 0, v_result_5731_);
                    leanh::lean_ctor_set(v___x_5745_, 1, v_result_5731_);
                    leanh::lean_ctor_set(v___x_5745_, 2, v_result_5731_);
                    return v___x_5745_;
                }
            }
            1 => {
                v___x_5736_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v___x_5732_, v_result_5731_, v___y_5734_, v___y_5735_);
                leanh::lean_dec(v___y_5735_);
                leanh::lean_inc_ref_n(v___x_5736_, 2);
                v___x_5737_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
                leanh::lean_ctor_set(v___x_5737_, 0, v___x_5736_);
                leanh::lean_ctor_set(v___x_5737_, 1, v___x_5736_);
                leanh::lean_ctor_set(v___x_5737_, 2, v___x_5736_);
                return v___x_5737_;
            }
            2 => {
                v___x_5743_ = lean_nat_dec_le(v___y_5742_, v___x_5740_);
                if v___x_5743_ == 0 {
                    leanh::lean_dec(v___x_5740_);
                    leanh::lean_inc(v___y_5742_);
                    v___y_5734_ = v___y_5742_;
                    v___y_5735_ = v___y_5742_;
                    state = 1;
                    continue;
                } else {
                    v___y_5734_ = v___y_5742_;
                    v___y_5735_ = v___x_5740_;
                    state = 1;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(
    mut v___f_5746_: *mut leanh::LeanObject,
    mut v_x_5747_: *mut leanh::LeanObject,
    mut v_s_5748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5749_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5749_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___f_5746_, v_x_5747_, v_s_5748_);
    leanh::lean_dec_ref(v_s_5748_);
    leanh::lean_dec_ref(v_x_5747_);
    return v_res_5749_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(
    mut v___x_5750_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5755_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5756_: u8 = 0;
    let mut v___x_5757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5759_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5760_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5761_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5762_: u8 = 0;
    let mut v_unused_5763_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5752_ = lean_st_ref_get(v___x_5750_);
                v_keys_5753_ = leanh::lean_ctor_get(v___x_5752_, 0);
                v_isSharedCheck_5762_ = (!leanh::lean_is_exclusive(v___x_5752_)) as u8;
                if v_isSharedCheck_5762_ == 0 {
                    v_unused_5763_ = leanh::lean_ctor_get(v___x_5752_, 1);
                    leanh::lean_dec(v_unused_5763_);
                    v___x_5755_ = v___x_5752_;
                    v_isShared_5756_ = v_isSharedCheck_5762_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_keys_5753_);
                    leanh::lean_dec(v___x_5752_);
                    v___x_5755_ = leanh::lean_box(0);
                    v_isShared_5756_ = v_isSharedCheck_5762_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5757_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once), _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
                if v_isShared_5756_ == 0 {
                    leanh::lean_ctor_set(v___x_5755_, 1, v___x_5757_);
                    v___x_5759_ = v___x_5755_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5761_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5761_, 0, v_keys_5753_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5761_, 1, v___x_5757_);
                    v___x_5759_ = v_reuseFailAlloc_5761_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5760_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5760_, 0, v___x_5759_);
                return v___x_5760_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(
    mut v___x_5764_: *mut leanh::LeanObject,
    mut v___y_5765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5766_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_5764_);
    leanh::lean_dec(v___x_5764_);
    return v_res_5766_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(
    mut v___x_5767_: *mut leanh::LeanObject,
    mut v_x_5768_: *mut leanh::LeanObject,
    mut v___y_5769_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v___x_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5781_: u8 = 0;
    let mut v_unused_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5771_ = lean_st_ref_get(v___x_5767_);
                v_keys_5772_ = leanh::lean_ctor_get(v___x_5771_, 0);
                v_isSharedCheck_5781_ = (!leanh::lean_is_exclusive(v___x_5771_)) as u8;
                if v_isSharedCheck_5781_ == 0 {
                    v_unused_5782_ = leanh::lean_ctor_get(v___x_5771_, 1);
                    leanh::lean_dec(v_unused_5782_);
                    v___x_5774_ = v___x_5771_;
                    v_isShared_5775_ = v_isSharedCheck_5781_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_keys_5772_);
                    leanh::lean_dec(v___x_5771_);
                    v___x_5774_ = leanh::lean_box(0);
                    v_isShared_5775_ = v_isSharedCheck_5781_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5776_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1_once), _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default___closed__1);
                if v_isShared_5775_ == 0 {
                    leanh::lean_ctor_set(v___x_5774_, 1, v___x_5776_);
                    v___x_5778_ = v___x_5774_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5780_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5780_, 0, v_keys_5772_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5780_, 1, v___x_5776_);
                    v___x_5778_ = v_reuseFailAlloc_5780_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_5779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_5779_, 0, v___x_5778_);
                return v___x_5779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(
    mut v___x_5783_: *mut leanh::LeanObject,
    mut v_x_5784_: *mut leanh::LeanObject,
    mut v___y_5785_: *mut leanh::LeanObject,
    mut v___y_5786_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5787_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5787_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_(v___x_5783_, v_x_5784_, v___y_5785_);
    leanh::lean_dec_ref(v___y_5785_);
    leanh::lean_dec_ref(v_x_5784_);
    leanh::lean_dec(v___x_5783_);
    return v_res_5787_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5802_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
    v___f_5803_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_5803_, 0, v___x_5802_);
    return v___f_5803_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5804_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
    v___f_5805_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 4, 1);
    leanh::lean_closure_set(v___f_5805_, 0, v___x_5804_);
    return v___f_5805_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5807_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_5812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5806_ = leanh::lean_box(0);
    v___x_5807_ = leanh::lean_box(2);
    v___f_5808_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
    v___f_5809_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
    v___f_5810_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
    v___f_5811_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
    v___f_5812_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
    v___x_5813_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
    v___x_5814_ = leanh::lean_alloc_ctor(0, 8, (0) as u32);
    leanh::lean_ctor_set(v___x_5814_, 0, v___x_5813_);
    leanh::lean_ctor_set(v___x_5814_, 1, v___f_5812_);
    leanh::lean_ctor_set(v___x_5814_, 2, v___f_5811_);
    leanh::lean_ctor_set(v___x_5814_, 3, v___f_5810_);
    leanh::lean_ctor_set(v___x_5814_, 4, v___f_5809_);
    leanh::lean_ctor_set(v___x_5814_, 5, v___f_5808_);
    leanh::lean_ctor_set(v___x_5814_, 6, v___x_5807_);
    leanh::lean_ctor_set(v___x_5814_, 7, v___x_5806_);
    return v___x_5814_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5816_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5817_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_5815_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_;
    v___x_5816_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
    v___x_5817_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_5817_, 0, v___x_5816_);
    leanh::lean_ctor_set(v___x_5817_, 1, v___f_5815_);
    return v___x_5817_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_5819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5820_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5819_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_);
    v___x_5820_ = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(v___x_5819_);
    return v___x_5820_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2____boxed(
    mut v_a_5821_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5822_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5822_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
    return v_res_5822_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(
    mut v_00_u03c3_5823_: *mut leanh::LeanObject,
    mut v_00_u03b2_5824_: *mut leanh::LeanObject,
    mut v_map_5825_: *mut leanh::LeanObject,
    mut v_f_5826_: *mut leanh::LeanObject,
    mut v_init_5827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5828_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5828_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___redArg(v_map_5825_, v_f_5826_, v_init_5827_);
    return v___x_5828_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0___boxed(
    mut v_00_u03c3_5829_: *mut leanh::LeanObject,
    mut v_00_u03b2_5830_: *mut leanh::LeanObject,
    mut v_map_5831_: *mut leanh::LeanObject,
    mut v_f_5832_: *mut leanh::LeanObject,
    mut v_init_5833_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5834_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5834_ = l_Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0(v_00_u03c3_5829_, v_00_u03b2_5830_, v_map_5831_, v_f_5832_, v_init_5833_);
    leanh::lean_dec_ref(v_map_5831_);
    return v_res_5834_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(
    mut v_n_5835_: *mut leanh::LeanObject,
    mut v_as_5836_: *mut leanh::LeanObject,
    mut v_lo_5837_: *mut leanh::LeanObject,
    mut v_hi_5838_: *mut leanh::LeanObject,
    mut v_w_5839_: *mut leanh::LeanObject,
    mut v_hlo_5840_: *mut leanh::LeanObject,
    mut v_hhi_5841_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5842_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5842_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___redArg(v_n_5835_, v_as_5836_, v_lo_5837_, v_hi_5838_);
    return v___x_5842_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1___boxed(
    mut v_n_5843_: *mut leanh::LeanObject,
    mut v_as_5844_: *mut leanh::LeanObject,
    mut v_lo_5845_: *mut leanh::LeanObject,
    mut v_hi_5846_: *mut leanh::LeanObject,
    mut v_w_5847_: *mut leanh::LeanObject,
    mut v_hlo_5848_: *mut leanh::LeanObject,
    mut v_hhi_5849_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5850_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1(v_n_5843_, v_as_5844_, v_lo_5845_, v_hi_5846_, v_w_5847_, v_hlo_5848_, v_hhi_5849_);
    leanh::lean_dec(v_hi_5846_);
    leanh::lean_dec(v_n_5843_);
    return v_res_5850_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(
    mut v_map_5851_: *mut leanh::LeanObject,
    mut v_f_5852_: *mut leanh::LeanObject,
    mut v_init_5853_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5854_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5854_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_5852_, v_map_5851_, v_init_5853_);
    return v___x_5854_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(
    mut v_map_5855_: *mut leanh::LeanObject,
    mut v_f_5856_: *mut leanh::LeanObject,
    mut v_init_5857_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5858_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___redArg(v_map_5855_, v_f_5856_, v_init_5857_);
    leanh::lean_dec_ref(v_map_5855_);
    return v_res_5858_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(
    mut v_00_u03c3_5859_: *mut leanh::LeanObject,
    mut v_00_u03b2_5860_: *mut leanh::LeanObject,
    mut v_map_5861_: *mut leanh::LeanObject,
    mut v_f_5862_: *mut leanh::LeanObject,
    mut v_init_5863_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5864_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5864_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_5862_, v_map_5861_, v_init_5863_);
    return v___x_5864_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0___boxed(
    mut v_00_u03c3_5865_: *mut leanh::LeanObject,
    mut v_00_u03b2_5866_: *mut leanh::LeanObject,
    mut v_map_5867_: *mut leanh::LeanObject,
    mut v_f_5868_: *mut leanh::LeanObject,
    mut v_init_5869_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5870_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5870_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0(v_00_u03c3_5865_, v_00_u03b2_5866_, v_map_5867_, v_f_5868_, v_init_5869_);
    leanh::lean_dec_ref(v_map_5867_);
    return v_res_5870_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(
    mut v_n_5871_: *mut leanh::LeanObject,
    mut v_lo_5872_: *mut leanh::LeanObject,
    mut v_hi_5873_: *mut leanh::LeanObject,
    mut v_hhi_5874_: *mut leanh::LeanObject,
    mut v_pivot_5875_: *mut leanh::LeanObject,
    mut v_as_5876_: *mut leanh::LeanObject,
    mut v_i_5877_: *mut leanh::LeanObject,
    mut v_k_5878_: *mut leanh::LeanObject,
    mut v_ilo_5879_: *mut leanh::LeanObject,
    mut v_ik_5880_: *mut leanh::LeanObject,
    mut v_w_5881_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5882_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___redArg(v_hi_5873_, v_pivot_5875_, v_as_5876_, v_i_5877_, v_k_5878_);
    return v___x_5882_;
}
pub unsafe fn l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2___boxed(
    mut v_n_5883_: *mut leanh::LeanObject,
    mut v_lo_5884_: *mut leanh::LeanObject,
    mut v_hi_5885_: *mut leanh::LeanObject,
    mut v_hhi_5886_: *mut leanh::LeanObject,
    mut v_pivot_5887_: *mut leanh::LeanObject,
    mut v_as_5888_: *mut leanh::LeanObject,
    mut v_i_5889_: *mut leanh::LeanObject,
    mut v_k_5890_: *mut leanh::LeanObject,
    mut v_ilo_5891_: *mut leanh::LeanObject,
    mut v_ik_5892_: *mut leanh::LeanObject,
    mut v_w_5893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5894_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5894_ = l___private_Init_Data_Array_QSort_Basic_0__Array_qpartition_loop___at___00__private_Init_Data_Array_QSort_Basic_0__Array_qsort_sort___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__1_spec__2(v_n_5883_, v_lo_5884_, v_hi_5885_, v_hhi_5886_, v_pivot_5887_, v_as_5888_, v_i_5889_, v_k_5890_, v_ilo_5891_, v_ik_5892_, v_w_5893_);
    leanh::lean_dec_ref(v_pivot_5887_);
    leanh::lean_dec(v_hi_5885_);
    leanh::lean_dec(v_lo_5884_);
    leanh::lean_dec(v_n_5883_);
    return v_res_5894_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(
    mut v_00_u03c3_5895_: *mut leanh::LeanObject,
    mut v_00_u03b1_5896_: *mut leanh::LeanObject,
    mut v_00_u03b2_5897_: *mut leanh::LeanObject,
    mut v_f_5898_: *mut leanh::LeanObject,
    mut v_x_5899_: *mut leanh::LeanObject,
    mut v_x_5900_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5901_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5901_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_f_5898_, v_x_5899_, v_x_5900_);
    return v___x_5901_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(
    mut v_00_u03c3_5902_: *mut leanh::LeanObject,
    mut v_00_u03b1_5903_: *mut leanh::LeanObject,
    mut v_00_u03b2_5904_: *mut leanh::LeanObject,
    mut v_f_5905_: *mut leanh::LeanObject,
    mut v_x_5906_: *mut leanh::LeanObject,
    mut v_x_5907_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5908_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5908_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03c3_5902_, v_00_u03b1_5903_, v_00_u03b2_5904_, v_f_5905_, v_x_5906_, v_x_5907_);
    leanh::lean_dec_ref(v_x_5906_);
    return v_res_5908_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(
    mut v_00_u03b1_5909_: *mut leanh::LeanObject,
    mut v_00_u03b2_5910_: *mut leanh::LeanObject,
    mut v_00_u03c3_5911_: *mut leanh::LeanObject,
    mut v_f_5912_: *mut leanh::LeanObject,
    mut v_as_5913_: *mut leanh::LeanObject,
    mut v_i_5914_: usize,
    mut v_stop_5915_: usize,
    mut v_b_5916_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5917_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___redArg(v_f_5912_, v_as_5913_, v_i_5914_, v_stop_5915_, v_b_5916_);
    return v___x_5917_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3___boxed(
    mut v_00_u03b1_5918_: *mut leanh::LeanObject,
    mut v_00_u03b2_5919_: *mut leanh::LeanObject,
    mut v_00_u03c3_5920_: *mut leanh::LeanObject,
    mut v_f_5921_: *mut leanh::LeanObject,
    mut v_as_5922_: *mut leanh::LeanObject,
    mut v_i_5923_: *mut leanh::LeanObject,
    mut v_stop_5924_: *mut leanh::LeanObject,
    mut v_b_5925_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_i_boxed_5926_: usize = 0;
    let mut v_stop_boxed_5927_: usize = 0;
    let mut v_res_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_5926_ = leanh::lean_unbox_usize(v_i_5923_);
    leanh::lean_dec(v_i_5923_);
    v_stop_boxed_5927_ = leanh::lean_unbox_usize(v_stop_5924_);
    leanh::lean_dec(v_stop_5924_);
    v_res_5928_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__3(v_00_u03b1_5918_, v_00_u03b2_5919_, v_00_u03c3_5920_, v_f_5921_, v_as_5922_, v_i_boxed_5926_, v_stop_boxed_5927_, v_b_5925_);
    leanh::lean_dec_ref(v_as_5922_);
    return v_res_5928_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(
    mut v_00_u03c3_5929_: *mut leanh::LeanObject,
    mut v_00_u03b1_5930_: *mut leanh::LeanObject,
    mut v_00_u03b2_5931_: *mut leanh::LeanObject,
    mut v_f_5932_: *mut leanh::LeanObject,
    mut v_keys_5933_: *mut leanh::LeanObject,
    mut v_vals_5934_: *mut leanh::LeanObject,
    mut v_heq_5935_: *mut leanh::LeanObject,
    mut v_i_5936_: *mut leanh::LeanObject,
    mut v_acc_5937_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5938_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5938_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___redArg(v_f_5932_, v_keys_5933_, v_vals_5934_, v_i_5936_, v_acc_5937_);
    return v___x_5938_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4___boxed(
    mut v_00_u03c3_5939_: *mut leanh::LeanObject,
    mut v_00_u03b1_5940_: *mut leanh::LeanObject,
    mut v_00_u03b2_5941_: *mut leanh::LeanObject,
    mut v_f_5942_: *mut leanh::LeanObject,
    mut v_keys_5943_: *mut leanh::LeanObject,
    mut v_vals_5944_: *mut leanh::LeanObject,
    mut v_heq_5945_: *mut leanh::LeanObject,
    mut v_i_5946_: *mut leanh::LeanObject,
    mut v_acc_5947_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5948_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5948_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_foldl___at___00__private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__4(v_00_u03c3_5939_, v_00_u03b1_5940_, v_00_u03b2_5941_, v_f_5942_, v_keys_5943_, v_vals_5944_, v_heq_5945_, v_i_5946_, v_acc_5947_);
    leanh::lean_dec_ref(v_vals_5944_);
    leanh::lean_dec_ref(v_keys_5943_);
    return v_res_5948_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(
    mut v_a_5949_: *mut leanh::LeanObject,
    mut v_x_5950_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5951_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_5952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_5953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5955_: u8 = 0;
    let mut v___x_5957_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_5950_) == 0 {
                    v___x_5951_ = leanh::lean_box(0);
                    return v___x_5951_;
                } else {
                    v_key_5952_ = leanh::lean_ctor_get(v_x_5950_, 0);
                    v_value_5953_ = leanh::lean_ctor_get(v_x_5950_, 1);
                    v_tail_5954_ = leanh::lean_ctor_get(v_x_5950_, 2);
                    v___x_5955_ = lean_name_eq(v_key_5952_, v_a_5949_);
                    if v___x_5955_ == 0 {
                        v_x_5950_ = v_tail_5954_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_inc(v_value_5953_);
                        v___x_5957_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5957_, 0, v_value_5953_);
                        return v___x_5957_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg___boxed(
    mut v_a_5958_: *mut leanh::LeanObject,
    mut v_x_5959_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5960_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_5958_, v_x_5959_);
    leanh::lean_dec(v_x_5959_);
    leanh::lean_dec(v_a_5958_);
    return v_res_5960_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(
    mut v_m_5961_: *mut leanh::LeanObject,
    mut v_a_5962_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_buckets_5963_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_5966_: u64 = 0;
    let mut v___x_5967_: u64 = 0;
    let mut v___x_5968_: u64 = 0;
    let mut v_fold_5969_: u64 = 0;
    let mut v___x_5970_: u64 = 0;
    let mut v___x_5971_: u64 = 0;
    let mut v___x_5972_: u64 = 0;
    let mut v___x_5973_: usize = 0;
    let mut v___x_5974_: usize = 0;
    let mut v___x_5975_: usize = 0;
    let mut v___x_5976_: usize = 0;
    let mut v___x_5977_: usize = 0;
    let mut v___x_5978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5980_: u64 = 0;
    let mut v_hash_5981_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_buckets_5963_ = leanh::lean_ctor_get(v_m_5961_, 1);
                v___x_5964_ = lean_array_get_size(v_buckets_5963_);
                if leanh::lean_obj_tag(v_a_5962_) == 0 {
                    v___x_5980_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_5966_ = v___x_5980_;
                    state = 1;
                    continue;
                } else {
                    v_hash_5981_ = leanh::lean_ctor_get_uint64(
                        v_a_5962_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_5966_ = v_hash_5981_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_5967_ = 32u64;
                v___x_5968_ = lean_uint64_shift_right(v___y_5966_, v___x_5967_);
                v_fold_5969_ = lean_uint64_xor(v___y_5966_, v___x_5968_);
                v___x_5970_ = 16u64;
                v___x_5971_ = lean_uint64_shift_right(v_fold_5969_, v___x_5970_);
                v___x_5972_ = lean_uint64_xor(v_fold_5969_, v___x_5971_);
                v___x_5973_ = lean_uint64_to_usize(v___x_5972_);
                v___x_5974_ = lean_usize_of_nat(v___x_5964_);
                v___x_5975_ = 1usize;
                v___x_5976_ = lean_usize_sub(v___x_5974_, v___x_5975_);
                v___x_5977_ = lean_usize_land(v___x_5973_, v___x_5976_);
                v___x_5978_ = lean_array_uget_borrowed(v_buckets_5963_, v___x_5977_);
                v___x_5979_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_5962_, v___x_5978_);
                return v___x_5979_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg___boxed(
    mut v_m_5982_: *mut leanh::LeanObject,
    mut v_a_5983_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5984_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_5982_, v_a_5983_);
    leanh::lean_dec(v_a_5983_);
    leanh::lean_dec_ref(v_m_5982_);
    return v_res_5984_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(
    mut v_as_5985_: *mut leanh::LeanObject,
    mut v_k_5986_: *mut leanh::LeanObject,
    mut v_x_5987_: *mut leanh::LeanObject,
    mut v_x_5988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_5991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5993_: u8 = 0;
    let mut v___x_5994_: u8 = 0;
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5997_: u8 = 0;
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5999_: u8 = 0;
    let mut v___x_6001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6004_: u8 = 0;
    let mut v___x_6005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5989_ = lean_nat_add(v_x_5987_, v_x_5988_);
                v___x_5990_ = leanh::lean_unsigned_to_nat(1);
                v_m_5991_ = lean_nat_shiftr(v___x_5989_, v___x_5990_);
                leanh::lean_dec(v___x_5989_);
                v_a_5992_ = lean_array_fget_borrowed(v_as_5985_, v_m_5991_);
                v___x_5993_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_a_5992_, v_k_5986_);
                if v___x_5993_ == 0 {
                    leanh::lean_dec(v_x_5988_);
                    v___x_5994_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocDecl_lt(v_k_5986_, v_a_5992_);
                    if v___x_5994_ == 0 {
                        leanh::lean_dec(v_m_5991_);
                        leanh::lean_dec(v_x_5987_);
                        leanh::lean_inc(v_a_5992_);
                        v___x_5995_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_5995_, 0, v_a_5992_);
                        return v___x_5995_;
                    } else {
                        v___x_5996_ = leanh::lean_unsigned_to_nat(0);
                        v___x_5997_ = lean_nat_dec_eq(v_m_5991_, v___x_5996_);
                        if v___x_5997_ == 0 {
                            v___x_5998_ = lean_nat_sub(v_m_5991_, v___x_5990_);
                            leanh::lean_dec(v_m_5991_);
                            v___x_5999_ = lean_nat_dec_lt(v___x_5998_, v_x_5987_);
                            if v___x_5999_ == 0 {
                                v_x_5988_ = v___x_5998_;
                                state = 0;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_5998_);
                                leanh::lean_dec(v_x_5987_);
                                v___x_6001_ = leanh::lean_box(0);
                                return v___x_6001_;
                            }
                        } else {
                            leanh::lean_dec(v_m_5991_);
                            leanh::lean_dec(v_x_5987_);
                            v___x_6002_ = leanh::lean_box(0);
                            return v___x_6002_;
                        }
                    }
                } else {
                    leanh::lean_dec(v_x_5987_);
                    v___x_6003_ = lean_nat_add(v_m_5991_, v___x_5990_);
                    leanh::lean_dec(v_m_5991_);
                    v___x_6004_ = lean_nat_dec_le(v___x_6003_, v_x_5988_);
                    if v___x_6004_ == 0 {
                        leanh::lean_dec(v___x_6003_);
                        leanh::lean_dec(v_x_5988_);
                        v___x_6005_ = leanh::lean_box(0);
                        return v___x_6005_;
                    } else {
                        v_x_5987_ = v___x_6003_;
                        state = 0;
                        continue;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg___boxed(
    mut v_as_6007_: *mut leanh::LeanObject,
    mut v_k_6008_: *mut leanh::LeanObject,
    mut v_x_6009_: *mut leanh::LeanObject,
    mut v_x_6010_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6011_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_6007_, v_k_6008_, v_x_6009_, v_x_6010_);
    leanh::lean_dec_ref(v_k_6008_);
    leanh::lean_dec_ref(v_as_6007_);
    return v_res_6011_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(
    mut v_keys_6012_: *mut leanh::LeanObject,
    mut v_vals_6013_: *mut leanh::LeanObject,
    mut v_i_6014_: *mut leanh::LeanObject,
    mut v_k_6015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6016_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6017_: u8 = 0;
    let mut v___x_6018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_6019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6020_: u8 = 0;
    let mut v___x_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6016_ = lean_array_get_size(v_keys_6012_);
                v___x_6017_ = lean_nat_dec_lt(v_i_6014_, v___x_6016_);
                if v___x_6017_ == 0 {
                    leanh::lean_dec(v_i_6014_);
                    v___x_6018_ = leanh::lean_box(0);
                    return v___x_6018_;
                } else {
                    v_k_x27_6019_ = lean_array_fget_borrowed(v_keys_6012_, v_i_6014_);
                    v___x_6020_ = lean_name_eq(v_k_6015_, v_k_x27_6019_);
                    if v___x_6020_ == 0 {
                        v___x_6021_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6022_ = lean_nat_add(v_i_6014_, v___x_6021_);
                        leanh::lean_dec(v_i_6014_);
                        v_i_6014_ = v___x_6022_;
                        state = 0;
                        continue;
                    } else {
                        v___x_6024_ = lean_array_fget_borrowed(v_vals_6013_, v_i_6014_);
                        leanh::lean_dec(v_i_6014_);
                        leanh::lean_inc(v___x_6024_);
                        v___x_6025_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6025_, 0, v___x_6024_);
                        return v___x_6025_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg___boxed(
    mut v_keys_6026_: *mut leanh::LeanObject,
    mut v_vals_6027_: *mut leanh::LeanObject,
    mut v_i_6028_: *mut leanh::LeanObject,
    mut v_k_6029_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6030_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6030_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_6026_, v_vals_6027_, v_i_6028_, v_k_6029_);
    leanh::lean_dec(v_k_6029_);
    leanh::lean_dec_ref(v_vals_6027_);
    leanh::lean_dec_ref(v_keys_6026_);
    return v_res_6030_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(
    mut v_x_6031_: *mut leanh::LeanObject,
    mut v_x_6032_: usize,
    mut v_x_6033_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_6034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6036_: usize = 0;
    let mut v___x_6037_: usize = 0;
    let mut v___x_6038_: usize = 0;
    let mut v_j_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6043_: u8 = 0;
    let mut v___x_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: usize = 0;
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_6050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6031_) == 0 {
                    v_es_6034_ = leanh::lean_ctor_get(v_x_6031_, 0);
                    v___x_6035_ = leanh::lean_box(2);
                    v___x_6036_ = 5usize;
                    v___x_6037_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
                    v___x_6038_ = lean_usize_land(v_x_6032_, v___x_6037_);
                    v_j_6039_ = lean_usize_to_nat(v___x_6038_);
                    v___x_6040_ = lean_array_get_borrowed(v___x_6035_, v_es_6034_, v_j_6039_);
                    leanh::lean_dec(v_j_6039_);
                    match leanh::lean_obj_tag(v___x_6040_) {
                        0 => {
                            v_key_6041_ = leanh::lean_ctor_get(v___x_6040_, 0);
                            v_val_6042_ = leanh::lean_ctor_get(v___x_6040_, 1);
                            v___x_6043_ = lean_name_eq(v_x_6033_, v_key_6041_);
                            if v___x_6043_ == 0 {
                                v___x_6044_ = leanh::lean_box(0);
                                return v___x_6044_;
                            } else {
                                leanh::lean_inc(v_val_6042_);
                                v___x_6045_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v___x_6045_, 0, v_val_6042_);
                                return v___x_6045_;
                            }
                        }
                        1 => {
                            v_node_6046_ = leanh::lean_ctor_get(v___x_6040_, 0);
                            v___x_6047_ = lean_usize_shift_right(v_x_6032_, v___x_6036_);
                            v_x_6031_ = v_node_6046_;
                            v_x_6032_ = v___x_6047_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_6049_ = leanh::lean_box(0);
                            return v___x_6049_;
                        }
                    }
                } else {
                    v_ks_6050_ = leanh::lean_ctor_get(v_x_6031_, 0);
                    v_vs_6051_ = leanh::lean_ctor_get(v_x_6031_, 1);
                    v___x_6052_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6053_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_ks_6050_, v_vs_6051_, v___x_6052_, v_x_6033_);
                    return v___x_6053_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg___boxed(
    mut v_x_6054_: *mut leanh::LeanObject,
    mut v_x_6055_: *mut leanh::LeanObject,
    mut v_x_6056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1442__boxed_6057_: usize = 0;
    let mut v_res_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1442__boxed_6057_ = leanh::lean_unbox_usize(v_x_6055_);
    leanh::lean_dec(v_x_6055_);
    v_res_6058_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_6054_, v_x_1442__boxed_6057_, v_x_6056_);
    leanh::lean_dec(v_x_6056_);
    leanh::lean_dec_ref(v_x_6054_);
    return v_res_6058_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(
    mut v_x_6059_: *mut leanh::LeanObject,
    mut v_x_6060_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_6062_: u64 = 0;
    let mut v___x_6063_: usize = 0;
    let mut v___x_6064_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6065_: u64 = 0;
    let mut v_hash_6066_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6060_) == 0 {
                    v___x_6065_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_6062_ = v___x_6065_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6066_ = leanh::lean_ctor_get_uint64(
                        v_x_6060_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_6062_ = v_hash_6066_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6063_ = lean_uint64_to_usize(v___y_6062_);
                v___x_6064_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_6059_, v___x_6063_, v_x_6060_);
                return v___x_6064_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg___boxed(
    mut v_x_6067_: *mut leanh::LeanObject,
    mut v_x_6068_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6069_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6069_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_6067_, v_x_6068_);
    leanh::lean_dec(v_x_6068_);
    leanh::lean_dec_ref(v_x_6067_);
    return v_res_6069_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(
    mut v_declName_6070_: *mut leanh::LeanObject,
    mut v_a_6071_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6073_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6074_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6077_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6079_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6081_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_builtin_6082_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6086_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6088_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_6091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6097_: u8 = 0;
    let mut v___x_6098_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6099_: u8 = 0;
    let mut v___x_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6103_: u8 = 0;
    let mut v___x_6104_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6106_: u8 = 0;
    let mut v___x_6107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6109_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6113_: u8 = 0;
    let mut v_keys_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6120_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6121_: u8 = 0;
    let mut v_isSharedCheck_6122_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6073_ = lean_st_ref_get(v_a_6071_);
                v_env_6074_ = leanh::lean_ctor_get(v___x_6073_, 0);
                leanh::lean_inc_ref(v_env_6074_);
                leanh::lean_dec(v___x_6073_);
                v___x_6075_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
                v___x_6085_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6074_, v_declName_6070_);
                if leanh::lean_obj_tag(v___x_6085_) == 0 {
                    v___x_6086_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
                    v_toEnvExtension_6087_ = leanh::lean_ctor_get(v___x_6086_, 0);
                    v_asyncMode_6088_ = leanh::lean_ctor_get(v_toEnvExtension_6087_, 2);
                    v___x_6089_ = leanh::lean_box(0);
                    leanh::lean_inc_ref(v_env_6074_);
                    v___x_6090_ = l_Lean_PersistentEnvExtension_getState___redArg(
                        v___x_6075_,
                        v___x_6086_,
                        v_env_6074_,
                        v_asyncMode_6088_,
                        v___x_6089_,
                    );
                    v_newEntries_6091_ = leanh::lean_ctor_get(v___x_6090_, 1);
                    leanh::lean_inc_ref(v_newEntries_6091_);
                    leanh::lean_dec(v___x_6090_);
                    v___x_6092_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_newEntries_6091_, v_declName_6070_);
                    leanh::lean_dec_ref(v_newEntries_6091_);
                    if leanh::lean_obj_tag(v___x_6092_) == 1 {
                        leanh::lean_dec_ref(v_env_6074_);
                        leanh::lean_dec(v_declName_6070_);
                        v___x_6093_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_6093_, 0, v___x_6092_);
                        return v___x_6093_;
                    } else {
                        leanh::lean_dec(v___x_6092_);
                        state = 1;
                        continue;
                    }
                } else {
                    v_val_6094_ = leanh::lean_ctor_get(v___x_6085_, 0);
                    v_isSharedCheck_6122_ = (!leanh::lean_is_exclusive(v___x_6085_)) as u8;
                    if v_isSharedCheck_6122_ == 0 {
                        v___x_6096_ = v___x_6085_;
                        v_isShared_6097_ = v_isSharedCheck_6122_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6094_);
                        leanh::lean_dec(v___x_6085_);
                        v___x_6096_ = leanh::lean_box(0);
                        v_isShared_6097_ = v_isSharedCheck_6122_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6077_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
                v_toEnvExtension_6078_ = leanh::lean_ctor_get(v___x_6077_, 0);
                v_asyncMode_6079_ = leanh::lean_ctor_get(v_toEnvExtension_6078_, 2);
                v___x_6080_ = leanh::lean_box(0);
                v___x_6081_ = l_Lean_PersistentEnvExtension_getState___redArg(
                    v___x_6075_,
                    v___x_6077_,
                    v_env_6074_,
                    v_asyncMode_6079_,
                    v___x_6080_,
                );
                v_builtin_6082_ = leanh::lean_ctor_get(v___x_6081_, 0);
                leanh::lean_inc_ref(v_builtin_6082_);
                leanh::lean_dec(v___x_6081_);
                v___x_6083_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_builtin_6082_, v_declName_6070_);
                leanh::lean_dec(v_declName_6070_);
                leanh::lean_dec_ref(v_builtin_6082_);
                v___x_6084_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6084_, 0, v___x_6083_);
                return v___x_6084_;
            }
            2 => {
                v___x_6098_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
                v___x_6099_ = 0;
                v___x_6100_ = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(
                    v___x_6075_,
                    v___x_6098_,
                    v_env_6074_,
                    v_val_6094_,
                    v___x_6099_,
                );
                leanh::lean_dec(v_val_6094_);
                v___x_6101_ = leanh::lean_unsigned_to_nat(0);
                v___x_6102_ = lean_array_get_size(v___x_6100_);
                v___x_6103_ = lean_nat_dec_lt(v___x_6101_, v___x_6102_);
                if v___x_6103_ == 0 {
                    leanh::lean_dec_ref(v___x_6100_);
                    leanh::lean_del_object(v___x_6096_);
                    state = 1;
                    continue;
                } else {
                    v___x_6104_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6105_ = lean_nat_sub(v___x_6102_, v___x_6104_);
                    v___x_6106_ = lean_nat_dec_le(v___x_6101_, v___x_6105_);
                    if v___x_6106_ == 0 {
                        leanh::lean_dec(v___x_6105_);
                        leanh::lean_dec_ref(v___x_6100_);
                        leanh::lean_del_object(v___x_6096_);
                        state = 1;
                        continue;
                    } else {
                        v___x_6107_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocOLeanEntry_default___closed__0;
                        leanh::lean_inc(v_declName_6070_);
                        v___x_6108_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6108_, 0, v_declName_6070_);
                        leanh::lean_ctor_set(v___x_6108_, 1, v___x_6107_);
                        v___x_6109_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v___x_6100_, v___x_6108_, v___x_6101_, v___x_6105_);
                        leanh::lean_dec_ref_known(v___x_6108_, 2);
                        leanh::lean_dec_ref(v___x_6100_);
                        if leanh::lean_obj_tag(v___x_6109_) == 1 {
                            leanh::lean_dec_ref(v_env_6074_);
                            leanh::lean_dec(v_declName_6070_);
                            v_val_6110_ = leanh::lean_ctor_get(v___x_6109_, 0);
                            v_isSharedCheck_6121_ =
                                (!leanh::lean_is_exclusive(v___x_6109_)) as u8;
                            if v_isSharedCheck_6121_ == 0 {
                                v___x_6112_ = v___x_6109_;
                                v_isShared_6113_ = v_isSharedCheck_6121_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_val_6110_);
                                leanh::lean_dec(v___x_6109_);
                                v___x_6112_ = leanh::lean_box(0);
                                v_isShared_6113_ = v_isSharedCheck_6121_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v___x_6109_);
                            leanh::lean_del_object(v___x_6096_);
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            3 => {
                v_keys_6114_ = leanh::lean_ctor_get(v_val_6110_, 1);
                leanh::lean_inc_ref(v_keys_6114_);
                leanh::lean_dec(v_val_6110_);
                if v_isShared_6113_ == 0 {
                    leanh::lean_ctor_set(v___x_6112_, 0, v_keys_6114_);
                    v___x_6116_ = v___x_6112_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6120_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6120_, 0, v_keys_6114_);
                    v___x_6116_ = v_reuseFailAlloc_6120_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_6097_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6096_, 0);
                    leanh::lean_ctor_set(v___x_6096_, 0, v___x_6116_);
                    v___x_6118_ = v___x_6096_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6119_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 0, v___x_6116_);
                    v___x_6118_ = v_reuseFailAlloc_6119_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6118_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg___boxed(
    mut v_declName_6123_: *mut leanh::LeanObject,
    mut v_a_6124_: *mut leanh::LeanObject,
    mut v_a_6125_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6126_ =
        l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_6123_, v_a_6124_);
    leanh::lean_dec(v_a_6124_);
    return v_res_6126_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(
    mut v_declName_6127_: *mut leanh::LeanObject,
    mut v_a_6128_: *mut leanh::LeanObject,
    mut v_a_6129_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6131_ =
        l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(v_declName_6127_, v_a_6129_);
    return v___x_6131_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___boxed(
    mut v_declName_6132_: *mut leanh::LeanObject,
    mut v_a_6133_: *mut leanh::LeanObject,
    mut v_a_6134_: *mut leanh::LeanObject,
    mut v_a_6135_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6136_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6136_ =
        l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f(v_declName_6132_, v_a_6133_, v_a_6134_);
    leanh::lean_dec(v_a_6134_);
    leanh::lean_dec_ref(v_a_6133_);
    return v_res_6136_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(
    mut v_00_u03b2_6137_: *mut leanh::LeanObject,
    mut v_m_6138_: *mut leanh::LeanObject,
    mut v_a_6139_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6140_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_m_6138_, v_a_6139_);
    return v___x_6140_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___boxed(
    mut v_00_u03b2_6141_: *mut leanh::LeanObject,
    mut v_m_6142_: *mut leanh::LeanObject,
    mut v_a_6143_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6144_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0(v_00_u03b2_6141_, v_m_6142_, v_a_6143_);
    leanh::lean_dec(v_a_6143_);
    leanh::lean_dec_ref(v_m_6142_);
    return v_res_6144_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(
    mut v_00_u03b2_6145_: *mut leanh::LeanObject,
    mut v_x_6146_: *mut leanh::LeanObject,
    mut v_x_6147_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6148_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___redArg(v_x_6146_, v_x_6147_);
    return v___x_6148_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1___boxed(
    mut v_00_u03b2_6149_: *mut leanh::LeanObject,
    mut v_x_6150_: *mut leanh::LeanObject,
    mut v_x_6151_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6152_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1(v_00_u03b2_6149_, v_x_6150_, v_x_6151_);
    leanh::lean_dec(v_x_6151_);
    leanh::lean_dec_ref(v_x_6150_);
    return v_res_6152_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(
    mut v_as_6153_: *mut leanh::LeanObject,
    mut v_k_6154_: *mut leanh::LeanObject,
    mut v_x_6155_: *mut leanh::LeanObject,
    mut v_x_6156_: *mut leanh::LeanObject,
    mut v_x_6157_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6158_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6158_ = l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___redArg(v_as_6153_, v_k_6154_, v_x_6155_, v_x_6156_);
    return v___x_6158_;
}
pub unsafe fn l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2___boxed(
    mut v_as_6159_: *mut leanh::LeanObject,
    mut v_k_6160_: *mut leanh::LeanObject,
    mut v_x_6161_: *mut leanh::LeanObject,
    mut v_x_6162_: *mut leanh::LeanObject,
    mut v_x_6163_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6164_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6164_ =
        l_Array_binSearchAux___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__2(
            v_as_6159_, v_k_6160_, v_x_6161_, v_x_6162_, v_x_6163_,
        );
    leanh::lean_dec_ref(v_k_6160_);
    leanh::lean_dec_ref(v_as_6159_);
    return v_res_6164_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(
    mut v_00_u03b2_6165_: *mut leanh::LeanObject,
    mut v_a_6166_: *mut leanh::LeanObject,
    mut v_x_6167_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6168_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6168_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___redArg(v_a_6166_, v_x_6167_);
    return v___x_6168_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_6169_: *mut leanh::LeanObject,
    mut v_a_6170_: *mut leanh::LeanObject,
    mut v_x_6171_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6172_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0_spec__0(v_00_u03b2_6169_, v_a_6170_, v_x_6171_);
    leanh::lean_dec(v_x_6171_);
    leanh::lean_dec(v_a_6170_);
    return v_res_6172_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(
    mut v_00_u03b2_6173_: *mut leanh::LeanObject,
    mut v_x_6174_: *mut leanh::LeanObject,
    mut v_x_6175_: usize,
    mut v_x_6176_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6177_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___redArg(v_x_6174_, v_x_6175_, v_x_6176_);
    return v___x_6177_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2___boxed(
    mut v_00_u03b2_6178_: *mut leanh::LeanObject,
    mut v_x_6179_: *mut leanh::LeanObject,
    mut v_x_6180_: *mut leanh::LeanObject,
    mut v_x_6181_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_1631__boxed_6182_: usize = 0;
    let mut v_res_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_1631__boxed_6182_ = leanh::lean_unbox_usize(v_x_6180_);
    leanh::lean_dec(v_x_6180_);
    v_res_6183_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2(v_00_u03b2_6178_, v_x_6179_, v_x_1631__boxed_6182_, v_x_6181_);
    leanh::lean_dec(v_x_6181_);
    leanh::lean_dec_ref(v_x_6179_);
    return v_res_6183_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(
    mut v_00_u03b2_6184_: *mut leanh::LeanObject,
    mut v_keys_6185_: *mut leanh::LeanObject,
    mut v_vals_6186_: *mut leanh::LeanObject,
    mut v_heq_6187_: *mut leanh::LeanObject,
    mut v_i_6188_: *mut leanh::LeanObject,
    mut v_k_6189_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6190_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6190_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___redArg(v_keys_6185_, v_vals_6186_, v_i_6188_, v_k_6189_);
    return v___x_6190_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3___boxed(
    mut v_00_u03b2_6191_: *mut leanh::LeanObject,
    mut v_keys_6192_: *mut leanh::LeanObject,
    mut v_vals_6193_: *mut leanh::LeanObject,
    mut v_heq_6194_: *mut leanh::LeanObject,
    mut v_i_6195_: *mut leanh::LeanObject,
    mut v_k_6196_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6197_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__1_spec__2_spec__3(v_00_u03b2_6191_, v_keys_6192_, v_vals_6193_, v_heq_6194_, v_i_6195_, v_k_6196_);
    leanh::lean_dec(v_k_6196_);
    leanh::lean_dec_ref(v_vals_6193_);
    leanh::lean_dec_ref(v_keys_6192_);
    return v_res_6197_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(
    mut v_declName_6198_: *mut leanh::LeanObject,
    mut v_a_6199_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6202_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6205_: u8 = 0;
    let mut v___x_6206_: u8 = 0;
    let mut v___x_6207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6210_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6211_: u8 = 0;
    let mut v___x_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6216_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6201_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(
                    v_declName_6198_,
                    v_a_6199_,
                );
                v_a_6202_ = leanh::lean_ctor_get(v___x_6201_, 0);
                v_isSharedCheck_6216_ = (!leanh::lean_is_exclusive(v___x_6201_)) as u8;
                if v_isSharedCheck_6216_ == 0 {
                    v___x_6204_ = v___x_6201_;
                    v_isShared_6205_ = v_isSharedCheck_6216_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6202_);
                    leanh::lean_dec(v___x_6201_);
                    v___x_6204_ = leanh::lean_box(0);
                    v_isShared_6205_ = v_isSharedCheck_6216_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6202_) == 0 {
                    v___x_6206_ = 0;
                    v___x_6207_ = leanh::lean_box((v___x_6206_) as usize);
                    if v_isShared_6205_ == 0 {
                        leanh::lean_ctor_set(v___x_6204_, 0, v___x_6207_);
                        v___x_6209_ = v___x_6204_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6210_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6210_, 0, v___x_6207_);
                        v___x_6209_ = v_reuseFailAlloc_6210_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref_known(v_a_6202_, 1);
                    v___x_6211_ = 1;
                    v___x_6212_ = leanh::lean_box((v___x_6211_) as usize);
                    if v_isShared_6205_ == 0 {
                        leanh::lean_ctor_set(v___x_6204_, 0, v___x_6212_);
                        v___x_6214_ = v___x_6204_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6215_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6215_, 0, v___x_6212_);
                        v___x_6214_ = v_reuseFailAlloc_6215_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6209_;
            }
            3 => {
                return v___x_6214_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg___boxed(
    mut v_declName_6217_: *mut leanh::LeanObject,
    mut v_a_6218_: *mut leanh::LeanObject,
    mut v_a_6219_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6220_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6220_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_6217_, v_a_6218_);
    leanh::lean_dec(v_a_6218_);
    return v_res_6220_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvSimproc(
    mut v_declName_6221_: *mut leanh::LeanObject,
    mut v_a_6222_: *mut leanh::LeanObject,
    mut v_a_6223_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6225_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6225_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_6221_, v_a_6223_);
    return v___x_6225_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isCbvSimproc___boxed(
    mut v_declName_6226_: *mut leanh::LeanObject,
    mut v_a_6227_: *mut leanh::LeanObject,
    mut v_a_6228_: *mut leanh::LeanObject,
    mut v_a_6229_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6230_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6230_ = l_Lean_Meta_Tactic_Cbv_isCbvSimproc(v_declName_6226_, v_a_6227_, v_a_6228_);
    leanh::lean_dec(v_a_6228_);
    leanh::lean_dec_ref(v_a_6227_);
    return v_res_6230_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(
    mut v_declName_6231_: *mut leanh::LeanObject,
    mut v_a_6232_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6240_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_builtin_6242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6243_: u8 = 0;
    let mut v___x_6244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6245_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6234_ = lean_st_ref_get(v_a_6232_);
    v_env_6235_ = leanh::lean_ctor_get(v___x_6234_, 0);
    leanh::lean_inc_ref(v_env_6235_);
    leanh::lean_dec(v___x_6234_);
    v___x_6236_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
    v_toEnvExtension_6237_ = leanh::lean_ctor_get(v___x_6236_, 0);
    v_asyncMode_6238_ = leanh::lean_ctor_get(v_toEnvExtension_6237_, 2);
    v___x_6239_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default;
    v___x_6240_ = leanh::lean_box(0);
    v___x_6241_ = l_Lean_PersistentEnvExtension_getState___redArg(
        v___x_6239_,
        v___x_6236_,
        v_env_6235_,
        v_asyncMode_6238_,
        v___x_6240_,
    );
    v_builtin_6242_ = leanh::lean_ctor_get(v___x_6241_, 0);
    leanh::lean_inc_ref(v_builtin_6242_);
    leanh::lean_dec(v___x_6241_);
    v___x_6243_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc_spec__0___redArg(v_builtin_6242_, v_declName_6231_);
    leanh::lean_dec_ref(v_builtin_6242_);
    v___x_6244_ = leanh::lean_box((v___x_6243_) as usize);
    v___x_6245_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6245_, 0, v___x_6244_);
    return v___x_6245_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg___boxed(
    mut v_declName_6246_: *mut leanh::LeanObject,
    mut v_a_6247_: *mut leanh::LeanObject,
    mut v_a_6248_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6249_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6249_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_6246_, v_a_6247_);
    leanh::lean_dec(v_a_6247_);
    leanh::lean_dec(v_declName_6246_);
    return v_res_6249_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(
    mut v_declName_6250_: *mut leanh::LeanObject,
    mut v_a_6251_: *mut leanh::LeanObject,
    mut v_a_6252_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6254_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6254_ = l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___redArg(v_declName_6250_, v_a_6252_);
    return v___x_6254_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc___boxed(
    mut v_declName_6255_: *mut leanh::LeanObject,
    mut v_a_6256_: *mut leanh::LeanObject,
    mut v_a_6257_: *mut leanh::LeanObject,
    mut v_a_6258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6259_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6259_ =
        l_Lean_Meta_Tactic_Cbv_isBuiltinCbvSimproc(v_declName_6255_, v_a_6256_, v_a_6257_);
    leanh::lean_dec(v_a_6257_);
    leanh::lean_dec_ref(v_a_6256_);
    leanh::lean_dec(v_declName_6255_);
    return v_res_6259_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0(
    mut v_declName_6260_: *mut leanh::LeanObject,
    mut v_keys_6261_: *mut leanh::LeanObject,
    mut v_s_6262_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_builtin_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_newEntries_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6267_: u8 = 0;
    let mut v___x_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6272_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_builtin_6263_ = leanh::lean_ctor_get(v_s_6262_, 0);
                v_newEntries_6264_ = leanh::lean_ctor_get(v_s_6262_, 1);
                v_isSharedCheck_6272_ = (!leanh::lean_is_exclusive(v_s_6262_)) as u8;
                if v_isSharedCheck_6272_ == 0 {
                    v___x_6266_ = v_s_6262_;
                    v_isShared_6267_ = v_isSharedCheck_6272_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_newEntries_6264_);
                    leanh::lean_inc(v_builtin_6263_);
                    leanh::lean_dec(v_s_6262_);
                    v___x_6266_ = leanh::lean_box(0);
                    v_isShared_6267_ = v_isSharedCheck_6272_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6268_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0___redArg(v_newEntries_6264_, v_declName_6260_, v_keys_6261_);
                if v_isShared_6267_ == 0 {
                    leanh::lean_ctor_set(v___x_6266_, 1, v___x_6268_);
                    v___x_6270_ = v___x_6266_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6271_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 0, v_builtin_6263_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6271_, 1, v___x_6268_);
                    v___x_6270_ = v_reuseFailAlloc_6271_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6270_;
            }
            _ => {}
        }
    }
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6273_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6273_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6274_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__0);
    v___x_6275_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6275_, 0, v___x_6274_);
    return v___x_6275_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6278_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6276_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
    v___x_6277_ = leanh::lean_unsigned_to_nat(0);
    v___x_6278_ = leanh::lean_alloc_ctor(0, 10, (0) as u32);
    leanh::lean_ctor_set(v___x_6278_, 0, v___x_6277_);
    leanh::lean_ctor_set(v___x_6278_, 1, v___x_6277_);
    leanh::lean_ctor_set(v___x_6278_, 2, v___x_6277_);
    leanh::lean_ctor_set(v___x_6278_, 3, v___x_6277_);
    leanh::lean_ctor_set(v___x_6278_, 4, v___x_6276_);
    leanh::lean_ctor_set(v___x_6278_, 5, v___x_6276_);
    leanh::lean_ctor_set(v___x_6278_, 6, v___x_6276_);
    leanh::lean_ctor_set(v___x_6278_, 7, v___x_6276_);
    leanh::lean_ctor_set(v___x_6278_, 8, v___x_6276_);
    leanh::lean_ctor_set(v___x_6278_, 9, v___x_6276_);
    return v___x_6278_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6281_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6279_ = leanh::lean_unsigned_to_nat(32);
    v___x_6280_ = lean_mk_empty_array_with_capacity(v___x_6279_);
    v___x_6281_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6281_, 0, v___x_6280_);
    return v___x_6281_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6282_: usize = 0;
    let mut v___x_6283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6282_ = 5usize;
    v___x_6283_ = leanh::lean_unsigned_to_nat(0);
    v___x_6284_ = leanh::lean_unsigned_to_nat(32);
    v___x_6285_ = lean_mk_empty_array_with_capacity(v___x_6284_);
    v___x_6286_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__3);
    v___x_6287_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_6287_, 0, v___x_6286_);
    leanh::lean_ctor_set(v___x_6287_, 1, v___x_6285_);
    leanh::lean_ctor_set(v___x_6287_, 2, v___x_6283_);
    leanh::lean_ctor_set(v___x_6287_, 3, v___x_6283_);
    leanh::lean_ctor_set_usize(v___x_6287_, 4, v___x_6282_);
    return v___x_6287_;
}
pub unsafe fn _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6288_ = leanh::lean_box(1);
    v___x_6289_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__4);
    v___x_6290_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
    v___x_6291_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6291_, 0, v___x_6290_);
    leanh::lean_ctor_set(v___x_6291_, 1, v___x_6289_);
    leanh::lean_ctor_set(v___x_6291_, 2, v___x_6288_);
    return v___x_6291_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(
    mut v_msgData_6292_: *mut leanh::LeanObject,
    mut v___y_6293_: *mut leanh::LeanObject,
    mut v___y_6294_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6298_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6301_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6302_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6296_ = lean_st_ref_get(v___y_6294_);
    v_env_6297_ = leanh::lean_ctor_get(v___x_6296_, 0);
    leanh::lean_inc_ref(v_env_6297_);
    leanh::lean_dec(v___x_6296_);
    v_options_6298_ = leanh::lean_ctor_get(v___y_6293_, 2);
    v___x_6299_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
    v___x_6300_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__5);
    leanh::lean_inc_ref(v_options_6298_);
    v___x_6301_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_6301_, 0, v_env_6297_);
    leanh::lean_ctor_set(v___x_6301_, 1, v___x_6299_);
    leanh::lean_ctor_set(v___x_6301_, 2, v___x_6300_);
    leanh::lean_ctor_set(v___x_6301_, 3, v_options_6298_);
    v___x_6302_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6302_, 0, v___x_6301_);
    leanh::lean_ctor_set(v___x_6302_, 1, v_msgData_6292_);
    v___x_6303_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6303_, 0, v___x_6302_);
    return v___x_6303_;
}
pub unsafe fn l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___boxed(
    mut v_msgData_6304_: *mut leanh::LeanObject,
    mut v___y_6305_: *mut leanh::LeanObject,
    mut v___y_6306_: *mut leanh::LeanObject,
    mut v___y_6307_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6308_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msgData_6304_, v___y_6305_, v___y_6306_);
    leanh::lean_dec(v___y_6306_);
    leanh::lean_dec_ref(v___y_6305_);
    return v_res_6308_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(
    mut v_msg_6309_: *mut leanh::LeanObject,
    mut v___y_6310_: *mut leanh::LeanObject,
    mut v___y_6311_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_ref_6313_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6318_: u8 = 0;
    let mut v___x_6319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6323_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_6313_ = leanh::lean_ctor_get(v___y_6310_, 5);
                v___x_6314_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0(v_msg_6309_, v___y_6310_, v___y_6311_);
                v_a_6315_ = leanh::lean_ctor_get(v___x_6314_, 0);
                v_isSharedCheck_6323_ = (!leanh::lean_is_exclusive(v___x_6314_)) as u8;
                if v_isSharedCheck_6323_ == 0 {
                    v___x_6317_ = v___x_6314_;
                    v_isShared_6318_ = v_isSharedCheck_6323_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_6315_);
                    leanh::lean_dec(v___x_6314_);
                    v___x_6317_ = leanh::lean_box(0);
                    v_isShared_6318_ = v_isSharedCheck_6323_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_ref_6313_);
                v___x_6319_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6319_, 0, v_ref_6313_);
                leanh::lean_ctor_set(v___x_6319_, 1, v_a_6315_);
                if v_isShared_6318_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6317_, 1);
                    leanh::lean_ctor_set(v___x_6317_, 0, v___x_6319_);
                    v___x_6321_ = v___x_6317_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6322_, 0, v___x_6319_);
                    v___x_6321_ = v_reuseFailAlloc_6322_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6321_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg___boxed(
    mut v_msg_6324_: *mut leanh::LeanObject,
    mut v___y_6325_: *mut leanh::LeanObject,
    mut v___y_6326_: *mut leanh::LeanObject,
    mut v___y_6327_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6328_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(
            v_msg_6324_,
            v___y_6325_,
            v___y_6326_,
        );
    leanh::lean_dec(v___y_6326_);
    leanh::lean_dec_ref(v___y_6325_);
    return v_res_6328_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6329_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(
        leanh::lean_box(0),
        leanh::lean_box(0),
    );
    return v___x_6329_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6330_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0_once),
        _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__0,
    );
    v___x_6331_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6331_, 0, v___x_6330_);
    return v___x_6331_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6332_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1_once),
        _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__1,
    );
    v___x_6333_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_6333_, 0, v___x_6332_);
    leanh::lean_ctor_set(v___x_6333_, 1, v___x_6332_);
    return v___x_6333_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6336_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6335_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__3;
    v___x_6336_ = l_Lean_stringToMessageData(v___x_6335_);
    return v___x_6336_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6338_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6337_ = l_Lean_Meta_Tactic_Cbv_registerBuiltinCbvSimproc___closed__3;
    v___x_6338_ = l_Lean_stringToMessageData(v___x_6337_);
    return v___x_6338_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_6340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6341_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6340_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__6;
    v___x_6341_ = l_Lean_stringToMessageData(v___x_6340_);
    return v___x_6341_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(
    mut v_declName_6342_: *mut leanh::LeanObject,
    mut v_keys_6343_: *mut leanh::LeanObject,
    mut v_a_6344_: *mut leanh::LeanObject,
    mut v_a_6345_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6357_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6359_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6363_: u8 = 0;
    let mut v___x_6364_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6367_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6376_: u8 = 0;
    let mut v_unused_6377_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6381_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6382_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6383_: u8 = 0;
    let mut v___x_6384_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6385_: u8 = 0;
    let mut v___x_6386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6394_: u8 = 0;
    let mut v___x_6396_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6397_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6398_: u8 = 0;
    let mut v___x_6399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6400_: u8 = 0;
    let mut v___x_6401_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6402_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6403_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6404_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6405_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6406_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6347_ = lean_st_ref_get(v_a_6345_);
                v_env_6348_ = leanh::lean_ctor_get(v___x_6347_, 0);
                leanh::lean_inc_ref(v_env_6348_);
                leanh::lean_dec(v___x_6347_);
                leanh::lean_inc(v_declName_6342_);
                v___f_6349_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___lam__0 as *mut core::ffi::c_void,
                    3,
                    2,
                );
                leanh::lean_closure_set(v___f_6349_, 0, v_declName_6342_);
                leanh::lean_closure_set(v___f_6349_, 1, v_keys_6343_);
                v___x_6399_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_6348_, v_declName_6342_);
                leanh::lean_dec_ref(v_env_6348_);
                if leanh::lean_obj_tag(v___x_6399_) == 0 {
                    v___y_6379_ = v_a_6344_;
                    v___y_6380_ = v_a_6345_;
                    state = 4;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_6399_, 1);
                    leanh::lean_dec_ref(v___f_6349_);
                    v___x_6400_ = 0;
                    v___x_6401_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4,
                    );
                    v___x_6402_ = l_Lean_MessageData_ofConstName(v_declName_6342_, v___x_6400_);
                    v___x_6403_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6403_, 0, v___x_6401_);
                    leanh::lean_ctor_set(v___x_6403_, 1, v___x_6402_);
                    v___x_6404_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__7,
                    );
                    v___x_6405_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6405_, 0, v___x_6403_);
                    leanh::lean_ctor_set(v___x_6405_, 1, v___x_6404_);
                    v___x_6406_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_6405_, v_a_6344_, v_a_6345_);
                    return v___x_6406_;
                }
            }
            1 => {
                v___x_6352_ = lean_st_ref_take(v___y_6351_);
                v_env_6353_ = leanh::lean_ctor_get(v___x_6352_, 0);
                v_nextMacroScope_6354_ = leanh::lean_ctor_get(v___x_6352_, 1);
                v_ngen_6355_ = leanh::lean_ctor_get(v___x_6352_, 2);
                v_auxDeclNGen_6356_ = leanh::lean_ctor_get(v___x_6352_, 3);
                v_traceState_6357_ = leanh::lean_ctor_get(v___x_6352_, 4);
                v_messages_6358_ = leanh::lean_ctor_get(v___x_6352_, 6);
                v_infoState_6359_ = leanh::lean_ctor_get(v___x_6352_, 7);
                v_snapshotTasks_6360_ = leanh::lean_ctor_get(v___x_6352_, 8);
                v_isSharedCheck_6376_ = (!leanh::lean_is_exclusive(v___x_6352_)) as u8;
                if v_isSharedCheck_6376_ == 0 {
                    v_unused_6377_ = leanh::lean_ctor_get(v___x_6352_, 5);
                    leanh::lean_dec(v_unused_6377_);
                    v___x_6362_ = v___x_6352_;
                    v_isShared_6363_ = v_isSharedCheck_6376_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6360_);
                    leanh::lean_inc(v_infoState_6359_);
                    leanh::lean_inc(v_messages_6358_);
                    leanh::lean_inc(v_traceState_6357_);
                    leanh::lean_inc(v_auxDeclNGen_6356_);
                    leanh::lean_inc(v_ngen_6355_);
                    leanh::lean_inc(v_nextMacroScope_6354_);
                    leanh::lean_inc(v_env_6353_);
                    leanh::lean_dec(v___x_6352_);
                    v___x_6362_ = leanh::lean_box(0);
                    v_isShared_6363_ = v_isSharedCheck_6376_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6364_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt;
                v_toEnvExtension_6365_ = leanh::lean_ctor_get(v___x_6364_, 0);
                v_asyncMode_6366_ = leanh::lean_ctor_get(v_toEnvExtension_6365_, 2);
                v___x_6367_ = leanh::lean_box(0);
                v___x_6368_ = l_Lean_PersistentEnvExtension_modifyState___redArg(
                    v___x_6364_,
                    v_env_6353_,
                    v___f_6349_,
                    v_asyncMode_6366_,
                    v___x_6367_,
                );
                v___x_6369_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2,
                );
                if v_isShared_6363_ == 0 {
                    leanh::lean_ctor_set(v___x_6362_, 5, v___x_6369_);
                    leanh::lean_ctor_set(v___x_6362_, 0, v___x_6368_);
                    v___x_6371_ = v___x_6362_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6375_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 0, v___x_6368_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 1, v_nextMacroScope_6354_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 2, v_ngen_6355_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 3, v_auxDeclNGen_6356_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 4, v_traceState_6357_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 5, v___x_6369_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 6, v_messages_6358_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 7, v_infoState_6359_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6375_, 8, v_snapshotTasks_6360_);
                    v___x_6371_ = v_reuseFailAlloc_6375_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6372_ = lean_st_ref_set(v___y_6351_, v___x_6371_);
                v___x_6373_ = leanh::lean_box(0);
                v___x_6374_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6374_, 0, v___x_6373_);
                return v___x_6374_;
            }
            4 => {
                leanh::lean_inc(v_declName_6342_);
                v___x_6381_ =
                    l_Lean_Meta_Tactic_Cbv_isCbvSimproc___redArg(v_declName_6342_, v___y_6380_);
                if leanh::lean_obj_tag(v___x_6381_) == 0 {
                    v_a_6382_ = leanh::lean_ctor_get(v___x_6381_, 0);
                    leanh::lean_inc(v_a_6382_);
                    leanh::lean_dec_ref_known(v___x_6381_, 1);
                    v___x_6383_ = (leanh::lean_unbox(v_a_6382_) as u8);
                    leanh::lean_dec(v_a_6382_);
                    if v___x_6383_ == 0 {
                        leanh::lean_dec(v_declName_6342_);
                        v___y_6351_ = v___y_6380_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec_ref(v___f_6349_);
                        v___x_6384_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__4,
                        );
                        v___x_6385_ = 0;
                        v___x_6386_ = l_Lean_MessageData_ofConstName(v_declName_6342_, v___x_6385_);
                        v___x_6387_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6387_, 0, v___x_6384_);
                        leanh::lean_ctor_set(v___x_6387_, 1, v___x_6386_);
                        v___x_6388_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__5,
                        );
                        v___x_6389_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6389_, 0, v___x_6387_);
                        leanh::lean_ctor_set(v___x_6389_, 1, v___x_6388_);
                        v___x_6390_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_6389_, v___y_6379_, v___y_6380_);
                        return v___x_6390_;
                    }
                } else {
                    leanh::lean_dec_ref(v___f_6349_);
                    leanh::lean_dec(v_declName_6342_);
                    v_a_6391_ = leanh::lean_ctor_get(v___x_6381_, 0);
                    v_isSharedCheck_6398_ = (!leanh::lean_is_exclusive(v___x_6381_)) as u8;
                    if v_isSharedCheck_6398_ == 0 {
                        v___x_6393_ = v___x_6381_;
                        v_isShared_6394_ = v_isSharedCheck_6398_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6391_);
                        leanh::lean_dec(v___x_6381_);
                        v___x_6393_ = leanh::lean_box(0);
                        v_isShared_6394_ = v_isSharedCheck_6398_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                if v_isShared_6394_ == 0 {
                    v___x_6396_ = v___x_6393_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6397_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6397_, 0, v_a_6391_);
                    v___x_6396_ = v_reuseFailAlloc_6397_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6396_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___boxed(
    mut v_declName_6407_: *mut leanh::LeanObject,
    mut v_keys_6408_: *mut leanh::LeanObject,
    mut v_a_6409_: *mut leanh::LeanObject,
    mut v_a_6410_: *mut leanh::LeanObject,
    mut v_a_6411_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6412_ = l_Lean_Meta_Tactic_Cbv_registerCbvSimproc(
        v_declName_6407_,
        v_keys_6408_,
        v_a_6409_,
        v_a_6410_,
    );
    leanh::lean_dec(v_a_6410_);
    leanh::lean_dec_ref(v_a_6409_);
    return v_res_6412_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(
    mut v_00_u03b1_6413_: *mut leanh::LeanObject,
    mut v_msg_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6418_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6418_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(
            v_msg_6414_,
            v___y_6415_,
            v___y_6416_,
        );
    return v___x_6418_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___boxed(
    mut v_00_u03b1_6419_: *mut leanh::LeanObject,
    mut v_msg_6420_: *mut leanh::LeanObject,
    mut v___y_6421_: *mut leanh::LeanObject,
    mut v___y_6422_: *mut leanh::LeanObject,
    mut v___y_6423_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6424_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6424_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0(
        v_00_u03b1_6419_,
        v_msg_6420_,
        v___y_6421_,
        v___y_6422_,
    );
    leanh::lean_dec(v___y_6422_);
    leanh::lean_dec_ref(v___y_6421_);
    return v_res_6424_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(
    mut v_e_6425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6430_: u8 = 0;
    let mut v___x_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6434_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6435_: u8 = 0;
    let mut v_a_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6439_: u8 = 0;
    let mut v___x_6441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6443_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_e_6425_) == 0 {
                    v_a_6427_ = leanh::lean_ctor_get(v_e_6425_, 0);
                    v_isSharedCheck_6435_ = (!leanh::lean_is_exclusive(v_e_6425_)) as u8;
                    if v_isSharedCheck_6435_ == 0 {
                        v___x_6429_ = v_e_6425_;
                        v_isShared_6430_ = v_isSharedCheck_6435_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6427_);
                        leanh::lean_dec(v_e_6425_);
                        v___x_6429_ = leanh::lean_box(0);
                        v_isShared_6430_ = v_isSharedCheck_6435_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6436_ = leanh::lean_ctor_get(v_e_6425_, 0);
                    v_isSharedCheck_6443_ = (!leanh::lean_is_exclusive(v_e_6425_)) as u8;
                    if v_isSharedCheck_6443_ == 0 {
                        v___x_6438_ = v_e_6425_;
                        v_isShared_6439_ = v_isSharedCheck_6443_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6436_);
                        leanh::lean_dec(v_e_6425_);
                        v___x_6438_ = leanh::lean_box(0);
                        v_isShared_6439_ = v_isSharedCheck_6443_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6431_ = lean_mk_io_user_error(v_a_6427_);
                if v_isShared_6430_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6429_, 1);
                    leanh::lean_ctor_set(v___x_6429_, 0, v___x_6431_);
                    v___x_6433_ = v___x_6429_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6434_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6434_, 0, v___x_6431_);
                    v___x_6433_ = v_reuseFailAlloc_6434_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6433_;
            }
            3 => {
                if v_isShared_6439_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6438_, 0);
                    v___x_6441_ = v___x_6438_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6442_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6442_, 0, v_a_6436_);
                    v___x_6441_ = v_reuseFailAlloc_6442_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6441_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg___boxed(
    mut v_e_6444_: *mut leanh::LeanObject,
    mut v_a_6445_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6446_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6446_ =
        l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(
            v_e_6444_,
        );
    return v_res_6446_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(
    mut v_00_u03b1_6447_: *mut leanh::LeanObject,
    mut v_e_6448_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6450_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6450_ =
        l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(
            v_e_6448_,
        );
    return v___x_6450_;
}
pub unsafe fn l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___boxed(
    mut v_00_u03b1_6451_: *mut leanh::LeanObject,
    mut v_e_6452_: *mut leanh::LeanObject,
    mut v_a_6453_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6454_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6454_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0(
        v_00_u03b1_6451_,
        v_e_6452_,
    );
    return v_res_6454_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(
    mut v_declName_6462_: *mut leanh::LeanObject,
    mut v_a_6463_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_env_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_opts_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6467_: u8 = 0;
    let mut v___x_6468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6470_: u8 = 0;
    let mut v___x_6471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6480_: u8 = 0;
    let mut v___x_6482_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6483_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6484_: u8 = 0;
    let mut v___x_6485_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6486_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6487_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6488_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6489_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6490_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6494_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6498_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6500_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_pre_6504_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_str_6509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6511_: u8 = 0;
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: u8 = 0;
    let mut v___x_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6515_: u8 = 0;
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6517_: u8 = 0;
    let mut v___x_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6519_: u8 = 0;
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6522_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_env_6465_ = leanh::lean_ctor_get(v_a_6463_, 0);
                v_opts_6466_ = leanh::lean_ctor_get(v_a_6463_, 1);
                v___x_6467_ = 0;
                leanh::lean_inc(v_declName_6462_);
                leanh::lean_inc_ref(v_env_6465_);
                v___x_6468_ =
                    l_Lean_Environment_find_x3f(v_env_6465_, v_declName_6462_, v___x_6467_);
                if leanh::lean_obj_tag(v___x_6468_) == 0 {
                    v___x_6469_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__0;
                    v___x_6470_ = 1;
                    v___x_6471_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v_declName_6462_,
                        v___x_6470_,
                    );
                    v___x_6472_ = lean_string_append(v___x_6469_, v___x_6471_);
                    leanh::lean_dec_ref(v___x_6471_);
                    v___x_6473_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1;
                    v___x_6474_ = lean_string_append(v___x_6472_, v___x_6473_);
                    v___x_6475_ = lean_mk_io_user_error(v___x_6474_);
                    v___x_6476_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6476_, 0, v___x_6475_);
                    return v___x_6476_;
                } else {
                    v_val_6477_ = leanh::lean_ctor_get(v___x_6468_, 0);
                    v_isSharedCheck_6522_ = (!leanh::lean_is_exclusive(v___x_6468_)) as u8;
                    if v_isSharedCheck_6522_ == 0 {
                        v___x_6479_ = v___x_6468_;
                        v_isShared_6480_ = v_isSharedCheck_6522_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6477_);
                        leanh::lean_dec(v___x_6468_);
                        v___x_6479_ = leanh::lean_box(0);
                        v_isShared_6480_ = v_isSharedCheck_6522_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6498_ = l_Lean_ConstantInfo_type(v_val_6477_);
                if leanh::lean_obj_tag(v___x_6498_) == 4 {
                    v_declName_6499_ = leanh::lean_ctor_get(v___x_6498_, 0);
                    leanh::lean_inc(v_declName_6499_);
                    leanh::lean_dec_ref_known(v___x_6498_, 2);
                    if leanh::lean_obj_tag(v_declName_6499_) == 1 {
                        v_pre_6500_ = leanh::lean_ctor_get(v_declName_6499_, 0);
                        leanh::lean_inc(v_pre_6500_);
                        if leanh::lean_obj_tag(v_pre_6500_) == 1 {
                            v_pre_6501_ = leanh::lean_ctor_get(v_pre_6500_, 0);
                            leanh::lean_inc(v_pre_6501_);
                            if leanh::lean_obj_tag(v_pre_6501_) == 1 {
                                v_pre_6502_ = leanh::lean_ctor_get(v_pre_6501_, 0);
                                leanh::lean_inc(v_pre_6502_);
                                if leanh::lean_obj_tag(v_pre_6502_) == 1 {
                                    v_pre_6503_ = leanh::lean_ctor_get(v_pre_6502_, 0);
                                    leanh::lean_inc(v_pre_6503_);
                                    if leanh::lean_obj_tag(v_pre_6503_) == 1 {
                                        v_pre_6504_ = leanh::lean_ctor_get(v_pre_6503_, 0);
                                        if leanh::lean_obj_tag(v_pre_6504_) == 0 {
                                            v_str_6505_ =
                                                leanh::lean_ctor_get(v_declName_6499_, 1);
                                            leanh::lean_inc_ref(v_str_6505_);
                                            leanh::lean_dec_ref_known(v_declName_6499_, 2);
                                            v_str_6506_ =
                                                leanh::lean_ctor_get(v_pre_6500_, 1);
                                            leanh::lean_inc_ref(v_str_6506_);
                                            leanh::lean_dec_ref_known(v_pre_6500_, 2);
                                            v_str_6507_ =
                                                leanh::lean_ctor_get(v_pre_6501_, 1);
                                            leanh::lean_inc_ref(v_str_6507_);
                                            leanh::lean_dec_ref_known(v_pre_6501_, 2);
                                            v_str_6508_ =
                                                leanh::lean_ctor_get(v_pre_6502_, 1);
                                            leanh::lean_inc_ref(v_str_6508_);
                                            leanh::lean_dec_ref_known(v_pre_6502_, 2);
                                            v_str_6509_ =
                                                leanh::lean_ctor_get(v_pre_6503_, 1);
                                            leanh::lean_inc_ref(v_str_6509_);
                                            leanh::lean_dec_ref_known(v_pre_6503_, 2);
                                            v___x_6510_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__0;
                                            v___x_6511_ =
                                                lean_string_dec_eq(v_str_6509_, v___x_6510_);
                                            leanh::lean_dec_ref(v_str_6509_);
                                            if v___x_6511_ == 0 {
                                                leanh::lean_dec_ref(v_str_6508_);
                                                leanh::lean_dec_ref(v_str_6507_);
                                                leanh::lean_dec_ref(v_str_6506_);
                                                leanh::lean_dec_ref(v_str_6505_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_6512_ = l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__1;
                                                v___x_6513_ =
                                                    lean_string_dec_eq(v_str_6508_, v___x_6512_);
                                                leanh::lean_dec_ref(v_str_6508_);
                                                if v___x_6513_ == 0 {
                                                    leanh::lean_dec_ref(v_str_6507_);
                                                    leanh::lean_dec_ref(v_str_6506_);
                                                    leanh::lean_dec_ref(v_str_6505_);
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_6514_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__4;
                                                    v___x_6515_ = lean_string_dec_eq(
                                                        v_str_6507_,
                                                        v___x_6514_,
                                                    );
                                                    leanh::lean_dec_ref(v_str_6507_);
                                                    if v___x_6515_ == 0 {
                                                        leanh::lean_dec_ref(v_str_6506_);
                                                        leanh::lean_dec_ref(v_str_6505_);
                                                        state = 2;
                                                        continue;
                                                    } else {
                                                        v___x_6516_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__5;
                                                        v___x_6517_ = lean_string_dec_eq(
                                                            v_str_6506_,
                                                            v___x_6516_,
                                                        );
                                                        leanh::lean_dec_ref(v_str_6506_);
                                                        if v___x_6517_ == 0 {
                                                            leanh::lean_dec_ref(v_str_6505_);
                                                            state = 2;
                                                            continue;
                                                        } else {
                                                            v___x_6518_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__6;
                                                            v___x_6519_ = lean_string_dec_eq(
                                                                v_str_6505_,
                                                                v___x_6518_,
                                                            );
                                                            leanh::lean_dec_ref(v_str_6505_);
                                                            if v___x_6519_ == 0 {
                                                                state = 2;
                                                                continue;
                                                            } else {
                                                                leanh::lean_del_object(
                                                                    v___x_6479_,
                                                                );
                                                                leanh::lean_dec(v_val_6477_);
                                                                v___x_6520_ = l_Lean_Environment_evalConst___redArg(v_env_6465_, v_opts_6466_, v_declName_6462_, v___x_6519_);
                                                                leanh::lean_dec(
                                                                    v_declName_6462_,
                                                                );
                                                                v___x_6521_ = l_IO_ofExcept___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl_spec__0___redArg(v___x_6520_);
                                                                return v___x_6521_;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        } else {
                                            leanh::lean_dec_ref_known(v_pre_6503_, 2);
                                            leanh::lean_dec_ref_known(v_pre_6502_, 2);
                                            leanh::lean_dec_ref_known(v_pre_6501_, 2);
                                            leanh::lean_dec_ref_known(v_pre_6500_, 2);
                                            leanh::lean_dec_ref_known(v_declName_6499_, 2);
                                            state = 2;
                                            continue;
                                        }
                                    } else {
                                        leanh::lean_dec(v_pre_6503_);
                                        leanh::lean_dec_ref_known(v_pre_6502_, 2);
                                        leanh::lean_dec_ref_known(v_pre_6501_, 2);
                                        leanh::lean_dec_ref_known(v_pre_6500_, 2);
                                        leanh::lean_dec_ref_known(v_declName_6499_, 2);
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec(v_pre_6502_);
                                    leanh::lean_dec_ref_known(v_pre_6501_, 2);
                                    leanh::lean_dec_ref_known(v_pre_6500_, 2);
                                    leanh::lean_dec_ref_known(v_declName_6499_, 2);
                                    state = 2;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_pre_6500_, 2);
                                leanh::lean_dec(v_pre_6501_);
                                leanh::lean_dec_ref_known(v_declName_6499_, 2);
                                state = 2;
                                continue;
                            }
                        } else {
                            leanh::lean_dec(v_pre_6500_);
                            leanh::lean_dec_ref_known(v_declName_6499_, 2);
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_declName_6499_);
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_6498_);
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6482_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__2;
                v___x_6483_ = l_Lean_privateToUserName(v_declName_6462_);
                v___x_6484_ = 1;
                v___x_6485_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                    v___x_6483_,
                    v___x_6484_,
                );
                v___x_6486_ = lean_string_append(v___x_6482_, v___x_6485_);
                leanh::lean_dec_ref(v___x_6485_);
                v___x_6487_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__3;
                v___x_6488_ = lean_string_append(v___x_6486_, v___x_6487_);
                v___x_6489_ = l_Lean_ConstantInfo_type(v_val_6477_);
                leanh::lean_dec(v_val_6477_);
                v___x_6490_ = lean_expr_dbg_to_string(v___x_6489_);
                leanh::lean_dec_ref(v___x_6489_);
                v___x_6491_ = lean_string_append(v___x_6488_, v___x_6490_);
                leanh::lean_dec_ref(v___x_6490_);
                v___x_6492_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1;
                v___x_6493_ = lean_string_append(v___x_6491_, v___x_6492_);
                v___x_6494_ = lean_mk_io_user_error(v___x_6493_);
                if v_isShared_6480_ == 0 {
                    leanh::lean_ctor_set(v___x_6479_, 0, v___x_6494_);
                    v___x_6496_ = v___x_6479_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6497_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6497_, 0, v___x_6494_);
                    v___x_6496_ = v_reuseFailAlloc_6497_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6496_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___boxed(
    mut v_declName_6523_: *mut leanh::LeanObject,
    mut v_a_6524_: *mut leanh::LeanObject,
    mut v_a_6525_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6526_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_6523_, v_a_6524_);
    leanh::lean_dec_ref(v_a_6524_);
    return v_res_6526_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(
    mut v_e_6527_: *mut leanh::LeanObject,
    mut v_a_6528_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_declName_6530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6535_: u8 = 0;
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6540_: u8 = 0;
    let mut v_a_6541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6544_: u8 = 0;
    let mut v___x_6546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_declName_6530_ = leanh::lean_ctor_get(v_e_6527_, 0);
                leanh::lean_inc(v_declName_6530_);
                v___x_6531_ =
                    l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_6530_, v_a_6528_);
                if leanh::lean_obj_tag(v___x_6531_) == 0 {
                    v_a_6532_ = leanh::lean_ctor_get(v___x_6531_, 0);
                    v_isSharedCheck_6540_ = (!leanh::lean_is_exclusive(v___x_6531_)) as u8;
                    if v_isSharedCheck_6540_ == 0 {
                        v___x_6534_ = v___x_6531_;
                        v_isShared_6535_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6532_);
                        leanh::lean_dec(v___x_6531_);
                        v___x_6534_ = leanh::lean_box(0);
                        v_isShared_6535_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_e_6527_);
                    v_a_6541_ = leanh::lean_ctor_get(v___x_6531_, 0);
                    v_isSharedCheck_6548_ = (!leanh::lean_is_exclusive(v___x_6531_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v___x_6543_ = v___x_6531_;
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6541_);
                        leanh::lean_dec(v___x_6531_);
                        v___x_6543_ = leanh::lean_box(0);
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6536_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6536_, 0, v_e_6527_);
                leanh::lean_ctor_set(v___x_6536_, 1, v_a_6532_);
                if v_isShared_6535_ == 0 {
                    leanh::lean_ctor_set(v___x_6534_, 0, v___x_6536_);
                    v___x_6538_ = v___x_6534_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6539_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6539_, 0, v___x_6536_);
                    v___x_6538_ = v_reuseFailAlloc_6539_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6538_;
            }
            3 => {
                if v_isShared_6544_ == 0 {
                    v___x_6546_ = v___x_6543_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
                    v___x_6546_ = v_reuseFailAlloc_6547_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry___boxed(
    mut v_e_6549_: *mut leanh::LeanObject,
    mut v_a_6550_: *mut leanh::LeanObject,
    mut v_a_6551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6552_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6552_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v_e_6549_, v_a_6550_);
    leanh::lean_dec_ref(v_a_6550_);
    return v_res_6552_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6556_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6554_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3
        ),
        core::ptr::addr_of_mut!(
            l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3_once
        ),
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default___closed__3,
    );
    v___x_6555_ = lean_st_mk_ref(v___x_6554_);
    v___x_6556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6556_, 0, v___x_6555_);
    return v___x_6556_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2____boxed(
    mut v_a_6557_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6558_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6558_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
    return v_res_6558_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(
    mut v___y_6559_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    leanh::lean_inc_ref(v___y_6559_);
    return v___y_6559_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(
    mut v___y_6560_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6561_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6561_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___y_6560_);
    leanh::lean_dec_ref(v___y_6560_);
    return v_res_6561_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(
    mut v_x_6562_: *mut leanh::LeanObject,
    mut v___y_6563_: *mut leanh::LeanObject,
    mut v___y_6564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6566_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6566_ = l_Lean_Meta_Tactic_Cbv_toCbvSimprocEntry(v___y_6563_, v___y_6564_);
    return v___x_6566_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(
    mut v_x_6567_: *mut leanh::LeanObject,
    mut v___y_6568_: *mut leanh::LeanObject,
    mut v___y_6569_: *mut leanh::LeanObject,
    mut v___y_6570_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6571_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6571_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_6567_, v___y_6568_, v___y_6569_);
    leanh::lean_dec_ref(v___y_6569_);
    leanh::lean_dec_ref(v_x_6567_);
    return v_res_6571_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(
    mut v_e_6572_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toCbvSimprocOLeanEntry_6573_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toCbvSimprocOLeanEntry_6573_ = leanh::lean_ctor_get(v_e_6572_, 0);
    leanh::lean_inc_ref(v_toCbvSimprocOLeanEntry_6573_);
    return v_toCbvSimprocOLeanEntry_6573_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(
    mut v_e_6574_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6575_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6575_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_e_6574_);
    leanh::lean_dec_ref(v_e_6574_);
    return v_res_6575_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(
    mut v_s_6576_: *mut leanh::LeanObject,
    mut v_e_6577_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_toCbvSimprocOLeanEntry_6578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_proc_6579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_declName_6580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_6581_: u8 = 0;
    let mut v_keys_6582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_toCbvSimprocOLeanEntry_6578_ = leanh::lean_ctor_get(v_e_6577_, 0);
    leanh::lean_inc_ref(v_toCbvSimprocOLeanEntry_6578_);
    v_proc_6579_ = leanh::lean_ctor_get(v_e_6577_, 1);
    leanh::lean_inc_ref(v_proc_6579_);
    leanh::lean_dec_ref(v_e_6577_);
    v_declName_6580_ = leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_6578_, 0);
    leanh::lean_inc(v_declName_6580_);
    v_phase_6581_ = leanh::lean_ctor_get_uint8(
        v_toCbvSimprocOLeanEntry_6578_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
    );
    v_keys_6582_ = leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_6578_, 1);
    leanh::lean_inc_ref(v_keys_6582_);
    leanh::lean_dec_ref(v_toCbvSimprocOLeanEntry_6578_);
    v___x_6583_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(
        v_s_6576_,
        v_keys_6582_,
        v_declName_6580_,
        v_phase_6581_,
        v_proc_6579_,
    );
    return v___x_6583_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(
    mut v_x_6584_: *mut leanh::LeanObject,
    mut v_a_6585_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6587_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6586_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6586_, 0, v_a_6585_);
    leanh::lean_inc_ref_n(v___x_6586_, 2);
    v___x_6587_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_6587_, 0, v___x_6586_);
    leanh::lean_ctor_set(v___x_6587_, 1, v___x_6586_);
    leanh::lean_ctor_set(v___x_6587_, 2, v___x_6586_);
    return v___x_6587_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(
    mut v_x_6588_: *mut leanh::LeanObject,
    mut v_a_6589_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6590_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v_x_6588_, v_a_6589_);
    leanh::lean_dec_ref(v_x_6588_);
    return v_res_6590_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(
    mut v___x_6591_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6594_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6593_ = lean_st_ref_get(v___x_6591_);
    v___x_6594_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6594_, 0, v___x_6593_);
    return v___x_6594_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(
    mut v___x_6595_: *mut leanh::LeanObject,
    mut v___y_6596_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6597_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6597_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_(v___x_6595_);
    leanh::lean_dec(v___x_6595_);
    return v_res_6597_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6607_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6606_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
    v___f_6607_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed as *mut core::ffi::c_void, 2, 1);
    leanh::lean_closure_set(v___f_6607_, 0, v___x_6606_);
    return v___f_6607_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_6608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_6608_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
    v___f_6609_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
    v___f_6610_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
    v___f_6611_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
    v___f_6612_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
    v___f_6613_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
    v___x_6614_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__6_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_;
    v___x_6615_ = leanh::lean_alloc_ctor(0, 7, (0) as u32);
    leanh::lean_ctor_set(v___x_6615_, 0, v___x_6614_);
    leanh::lean_ctor_set(v___x_6615_, 1, v___f_6613_);
    leanh::lean_ctor_set(v___x_6615_, 2, v___f_6612_);
    leanh::lean_ctor_set(v___x_6615_, 3, v___f_6611_);
    leanh::lean_ctor_set(v___x_6615_, 4, v___f_6610_);
    leanh::lean_ctor_set(v___x_6615_, 5, v___f_6609_);
    leanh::lean_ctor_set(v___x_6615_, 6, v___f_6608_);
    return v___x_6615_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_6617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6618_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6617_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_);
    v___x_6618_ = l_Lean_registerScopedEnvExtensionUnsafe___redArg(v___x_6617_);
    return v___x_6618_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2____boxed(
    mut v_a_6619_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6620_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6620_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
    return v_res_6620_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0(
    mut v_declName_6621_: *mut leanh::LeanObject,
    mut v_s_6622_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6623_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6623_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_erase(v_s_6622_, v_declName_6621_);
    return v___x_6623_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(
    mut v_keys_6624_: *mut leanh::LeanObject,
    mut v_i_6625_: *mut leanh::LeanObject,
    mut v_k_6626_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6628_: u8 = 0;
    let mut v_k_x27_6629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: u8 = 0;
    let mut v___x_6631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6627_ = lean_array_get_size(v_keys_6624_);
                v___x_6628_ = lean_nat_dec_lt(v_i_6625_, v___x_6627_);
                if v___x_6628_ == 0 {
                    leanh::lean_dec(v_i_6625_);
                    return v___x_6628_;
                } else {
                    v_k_x27_6629_ = lean_array_fget_borrowed(v_keys_6624_, v_i_6625_);
                    v___x_6630_ = lean_name_eq(v_k_6626_, v_k_x27_6629_);
                    if v___x_6630_ == 0 {
                        v___x_6631_ = leanh::lean_unsigned_to_nat(1);
                        v___x_6632_ = lean_nat_add(v_i_6625_, v___x_6631_);
                        leanh::lean_dec(v_i_6625_);
                        v_i_6625_ = v___x_6632_;
                        state = 0;
                        continue;
                    } else {
                        leanh::lean_dec(v_i_6625_);
                        return v___x_6630_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_6634_: *mut leanh::LeanObject,
    mut v_i_6635_: *mut leanh::LeanObject,
    mut v_k_6636_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6637_: u8 = 0;
    let mut v_r_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6637_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_6634_, v_i_6635_, v_k_6636_);
    leanh::lean_dec(v_k_6636_);
    leanh::lean_dec_ref(v_keys_6634_);
    v_r_6638_ = leanh::lean_box((v_res_6637_) as usize);
    return v_r_6638_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(
    mut v_x_6639_: *mut leanh::LeanObject,
    mut v_x_6640_: usize,
    mut v_x_6641_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_es_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: usize = 0;
    let mut v___x_6645_: usize = 0;
    let mut v___x_6646_: usize = 0;
    let mut v_j_6647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6650_: u8 = 0;
    let mut v_node_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6652_: usize = 0;
    let mut v___x_6654_: u8 = 0;
    let mut v_ks_6655_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6657_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6639_) == 0 {
                    v_es_6642_ = leanh::lean_ctor_get(v_x_6639_, 0);
                    v___x_6643_ = leanh::lean_box(2);
                    v___x_6644_ = 5usize;
                    v___x_6645_ = leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__2_spec__5_spec__10___redArg___closed__1);
                    v___x_6646_ = lean_usize_land(v_x_6640_, v___x_6645_);
                    v_j_6647_ = lean_usize_to_nat(v___x_6646_);
                    v___x_6648_ = lean_array_get_borrowed(v___x_6643_, v_es_6642_, v_j_6647_);
                    leanh::lean_dec(v_j_6647_);
                    match leanh::lean_obj_tag(v___x_6648_) {
                        0 => {
                            v_key_6649_ = leanh::lean_ctor_get(v___x_6648_, 0);
                            v___x_6650_ = lean_name_eq(v_x_6641_, v_key_6649_);
                            return v___x_6650_;
                        }
                        1 => {
                            v_node_6651_ = leanh::lean_ctor_get(v___x_6648_, 0);
                            v___x_6652_ = lean_usize_shift_right(v_x_6640_, v___x_6644_);
                            v_x_6639_ = v_node_6651_;
                            v_x_6640_ = v___x_6652_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_6654_ = 0;
                            return v___x_6654_;
                        }
                    }
                } else {
                    v_ks_6655_ = leanh::lean_ctor_get(v_x_6639_, 0);
                    v___x_6656_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6657_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_ks_6655_, v___x_6656_, v_x_6641_);
                    return v___x_6657_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg___boxed(
    mut v_x_6658_: *mut leanh::LeanObject,
    mut v_x_6659_: *mut leanh::LeanObject,
    mut v_x_6660_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_557__boxed_6661_: usize = 0;
    let mut v_res_6662_: u8 = 0;
    let mut v_r_6663_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_557__boxed_6661_ = leanh::lean_unbox_usize(v_x_6659_);
    leanh::lean_dec(v_x_6659_);
    v_res_6662_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_6658_, v_x_557__boxed_6661_, v_x_6660_);
    leanh::lean_dec(v_x_6660_);
    leanh::lean_dec_ref(v_x_6658_);
    v_r_6663_ = leanh::lean_box((v_res_6662_) as usize);
    return v_r_6663_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(
    mut v_x_6664_: *mut leanh::LeanObject,
    mut v_x_6665_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___y_6667_: u64 = 0;
    let mut v___x_6668_: usize = 0;
    let mut v___x_6669_: u8 = 0;
    let mut v___x_6670_: u64 = 0;
    let mut v_hash_6671_: u64 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6665_) == 0 {
                    v___x_6670_ = leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0_once), _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore_spec__0_spec__0_spec__2___redArg___closed__0);
                    v___y_6667_ = v___x_6670_;
                    state = 1;
                    continue;
                } else {
                    v_hash_6671_ = leanh::lean_ctor_get_uint64(
                        v_x_6665_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                    );
                    v___y_6667_ = v_hash_6671_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6668_ = lean_uint64_to_usize(v___y_6667_);
                v___x_6669_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_6664_, v___x_6668_, v_x_6665_);
                return v___x_6669_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg___boxed(
    mut v_x_6672_: *mut leanh::LeanObject,
    mut v_x_6673_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6674_: u8 = 0;
    let mut v_r_6675_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6674_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_6672_, v_x_6673_);
    leanh::lean_dec(v_x_6673_);
    leanh::lean_dec_ref(v_x_6672_);
    v_r_6675_ = leanh::lean_box((v_res_6674_) as usize);
    return v_r_6675_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6676_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6677_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6676_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl___closed__1;
    v___x_6677_ = l_Lean_stringToMessageData(v___x_6676_);
    return v___x_6677_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6679_ = l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__1;
    v___x_6680_ = l_Lean_stringToMessageData(v___x_6679_);
    return v___x_6680_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(
    mut v_declName_6681_: *mut leanh::LeanObject,
    mut v_a_6682_: *mut leanh::LeanObject,
    mut v_a_6683_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_6690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6691_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6692_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_simprocNames_6693_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6694_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_6696_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6697_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6698_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6702_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6703_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6704_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6708_: u8 = 0;
    let mut v___x_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6717_: u8 = 0;
    let mut v_unused_6718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6719_: u8 = 0;
    let mut v___x_6720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6685_ = lean_st_ref_get(v_a_6683_);
                v_env_6686_ = leanh::lean_ctor_get(v___x_6685_, 0);
                leanh::lean_inc_ref(v_env_6686_);
                leanh::lean_dec(v___x_6685_);
                v___x_6687_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
                v_ext_6688_ = leanh::lean_ctor_get(v___x_6687_, 1);
                v_toEnvExtension_6689_ = leanh::lean_ctor_get(v_ext_6688_, 0);
                v_asyncMode_6690_ = leanh::lean_ctor_get(v_toEnvExtension_6689_, 2);
                v___x_6691_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
                v___x_6692_ = l_Lean_ScopedEnvExtension_getState___redArg(
                    v___x_6691_,
                    v___x_6687_,
                    v_env_6686_,
                    v_asyncMode_6690_,
                );
                v_simprocNames_6693_ = leanh::lean_ctor_get(v___x_6692_, 3);
                leanh::lean_inc_ref(v_simprocNames_6693_);
                leanh::lean_dec(v___x_6692_);
                leanh::lean_inc(v_declName_6681_);
                v___f_6694_ = leanh::lean_alloc_closure(
                    l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___lam__0 as *mut core::ffi::c_void,
                    2,
                    1,
                );
                leanh::lean_closure_set(v___f_6694_, 0, v_declName_6681_);
                v___x_6719_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_simprocNames_6693_, v_declName_6681_);
                leanh::lean_dec_ref(v_simprocNames_6693_);
                if v___x_6719_ == 0 {
                    leanh::lean_dec_ref(v___f_6694_);
                    v___x_6720_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__0,
                    );
                    v___x_6721_ = l_Lean_MessageData_ofConstName(v_declName_6681_, v___x_6719_);
                    v___x_6722_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6722_, 0, v___x_6720_);
                    leanh::lean_ctor_set(v___x_6722_, 1, v___x_6721_);
                    v___x_6723_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___closed__2,
                    );
                    v___x_6724_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6724_, 0, v___x_6722_);
                    leanh::lean_ctor_set(v___x_6724_, 1, v___x_6723_);
                    v___x_6725_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_6724_, v_a_6682_, v_a_6683_);
                    return v___x_6725_;
                } else {
                    leanh::lean_dec(v_declName_6681_);
                    v___y_6696_ = v_a_6683_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_6697_ = lean_st_ref_take(v___y_6696_);
                v_env_6698_ = leanh::lean_ctor_get(v___x_6697_, 0);
                v_nextMacroScope_6699_ = leanh::lean_ctor_get(v___x_6697_, 1);
                v_ngen_6700_ = leanh::lean_ctor_get(v___x_6697_, 2);
                v_auxDeclNGen_6701_ = leanh::lean_ctor_get(v___x_6697_, 3);
                v_traceState_6702_ = leanh::lean_ctor_get(v___x_6697_, 4);
                v_messages_6703_ = leanh::lean_ctor_get(v___x_6697_, 6);
                v_infoState_6704_ = leanh::lean_ctor_get(v___x_6697_, 7);
                v_snapshotTasks_6705_ = leanh::lean_ctor_get(v___x_6697_, 8);
                v_isSharedCheck_6717_ = (!leanh::lean_is_exclusive(v___x_6697_)) as u8;
                if v_isSharedCheck_6717_ == 0 {
                    v_unused_6718_ = leanh::lean_ctor_get(v___x_6697_, 5);
                    leanh::lean_dec(v_unused_6718_);
                    v___x_6707_ = v___x_6697_;
                    v_isShared_6708_ = v_isSharedCheck_6717_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6705_);
                    leanh::lean_inc(v_infoState_6704_);
                    leanh::lean_inc(v_messages_6703_);
                    leanh::lean_inc(v_traceState_6702_);
                    leanh::lean_inc(v_auxDeclNGen_6701_);
                    leanh::lean_inc(v_ngen_6700_);
                    leanh::lean_inc(v_nextMacroScope_6699_);
                    leanh::lean_inc(v_env_6698_);
                    leanh::lean_dec(v___x_6697_);
                    v___x_6707_ = leanh::lean_box(0);
                    v_isShared_6708_ = v_isSharedCheck_6717_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6709_ = l_Lean_ScopedEnvExtension_modifyState___redArg(
                    v___x_6687_,
                    v_env_6698_,
                    v___f_6694_,
                );
                v___x_6710_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2,
                );
                if v_isShared_6708_ == 0 {
                    leanh::lean_ctor_set(v___x_6707_, 5, v___x_6710_);
                    leanh::lean_ctor_set(v___x_6707_, 0, v___x_6709_);
                    v___x_6712_ = v___x_6707_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6716_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 0, v___x_6709_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 1, v_nextMacroScope_6699_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 2, v_ngen_6700_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 3, v_auxDeclNGen_6701_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 4, v_traceState_6702_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 5, v___x_6710_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 6, v_messages_6703_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 7, v_infoState_6704_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6716_, 8, v_snapshotTasks_6705_);
                    v___x_6712_ = v_reuseFailAlloc_6716_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_6713_ = lean_st_ref_set(v___y_6696_, v___x_6712_);
                v___x_6714_ = leanh::lean_box(0);
                v___x_6715_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6715_, 0, v___x_6714_);
                return v___x_6715_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr___boxed(
    mut v_declName_6726_: *mut leanh::LeanObject,
    mut v_a_6727_: *mut leanh::LeanObject,
    mut v_a_6728_: *mut leanh::LeanObject,
    mut v_a_6729_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6730_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6730_ =
        l_Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr(v_declName_6726_, v_a_6727_, v_a_6728_);
    leanh::lean_dec(v_a_6728_);
    leanh::lean_dec_ref(v_a_6727_);
    return v_res_6730_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(
    mut v_00_u03b2_6731_: *mut leanh::LeanObject,
    mut v_x_6732_: *mut leanh::LeanObject,
    mut v_x_6733_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6734_: u8 = 0;
    v___x_6734_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_x_6732_, v_x_6733_);
    return v___x_6734_;
}
pub unsafe fn l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___boxed(
    mut v_00_u03b2_6735_: *mut leanh::LeanObject,
    mut v_x_6736_: *mut leanh::LeanObject,
    mut v_x_6737_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6738_: u8 = 0;
    let mut v_r_6739_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6738_ =
        l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0(
            v_00_u03b2_6735_,
            v_x_6736_,
            v_x_6737_,
        );
    leanh::lean_dec(v_x_6737_);
    leanh::lean_dec_ref(v_x_6736_);
    v_r_6739_ = leanh::lean_box((v_res_6738_) as usize);
    return v_r_6739_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(
    mut v_00_u03b2_6740_: *mut leanh::LeanObject,
    mut v_x_6741_: *mut leanh::LeanObject,
    mut v_x_6742_: usize,
    mut v_x_6743_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6744_: u8 = 0;
    v___x_6744_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___redArg(v_x_6741_, v_x_6742_, v_x_6743_);
    return v___x_6744_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0___boxed(
    mut v_00_u03b2_6745_: *mut leanh::LeanObject,
    mut v_x_6746_: *mut leanh::LeanObject,
    mut v_x_6747_: *mut leanh::LeanObject,
    mut v_x_6748_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_710__boxed_6749_: usize = 0;
    let mut v_res_6750_: u8 = 0;
    let mut v_r_6751_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_710__boxed_6749_ = leanh::lean_unbox_usize(v_x_6747_);
    leanh::lean_dec(v_x_6747_);
    v_res_6750_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0(v_00_u03b2_6745_, v_x_6746_, v_x_710__boxed_6749_, v_x_6748_);
    leanh::lean_dec(v_x_6748_);
    leanh::lean_dec_ref(v_x_6746_);
    v_r_6751_ = leanh::lean_box((v_res_6750_) as usize);
    return v_r_6751_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(
    mut v_00_u03b2_6752_: *mut leanh::LeanObject,
    mut v_keys_6753_: *mut leanh::LeanObject,
    mut v_vals_6754_: *mut leanh::LeanObject,
    mut v_heq_6755_: *mut leanh::LeanObject,
    mut v_i_6756_: *mut leanh::LeanObject,
    mut v_k_6757_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6758_: u8 = 0;
    v___x_6758_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___redArg(v_keys_6753_, v_i_6756_, v_k_6757_);
    return v___x_6758_;
}
pub unsafe fn l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_6759_: *mut leanh::LeanObject,
    mut v_keys_6760_: *mut leanh::LeanObject,
    mut v_vals_6761_: *mut leanh::LeanObject,
    mut v_heq_6762_: *mut leanh::LeanObject,
    mut v_i_6763_: *mut leanh::LeanObject,
    mut v_k_6764_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6765_: u8 = 0;
    let mut v_r_6766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6765_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0_spec__0_spec__1(v_00_u03b2_6759_, v_keys_6760_, v_vals_6761_, v_heq_6762_, v_i_6763_, v_k_6764_);
    leanh::lean_dec(v_k_6764_);
    leanh::lean_dec_ref(v_vals_6761_);
    leanh::lean_dec_ref(v_keys_6760_);
    v_r_6766_ = leanh::lean_box((v_res_6765_) as usize);
    return v_r_6766_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(
    mut v_ext_6767_: *mut leanh::LeanObject,
    mut v_b_6768_: *mut leanh::LeanObject,
    mut v_kind_6769_: u8,
    mut v___y_6770_: *mut leanh::LeanObject,
    mut v___y_6771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_currNamespace_6773_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_6776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6784_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6785_: u8 = 0;
    let mut v___x_6786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6794_: u8 = 0;
    let mut v_unused_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_currNamespace_6773_ = leanh::lean_ctor_get(v___y_6770_, 6);
                v___x_6774_ = lean_st_ref_take(v___y_6771_);
                v_env_6775_ = leanh::lean_ctor_get(v___x_6774_, 0);
                v_nextMacroScope_6776_ = leanh::lean_ctor_get(v___x_6774_, 1);
                v_ngen_6777_ = leanh::lean_ctor_get(v___x_6774_, 2);
                v_auxDeclNGen_6778_ = leanh::lean_ctor_get(v___x_6774_, 3);
                v_traceState_6779_ = leanh::lean_ctor_get(v___x_6774_, 4);
                v_messages_6780_ = leanh::lean_ctor_get(v___x_6774_, 6);
                v_infoState_6781_ = leanh::lean_ctor_get(v___x_6774_, 7);
                v_snapshotTasks_6782_ = leanh::lean_ctor_get(v___x_6774_, 8);
                v_isSharedCheck_6794_ = (!leanh::lean_is_exclusive(v___x_6774_)) as u8;
                if v_isSharedCheck_6794_ == 0 {
                    v_unused_6795_ = leanh::lean_ctor_get(v___x_6774_, 5);
                    leanh::lean_dec(v_unused_6795_);
                    v___x_6784_ = v___x_6774_;
                    v_isShared_6785_ = v_isSharedCheck_6794_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_6782_);
                    leanh::lean_inc(v_infoState_6781_);
                    leanh::lean_inc(v_messages_6780_);
                    leanh::lean_inc(v_traceState_6779_);
                    leanh::lean_inc(v_auxDeclNGen_6778_);
                    leanh::lean_inc(v_ngen_6777_);
                    leanh::lean_inc(v_nextMacroScope_6776_);
                    leanh::lean_inc(v_env_6775_);
                    leanh::lean_dec(v___x_6774_);
                    v___x_6784_ = leanh::lean_box(0);
                    v_isShared_6785_ = v_isSharedCheck_6794_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                leanh::lean_inc(v_currNamespace_6773_);
                v___x_6786_ = l_Lean_ScopedEnvExtension_addCore___redArg(
                    v_env_6775_,
                    v_ext_6767_,
                    v_b_6768_,
                    v_kind_6769_,
                    v_currNamespace_6773_,
                );
                v___x_6787_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2_once
                    ),
                    _init_l_Lean_Meta_Tactic_Cbv_registerCbvSimproc___closed__2,
                );
                if v_isShared_6785_ == 0 {
                    leanh::lean_ctor_set(v___x_6784_, 5, v___x_6787_);
                    leanh::lean_ctor_set(v___x_6784_, 0, v___x_6786_);
                    v___x_6789_ = v___x_6784_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6793_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 0, v___x_6786_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 1, v_nextMacroScope_6776_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 2, v_ngen_6777_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 3, v_auxDeclNGen_6778_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 4, v_traceState_6779_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 5, v___x_6787_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 6, v_messages_6780_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 7, v_infoState_6781_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6793_, 8, v_snapshotTasks_6782_);
                    v___x_6789_ = v_reuseFailAlloc_6793_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_6790_ = lean_st_ref_set(v___y_6771_, v___x_6789_);
                v___x_6791_ = leanh::lean_box(0);
                v___x_6792_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6792_, 0, v___x_6791_);
                return v___x_6792_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg___boxed(
    mut v_ext_6796_: *mut leanh::LeanObject,
    mut v_b_6797_: *mut leanh::LeanObject,
    mut v_kind_6798_: *mut leanh::LeanObject,
    mut v___y_6799_: *mut leanh::LeanObject,
    mut v___y_6800_: *mut leanh::LeanObject,
    mut v___y_6801_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6802_: u8 = 0;
    let mut v_res_6803_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6802_ = (leanh::lean_unbox(v_kind_6798_) as u8);
    v_res_6803_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_6796_, v_b_6797_, v_kind_boxed_6802_, v___y_6799_, v___y_6800_);
    leanh::lean_dec(v___y_6800_);
    leanh::lean_dec_ref(v___y_6799_);
    return v_res_6803_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(
    mut v_00_u03b1_6804_: *mut leanh::LeanObject,
    mut v_00_u03b2_6805_: *mut leanh::LeanObject,
    mut v_00_u03c3_6806_: *mut leanh::LeanObject,
    mut v_ext_6807_: *mut leanh::LeanObject,
    mut v_b_6808_: *mut leanh::LeanObject,
    mut v_kind_6809_: u8,
    mut v___y_6810_: *mut leanh::LeanObject,
    mut v___y_6811_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6813_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v_ext_6807_, v_b_6808_, v_kind_6809_, v___y_6810_, v___y_6811_);
    return v___x_6813_;
}
pub unsafe fn l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___boxed(
    mut v_00_u03b1_6814_: *mut leanh::LeanObject,
    mut v_00_u03b2_6815_: *mut leanh::LeanObject,
    mut v_00_u03c3_6816_: *mut leanh::LeanObject,
    mut v_ext_6817_: *mut leanh::LeanObject,
    mut v_b_6818_: *mut leanh::LeanObject,
    mut v_kind_6819_: *mut leanh::LeanObject,
    mut v___y_6820_: *mut leanh::LeanObject,
    mut v___y_6821_: *mut leanh::LeanObject,
    mut v___y_6822_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6823_: u8 = 0;
    let mut v_res_6824_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6823_ = (leanh::lean_unbox(v_kind_6819_) as u8);
    v_res_6824_ =
        l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0(
            v_00_u03b1_6814_,
            v_00_u03b2_6815_,
            v_00_u03c3_6816_,
            v_ext_6817_,
            v_b_6818_,
            v_kind_boxed_6823_,
            v___y_6820_,
            v___y_6821_,
        );
    leanh::lean_dec(v___y_6821_);
    leanh::lean_dec_ref(v___y_6820_);
    return v_res_6824_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6827_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6826_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__0;
    v___x_6827_ = l_Lean_stringToMessageData(v___x_6826_);
    return v___x_6827_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6830_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6829_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__2;
    v___x_6830_ = l_Lean_stringToMessageData(v___x_6829_);
    return v___x_6830_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(
    mut v_declName_6831_: *mut leanh::LeanObject,
    mut v_kind_6832_: u8,
    mut v_phase_6833_: u8,
    mut v_a_6834_: *mut leanh::LeanObject,
    mut v_a_6835_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_6838_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_6839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_6840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6841_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6852_: u8 = 0;
    let mut v___x_6853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6861_: u8 = 0;
    let mut v___x_6862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6869_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6837_ = lean_st_ref_get(v_a_6835_);
                v_env_6838_ = leanh::lean_ctor_get(v___x_6837_, 0);
                leanh::lean_inc_ref(v_env_6838_);
                leanh::lean_dec(v___x_6837_);
                v_options_6839_ = leanh::lean_ctor_get(v_a_6834_, 2);
                v_ref_6840_ = leanh::lean_ctor_get(v_a_6834_, 5);
                leanh::lean_inc_ref(v_options_6839_);
                v___x_6841_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6841_, 0, v_env_6838_);
                leanh::lean_ctor_set(v___x_6841_, 1, v_options_6839_);
                leanh::lean_inc(v_declName_6831_);
                v___x_6842_ =
                    l_Lean_Meta_Tactic_Cbv_getCbvSimprocFromDeclImpl(v_declName_6831_, v___x_6841_);
                leanh::lean_dec_ref_known(v___x_6841_, 2);
                if leanh::lean_obj_tag(v___x_6842_) == 0 {
                    v_a_6843_ = leanh::lean_ctor_get(v___x_6842_, 0);
                    leanh::lean_inc(v_a_6843_);
                    leanh::lean_dec_ref_known(v___x_6842_, 1);
                    leanh::lean_inc(v_declName_6831_);
                    v___x_6844_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f___redArg(
                        v_declName_6831_,
                        v_a_6835_,
                    );
                    v_a_6845_ = leanh::lean_ctor_get(v___x_6844_, 0);
                    leanh::lean_inc(v_a_6845_);
                    leanh::lean_dec_ref(v___x_6844_);
                    if leanh::lean_obj_tag(v_a_6845_) == 1 {
                        v_val_6846_ = leanh::lean_ctor_get(v_a_6845_, 0);
                        leanh::lean_inc(v_val_6846_);
                        leanh::lean_dec_ref_known(v_a_6845_, 1);
                        v___x_6847_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
                        v___x_6848_ = leanh::lean_alloc_ctor(0, 2, (1) as u32);
                        leanh::lean_ctor_set(v___x_6848_, 0, v_declName_6831_);
                        leanh::lean_ctor_set(v___x_6848_, 1, v_val_6846_);
                        leanh::lean_ctor_set_uint8(
                            v___x_6848_,
                            (core::mem::size_of::<*mut leanh::LeanObject>() * 2) as u32,
                            v_phase_6833_,
                        );
                        v___x_6849_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6849_, 0, v___x_6848_);
                        leanh::lean_ctor_set(v___x_6849_, 1, v_a_6843_);
                        v___x_6850_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore_spec__0___redArg(v___x_6847_, v___x_6849_, v_kind_6832_, v_a_6834_, v_a_6835_);
                        return v___x_6850_;
                    } else {
                        leanh::lean_dec(v_a_6845_);
                        leanh::lean_dec(v_a_6843_);
                        v___x_6851_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__1,
                        );
                        v___x_6852_ = 0;
                        v___x_6853_ = l_Lean_MessageData_ofConstName(v_declName_6831_, v___x_6852_);
                        v___x_6854_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6854_, 0, v___x_6851_);
                        leanh::lean_ctor_set(v___x_6854_, 1, v___x_6853_);
                        v___x_6855_ = leanh::lean_obj_once(
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3
                            ),
                            core::ptr::addr_of_mut!(
                                l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3_once
                            ),
                            _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___closed__3,
                        );
                        v___x_6856_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_6856_, 0, v___x_6854_);
                        leanh::lean_ctor_set(v___x_6856_, 1, v___x_6855_);
                        v___x_6857_ = l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(v___x_6856_, v_a_6834_, v_a_6835_);
                        return v___x_6857_;
                    }
                } else {
                    leanh::lean_dec(v_declName_6831_);
                    v_a_6858_ = leanh::lean_ctor_get(v___x_6842_, 0);
                    v_isSharedCheck_6869_ = (!leanh::lean_is_exclusive(v___x_6842_)) as u8;
                    if v_isSharedCheck_6869_ == 0 {
                        v___x_6860_ = v___x_6842_;
                        v_isShared_6861_ = v_isSharedCheck_6869_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6858_);
                        leanh::lean_dec(v___x_6842_);
                        v___x_6860_ = leanh::lean_box(0);
                        v_isShared_6861_ = v_isSharedCheck_6869_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6862_ = lean_io_error_to_string(v_a_6858_);
                v___x_6863_ = leanh::lean_alloc_ctor(3, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6863_, 0, v___x_6862_);
                v___x_6864_ = l_Lean_MessageData_ofFormat(v___x_6863_);
                leanh::lean_inc(v_ref_6840_);
                v___x_6865_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6865_, 0, v_ref_6840_);
                leanh::lean_ctor_set(v___x_6865_, 1, v___x_6864_);
                if v_isShared_6861_ == 0 {
                    leanh::lean_ctor_set(v___x_6860_, 0, v___x_6865_);
                    v___x_6867_ = v___x_6860_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6868_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6868_, 0, v___x_6865_);
                    v___x_6867_ = v_reuseFailAlloc_6868_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6867_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore___boxed(
    mut v_declName_6870_: *mut leanh::LeanObject,
    mut v_kind_6871_: *mut leanh::LeanObject,
    mut v_phase_6872_: *mut leanh::LeanObject,
    mut v_a_6873_: *mut leanh::LeanObject,
    mut v_a_6874_: *mut leanh::LeanObject,
    mut v_a_6875_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_kind_boxed_6876_: u8 = 0;
    let mut v_phase_boxed_6877_: u8 = 0;
    let mut v_res_6878_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_kind_boxed_6876_ = (leanh::lean_unbox(v_kind_6871_) as u8);
    v_phase_boxed_6877_ = (leanh::lean_unbox(v_phase_6872_) as u8);
    v_res_6878_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(
        v_declName_6870_,
        v_kind_boxed_6876_,
        v_phase_boxed_6877_,
        v_a_6873_,
        v_a_6874_,
    );
    leanh::lean_dec(v_a_6874_);
    leanh::lean_dec_ref(v_a_6873_);
    return v_res_6878_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(
    mut v_stx_6891_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_6892_: u8 = 0;
    v___x_6892_ = l_Lean_Syntax_isNone(v_stx_6891_);
    if v___x_6892_ == 0 {
        let mut v___x_6893_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_inner_6894_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6896_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_6897_: u8 = 0;
        v___x_6893_ = leanh::lean_unsigned_to_nat(0);
        v_inner_6894_ = l_Lean_Syntax_getArg(v_stx_6891_, v___x_6893_);
        v___x_6895_ = l_Lean_Syntax_getKind(v_inner_6894_);
        v___x_6896_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__2;
        v___x_6897_ = lean_name_eq(v___x_6895_, v___x_6896_);
        if v___x_6897_ == 0 {
            let mut v___x_6898_: *mut leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_6899_: u8 = 0;
            v___x_6898_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___closed__4;
            v___x_6899_ = lean_name_eq(v___x_6895_, v___x_6898_);
            leanh::lean_dec(v___x_6895_);
            if v___x_6899_ == 0 {
                let mut v___x_6900_: u8 = 0;
                v___x_6900_ = 2;
                return v___x_6900_;
            } else {
                let mut v___x_6901_: u8 = 0;
                v___x_6901_ = 1;
                return v___x_6901_;
            }
        } else {
            let mut v___x_6902_: u8 = 0;
            leanh::lean_dec(v___x_6895_);
            v___x_6902_ = 0;
            return v___x_6902_;
        }
    } else {
        let mut v___x_6903_: u8 = 0;
        v___x_6903_ = 2;
        return v___x_6903_;
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase___boxed(
    mut v_stx_6904_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6905_: u8 = 0;
    let mut v_r_6906_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6905_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v_stx_6904_);
    leanh::lean_dec(v_stx_6904_);
    v_r_6906_ = leanh::lean_box((v_res_6905_) as usize);
    return v_r_6906_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6910_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
    v___x_6911_ = leanh::lean_alloc_ctor(0, 6, (0) as u32);
    leanh::lean_ctor_set(v___x_6911_, 0, v___x_6910_);
    leanh::lean_ctor_set(v___x_6911_, 1, v___x_6910_);
    leanh::lean_ctor_set(v___x_6911_, 2, v___x_6910_);
    leanh::lean_ctor_set(v___x_6911_, 3, v___x_6910_);
    leanh::lean_ctor_set(v___x_6911_, 4, v___x_6910_);
    leanh::lean_ctor_set(v___x_6911_, 5, v___x_6910_);
    return v___x_6911_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_6912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6914_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6912_ = leanh::lean_unsigned_to_nat(32);
    v___x_6913_ = lean_mk_empty_array_with_capacity(v___x_6912_);
    v___x_6914_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_6914_, 0, v___x_6913_);
    return v___x_6914_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_6915_: usize = 0;
    let mut v___x_6916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6920_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6915_ = 5usize;
    v___x_6916_ = leanh::lean_unsigned_to_nat(0);
    v___x_6917_ = leanh::lean_unsigned_to_nat(32);
    v___x_6918_ = lean_mk_empty_array_with_capacity(v___x_6917_);
    v___x_6919_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3_once),
        _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__3,
    );
    v___x_6920_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_6920_, 0, v___x_6919_);
    leanh::lean_ctor_set(v___x_6920_, 1, v___x_6918_);
    leanh::lean_ctor_set(v___x_6920_, 2, v___x_6916_);
    leanh::lean_ctor_set(v___x_6920_, 3, v___x_6916_);
    leanh::lean_ctor_set_usize(v___x_6920_, 4, v___x_6915_);
    return v___x_6920_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_6921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6922_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6921_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__1);
    v___x_6922_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_6922_, 0, v___x_6921_);
    leanh::lean_ctor_set(v___x_6922_, 1, v___x_6921_);
    leanh::lean_ctor_set(v___x_6922_, 2, v___x_6921_);
    leanh::lean_ctor_set(v___x_6922_, 3, v___x_6921_);
    leanh::lean_ctor_set(v___x_6922_, 4, v___x_6921_);
    return v___x_6922_;
}
pub unsafe fn _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6()
-> *mut leanh::LeanObject {
    let mut v___x_6923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6928_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6923_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5_once),
        _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__5,
    );
    v___x_6924_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4_once),
        _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__4,
    );
    v___x_6925_ = leanh::lean_box(1);
    v___x_6926_ = leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2),
        core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2_once),
        _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__2,
    );
    v___x_6927_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2), core::ptr::addr_of_mut!(l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2_once), _init_l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0_spec__0___closed__2);
    v___x_6928_ = leanh::lean_alloc_ctor(0, 5, (0) as u32);
    leanh::lean_ctor_set(v___x_6928_, 0, v___x_6927_);
    leanh::lean_ctor_set(v___x_6928_, 1, v___x_6926_);
    leanh::lean_ctor_set(v___x_6928_, 2, v___x_6925_);
    leanh::lean_ctor_set(v___x_6928_, 3, v___x_6924_);
    leanh::lean_ctor_set(v___x_6928_, 4, v___x_6923_);
    return v___x_6928_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(
    mut v_declName_6929_: *mut leanh::LeanObject,
    mut v_stx_6930_: *mut leanh::LeanObject,
    mut v_attrKind_6931_: u8,
    mut v_a_6932_: *mut leanh::LeanObject,
    mut v_a_6933_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6941_: u8 = 0;
    let mut v___x_6942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6945_: u8 = 0;
    let mut v___x_6946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6947_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6951_: u8 = 0;
    let mut v_unused_6952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6935_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__1;
                leanh::lean_inc(v_declName_6929_);
                v___x_6936_ = l_Lean_ensureAttrDeclIsMeta(
                    v___x_6935_,
                    v_declName_6929_,
                    v_attrKind_6931_,
                    v_a_6932_,
                    v_a_6933_,
                );
                if leanh::lean_obj_tag(v___x_6936_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6936_, 1);
                    v___x_6937_ = leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once
                        ),
                        _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6,
                    );
                    v___x_6938_ = lean_st_mk_ref(v___x_6937_);
                    v___x_6939_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6940_ = l_Lean_Syntax_getArg(v_stx_6930_, v___x_6939_);
                    v___x_6941_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_6940_);
                    leanh::lean_dec(v___x_6940_);
                    v___x_6942_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttrCore(
                        v_declName_6929_,
                        v_attrKind_6931_,
                        v___x_6941_,
                        v_a_6932_,
                        v_a_6933_,
                    );
                    if leanh::lean_obj_tag(v___x_6942_) == 0 {
                        v_isSharedCheck_6951_ =
                            (!leanh::lean_is_exclusive(v___x_6942_)) as u8;
                        if v_isSharedCheck_6951_ == 0 {
                            v_unused_6952_ = leanh::lean_ctor_get(v___x_6942_, 0);
                            leanh::lean_dec(v_unused_6952_);
                            v___x_6944_ = v___x_6942_;
                            v_isShared_6945_ = v_isSharedCheck_6951_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_dec(v___x_6942_);
                            v___x_6944_ = leanh::lean_box(0);
                            v_isShared_6945_ = v_isSharedCheck_6951_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_6938_);
                        return v___x_6942_;
                    }
                } else {
                    leanh::lean_dec(v_declName_6929_);
                    return v___x_6936_;
                }
            }
            1 => {
                v___x_6946_ = lean_st_ref_get(v___x_6938_);
                leanh::lean_dec(v___x_6938_);
                leanh::lean_dec(v___x_6946_);
                v___x_6947_ = leanh::lean_box(0);
                if v_isShared_6945_ == 0 {
                    leanh::lean_ctor_set(v___x_6944_, 0, v___x_6947_);
                    v___x_6949_ = v___x_6944_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6950_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6950_, 0, v___x_6947_);
                    v___x_6949_ = v_reuseFailAlloc_6950_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6949_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___boxed(
    mut v_declName_6953_: *mut leanh::LeanObject,
    mut v_stx_6954_: *mut leanh::LeanObject,
    mut v_attrKind_6955_: *mut leanh::LeanObject,
    mut v_a_6956_: *mut leanh::LeanObject,
    mut v_a_6957_: *mut leanh::LeanObject,
    mut v_a_6958_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_attrKind_boxed_6959_: u8 = 0;
    let mut v_res_6960_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_attrKind_boxed_6959_ = (leanh::lean_unbox(v_attrKind_6955_) as u8);
    v_res_6960_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr(
        v_declName_6953_,
        v_stx_6954_,
        v_attrKind_boxed_6959_,
        v_a_6956_,
        v_a_6957_,
    );
    leanh::lean_dec(v_a_6957_);
    leanh::lean_dec_ref(v_a_6956_);
    leanh::lean_dec(v_stx_6954_);
    return v_res_6960_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(
    mut v_ref_6963_: *mut leanh::LeanObject,
    mut v_declName_6964_: *mut leanh::LeanObject,
    mut v_phase_6965_: u8,
    mut v_proc_6966_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_keys_6970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6971_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6975_: u8 = 0;
    let mut v___x_6976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6978_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6980_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6982_: u8 = 0;
    let mut v___x_6983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6985_: u8 = 0;
    let mut v___x_6986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6987_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6990_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6991_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6968_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef;
                v___x_6969_ = lean_st_ref_get(v___x_6968_);
                v_keys_6970_ = leanh::lean_ctor_get(v___x_6969_, 0);
                leanh::lean_inc_ref(v_keys_6970_);
                leanh::lean_dec(v___x_6969_);
                v___x_6971_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Tactic_Cbv_getCbvSimprocDeclKeys_x3f_spec__0___redArg(v_keys_6970_, v_declName_6964_);
                leanh::lean_dec_ref(v_keys_6970_);
                if leanh::lean_obj_tag(v___x_6971_) == 1 {
                    v_val_6972_ = leanh::lean_ctor_get(v___x_6971_, 0);
                    v_isSharedCheck_6982_ = (!leanh::lean_is_exclusive(v___x_6971_)) as u8;
                    if v_isSharedCheck_6982_ == 0 {
                        v___x_6974_ = v___x_6971_;
                        v_isShared_6975_ = v_isSharedCheck_6982_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_val_6972_);
                        leanh::lean_dec(v___x_6971_);
                        v___x_6974_ = leanh::lean_box(0);
                        v_isShared_6975_ = v_isSharedCheck_6982_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec(v___x_6971_);
                    leanh::lean_dec_ref(v_proc_6966_);
                    v___x_6983_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__0;
                    v___x_6984_ = l_Lean_privateToUserName(v_declName_6964_);
                    v___x_6985_ = 1;
                    v___x_6986_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(
                        v___x_6984_,
                        v___x_6985_,
                    );
                    v___x_6987_ = lean_string_append(v___x_6983_, v___x_6986_);
                    leanh::lean_dec_ref(v___x_6986_);
                    v___x_6988_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___closed__1;
                    v___x_6989_ = lean_string_append(v___x_6987_, v___x_6988_);
                    v___x_6990_ = lean_mk_io_user_error(v___x_6989_);
                    v___x_6991_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6991_, 0, v___x_6990_);
                    return v___x_6991_;
                }
            }
            1 => {
                v___x_6976_ = lean_st_ref_take(v_ref_6963_);
                v___x_6977_ = l_Lean_Meta_Tactic_Cbv_CbvSimprocs_addCore(
                    v___x_6976_,
                    v_val_6972_,
                    v_declName_6964_,
                    v_phase_6965_,
                    v_proc_6966_,
                );
                v___x_6978_ = lean_st_ref_set(v_ref_6963_, v___x_6977_);
                if v_isShared_6975_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_6974_, 0);
                    leanh::lean_ctor_set(v___x_6974_, 0, v___x_6978_);
                    v___x_6980_ = v___x_6974_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6981_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6981_, 0, v___x_6978_);
                    v___x_6980_ = v_reuseFailAlloc_6981_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6980_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore___boxed(
    mut v_ref_6992_: *mut leanh::LeanObject,
    mut v_declName_6993_: *mut leanh::LeanObject,
    mut v_phase_6994_: *mut leanh::LeanObject,
    mut v_proc_6995_: *mut leanh::LeanObject,
    mut v_a_6996_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_6997_: u8 = 0;
    let mut v_res_6998_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_6997_ = (leanh::lean_unbox(v_phase_6994_) as u8);
    v_res_6998_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(
        v_ref_6992_,
        v_declName_6993_,
        v_phase_boxed_6997_,
        v_proc_6995_,
    );
    leanh::lean_dec(v_ref_6992_);
    return v_res_6998_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(
    mut v_declName_6999_: *mut leanh::LeanObject,
    mut v_phase_7000_: u8,
    mut v_proc_7001_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7003_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7004_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7003_ = l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef;
    v___x_7004_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttrCore(
        v___x_7003_,
        v_declName_6999_,
        v_phase_7000_,
        v_proc_7001_,
    );
    return v___x_7004_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr___boxed(
    mut v_declName_7005_: *mut leanh::LeanObject,
    mut v_phase_7006_: *mut leanh::LeanObject,
    mut v_proc_7007_: *mut leanh::LeanObject,
    mut v_a_7008_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_phase_boxed_7009_: u8 = 0;
    let mut v_res_7010_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_phase_boxed_7009_ = (leanh::lean_unbox(v_phase_7006_) as u8);
    v_res_7010_ = l_Lean_Meta_Tactic_Cbv_addCbvSimprocBuiltinAttr(
        v_declName_7005_,
        v_phase_boxed_7009_,
        v_proc_7007_,
    );
    return v_res_7010_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7020_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7018_ = leanh::lean_box(0);
    v___x_7019_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__1;
    v___x_7020_ = l_Lean_mkConst(v___x_7019_, v___x_7018_);
    return v___x_7020_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(
    mut v_declName_7024_: *mut leanh::LeanObject,
    mut v_stx_7025_: *mut leanh::LeanObject,
    mut v_a_7026_: *mut leanh::LeanObject,
    mut v_a_7027_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_phase_7031_: u8 = 0;
    let mut v___x_7032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7038_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_7049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7053_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7054_: u8 = 0;
    let mut v___x_7055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7057_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7059_: u8 = 0;
    let mut v_a_7060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7063_: u8 = 0;
    let mut v___x_7065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7067_: u8 = 0;
    let mut v___x_7068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7029_ = leanh::lean_unsigned_to_nat(1);
                v___x_7030_ = l_Lean_Syntax_getArg(v_stx_7025_, v___x_7029_);
                v_phase_7031_ = l_Lean_Meta_Tactic_Cbv_parseCbvSimprocPhase(v___x_7030_);
                leanh::lean_dec(v___x_7030_);
                v___x_7032_ = leanh::lean_box(0);
                v___x_7033_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2_once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__2);
                leanh::lean_inc(v_declName_7024_);
                v___x_7034_ = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(v_declName_7024_);
                match v_phase_7031_ {
                    0 => {
                        v___x_7068_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7_once), _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__7);
                        v___y_7036_ = v___x_7068_;
                        state = 1;
                        continue;
                    }
                    1 => {
                        v___x_7069_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10_once), _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__10);
                        v___y_7036_ = v___x_7069_;
                        state = 1;
                        continue;
                    }
                    _ => {
                        v___x_7070_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13), core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13_once), _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase___lam__0___closed__13);
                        v___y_7036_ = v___x_7070_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7037_ = leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6_once
                    ),
                    _init_l_Lean_Meta_Tactic_Cbv_addCbvSimprocAttr___closed__6,
                );
                v___x_7038_ = lean_st_mk_ref(v___x_7037_);
                leanh::lean_inc(v_declName_7024_);
                v___x_7039_ = l_Lean_mkConst(v_declName_7024_, v___x_7032_);
                v___x_7040_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___closed__4;
                v___x_7041_ = l_Lean_Name_append(v_declName_7024_, v___x_7040_);
                v___x_7042_ = l_Lean_Core_mkFreshUserName(v___x_7041_, v_a_7026_, v_a_7027_);
                if leanh::lean_obj_tag(v___x_7042_) == 0 {
                    v_a_7043_ = leanh::lean_ctor_get(v___x_7042_, 0);
                    leanh::lean_inc(v_a_7043_);
                    leanh::lean_dec_ref_known(v___x_7042_, 1);
                    v___x_7044_ = leanh::lean_unsigned_to_nat(3);
                    v___x_7045_ = lean_mk_empty_array_with_capacity(v___x_7044_);
                    v___x_7046_ = lean_array_push(v___x_7045_, v___x_7034_);
                    leanh::lean_inc_ref(v___y_7036_);
                    v___x_7047_ = lean_array_push(v___x_7046_, v___y_7036_);
                    v___x_7048_ = lean_array_push(v___x_7047_, v___x_7039_);
                    v_val_7049_ = l_Lean_mkAppN(v___x_7033_, v___x_7048_);
                    leanh::lean_dec_ref(v___x_7048_);
                    v___x_7050_ =
                        l_Lean_declareBuiltin(v_a_7043_, v_val_7049_, v_a_7026_, v_a_7027_);
                    if leanh::lean_obj_tag(v___x_7050_) == 0 {
                        v_a_7051_ = leanh::lean_ctor_get(v___x_7050_, 0);
                        v_isSharedCheck_7059_ =
                            (!leanh::lean_is_exclusive(v___x_7050_)) as u8;
                        if v_isSharedCheck_7059_ == 0 {
                            v___x_7053_ = v___x_7050_;
                            v_isShared_7054_ = v_isSharedCheck_7059_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7051_);
                            leanh::lean_dec(v___x_7050_);
                            v___x_7053_ = leanh::lean_box(0);
                            v_isShared_7054_ = v_isSharedCheck_7059_;
                            state = 2;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v___x_7038_);
                        return v___x_7050_;
                    }
                } else {
                    leanh::lean_dec_ref(v___x_7039_);
                    leanh::lean_dec(v___x_7038_);
                    leanh::lean_dec_ref(v___x_7034_);
                    v_a_7060_ = leanh::lean_ctor_get(v___x_7042_, 0);
                    v_isSharedCheck_7067_ = (!leanh::lean_is_exclusive(v___x_7042_)) as u8;
                    if v_isSharedCheck_7067_ == 0 {
                        v___x_7062_ = v___x_7042_;
                        v_isShared_7063_ = v_isSharedCheck_7067_;
                        state = 4;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7060_);
                        leanh::lean_dec(v___x_7042_);
                        v___x_7062_ = leanh::lean_box(0);
                        v_isShared_7063_ = v_isSharedCheck_7067_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                v___x_7055_ = lean_st_ref_get(v___x_7038_);
                leanh::lean_dec(v___x_7038_);
                leanh::lean_dec(v___x_7055_);
                if v_isShared_7054_ == 0 {
                    v___x_7057_ = v___x_7053_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7058_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7058_, 0, v_a_7051_);
                    v___x_7057_ = v_reuseFailAlloc_7058_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_7057_;
            }
            4 => {
                if v_isShared_7063_ == 0 {
                    v___x_7065_ = v___x_7062_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7066_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7066_, 0, v_a_7060_);
                    v___x_7065_ = v_reuseFailAlloc_7066_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_7065_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc___boxed(
    mut v_declName_7071_: *mut leanh::LeanObject,
    mut v_stx_7072_: *mut leanh::LeanObject,
    mut v_a_7073_: *mut leanh::LeanObject,
    mut v_a_7074_: *mut leanh::LeanObject,
    mut v_a_7075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7076_ =
        l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(
            v_declName_7071_,
            v_stx_7072_,
            v_a_7073_,
            v_a_7074_,
        );
    leanh::lean_dec(v_a_7074_);
    leanh::lean_dec_ref(v_a_7073_);
    leanh::lean_dec(v_stx_7072_);
    return v_res_7076_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7162_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7163_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7162_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__32_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_;
    v___x_7163_ = l_Lean_registerBuiltinAttribute(v___x_7162_);
    return v___x_7163_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2____boxed(
    mut v_a_7164_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7165_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7165_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
    return v_res_7165_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(
    mut v_declName_7166_: *mut leanh::LeanObject,
    mut v_stx_7167_: *mut leanh::LeanObject,
    mut v_x_7168_: u8,
    mut v___y_7169_: *mut leanh::LeanObject,
    mut v___y_7170_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7172_ =
        l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_addBuiltinCbvSimproc(
            v_declName_7166_,
            v_stx_7167_,
            v___y_7169_,
            v___y_7170_,
        );
    return v___x_7172_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(
    mut v_declName_7173_: *mut leanh::LeanObject,
    mut v_stx_7174_: *mut leanh::LeanObject,
    mut v_x_7175_: *mut leanh::LeanObject,
    mut v___y_7176_: *mut leanh::LeanObject,
    mut v___y_7177_: *mut leanh::LeanObject,
    mut v___y_7178_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_116__boxed_7179_: u8 = 0;
    let mut v_res_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_x_116__boxed_7179_ = (leanh::lean_unbox(v_x_7175_) as u8);
    v_res_7180_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_declName_7173_, v_stx_7174_, v_x_116__boxed_7179_, v___y_7176_, v___y_7177_);
    leanh::lean_dec(v___y_7177_);
    leanh::lean_dec_ref(v___y_7176_);
    leanh::lean_dec(v_stx_7174_);
    return v_res_7180_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7183_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7182_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
    v___x_7183_ = l_Lean_stringToMessageData(v___x_7182_);
    return v___x_7183_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(
    mut v_x_7184_: *mut leanh::LeanObject,
    mut v___y_7185_: *mut leanh::LeanObject,
    mut v___y_7186_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7188_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
    v___x_7189_ =
        l_Lean_throwError___at___00Lean_Meta_Tactic_Cbv_registerCbvSimproc_spec__0___redArg(
            v___x_7188_,
            v___y_7185_,
            v___y_7186_,
        );
    return v___x_7189_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(
    mut v_x_7190_: *mut leanh::LeanObject,
    mut v___y_7191_: *mut leanh::LeanObject,
    mut v___y_7192_: *mut leanh::LeanObject,
    mut v___y_7193_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7194_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___lam__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_(v_x_7190_, v___y_7191_, v___y_7192_);
    leanh::lean_dec(v___y_7192_);
    leanh::lean_dec_ref(v___y_7191_);
    leanh::lean_dec(v_x_7190_);
    return v_res_7194_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7198_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7199_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7197_ = leanh::lean_unsigned_to_nat(3124561870);
    v___x_7198_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__23_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_;
    v___x_7199_ = l_Lean_Name_num___override(v___x_7198_, v___x_7197_);
    return v___x_7199_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7200_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7202_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7200_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__25_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_;
    v___x_7201_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__2_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
    v___x_7202_ = l_Lean_Name_str___override(v___x_7201_, v___x_7200_);
    return v___x_7202_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7204_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7205_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7203_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__27_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_;
    v___x_7204_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__3_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
    v___x_7205_ = l_Lean_Name_str___override(v___x_7204_, v___x_7203_);
    return v___x_7205_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7206_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7207_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7206_ = leanh::lean_unsigned_to_nat(2);
    v___x_7207_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__4_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
    v___x_7208_ = l_Lean_Name_num___override(v___x_7207_, v___x_7206_);
    return v___x_7208_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7213_: u8 = 0;
    let mut v___x_7214_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7215_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7216_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7217_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7213_ = 1;
    v___x_7214_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__8_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
    v___x_7215_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__7_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
    v___x_7216_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__5_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
    v___x_7217_ = leanh::lean_alloc_ctor(0, 3, (1) as u32);
    leanh::lean_ctor_set(v___x_7217_, 0, v___x_7216_);
    leanh::lean_ctor_set(v___x_7217_, 1, v___x_7215_);
    leanh::lean_ctor_set(v___x_7217_, 2, v___x_7214_);
    leanh::lean_ctor_set_uint8(
        v___x_7217_,
        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
        v___x_7213_,
    );
    return v___x_7217_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___f_7218_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7219_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7220_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7221_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___f_7218_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__1_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
    v___f_7219_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__0_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_;
    v___x_7220_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__9_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
    v___x_7221_ = leanh::lean_alloc_ctor(0, 3, (0) as u32);
    leanh::lean_ctor_set(v___x_7221_, 0, v___x_7220_);
    leanh::lean_ctor_set(v___x_7221_, 1, v___f_7219_);
    leanh::lean_ctor_set(v___x_7221_, 2, v___f_7218_);
    return v___x_7221_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_()
-> *mut leanh::LeanObject {
    let mut v___x_7223_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7224_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7223_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2__once), _init_l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn___closed__10_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_);
    v___x_7224_ = l_Lean_registerBuiltinAttribute(v___x_7223_);
    return v___x_7224_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2____boxed(
    mut v_a_7225_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7226_ = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
    return v_res_7226_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(
    mut v_a_7227_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7230_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ext_7232_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toEnvExtension_7233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_asyncMode_7234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7237_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7229_ = lean_st_ref_get(v_a_7227_);
    v_env_7230_ = leanh::lean_ctor_get(v___x_7229_, 0);
    leanh::lean_inc_ref(v_env_7230_);
    leanh::lean_dec(v___x_7229_);
    v___x_7231_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension;
    v_ext_7232_ = leanh::lean_ctor_get(v___x_7231_, 1);
    v_toEnvExtension_7233_ = leanh::lean_ctor_get(v_ext_7232_, 0);
    v_asyncMode_7234_ = leanh::lean_ctor_get(v_toEnvExtension_7233_, 2);
    v___x_7235_ = l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default;
    v___x_7236_ = l_Lean_ScopedEnvExtension_getState___redArg(
        v___x_7235_,
        v___x_7231_,
        v_env_7230_,
        v_asyncMode_7234_,
    );
    v___x_7237_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7237_, 0, v___x_7236_);
    return v___x_7237_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg___boxed(
    mut v_a_7238_: *mut leanh::LeanObject,
    mut v_a_7239_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7240_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7240_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_7238_);
    leanh::lean_dec(v_a_7238_);
    return v_res_7240_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(
    mut v_a_7241_: *mut leanh::LeanObject,
    mut v_a_7242_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7244_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___redArg(v_a_7242_);
    return v___x_7244_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_getCbvSimprocs___boxed(
    mut v_a_7245_: *mut leanh::LeanObject,
    mut v_a_7246_: *mut leanh::LeanObject,
    mut v_a_7247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7248_ = l_Lean_Meta_Tactic_Cbv_getCbvSimprocs(v_a_7245_, v_a_7246_);
    leanh::lean_dec(v_a_7246_);
    leanh::lean_dec_ref(v_a_7245_);
    return v_res_7248_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_7249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7250_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7251_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7249_ = leanh::lean_unsigned_to_nat(32);
    v___x_7250_ = lean_mk_empty_array_with_capacity(v___x_7249_);
    v___x_7251_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7251_, 0, v___x_7250_);
    return v___x_7251_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7252_: usize = 0;
    let mut v___x_7253_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7255_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7257_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7252_ = 5usize;
    v___x_7253_ = leanh::lean_unsigned_to_nat(0);
    v___x_7254_ = leanh::lean_unsigned_to_nat(32);
    v___x_7255_ = lean_mk_empty_array_with_capacity(v___x_7254_);
    v___x_7256_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__0);
    v___x_7257_ = leanh::lean_alloc_ctor(0, 4, (core::mem::size_of::<usize>() * 1) as u32);
    leanh::lean_ctor_set(v___x_7257_, 0, v___x_7256_);
    leanh::lean_ctor_set(v___x_7257_, 1, v___x_7255_);
    leanh::lean_ctor_set(v___x_7257_, 2, v___x_7253_);
    leanh::lean_ctor_set(v___x_7257_, 3, v___x_7253_);
    leanh::lean_ctor_set_usize(v___x_7257_, 4, v___x_7252_);
    return v___x_7257_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(
    mut v___y_7258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7261_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_7262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7269_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7271_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7275_: u8 = 0;
    let mut v_tid_7276_: u64 = 0;
    let mut v___x_7278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7279_: u8 = 0;
    let mut v___x_7280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7289_: u8 = 0;
    let mut v_unused_7290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7291_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7260_ = lean_st_ref_get(v___y_7258_);
                v_traceState_7261_ = leanh::lean_ctor_get(v___x_7260_, 4);
                leanh::lean_inc_ref(v_traceState_7261_);
                leanh::lean_dec(v___x_7260_);
                v_traces_7262_ = leanh::lean_ctor_get(v_traceState_7261_, 0);
                leanh::lean_inc_ref(v_traces_7262_);
                leanh::lean_dec_ref(v_traceState_7261_);
                v___x_7263_ = lean_st_ref_take(v___y_7258_);
                v_traceState_7264_ = leanh::lean_ctor_get(v___x_7263_, 4);
                v_env_7265_ = leanh::lean_ctor_get(v___x_7263_, 0);
                v_nextMacroScope_7266_ = leanh::lean_ctor_get(v___x_7263_, 1);
                v_ngen_7267_ = leanh::lean_ctor_get(v___x_7263_, 2);
                v_auxDeclNGen_7268_ = leanh::lean_ctor_get(v___x_7263_, 3);
                v_cache_7269_ = leanh::lean_ctor_get(v___x_7263_, 5);
                v_messages_7270_ = leanh::lean_ctor_get(v___x_7263_, 6);
                v_infoState_7271_ = leanh::lean_ctor_get(v___x_7263_, 7);
                v_snapshotTasks_7272_ = leanh::lean_ctor_get(v___x_7263_, 8);
                v_isSharedCheck_7291_ = (!leanh::lean_is_exclusive(v___x_7263_)) as u8;
                if v_isSharedCheck_7291_ == 0 {
                    v___x_7274_ = v___x_7263_;
                    v_isShared_7275_ = v_isSharedCheck_7291_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_7272_);
                    leanh::lean_inc(v_infoState_7271_);
                    leanh::lean_inc(v_messages_7270_);
                    leanh::lean_inc(v_cache_7269_);
                    leanh::lean_inc(v_traceState_7264_);
                    leanh::lean_inc(v_auxDeclNGen_7268_);
                    leanh::lean_inc(v_ngen_7267_);
                    leanh::lean_inc(v_nextMacroScope_7266_);
                    leanh::lean_inc(v_env_7265_);
                    leanh::lean_dec(v___x_7263_);
                    v___x_7274_ = leanh::lean_box(0);
                    v_isShared_7275_ = v_isSharedCheck_7291_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_tid_7276_ = leanh::lean_ctor_get_uint64(
                    v_traceState_7264_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_7289_ =
                    (!leanh::lean_is_exclusive(v_traceState_7264_)) as u8;
                if v_isSharedCheck_7289_ == 0 {
                    v_unused_7290_ = leanh::lean_ctor_get(v_traceState_7264_, 0);
                    leanh::lean_dec(v_unused_7290_);
                    v___x_7278_ = v_traceState_7264_;
                    v_isShared_7279_ = v_isSharedCheck_7289_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_7264_);
                    v___x_7278_ = leanh::lean_box(0);
                    v_isShared_7279_ = v_isSharedCheck_7289_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_7280_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___closed__1);
                if v_isShared_7279_ == 0 {
                    leanh::lean_ctor_set(v___x_7278_, 0, v___x_7280_);
                    v___x_7282_ = v___x_7278_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_7288_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7288_, 0, v___x_7280_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_7288_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_7276_,
                    );
                    v___x_7282_ = v_reuseFailAlloc_7288_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_7275_ == 0 {
                    leanh::lean_ctor_set(v___x_7274_, 4, v___x_7282_);
                    v___x_7284_ = v___x_7274_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7287_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 0, v_env_7265_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 1, v_nextMacroScope_7266_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 2, v_ngen_7267_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 3, v_auxDeclNGen_7268_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 4, v___x_7282_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 5, v_cache_7269_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 6, v_messages_7270_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 7, v_infoState_7271_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7287_, 8, v_snapshotTasks_7272_);
                    v___x_7284_ = v_reuseFailAlloc_7287_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_7285_ = lean_st_ref_set(v___y_7258_, v___x_7284_);
                v___x_7286_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7286_, 0, v_traces_7262_);
                return v___x_7286_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg___boxed(
    mut v___y_7292_: *mut leanh::LeanObject,
    mut v___y_7293_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7294_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7294_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_7292_);
    leanh::lean_dec(v___y_7292_);
    return v_res_7294_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(
    mut v___y_7295_: *mut leanh::LeanObject,
    mut v___y_7296_: *mut leanh::LeanObject,
    mut v___y_7297_: *mut leanh::LeanObject,
    mut v___y_7298_: *mut leanh::LeanObject,
    mut v___y_7299_: *mut leanh::LeanObject,
    mut v___y_7300_: *mut leanh::LeanObject,
    mut v___y_7301_: *mut leanh::LeanObject,
    mut v___y_7302_: *mut leanh::LeanObject,
    mut v___y_7303_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7305_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7305_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_7303_);
    return v___x_7305_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___boxed(
    mut v___y_7306_: *mut leanh::LeanObject,
    mut v___y_7307_: *mut leanh::LeanObject,
    mut v___y_7308_: *mut leanh::LeanObject,
    mut v___y_7309_: *mut leanh::LeanObject,
    mut v___y_7310_: *mut leanh::LeanObject,
    mut v___y_7311_: *mut leanh::LeanObject,
    mut v___y_7312_: *mut leanh::LeanObject,
    mut v___y_7313_: *mut leanh::LeanObject,
    mut v___y_7314_: *mut leanh::LeanObject,
    mut v___y_7315_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7316_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7316_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0(v___y_7306_, v___y_7307_, v___y_7308_, v___y_7309_, v___y_7310_, v___y_7311_, v___y_7312_, v___y_7313_, v___y_7314_);
    leanh::lean_dec(v___y_7314_);
    leanh::lean_dec_ref(v___y_7313_);
    leanh::lean_dec(v___y_7312_);
    leanh::lean_dec_ref(v___y_7311_);
    leanh::lean_dec(v___y_7310_);
    leanh::lean_dec_ref(v___y_7309_);
    leanh::lean_dec(v___y_7308_);
    leanh::lean_dec_ref(v___y_7307_);
    leanh::lean_dec(v___y_7306_);
    return v_res_7316_;
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(
    mut v_opts_7317_: *mut leanh::LeanObject,
    mut v_opt_7318_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_name_7319_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_7320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_7321_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7322_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_7319_ = leanh::lean_ctor_get(v_opt_7318_, 0);
    v_defValue_7320_ = leanh::lean_ctor_get(v_opt_7318_, 1);
    v_map_7321_ = leanh::lean_ctor_get(v_opts_7317_, 0);
    v___x_7322_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_7321_,
            v_name_7319_,
        );
    if leanh::lean_obj_tag(v___x_7322_) == 0 {
        let mut v___x_7323_: u8 = 0;
        v___x_7323_ = (leanh::lean_unbox(v_defValue_7320_) as u8);
        return v___x_7323_;
    } else {
        let mut v_val_7324_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_7324_ = leanh::lean_ctor_get(v___x_7322_, 0);
        leanh::lean_inc(v_val_7324_);
        leanh::lean_dec_ref_known(v___x_7322_, 1);
        if leanh::lean_obj_tag(v_val_7324_) == 1 {
            let mut v_v_7325_: u8 = 0;
            v_v_7325_ = leanh::lean_ctor_get_uint8(v_val_7324_, 0 as u32);
            leanh::lean_dec_ref_known(v_val_7324_, 0);
            return v_v_7325_;
        } else {
            let mut v___x_7326_: u8 = 0;
            leanh::lean_dec(v_val_7324_);
            v___x_7326_ = (leanh::lean_unbox(v_defValue_7320_) as u8);
            return v___x_7326_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1___boxed(
    mut v_opts_7327_: *mut leanh::LeanObject,
    mut v_opt_7328_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7329_: u8 = 0;
    let mut v_r_7330_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7329_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(
        v_opts_7327_,
        v_opt_7328_,
    );
    leanh::lean_dec_ref(v_opt_7328_);
    leanh::lean_dec_ref(v_opts_7327_);
    v_r_7330_ = leanh::lean_box((v_res_7329_) as usize);
    return v_r_7330_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(
    mut v___x_7331_: u8,
    mut v_e_7332_: *mut leanh::LeanObject,
    mut v_snd_7333_: *mut leanh::LeanObject,
    mut v_proc_7334_: *mut leanh::LeanObject,
    mut v___y_7335_: *mut leanh::LeanObject,
    mut v___y_7336_: *mut leanh::LeanObject,
    mut v___y_7337_: *mut leanh::LeanObject,
    mut v___y_7338_: *mut leanh::LeanObject,
    mut v___y_7339_: *mut leanh::LeanObject,
    mut v___y_7340_: *mut leanh::LeanObject,
    mut v___y_7341_: *mut leanh::LeanObject,
    mut v___y_7342_: *mut leanh::LeanObject,
    mut v___y_7343_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if v___x_7331_ == 0 {
        let mut v___x_7345_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_7345_ = l_Lean_Meta_Sym_Simp_simpOverApplied(
            v_e_7332_,
            v_snd_7333_,
            v_proc_7334_,
            v___y_7335_,
            v___y_7336_,
            v___y_7337_,
            v___y_7338_,
            v___y_7339_,
            v___y_7340_,
            v___y_7341_,
            v___y_7342_,
            v___y_7343_,
        );
        return v___x_7345_;
    } else {
        let mut v___x_7346_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_inc(v___y_7343_);
        leanh::lean_inc_ref(v___y_7342_);
        leanh::lean_inc(v___y_7341_);
        leanh::lean_inc_ref(v___y_7340_);
        leanh::lean_inc(v___y_7339_);
        leanh::lean_inc_ref(v___y_7338_);
        leanh::lean_inc(v___y_7337_);
        leanh::lean_inc_ref(v___y_7336_);
        leanh::lean_inc(v___y_7335_);
        v___x_7346_ = leanh::lean_apply_11(
            v_proc_7334_,
            v_e_7332_,
            v___y_7335_,
            v___y_7336_,
            v___y_7337_,
            v___y_7338_,
            v___y_7339_,
            v___y_7340_,
            v___y_7341_,
            v___y_7342_,
            v___y_7343_,
            leanh::lean_box(0),
        );
        return v___x_7346_;
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0___boxed(
    mut v___x_7347_: *mut leanh::LeanObject,
    mut v_e_7348_: *mut leanh::LeanObject,
    mut v_snd_7349_: *mut leanh::LeanObject,
    mut v_proc_7350_: *mut leanh::LeanObject,
    mut v___y_7351_: *mut leanh::LeanObject,
    mut v___y_7352_: *mut leanh::LeanObject,
    mut v___y_7353_: *mut leanh::LeanObject,
    mut v___y_7354_: *mut leanh::LeanObject,
    mut v___y_7355_: *mut leanh::LeanObject,
    mut v___y_7356_: *mut leanh::LeanObject,
    mut v___y_7357_: *mut leanh::LeanObject,
    mut v___y_7358_: *mut leanh::LeanObject,
    mut v___y_7359_: *mut leanh::LeanObject,
    mut v___y_7360_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_49151__boxed_7361_: u8 = 0;
    let mut v_res_7362_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_49151__boxed_7361_ = (leanh::lean_unbox(v___x_7347_) as u8);
    v_res_7362_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_49151__boxed_7361_, v_e_7348_, v_snd_7349_, v_proc_7350_, v___y_7351_, v___y_7352_, v___y_7353_, v___y_7354_, v___y_7355_, v___y_7356_, v___y_7357_, v___y_7358_, v___y_7359_);
    leanh::lean_dec(v___y_7359_);
    leanh::lean_dec_ref(v___y_7358_);
    leanh::lean_dec(v___y_7357_);
    leanh::lean_dec_ref(v___y_7356_);
    leanh::lean_dec(v___y_7355_);
    leanh::lean_dec_ref(v___y_7354_);
    leanh::lean_dec(v___y_7353_);
    leanh::lean_dec_ref(v___y_7352_);
    leanh::lean_dec(v___y_7351_);
    leanh::lean_dec(v_snd_7349_);
    return v_res_7362_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5(
    mut v_msgData_7363_: *mut leanh::LeanObject,
    mut v___y_7364_: *mut leanh::LeanObject,
    mut v___y_7365_: *mut leanh::LeanObject,
    mut v___y_7366_: *mut leanh::LeanObject,
    mut v___y_7367_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7369_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7370_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_7372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_7373_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7375_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7377_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7369_ = lean_st_ref_get(v___y_7367_);
    v_env_7370_ = leanh::lean_ctor_get(v___x_7369_, 0);
    leanh::lean_inc_ref(v_env_7370_);
    leanh::lean_dec(v___x_7369_);
    v___x_7371_ = lean_st_ref_get(v___y_7365_);
    v_mctx_7372_ = leanh::lean_ctor_get(v___x_7371_, 0);
    leanh::lean_inc_ref(v_mctx_7372_);
    leanh::lean_dec(v___x_7371_);
    v_lctx_7373_ = leanh::lean_ctor_get(v___y_7364_, 2);
    v_options_7374_ = leanh::lean_ctor_get(v___y_7366_, 2);
    leanh::lean_inc_ref(v_options_7374_);
    leanh::lean_inc_ref(v_lctx_7373_);
    v___x_7375_ = leanh::lean_alloc_ctor(0, 4, (0) as u32);
    leanh::lean_ctor_set(v___x_7375_, 0, v_env_7370_);
    leanh::lean_ctor_set(v___x_7375_, 1, v_mctx_7372_);
    leanh::lean_ctor_set(v___x_7375_, 2, v_lctx_7373_);
    leanh::lean_ctor_set(v___x_7375_, 3, v_options_7374_);
    v___x_7376_ = leanh::lean_alloc_ctor(3, 2, (0) as u32);
    leanh::lean_ctor_set(v___x_7376_, 0, v___x_7375_);
    leanh::lean_ctor_set(v___x_7376_, 1, v_msgData_7363_);
    v___x_7377_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
    leanh::lean_ctor_set(v___x_7377_, 0, v___x_7376_);
    return v___x_7377_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5___boxed(
    mut v_msgData_7378_: *mut leanh::LeanObject,
    mut v___y_7379_: *mut leanh::LeanObject,
    mut v___y_7380_: *mut leanh::LeanObject,
    mut v___y_7381_: *mut leanh::LeanObject,
    mut v___y_7382_: *mut leanh::LeanObject,
    mut v___y_7383_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7384_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7384_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5(v_msgData_7378_, v___y_7379_, v___y_7380_, v___y_7381_, v___y_7382_);
    leanh::lean_dec(v___y_7382_);
    leanh::lean_dec_ref(v___y_7381_);
    leanh::lean_dec(v___y_7380_);
    leanh::lean_dec_ref(v___y_7379_);
    return v_res_7384_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4(
    mut v_sz_7385_: usize,
    mut v_i_7386_: usize,
    mut v_bs_7387_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7388_: u8 = 0;
    let mut v_v_7389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_7390_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7391_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_bs_x27_7392_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7393_: usize = 0;
    let mut v___x_7394_: usize = 0;
    let mut v___x_7395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7388_ = lean_usize_dec_lt(v_i_7386_, v_sz_7385_);
                if v___x_7388_ == 0 {
                    return v_bs_7387_;
                } else {
                    v_v_7389_ = lean_array_uget_borrowed(v_bs_7387_, v_i_7386_);
                    v_msg_7390_ = leanh::lean_ctor_get(v_v_7389_, 1);
                    leanh::lean_inc_ref(v_msg_7390_);
                    v___x_7391_ = leanh::lean_unsigned_to_nat(0);
                    v_bs_x27_7392_ = lean_array_uset(v_bs_7387_, v_i_7386_, v___x_7391_);
                    v___x_7393_ = 1usize;
                    v___x_7394_ = lean_usize_add(v_i_7386_, v___x_7393_);
                    v___x_7395_ = lean_array_uset(v_bs_x27_7392_, v_i_7386_, v_msg_7390_);
                    v_i_7386_ = v___x_7394_;
                    v_bs_7387_ = v___x_7395_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4___boxed(
    mut v_sz_7397_: *mut leanh::LeanObject,
    mut v_i_7398_: *mut leanh::LeanObject,
    mut v_bs_7399_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7400_: usize = 0;
    let mut v_i_boxed_7401_: usize = 0;
    let mut v_res_7402_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7400_ = leanh::lean_unbox_usize(v_sz_7397_);
    leanh::lean_dec(v_sz_7397_);
    v_i_boxed_7401_ = leanh::lean_unbox_usize(v_i_7398_);
    leanh::lean_dec(v_i_7398_);
    v_res_7402_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4(v_sz_boxed_7400_, v_i_boxed_7401_, v_bs_7399_);
    return v_res_7402_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(
    mut v_oldTraces_7403_: *mut leanh::LeanObject,
    mut v_data_7404_: *mut leanh::LeanObject,
    mut v_ref_7405_: *mut leanh::LeanObject,
    mut v_msg_7406_: *mut leanh::LeanObject,
    mut v___y_7407_: *mut leanh::LeanObject,
    mut v___y_7408_: *mut leanh::LeanObject,
    mut v___y_7409_: *mut leanh::LeanObject,
    mut v___y_7410_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fileName_7412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fileMap_7413_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currRecDepth_7415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxRecDepth_7416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currNamespace_7418_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_openDecls_7419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_initHeartbeats_7420_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_maxHeartbeats_7421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_quotContext_7422_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_currMacroScope_7423_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diag_7424_: u8 = 0;
    let mut v_cancelTk_x3f_7425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_suppressElabErrors_7426_: u8 = 0;
    let mut v_inheritedTraceOptions_7427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traces_7430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_7434_: usize = 0;
    let mut v___x_7435_: usize = 0;
    let mut v___x_7436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_msg_7437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7442_: u8 = 0;
    let mut v___x_7443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7444_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7448_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7450_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7451_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7454_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7455_: u8 = 0;
    let mut v_tid_7456_: u64 = 0;
    let mut v___x_7458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7459_: u8 = 0;
    let mut v___x_7460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7470_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7473_: u8 = 0;
    let mut v_unused_7474_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7475_: u8 = 0;
    let mut v_isSharedCheck_7476_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fileName_7412_ = leanh::lean_ctor_get(v___y_7409_, 0);
                v_fileMap_7413_ = leanh::lean_ctor_get(v___y_7409_, 1);
                v_options_7414_ = leanh::lean_ctor_get(v___y_7409_, 2);
                v_currRecDepth_7415_ = leanh::lean_ctor_get(v___y_7409_, 3);
                v_maxRecDepth_7416_ = leanh::lean_ctor_get(v___y_7409_, 4);
                v_ref_7417_ = leanh::lean_ctor_get(v___y_7409_, 5);
                v_currNamespace_7418_ = leanh::lean_ctor_get(v___y_7409_, 6);
                v_openDecls_7419_ = leanh::lean_ctor_get(v___y_7409_, 7);
                v_initHeartbeats_7420_ = leanh::lean_ctor_get(v___y_7409_, 8);
                v_maxHeartbeats_7421_ = leanh::lean_ctor_get(v___y_7409_, 9);
                v_quotContext_7422_ = leanh::lean_ctor_get(v___y_7409_, 10);
                v_currMacroScope_7423_ = leanh::lean_ctor_get(v___y_7409_, 11);
                v_diag_7424_ = leanh::lean_ctor_get_uint8(
                    v___y_7409_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                );
                v_cancelTk_x3f_7425_ = leanh::lean_ctor_get(v___y_7409_, 12);
                v_suppressElabErrors_7426_ = leanh::lean_ctor_get_uint8(
                    v___y_7409_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                );
                v_inheritedTraceOptions_7427_ = leanh::lean_ctor_get(v___y_7409_, 13);
                v___x_7428_ = lean_st_ref_get(v___y_7410_);
                v_traceState_7429_ = leanh::lean_ctor_get(v___x_7428_, 4);
                leanh::lean_inc_ref(v_traceState_7429_);
                leanh::lean_dec(v___x_7428_);
                v_traces_7430_ = leanh::lean_ctor_get(v_traceState_7429_, 0);
                leanh::lean_inc_ref(v_traces_7430_);
                leanh::lean_dec_ref(v_traceState_7429_);
                v_ref_7431_ = l_Lean_replaceRef(v_ref_7405_, v_ref_7417_);
                leanh::lean_inc_ref(v_inheritedTraceOptions_7427_);
                leanh::lean_inc(v_cancelTk_x3f_7425_);
                leanh::lean_inc(v_currMacroScope_7423_);
                leanh::lean_inc(v_quotContext_7422_);
                leanh::lean_inc(v_maxHeartbeats_7421_);
                leanh::lean_inc(v_initHeartbeats_7420_);
                leanh::lean_inc(v_openDecls_7419_);
                leanh::lean_inc(v_currNamespace_7418_);
                leanh::lean_inc(v_maxRecDepth_7416_);
                leanh::lean_inc(v_currRecDepth_7415_);
                leanh::lean_inc_ref(v_options_7414_);
                leanh::lean_inc_ref(v_fileMap_7413_);
                leanh::lean_inc_ref(v_fileName_7412_);
                v___x_7432_ = leanh::lean_alloc_ctor(0, 14, (2) as u32);
                leanh::lean_ctor_set(v___x_7432_, 0, v_fileName_7412_);
                leanh::lean_ctor_set(v___x_7432_, 1, v_fileMap_7413_);
                leanh::lean_ctor_set(v___x_7432_, 2, v_options_7414_);
                leanh::lean_ctor_set(v___x_7432_, 3, v_currRecDepth_7415_);
                leanh::lean_ctor_set(v___x_7432_, 4, v_maxRecDepth_7416_);
                leanh::lean_ctor_set(v___x_7432_, 5, v_ref_7431_);
                leanh::lean_ctor_set(v___x_7432_, 6, v_currNamespace_7418_);
                leanh::lean_ctor_set(v___x_7432_, 7, v_openDecls_7419_);
                leanh::lean_ctor_set(v___x_7432_, 8, v_initHeartbeats_7420_);
                leanh::lean_ctor_set(v___x_7432_, 9, v_maxHeartbeats_7421_);
                leanh::lean_ctor_set(v___x_7432_, 10, v_quotContext_7422_);
                leanh::lean_ctor_set(v___x_7432_, 11, v_currMacroScope_7423_);
                leanh::lean_ctor_set(v___x_7432_, 12, v_cancelTk_x3f_7425_);
                leanh::lean_ctor_set(v___x_7432_, 13, v_inheritedTraceOptions_7427_);
                leanh::lean_ctor_set_uint8(
                    v___x_7432_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14) as u32,
                    v_diag_7424_,
                );
                leanh::lean_ctor_set_uint8(
                    v___x_7432_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 14 + 1) as u32,
                    v_suppressElabErrors_7426_,
                );
                v___x_7433_ = l_Lean_PersistentArray_toArray___redArg(v_traces_7430_);
                leanh::lean_dec_ref(v_traces_7430_);
                v_sz_7434_ = lean_array_size(v___x_7433_);
                v___x_7435_ = 0usize;
                v___x_7436_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__4(v_sz_7434_, v___x_7435_, v___x_7433_);
                v_msg_7437_ = leanh::lean_alloc_ctor(9, 3, (0) as u32);
                leanh::lean_ctor_set(v_msg_7437_, 0, v_data_7404_);
                leanh::lean_ctor_set(v_msg_7437_, 1, v_msg_7406_);
                leanh::lean_ctor_set(v_msg_7437_, 2, v___x_7436_);
                v___x_7438_ = l_Lean_addMessageContextFull___at___00__private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3_spec__5(v_msg_7437_, v___y_7407_, v___y_7408_, v___x_7432_, v___y_7410_);
                leanh::lean_dec_ref_known(v___x_7432_, 14);
                v_a_7439_ = leanh::lean_ctor_get(v___x_7438_, 0);
                v_isSharedCheck_7476_ = (!leanh::lean_is_exclusive(v___x_7438_)) as u8;
                if v_isSharedCheck_7476_ == 0 {
                    v___x_7441_ = v___x_7438_;
                    v_isShared_7442_ = v_isSharedCheck_7476_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_a_7439_);
                    leanh::lean_dec(v___x_7438_);
                    v___x_7441_ = leanh::lean_box(0);
                    v_isShared_7442_ = v_isSharedCheck_7476_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_7443_ = lean_st_ref_take(v___y_7410_);
                v_traceState_7444_ = leanh::lean_ctor_get(v___x_7443_, 4);
                v_env_7445_ = leanh::lean_ctor_get(v___x_7443_, 0);
                v_nextMacroScope_7446_ = leanh::lean_ctor_get(v___x_7443_, 1);
                v_ngen_7447_ = leanh::lean_ctor_get(v___x_7443_, 2);
                v_auxDeclNGen_7448_ = leanh::lean_ctor_get(v___x_7443_, 3);
                v_cache_7449_ = leanh::lean_ctor_get(v___x_7443_, 5);
                v_messages_7450_ = leanh::lean_ctor_get(v___x_7443_, 6);
                v_infoState_7451_ = leanh::lean_ctor_get(v___x_7443_, 7);
                v_snapshotTasks_7452_ = leanh::lean_ctor_get(v___x_7443_, 8);
                v_isSharedCheck_7475_ = (!leanh::lean_is_exclusive(v___x_7443_)) as u8;
                if v_isSharedCheck_7475_ == 0 {
                    v___x_7454_ = v___x_7443_;
                    v_isShared_7455_ = v_isSharedCheck_7475_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_inc(v_snapshotTasks_7452_);
                    leanh::lean_inc(v_infoState_7451_);
                    leanh::lean_inc(v_messages_7450_);
                    leanh::lean_inc(v_cache_7449_);
                    leanh::lean_inc(v_traceState_7444_);
                    leanh::lean_inc(v_auxDeclNGen_7448_);
                    leanh::lean_inc(v_ngen_7447_);
                    leanh::lean_inc(v_nextMacroScope_7446_);
                    leanh::lean_inc(v_env_7445_);
                    leanh::lean_dec(v___x_7443_);
                    v___x_7454_ = leanh::lean_box(0);
                    v_isShared_7455_ = v_isSharedCheck_7475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v_tid_7456_ = leanh::lean_ctor_get_uint64(
                    v_traceState_7444_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_isSharedCheck_7473_ =
                    (!leanh::lean_is_exclusive(v_traceState_7444_)) as u8;
                if v_isSharedCheck_7473_ == 0 {
                    v_unused_7474_ = leanh::lean_ctor_get(v_traceState_7444_, 0);
                    leanh::lean_dec(v_unused_7474_);
                    v___x_7458_ = v_traceState_7444_;
                    v_isShared_7459_ = v_isSharedCheck_7473_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_dec(v_traceState_7444_);
                    v___x_7458_ = leanh::lean_box(0);
                    v_isShared_7459_ = v_isSharedCheck_7473_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_7460_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7460_, 0, v_ref_7405_);
                leanh::lean_ctor_set(v___x_7460_, 1, v_a_7439_);
                v___x_7461_ = l_Lean_PersistentArray_push___redArg(v_oldTraces_7403_, v___x_7460_);
                if v_isShared_7459_ == 0 {
                    leanh::lean_ctor_set(v___x_7458_, 0, v___x_7461_);
                    v___x_7463_ = v___x_7458_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7472_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7472_, 0, v___x_7461_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_7472_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_7456_,
                    );
                    v___x_7463_ = v_reuseFailAlloc_7472_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                if v_isShared_7455_ == 0 {
                    leanh::lean_ctor_set(v___x_7454_, 4, v___x_7463_);
                    v___x_7465_ = v___x_7454_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7471_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 0, v_env_7445_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 1, v_nextMacroScope_7446_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 2, v_ngen_7447_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 3, v_auxDeclNGen_7448_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 4, v___x_7463_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 5, v_cache_7449_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 6, v_messages_7450_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 7, v_infoState_7451_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7471_, 8, v_snapshotTasks_7452_);
                    v___x_7465_ = v_reuseFailAlloc_7471_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7466_ = lean_st_ref_set(v___y_7410_, v___x_7465_);
                v___x_7467_ = leanh::lean_box(0);
                if v_isShared_7442_ == 0 {
                    leanh::lean_ctor_set(v___x_7441_, 0, v___x_7467_);
                    v___x_7469_ = v___x_7441_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_7470_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7470_, 0, v___x_7467_);
                    v___x_7469_ = v_reuseFailAlloc_7470_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_7469_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg___boxed(
    mut v_oldTraces_7477_: *mut leanh::LeanObject,
    mut v_data_7478_: *mut leanh::LeanObject,
    mut v_ref_7479_: *mut leanh::LeanObject,
    mut v_msg_7480_: *mut leanh::LeanObject,
    mut v___y_7481_: *mut leanh::LeanObject,
    mut v___y_7482_: *mut leanh::LeanObject,
    mut v___y_7483_: *mut leanh::LeanObject,
    mut v___y_7484_: *mut leanh::LeanObject,
    mut v___y_7485_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7486_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7486_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_oldTraces_7477_, v_data_7478_, v_ref_7479_, v_msg_7480_, v___y_7481_, v___y_7482_, v___y_7483_, v___y_7484_);
    leanh::lean_dec(v___y_7484_);
    leanh::lean_dec_ref(v___y_7483_);
    leanh::lean_dec(v___y_7482_);
    leanh::lean_dec_ref(v___y_7481_);
    return v_res_7486_;
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(
    mut v_e_7487_: *mut leanh::LeanObject,
) -> u8 {
    if leanh::lean_obj_tag(v_e_7487_) == 0 {
        let mut v___x_7488_: u8 = 0;
        v___x_7488_ = 2;
        return v___x_7488_;
    } else {
        let mut v___x_7489_: u8 = 0;
        v___x_7489_ = 0;
        return v___x_7489_;
    }
}
pub unsafe fn l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2___boxed(
    mut v_e_7490_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7491_: u8 = 0;
    let mut v_r_7492_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7491_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_e_7490_);
    leanh::lean_dec_ref(v_e_7490_);
    v_r_7492_ = leanh::lean_box((v_res_7491_) as usize);
    return v_r_7492_;
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(
    mut v_opts_7493_: *mut leanh::LeanObject,
    mut v_opt_7494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_name_7495_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_defValue_7496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_map_7497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7498_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_name_7495_ = leanh::lean_ctor_get(v_opt_7494_, 0);
    v_defValue_7496_ = leanh::lean_ctor_get(v_opt_7494_, 1);
    v_map_7497_ = leanh::lean_ctor_get(v_opts_7493_, 0);
    v___x_7498_ =
        l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(
            v_map_7497_,
            v_name_7495_,
        );
    if leanh::lean_obj_tag(v___x_7498_) == 0 {
        leanh::lean_inc(v_defValue_7496_);
        return v_defValue_7496_;
    } else {
        let mut v_val_7499_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_val_7499_ = leanh::lean_ctor_get(v___x_7498_, 0);
        leanh::lean_inc(v_val_7499_);
        leanh::lean_dec_ref_known(v___x_7498_, 1);
        if leanh::lean_obj_tag(v_val_7499_) == 3 {
            let mut v_v_7500_: *mut leanh::LeanObject = core::ptr::null_mut();
            v_v_7500_ = leanh::lean_ctor_get(v_val_7499_, 0);
            leanh::lean_inc(v_v_7500_);
            leanh::lean_dec_ref_known(v_val_7499_, 1);
            return v_v_7500_;
        } else {
            leanh::lean_dec(v_val_7499_);
            leanh::lean_inc(v_defValue_7496_);
            return v_defValue_7496_;
        }
    }
}
pub unsafe fn l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5___boxed(
    mut v_opts_7501_: *mut leanh::LeanObject,
    mut v_opt_7502_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7503_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7503_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_7501_, v_opt_7502_);
    leanh::lean_dec_ref(v_opt_7502_);
    leanh::lean_dec_ref(v_opts_7501_);
    return v_res_7503_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(
    mut v_x_7504_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7508_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7509_: u8 = 0;
    let mut v___x_7511_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7513_: u8 = 0;
    let mut v_a_7514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7517_: u8 = 0;
    let mut v___x_7519_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7504_) == 0 {
                    v_a_7506_ = leanh::lean_ctor_get(v_x_7504_, 0);
                    v_isSharedCheck_7513_ = (!leanh::lean_is_exclusive(v_x_7504_)) as u8;
                    if v_isSharedCheck_7513_ == 0 {
                        v___x_7508_ = v_x_7504_;
                        v_isShared_7509_ = v_isSharedCheck_7513_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7506_);
                        leanh::lean_dec(v_x_7504_);
                        v___x_7508_ = leanh::lean_box(0);
                        v_isShared_7509_ = v_isSharedCheck_7513_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7514_ = leanh::lean_ctor_get(v_x_7504_, 0);
                    v_isSharedCheck_7521_ = (!leanh::lean_is_exclusive(v_x_7504_)) as u8;
                    if v_isSharedCheck_7521_ == 0 {
                        v___x_7516_ = v_x_7504_;
                        v_isShared_7517_ = v_isSharedCheck_7521_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7514_);
                        leanh::lean_dec(v_x_7504_);
                        v___x_7516_ = leanh::lean_box(0);
                        v_isShared_7517_ = v_isSharedCheck_7521_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_7509_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7508_, 1);
                    v___x_7511_ = v___x_7508_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7512_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7512_, 0, v_a_7506_);
                    v___x_7511_ = v_reuseFailAlloc_7512_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7511_;
            }
            3 => {
                if v_isShared_7517_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7516_, 0);
                    v___x_7519_ = v___x_7516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7520_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7520_, 0, v_a_7514_);
                    v___x_7519_ = v_reuseFailAlloc_7520_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg___boxed(
    mut v_x_7522_: *mut leanh::LeanObject,
    mut v___y_7523_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7524_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7524_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_x_7522_);
    return v_res_7524_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7527_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7526_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__0;
    v___x_7527_ = l_Lean_stringToMessageData(v___x_7526_);
    return v___x_7527_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2()
-> f64 {
    let mut v___x_7528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7529_: f64 = 0.0;
    v___x_7528_ = leanh::lean_unsigned_to_nat(0);
    v___x_7529_ = lean_float_of_nat(v___x_7528_);
    return v___x_7529_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4()
-> *mut leanh::LeanObject {
    let mut v___x_7531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7532_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7531_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__3;
    v___x_7532_ = l_Lean_stringToMessageData(v___x_7531_);
    return v___x_7532_;
}
pub unsafe fn _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5()
-> f64 {
    let mut v___x_7533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7534_: f64 = 0.0;
    v___x_7533_ = leanh::lean_unsigned_to_nat(1000);
    v___x_7534_ = lean_float_of_nat(v___x_7533_);
    return v___x_7534_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(
    mut v_cls_7535_: *mut leanh::LeanObject,
    mut v_collapsed_7536_: u8,
    mut v_tag_7537_: *mut leanh::LeanObject,
    mut v_opts_7538_: *mut leanh::LeanObject,
    mut v_clsEnabled_7539_: u8,
    mut v_oldTraces_7540_: *mut leanh::LeanObject,
    mut v_msg_7541_: *mut leanh::LeanObject,
    mut v_resStartStop_7542_: *mut leanh::LeanObject,
    mut v___y_7543_: *mut leanh::LeanObject,
    mut v___y_7544_: *mut leanh::LeanObject,
    mut v___y_7545_: *mut leanh::LeanObject,
    mut v___y_7546_: *mut leanh::LeanObject,
    mut v___y_7547_: *mut leanh::LeanObject,
    mut v___y_7548_: *mut leanh::LeanObject,
    mut v___y_7549_: *mut leanh::LeanObject,
    mut v___y_7550_: *mut leanh::LeanObject,
    mut v___y_7551_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_fst_7553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7554_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7557_: u8 = 0;
    let mut v___y_7559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7560_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7562_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7564_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7567_: u8 = 0;
    let mut v___x_7569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7570_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7571_: u8 = 0;
    let mut v_fst_7572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7576_: u8 = 0;
    let mut v___x_7577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7578_: u8 = 0;
    let mut v___y_7580_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_result_7582_: u8 = 0;
    let mut v___x_7583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_m_7589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7592_: f64 = 0.0;
    let mut v_data_7593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_data_7594_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7595_: f64 = 0.0;
    let mut v___x_7596_: f64 = 0.0;
    let mut v_reuseFailAlloc_7597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7598_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ref_7600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7602_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7603_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7605_: u8 = 0;
    let mut v___x_7606_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_traceState_7607_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_7608_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_nextMacroScope_7609_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_ngen_7610_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_auxDeclNGen_7611_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_cache_7612_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_messages_7613_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_infoState_7614_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snapshotTasks_7615_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7617_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7618_: u8 = 0;
    let mut v_tid_7619_: u64 = 0;
    let mut v_traces_7620_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7622_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7623_: u8 = 0;
    let mut v___x_7624_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7629_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7633_: u8 = 0;
    let mut v_isSharedCheck_7634_: u8 = 0;
    let mut v___y_7636_: f64 = 0.0;
    let mut v___x_7637_: f64 = 0.0;
    let mut v___x_7638_: f64 = 0.0;
    let mut v___x_7639_: f64 = 0.0;
    let mut v___x_7640_: u8 = 0;
    let mut v___x_7641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7642_: u8 = 0;
    let mut v___x_7643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7645_: f64 = 0.0;
    let mut v___x_7646_: f64 = 0.0;
    let mut v___x_7647_: f64 = 0.0;
    let mut v___x_7648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7650_: f64 = 0.0;
    let mut v_isSharedCheck_7651_: u8 = 0;
    let mut v_isSharedCheck_7652_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_7553_ = leanh::lean_ctor_get(v_resStartStop_7542_, 0);
                v_snd_7554_ = leanh::lean_ctor_get(v_resStartStop_7542_, 1);
                v_isSharedCheck_7652_ =
                    (!leanh::lean_is_exclusive(v_resStartStop_7542_)) as u8;
                if v_isSharedCheck_7652_ == 0 {
                    v___x_7556_ = v_resStartStop_7542_;
                    v_isShared_7557_ = v_isSharedCheck_7652_;
                    state = 1;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7554_);
                    leanh::lean_inc(v_fst_7553_);
                    leanh::lean_dec(v_resStartStop_7542_);
                    v___x_7556_ = leanh::lean_box(0);
                    v_isShared_7557_ = v_isSharedCheck_7652_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_fst_7572_ = leanh::lean_ctor_get(v_snd_7554_, 0);
                v_snd_7573_ = leanh::lean_ctor_get(v_snd_7554_, 1);
                v_isSharedCheck_7651_ = (!leanh::lean_is_exclusive(v_snd_7554_)) as u8;
                if v_isSharedCheck_7651_ == 0 {
                    v___x_7575_ = v_snd_7554_;
                    v_isShared_7576_ = v_isSharedCheck_7651_;
                    state = 5;
                    continue;
                } else {
                    leanh::lean_inc(v_snd_7573_);
                    leanh::lean_inc(v_fst_7572_);
                    leanh::lean_dec(v_snd_7554_);
                    v___x_7575_ = leanh::lean_box(0);
                    v_isShared_7576_ = v_isSharedCheck_7651_;
                    state = 5;
                    continue;
                }
            }
            2 => {
                leanh::lean_inc(v___y_7559_);
                v___x_7562_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_oldTraces_7540_, v_data_7561_, v___y_7559_, v___y_7560_, v___y_7548_, v___y_7549_, v___y_7550_, v___y_7551_);
                if leanh::lean_obj_tag(v___x_7562_) == 0 {
                    leanh::lean_dec_ref_known(v___x_7562_, 1);
                    v___x_7563_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_fst_7553_);
                    return v___x_7563_;
                } else {
                    leanh::lean_dec(v_fst_7553_);
                    v_a_7564_ = leanh::lean_ctor_get(v___x_7562_, 0);
                    v_isSharedCheck_7571_ = (!leanh::lean_is_exclusive(v___x_7562_)) as u8;
                    if v_isSharedCheck_7571_ == 0 {
                        v___x_7566_ = v___x_7562_;
                        v_isShared_7567_ = v_isSharedCheck_7571_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7564_);
                        leanh::lean_dec(v___x_7562_);
                        v___x_7566_ = leanh::lean_box(0);
                        v_isShared_7567_ = v_isSharedCheck_7571_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_7567_ == 0 {
                    v___x_7569_ = v___x_7566_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7570_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7570_, 0, v_a_7564_);
                    v___x_7569_ = v_reuseFailAlloc_7570_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7569_;
            }
            5 => {
                v___x_7577_ = l_Lean_trace_profiler;
                v___x_7578_ =
                    l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(
                        v_opts_7538_,
                        v___x_7577_,
                    );
                if v___x_7578_ == 0 {
                    v___y_7605_ = v___x_7578_;
                    state = 10;
                    continue;
                } else {
                    v___x_7641_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_7642_ =
                        l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(
                            v_opts_7538_,
                            v___x_7641_,
                        );
                    if v___x_7642_ == 0 {
                        v___x_7643_ = l_Lean_trace_profiler_threshold;
                        v___x_7644_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_7538_, v___x_7643_);
                        v___x_7645_ = lean_float_of_nat(v___x_7644_);
                        v___x_7646_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__5);
                        v___x_7647_ = lean_float_div(v___x_7645_, v___x_7646_);
                        v___y_7636_ = v___x_7647_;
                        state = 15;
                        continue;
                    } else {
                        v___x_7648_ = l_Lean_trace_profiler_threshold;
                        v___x_7649_ = l_Lean_Option_get___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__5(v_opts_7538_, v___x_7648_);
                        v___x_7650_ = lean_float_of_nat(v___x_7649_);
                        v___y_7636_ = v___x_7650_;
                        state = 15;
                        continue;
                    }
                }
            }
            6 => {
                v_result_7582_ = l_Except_toTraceResult___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__2(v_fst_7553_);
                v___x_7583_ = l_Lean_TraceResult_toEmoji(v_result_7582_);
                v___x_7584_ = l_Lean_stringToMessageData(v___x_7583_);
                v___x_7585_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__1);
                if v_isShared_7576_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7575_, 7);
                    leanh::lean_ctor_set(v___x_7575_, 1, v___x_7585_);
                    leanh::lean_ctor_set(v___x_7575_, 0, v___x_7584_);
                    v___x_7587_ = v___x_7575_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_7598_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7598_, 0, v___x_7584_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7598_, 1, v___x_7585_);
                    v___x_7587_ = v_reuseFailAlloc_7598_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                if v_isShared_7557_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7556_, 7);
                    leanh::lean_ctor_set(v___x_7556_, 1, v_a_7581_);
                    leanh::lean_ctor_set(v___x_7556_, 0, v___x_7587_);
                    v_m_7589_ = v___x_7556_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_7597_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7597_, 0, v___x_7587_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7597_, 1, v_a_7581_);
                    v_m_7589_ = v_reuseFailAlloc_7597_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                v___x_7590_ = leanh::lean_box((v_result_7582_) as usize);
                v___x_7591_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7591_, 0, v___x_7590_);
                v___x_7592_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__2);
                leanh::lean_inc_ref(v_tag_7537_);
                leanh::lean_inc_ref(v___x_7591_);
                leanh::lean_inc(v_cls_7535_);
                v_data_7593_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                leanh::lean_ctor_set(v_data_7593_, 0, v_cls_7535_);
                leanh::lean_ctor_set(v_data_7593_, 1, v___x_7591_);
                leanh::lean_ctor_set(v_data_7593_, 2, v_tag_7537_);
                leanh::lean_ctor_set_float(
                    v_data_7593_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                    v___x_7592_,
                );
                leanh::lean_ctor_set_float(
                    v_data_7593_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                    v___x_7592_,
                );
                leanh::lean_ctor_set_uint8(
                    v_data_7593_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                    v_collapsed_7536_,
                );
                if v___x_7578_ == 0 {
                    leanh::lean_dec_ref_known(v___x_7591_, 1);
                    leanh::lean_dec(v_snd_7573_);
                    leanh::lean_dec(v_fst_7572_);
                    leanh::lean_dec_ref(v_tag_7537_);
                    leanh::lean_dec(v_cls_7535_);
                    v___y_7559_ = v___y_7580_;
                    v___y_7560_ = v_m_7589_;
                    v_data_7561_ = v_data_7593_;
                    state = 2;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v_data_7593_, 3);
                    v_data_7594_ = leanh::lean_alloc_ctor(0, 3, (17) as u32);
                    leanh::lean_ctor_set(v_data_7594_, 0, v_cls_7535_);
                    leanh::lean_ctor_set(v_data_7594_, 1, v___x_7591_);
                    leanh::lean_ctor_set(v_data_7594_, 2, v_tag_7537_);
                    v___x_7595_ = leanh::lean_unbox_float(v_fst_7572_);
                    leanh::lean_dec(v_fst_7572_);
                    leanh::lean_ctor_set_float(
                        v_data_7594_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3) as u32,
                        v___x_7595_,
                    );
                    v___x_7596_ = leanh::lean_unbox_float(v_snd_7573_);
                    leanh::lean_dec(v_snd_7573_);
                    leanh::lean_ctor_set_float(
                        v_data_7594_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 8) as u32,
                        v___x_7596_,
                    );
                    leanh::lean_ctor_set_uint8(
                        v_data_7594_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 3 + 16) as u32,
                        v_collapsed_7536_,
                    );
                    v___y_7559_ = v___y_7580_;
                    v___y_7560_ = v_m_7589_;
                    v_data_7561_ = v_data_7594_;
                    state = 2;
                    continue;
                }
            }
            9 => {
                v_ref_7600_ = leanh::lean_ctor_get(v___y_7550_, 5);
                leanh::lean_inc(v___y_7551_);
                leanh::lean_inc_ref(v___y_7550_);
                leanh::lean_inc(v___y_7549_);
                leanh::lean_inc_ref(v___y_7548_);
                leanh::lean_inc(v___y_7547_);
                leanh::lean_inc_ref(v___y_7546_);
                leanh::lean_inc(v___y_7545_);
                leanh::lean_inc_ref(v___y_7544_);
                leanh::lean_inc(v___y_7543_);
                leanh::lean_inc(v_fst_7553_);
                v___x_7601_ = leanh::lean_apply_11(
                    v_msg_7541_,
                    v_fst_7553_,
                    v___y_7543_,
                    v___y_7544_,
                    v___y_7545_,
                    v___y_7546_,
                    v___y_7547_,
                    v___y_7548_,
                    v___y_7549_,
                    v___y_7550_,
                    v___y_7551_,
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_7601_) == 0 {
                    v_a_7602_ = leanh::lean_ctor_get(v___x_7601_, 0);
                    leanh::lean_inc(v_a_7602_);
                    leanh::lean_dec_ref_known(v___x_7601_, 1);
                    v___y_7580_ = v_ref_7600_;
                    v_a_7581_ = v_a_7602_;
                    state = 6;
                    continue;
                } else {
                    leanh::lean_dec_ref_known(v___x_7601_, 1);
                    v___x_7603_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4_once), _init_l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___closed__4);
                    v___y_7580_ = v_ref_7600_;
                    v_a_7581_ = v___x_7603_;
                    state = 6;
                    continue;
                }
            }
            10 => {
                if v_clsEnabled_7539_ == 0 {
                    if v___y_7605_ == 0 {
                        leanh::lean_del_object(v___x_7575_);
                        leanh::lean_dec(v_snd_7573_);
                        leanh::lean_dec(v_fst_7572_);
                        leanh::lean_del_object(v___x_7556_);
                        leanh::lean_dec_ref(v_msg_7541_);
                        leanh::lean_dec_ref(v_tag_7537_);
                        leanh::lean_dec(v_cls_7535_);
                        v___x_7606_ = lean_st_ref_take(v___y_7551_);
                        v_traceState_7607_ = leanh::lean_ctor_get(v___x_7606_, 4);
                        v_env_7608_ = leanh::lean_ctor_get(v___x_7606_, 0);
                        v_nextMacroScope_7609_ = leanh::lean_ctor_get(v___x_7606_, 1);
                        v_ngen_7610_ = leanh::lean_ctor_get(v___x_7606_, 2);
                        v_auxDeclNGen_7611_ = leanh::lean_ctor_get(v___x_7606_, 3);
                        v_cache_7612_ = leanh::lean_ctor_get(v___x_7606_, 5);
                        v_messages_7613_ = leanh::lean_ctor_get(v___x_7606_, 6);
                        v_infoState_7614_ = leanh::lean_ctor_get(v___x_7606_, 7);
                        v_snapshotTasks_7615_ = leanh::lean_ctor_get(v___x_7606_, 8);
                        v_isSharedCheck_7634_ =
                            (!leanh::lean_is_exclusive(v___x_7606_)) as u8;
                        if v_isSharedCheck_7634_ == 0 {
                            v___x_7617_ = v___x_7606_;
                            v_isShared_7618_ = v_isSharedCheck_7634_;
                            state = 11;
                            continue;
                        } else {
                            leanh::lean_inc(v_snapshotTasks_7615_);
                            leanh::lean_inc(v_infoState_7614_);
                            leanh::lean_inc(v_messages_7613_);
                            leanh::lean_inc(v_cache_7612_);
                            leanh::lean_inc(v_traceState_7607_);
                            leanh::lean_inc(v_auxDeclNGen_7611_);
                            leanh::lean_inc(v_ngen_7610_);
                            leanh::lean_inc(v_nextMacroScope_7609_);
                            leanh::lean_inc(v_env_7608_);
                            leanh::lean_dec(v___x_7606_);
                            v___x_7617_ = leanh::lean_box(0);
                            v_isShared_7618_ = v_isSharedCheck_7634_;
                            state = 11;
                            continue;
                        }
                    } else {
                        state = 9;
                        continue;
                    }
                } else {
                    state = 9;
                    continue;
                }
            }
            11 => {
                v_tid_7619_ = leanh::lean_ctor_get_uint64(
                    v_traceState_7607_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                );
                v_traces_7620_ = leanh::lean_ctor_get(v_traceState_7607_, 0);
                v_isSharedCheck_7633_ =
                    (!leanh::lean_is_exclusive(v_traceState_7607_)) as u8;
                if v_isSharedCheck_7633_ == 0 {
                    v___x_7622_ = v_traceState_7607_;
                    v_isShared_7623_ = v_isSharedCheck_7633_;
                    state = 12;
                    continue;
                } else {
                    leanh::lean_inc(v_traces_7620_);
                    leanh::lean_dec(v_traceState_7607_);
                    v___x_7622_ = leanh::lean_box(0);
                    v_isShared_7623_ = v_isSharedCheck_7633_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                v___x_7624_ =
                    l_Lean_PersistentArray_append___redArg(v_oldTraces_7540_, v_traces_7620_);
                leanh::lean_dec_ref(v_traces_7620_);
                if v_isShared_7623_ == 0 {
                    leanh::lean_ctor_set(v___x_7622_, 0, v___x_7624_);
                    v___x_7626_ = v___x_7622_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_7632_ = leanh::lean_alloc_ctor(0, 1, (8) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7632_, 0, v___x_7624_);
                    leanh::lean_ctor_set_uint64(
                        v_reuseFailAlloc_7632_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                        v_tid_7619_,
                    );
                    v___x_7626_ = v_reuseFailAlloc_7632_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                if v_isShared_7618_ == 0 {
                    leanh::lean_ctor_set(v___x_7617_, 4, v___x_7626_);
                    v___x_7628_ = v___x_7617_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_7631_ = leanh::lean_alloc_ctor(0, 9, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 0, v_env_7608_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 1, v_nextMacroScope_7609_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 2, v_ngen_7610_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 3, v_auxDeclNGen_7611_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 4, v___x_7626_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 5, v_cache_7612_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 6, v_messages_7613_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 7, v_infoState_7614_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7631_, 8, v_snapshotTasks_7615_);
                    v___x_7628_ = v_reuseFailAlloc_7631_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                v___x_7629_ = lean_st_ref_set(v___y_7551_, v___x_7628_);
                v___x_7630_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_fst_7553_);
                return v___x_7630_;
            }
            15 => {
                v___x_7637_ = leanh::lean_unbox_float(v_snd_7573_);
                v___x_7638_ = leanh::lean_unbox_float(v_fst_7572_);
                v___x_7639_ = lean_float_sub(v___x_7637_, v___x_7638_);
                v___x_7640_ = lean_float_decLt(v___y_7636_, v___x_7639_);
                v___y_7605_ = v___x_7640_;
                state = 10;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cls_7653_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_collapsed_7654_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_tag_7655_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_opts_7656_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_clsEnabled_7657_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_oldTraces_7658_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_msg_7659_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_resStartStop_7660_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_7661_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_7662_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_7663_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_7664_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_7665_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7666_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7667_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7668_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7669_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_7670_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_collapsed_boxed_7671_: u8 = 0;
    let mut v_clsEnabled_boxed_7672_: u8 = 0;
    let mut v_res_7673_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_collapsed_boxed_7671_ = (leanh::lean_unbox(v_collapsed_7654_) as u8);
    v_clsEnabled_boxed_7672_ = (leanh::lean_unbox(v_clsEnabled_7657_) as u8);
    v_res_7673_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v_cls_7653_, v_collapsed_boxed_7671_, v_tag_7655_, v_opts_7656_, v_clsEnabled_boxed_7672_, v_oldTraces_7658_, v_msg_7659_, v_resStartStop_7660_, v___y_7661_, v___y_7662_, v___y_7663_, v___y_7664_, v___y_7665_, v___y_7666_, v___y_7667_, v___y_7668_, v___y_7669_);
    leanh::lean_dec(v___y_7669_);
    leanh::lean_dec_ref(v___y_7668_);
    leanh::lean_dec(v___y_7667_);
    leanh::lean_dec_ref(v___y_7666_);
    leanh::lean_dec(v___y_7665_);
    leanh::lean_dec_ref(v___y_7664_);
    leanh::lean_dec(v___y_7663_);
    leanh::lean_dec_ref(v___y_7662_);
    leanh::lean_dec(v___y_7661_);
    leanh::lean_dec_ref(v_opts_7656_);
    return v_res_7673_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_7675_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7676_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7675_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__0;
    v___x_7676_ = l_Lean_stringToMessageData(v___x_7675_);
    return v___x_7676_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_7678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7679_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7678_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__2;
    v___x_7679_ = l_Lean_stringToMessageData(v___x_7678_);
    return v___x_7679_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5()
-> *mut leanh::LeanObject {
    let mut v___x_7681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__4;
    v___x_7682_ = l_Lean_stringToMessageData(v___x_7681_);
    return v___x_7682_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7()
-> *mut leanh::LeanObject {
    let mut v___x_7684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7685_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__6;
    v___x_7685_ = l_Lean_stringToMessageData(v___x_7684_);
    return v___x_7685_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_7687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7688_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7687_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__8;
    v___x_7688_ = l_Lean_stringToMessageData(v___x_7687_);
    return v___x_7688_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11()
-> *mut leanh::LeanObject {
    let mut v___x_7690_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7691_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7690_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__10;
    v___x_7691_ = l_Lean_stringToMessageData(v___x_7690_);
    return v___x_7691_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(
    mut v___x_7692_: *mut leanh::LeanObject,
    mut v_e_7693_: *mut leanh::LeanObject,
    mut v_x_7694_: *mut leanh::LeanObject,
    mut v___y_7695_: *mut leanh::LeanObject,
    mut v___y_7696_: *mut leanh::LeanObject,
    mut v___y_7697_: *mut leanh::LeanObject,
    mut v___y_7698_: *mut leanh::LeanObject,
    mut v___y_7699_: *mut leanh::LeanObject,
    mut v___y_7700_: *mut leanh::LeanObject,
    mut v___y_7701_: *mut leanh::LeanObject,
    mut v___y_7702_: *mut leanh::LeanObject,
    mut v___y_7703_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7705_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7707_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7708_: u8 = 0;
    let mut v___x_7709_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7710_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7711_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7712_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7713_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7719_: u8 = 0;
    let mut v_a_7720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7723_: u8 = 0;
    let mut v_done_7724_: u8 = 0;
    let mut v___x_7725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7727_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7729_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7730_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_e_x27_7743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7746_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7753_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7756_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7758_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_7694_) == 0 {
                    leanh::lean_dec_ref(v_e_7693_);
                    v_a_7705_ = leanh::lean_ctor_get(v_x_7694_, 0);
                    v_isSharedCheck_7719_ = (!leanh::lean_is_exclusive(v_x_7694_)) as u8;
                    if v_isSharedCheck_7719_ == 0 {
                        v___x_7707_ = v_x_7694_;
                        v_isShared_7708_ = v_isSharedCheck_7719_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7705_);
                        leanh::lean_dec(v_x_7694_);
                        v___x_7707_ = leanh::lean_box(0);
                        v_isShared_7708_ = v_isSharedCheck_7719_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_7720_ = leanh::lean_ctor_get(v_x_7694_, 0);
                    v_isSharedCheck_7758_ = (!leanh::lean_is_exclusive(v_x_7694_)) as u8;
                    if v_isSharedCheck_7758_ == 0 {
                        v___x_7722_ = v_x_7694_;
                        v_isShared_7723_ = v_isSharedCheck_7758_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7720_);
                        leanh::lean_dec(v_x_7694_);
                        v___x_7722_ = leanh::lean_box(0);
                        v_isShared_7723_ = v_isSharedCheck_7758_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7709_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
                v___x_7710_ = l_Lean_MessageData_ofName(v___x_7692_);
                v___x_7711_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7711_, 0, v___x_7709_);
                leanh::lean_ctor_set(v___x_7711_, 1, v___x_7710_);
                v___x_7712_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__3);
                v___x_7713_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7713_, 0, v___x_7711_);
                leanh::lean_ctor_set(v___x_7713_, 1, v___x_7712_);
                v___x_7714_ = l_Lean_Exception_toMessageData(v_a_7705_);
                v___x_7715_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7715_, 0, v___x_7713_);
                leanh::lean_ctor_set(v___x_7715_, 1, v___x_7714_);
                if v_isShared_7708_ == 0 {
                    leanh::lean_ctor_set(v___x_7707_, 0, v___x_7715_);
                    v___x_7717_ = v___x_7707_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7718_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7718_, 0, v___x_7715_);
                    v___x_7717_ = v_reuseFailAlloc_7718_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7717_;
            }
            3 => {
                if leanh::lean_obj_tag(v_a_7720_) == 0 {
                    v_done_7724_ = leanh::lean_ctor_get_uint8(v_a_7720_, 0 as u32);
                    leanh::lean_dec_ref_known(v_a_7720_, 0);
                    if v_done_7724_ == 1 {
                        v___x_7725_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
                        v___x_7726_ = l_Lean_MessageData_ofName(v___x_7692_);
                        v___x_7727_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7727_, 0, v___x_7725_);
                        leanh::lean_ctor_set(v___x_7727_, 1, v___x_7726_);
                        v___x_7728_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__5);
                        v___x_7729_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7729_, 0, v___x_7727_);
                        leanh::lean_ctor_set(v___x_7729_, 1, v___x_7728_);
                        v___x_7730_ = l_Lean_indentExpr(v_e_7693_);
                        v___x_7731_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7731_, 0, v___x_7729_);
                        leanh::lean_ctor_set(v___x_7731_, 1, v___x_7730_);
                        if v_isShared_7723_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_7722_, 0);
                            leanh::lean_ctor_set(v___x_7722_, 0, v___x_7731_);
                            v___x_7733_ = v___x_7722_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_7734_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7734_, 0, v___x_7731_);
                            v___x_7733_ = v_reuseFailAlloc_7734_;
                            state = 4;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_e_7693_);
                        v___x_7735_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
                        v___x_7736_ = l_Lean_MessageData_ofName(v___x_7692_);
                        v___x_7737_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7737_, 0, v___x_7735_);
                        leanh::lean_ctor_set(v___x_7737_, 1, v___x_7736_);
                        v___x_7738_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__7);
                        v___x_7739_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                        leanh::lean_ctor_set(v___x_7739_, 0, v___x_7737_);
                        leanh::lean_ctor_set(v___x_7739_, 1, v___x_7738_);
                        if v_isShared_7723_ == 0 {
                            leanh::lean_ctor_set_tag(v___x_7722_, 0);
                            leanh::lean_ctor_set(v___x_7722_, 0, v___x_7739_);
                            v___x_7741_ = v___x_7722_;
                            state = 5;
                            continue;
                        } else {
                            v_reuseFailAlloc_7742_ =
                                leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            leanh::lean_ctor_set(v_reuseFailAlloc_7742_, 0, v___x_7739_);
                            v___x_7741_ = v_reuseFailAlloc_7742_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_e_x27_7743_ = leanh::lean_ctor_get(v_a_7720_, 0);
                    leanh::lean_inc_ref(v_e_x27_7743_);
                    leanh::lean_dec_ref_known(v_a_7720_, 2);
                    v___x_7744_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__1);
                    v___x_7745_ = l_Lean_MessageData_ofName(v___x_7692_);
                    v___x_7746_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7746_, 0, v___x_7744_);
                    leanh::lean_ctor_set(v___x_7746_, 1, v___x_7745_);
                    v___x_7747_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__9);
                    v___x_7748_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7748_, 0, v___x_7746_);
                    leanh::lean_ctor_set(v___x_7748_, 1, v___x_7747_);
                    v___x_7749_ = l_Lean_indentExpr(v_e_7693_);
                    v___x_7750_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7750_, 0, v___x_7748_);
                    leanh::lean_ctor_set(v___x_7750_, 1, v___x_7749_);
                    v___x_7751_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___closed__11);
                    v___x_7752_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7752_, 0, v___x_7750_);
                    leanh::lean_ctor_set(v___x_7752_, 1, v___x_7751_);
                    v___x_7753_ = l_Lean_indentExpr(v_e_x27_7743_);
                    v___x_7754_ = leanh::lean_alloc_ctor(7, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_7754_, 0, v___x_7752_);
                    leanh::lean_ctor_set(v___x_7754_, 1, v___x_7753_);
                    if v_isShared_7723_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_7722_, 0);
                        leanh::lean_ctor_set(v___x_7722_, 0, v___x_7754_);
                        v___x_7756_ = v___x_7722_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_7757_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_7757_, 0, v___x_7754_);
                        v___x_7756_ = v_reuseFailAlloc_7757_;
                        state = 6;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_7733_;
            }
            5 => {
                return v___x_7741_;
            }
            6 => {
                return v___x_7756_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed(
    mut v___x_7759_: *mut leanh::LeanObject,
    mut v_e_7760_: *mut leanh::LeanObject,
    mut v_x_7761_: *mut leanh::LeanObject,
    mut v___y_7762_: *mut leanh::LeanObject,
    mut v___y_7763_: *mut leanh::LeanObject,
    mut v___y_7764_: *mut leanh::LeanObject,
    mut v___y_7765_: *mut leanh::LeanObject,
    mut v___y_7766_: *mut leanh::LeanObject,
    mut v___y_7767_: *mut leanh::LeanObject,
    mut v___y_7768_: *mut leanh::LeanObject,
    mut v___y_7769_: *mut leanh::LeanObject,
    mut v___y_7770_: *mut leanh::LeanObject,
    mut v___y_7771_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7772_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1(v___x_7759_, v_e_7760_, v_x_7761_, v___y_7762_, v___y_7763_, v___y_7764_, v___y_7765_, v___y_7766_, v___y_7767_, v___y_7768_, v___y_7769_, v___y_7770_);
    leanh::lean_dec(v___y_7770_);
    leanh::lean_dec_ref(v___y_7769_);
    leanh::lean_dec(v___y_7768_);
    leanh::lean_dec_ref(v___y_7767_);
    leanh::lean_dec(v___y_7766_);
    leanh::lean_dec_ref(v___y_7765_);
    leanh::lean_dec(v___y_7764_);
    leanh::lean_dec_ref(v___y_7763_);
    leanh::lean_dec(v___y_7762_);
    return v_res_7772_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9()
-> *mut leanh::LeanObject {
    let mut v___x_7797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7799_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5;
    v___x_7798_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__8;
    v___x_7799_ = l_Lean_Name_append(v___x_7798_, v___x_7797_);
    return v___x_7799_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10()
-> f64 {
    let mut v___x_7800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7801_: f64 = 0.0;
    v___x_7800_ = leanh::lean_unsigned_to_nat(1000000000);
    v___x_7801_ = lean_float_of_nat(v___x_7800_);
    return v___x_7801_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(
    mut v_erased_7802_: *mut leanh::LeanObject,
    mut v_e_7803_: *mut leanh::LeanObject,
    mut v_as_7804_: *mut leanh::LeanObject,
    mut v_sz_7805_: usize,
    mut v_i_7806_: usize,
    mut v_b_7807_: *mut leanh::LeanObject,
    mut v___y_7808_: *mut leanh::LeanObject,
    mut v___y_7809_: *mut leanh::LeanObject,
    mut v___y_7810_: *mut leanh::LeanObject,
    mut v___y_7811_: *mut leanh::LeanObject,
    mut v___y_7812_: *mut leanh::LeanObject,
    mut v___y_7813_: *mut leanh::LeanObject,
    mut v___y_7814_: *mut leanh::LeanObject,
    mut v___y_7815_: *mut leanh::LeanObject,
    mut v___y_7816_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_7819_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7820_: usize = 0;
    let mut v___x_7821_: usize = 0;
    let mut v___x_7823_: u8 = 0;
    let mut v___x_7824_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_7826_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_toCbvSimprocOLeanEntry_7827_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_7828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7831_: u8 = 0;
    let mut v_proc_7832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7834_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7835_: u8 = 0;
    let mut v_declName_7836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7840_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7844_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7846_: u8 = 0;
    let mut v___y_7848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7849_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7852_: u8 = 0;
    let mut v_done_7853_: u8 = 0;
    let mut v_contextDependent_7854_: u8 = 0;
    let mut v___x_7855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7862_: u8 = 0;
    let mut v_a_7863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7866_: u8 = 0;
    let mut v___x_7868_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7870_: u8 = 0;
    let mut v___x_7871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_7872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_inheritedTraceOptions_7873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_hasTrace_7874_: u8 = 0;
    let mut v___x_7875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7876_: u8 = 0;
    let mut v___x_7877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7882_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_7883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7887_: u8 = 0;
    let mut v___y_7889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7892_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7893_: f64 = 0.0;
    let mut v___x_7894_: f64 = 0.0;
    let mut v___x_7895_: f64 = 0.0;
    let mut v___x_7896_: f64 = 0.0;
    let mut v___x_7897_: f64 = 0.0;
    let mut v___x_7898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7899_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7900_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7904_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7908_: f64 = 0.0;
    let mut v___x_7909_: f64 = 0.0;
    let mut v___x_7910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7917_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7919_: u8 = 0;
    let mut v___x_7920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7925_: u8 = 0;
    let mut v___x_7927_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7929_: u8 = 0;
    let mut v_a_7930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7933_: u8 = 0;
    let mut v___x_7935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7937_: u8 = 0;
    let mut v___x_7938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7943_: u8 = 0;
    let mut v___x_7945_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7946_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7947_: u8 = 0;
    let mut v_a_7948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7951_: u8 = 0;
    let mut v___x_7953_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7954_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7955_: u8 = 0;
    let mut v_a_7956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7958_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7959_: u8 = 0;
    let mut v___x_7961_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7962_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7963_: u8 = 0;
    let mut v___x_7964_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7965_: u8 = 0;
    let mut v___x_7966_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7967_: u8 = 0;
    let mut v_unused_7968_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7969_: u8 = 0;
    let mut v_unused_7970_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7823_ = lean_usize_dec_lt(v_i_7806_, v_sz_7805_);
                if v___x_7823_ == 0 {
                    leanh::lean_dec_ref(v_e_7803_);
                    v___x_7824_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7824_, 0, v_b_7807_);
                    return v___x_7824_;
                } else {
                    leanh::lean_dec_ref(v_b_7807_);
                    v_a_7825_ = lean_array_uget(v_as_7804_, v_i_7806_);
                    v_fst_7826_ = leanh::lean_ctor_get(v_a_7825_, 0);
                    leanh::lean_inc(v_fst_7826_);
                    v_toCbvSimprocOLeanEntry_7827_ = leanh::lean_ctor_get(v_fst_7826_, 0);
                    leanh::lean_inc_ref(v_toCbvSimprocOLeanEntry_7827_);
                    v_snd_7828_ = leanh::lean_ctor_get(v_a_7825_, 1);
                    v_isSharedCheck_7969_ = (!leanh::lean_is_exclusive(v_a_7825_)) as u8;
                    if v_isSharedCheck_7969_ == 0 {
                        v_unused_7970_ = leanh::lean_ctor_get(v_a_7825_, 0);
                        leanh::lean_dec(v_unused_7970_);
                        v___x_7830_ = v_a_7825_;
                        v_isShared_7831_ = v_isSharedCheck_7969_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_7828_);
                        leanh::lean_dec(v_a_7825_);
                        v___x_7830_ = leanh::lean_box(0);
                        v_isShared_7831_ = v_isSharedCheck_7969_;
                        state = 2;
                        continue;
                    }
                }
            }
            1 => {
                v___x_7820_ = 1usize;
                v___x_7821_ = lean_usize_add(v_i_7806_, v___x_7820_);
                leanh::lean_inc_ref(v_a_7819_);
                v_i_7806_ = v___x_7821_;
                v_b_7807_ = v_a_7819_;
                state = 0;
                continue;
            }
            2 => {
                v_proc_7832_ = leanh::lean_ctor_get(v_fst_7826_, 1);
                v_isSharedCheck_7967_ = (!leanh::lean_is_exclusive(v_fst_7826_)) as u8;
                if v_isSharedCheck_7967_ == 0 {
                    v_unused_7968_ = leanh::lean_ctor_get(v_fst_7826_, 0);
                    leanh::lean_dec(v_unused_7968_);
                    v___x_7834_ = v_fst_7826_;
                    v_isShared_7835_ = v_isSharedCheck_7967_;
                    state = 3;
                    continue;
                } else {
                    leanh::lean_inc(v_proc_7832_);
                    leanh::lean_dec(v_fst_7826_);
                    v___x_7834_ = leanh::lean_box(0);
                    v_isShared_7835_ = v_isSharedCheck_7967_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v_declName_7836_ = leanh::lean_ctor_get(v_toCbvSimprocOLeanEntry_7827_, 0);
                leanh::lean_inc(v_declName_7836_);
                leanh::lean_dec_ref(v_toCbvSimprocOLeanEntry_7827_);
                v___x_7837_ = leanh::lean_box(0);
                v___x_7845_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0;
                v___x_7846_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Tactic_Cbv_eraseCbvSimprocAttr_spec__0___redArg(v_erased_7802_, v_declName_7836_);
                if v___x_7846_ == 0 {
                    v___x_7871_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__1;
                    v_options_7872_ = leanh::lean_ctor_get(v___y_7815_, 2);
                    v_inheritedTraceOptions_7873_ = leanh::lean_ctor_get(v___y_7815_, 13);
                    v_hasTrace_7874_ = leanh::lean_ctor_get_uint8(
                        v_options_7872_,
                        (core::mem::size_of::<*mut leanh::LeanObject>() * 1) as u32,
                    );
                    v___x_7875_ = leanh::lean_unsigned_to_nat(0);
                    v___x_7876_ = lean_nat_dec_eq(v_snd_7828_, v___x_7875_);
                    if v_hasTrace_7874_ == 0 {
                        leanh::lean_dec(v_declName_7836_);
                        leanh::lean_inc_ref(v_e_7803_);
                        v___x_7877_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_7876_, v_e_7803_, v_snd_7828_, v_proc_7832_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_, v___y_7815_, v___y_7816_);
                        leanh::lean_dec(v_snd_7828_);
                        v___y_7848_ = v___x_7877_;
                        state = 6;
                        continue;
                    } else {
                        v___x_7878_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__2;
                        v___x_7879_ = l_Lean_privateToUserName(v_declName_7836_);
                        v___x_7880_ = leanh::lean_box(0);
                        v___x_7881_ =
                            l_Lean_Name_replacePrefix(v___x_7879_, v___x_7871_, v___x_7880_);
                        v___x_7882_ =
                            l_Lean_Name_replacePrefix(v___x_7881_, v___x_7878_, v___x_7880_);
                        leanh::lean_inc_ref(v_e_7803_);
                        v___f_7883_ = leanh::lean_alloc_closure(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__1___boxed as *mut core::ffi::c_void, 13, 2);
                        leanh::lean_closure_set(v___f_7883_, 0, v___x_7882_);
                        leanh::lean_closure_set(v___f_7883_, 1, v_e_7803_);
                        v___x_7884_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__5;
                        v___x_7885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__6;
                        v___x_7886_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__9);
                        v___x_7887_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(
                            v_inheritedTraceOptions_7873_,
                            v_options_7872_,
                            v___x_7886_,
                        );
                        if v___x_7887_ == 0 {
                            v___x_7964_ = l_Lean_trace_profiler;
                            v___x_7965_ = l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(v_options_7872_, v___x_7964_);
                            if v___x_7965_ == 0 {
                                leanh::lean_dec_ref(v___f_7883_);
                                leanh::lean_inc_ref(v_e_7803_);
                                v___x_7966_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_7876_, v_e_7803_, v_snd_7828_, v_proc_7832_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_, v___y_7815_, v___y_7816_);
                                leanh::lean_dec(v_snd_7828_);
                                v___y_7848_ = v___x_7966_;
                                state = 6;
                                continue;
                            } else {
                                state = 14;
                                continue;
                            }
                        } else {
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec(v_declName_7836_);
                    leanh::lean_del_object(v___x_7834_);
                    leanh::lean_dec_ref(v_proc_7832_);
                    leanh::lean_del_object(v___x_7830_);
                    leanh::lean_dec(v_snd_7828_);
                    v_a_7819_ = v___x_7845_;
                    state = 1;
                    continue;
                }
            }
            4 => {
                v___x_7840_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7840_, 0, v___y_7839_);
                if v_isShared_7831_ == 0 {
                    leanh::lean_ctor_set(v___x_7830_, 1, v___x_7837_);
                    leanh::lean_ctor_set(v___x_7830_, 0, v___x_7840_);
                    v___x_7842_ = v___x_7830_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_7844_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7844_, 0, v___x_7840_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7844_, 1, v___x_7837_);
                    v___x_7842_ = v_reuseFailAlloc_7844_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_7843_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_7843_, 0, v___x_7842_);
                return v___x_7843_;
            }
            6 => {
                if leanh::lean_obj_tag(v___y_7848_) == 0 {
                    v_a_7849_ = leanh::lean_ctor_get(v___y_7848_, 0);
                    v_isSharedCheck_7862_ = (!leanh::lean_is_exclusive(v___y_7848_)) as u8;
                    if v_isSharedCheck_7862_ == 0 {
                        v___x_7851_ = v___y_7848_;
                        v_isShared_7852_ = v_isSharedCheck_7862_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7849_);
                        leanh::lean_dec(v___y_7848_);
                        v___x_7851_ = leanh::lean_box(0);
                        v_isShared_7852_ = v_isSharedCheck_7862_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_7834_);
                    leanh::lean_del_object(v___x_7830_);
                    leanh::lean_dec_ref(v_e_7803_);
                    v_a_7863_ = leanh::lean_ctor_get(v___y_7848_, 0);
                    v_isSharedCheck_7870_ = (!leanh::lean_is_exclusive(v___y_7848_)) as u8;
                    if v_isSharedCheck_7870_ == 0 {
                        v___x_7865_ = v___y_7848_;
                        v_isShared_7866_ = v_isSharedCheck_7870_;
                        state = 10;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7863_);
                        leanh::lean_dec(v___y_7848_);
                        v___x_7865_ = leanh::lean_box(0);
                        v_isShared_7866_ = v_isSharedCheck_7870_;
                        state = 10;
                        continue;
                    }
                }
            }
            7 => {
                if leanh::lean_obj_tag(v_a_7849_) == 1 {
                    leanh::lean_del_object(v___x_7851_);
                    leanh::lean_del_object(v___x_7834_);
                    leanh::lean_dec_ref(v_e_7803_);
                    v___y_7839_ = v_a_7849_;
                    state = 4;
                    continue;
                } else {
                    if v___x_7846_ == 0 {
                        leanh::lean_del_object(v___x_7830_);
                        if leanh::lean_obj_tag(v_a_7849_) == 0 {
                            v_done_7853_ = leanh::lean_ctor_get_uint8(v_a_7849_, 0 as u32);
                            if v_done_7853_ == 1 {
                                v_contextDependent_7854_ =
                                    leanh::lean_ctor_get_uint8(v_a_7849_, 1 as u32);
                                if v_contextDependent_7854_ == 0 {
                                    leanh::lean_dec_ref(v_e_7803_);
                                    v___x_7855_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                    leanh::lean_ctor_set(v___x_7855_, 0, v_a_7849_);
                                    if v_isShared_7835_ == 0 {
                                        leanh::lean_ctor_set(v___x_7834_, 1, v___x_7837_);
                                        leanh::lean_ctor_set(v___x_7834_, 0, v___x_7855_);
                                        v___x_7857_ = v___x_7834_;
                                        state = 8;
                                        continue;
                                    } else {
                                        v_reuseFailAlloc_7861_ =
                                            leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7861_,
                                            0,
                                            v___x_7855_,
                                        );
                                        leanh::lean_ctor_set(
                                            v_reuseFailAlloc_7861_,
                                            1,
                                            v___x_7837_,
                                        );
                                        v___x_7857_ = v_reuseFailAlloc_7861_;
                                        state = 8;
                                        continue;
                                    }
                                } else {
                                    leanh::lean_dec_ref_known(v_a_7849_, 0);
                                    leanh::lean_del_object(v___x_7851_);
                                    leanh::lean_del_object(v___x_7834_);
                                    v_a_7819_ = v___x_7845_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                leanh::lean_dec_ref_known(v_a_7849_, 0);
                                leanh::lean_del_object(v___x_7851_);
                                leanh::lean_del_object(v___x_7834_);
                                v_a_7819_ = v___x_7845_;
                                state = 1;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_7851_);
                            leanh::lean_dec(v_a_7849_);
                            leanh::lean_del_object(v___x_7834_);
                            v_a_7819_ = v___x_7845_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_del_object(v___x_7851_);
                        leanh::lean_del_object(v___x_7834_);
                        leanh::lean_dec_ref(v_e_7803_);
                        v___y_7839_ = v_a_7849_;
                        state = 4;
                        continue;
                    }
                }
            }
            8 => {
                if v_isShared_7852_ == 0 {
                    leanh::lean_ctor_set(v___x_7851_, 0, v___x_7857_);
                    v___x_7859_ = v___x_7851_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_7860_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7860_, 0, v___x_7857_);
                    v___x_7859_ = v_reuseFailAlloc_7860_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_7859_;
            }
            10 => {
                if v_isShared_7866_ == 0 {
                    v___x_7868_ = v___x_7865_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_7869_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7869_, 0, v_a_7863_);
                    v___x_7868_ = v_reuseFailAlloc_7869_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_7868_;
            }
            12 => {
                v___x_7892_ = lean_io_mono_nanos_now();
                v___x_7893_ = lean_float_of_nat(v___y_7889_);
                v___x_7894_ = leanh::lean_float_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__10);
                v___x_7895_ = lean_float_div(v___x_7893_, v___x_7894_);
                v___x_7896_ = lean_float_of_nat(v___x_7892_);
                v___x_7897_ = lean_float_div(v___x_7896_, v___x_7894_);
                v___x_7898_ = leanh::lean_box_float(v___x_7895_);
                v___x_7899_ = leanh::lean_box_float(v___x_7897_);
                v___x_7900_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7900_, 0, v___x_7898_);
                leanh::lean_ctor_set(v___x_7900_, 1, v___x_7899_);
                v___x_7901_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7901_, 0, v_a_7891_);
                leanh::lean_ctor_set(v___x_7901_, 1, v___x_7900_);
                v___x_7902_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_7884_, v_hasTrace_7874_, v___x_7885_, v_options_7872_, v___x_7887_, v___y_7890_, v___f_7883_, v___x_7901_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_, v___y_7815_, v___y_7816_);
                v___y_7848_ = v___x_7902_;
                state = 6;
                continue;
            }
            13 => {
                v___x_7907_ = lean_io_get_num_heartbeats();
                v___x_7908_ = lean_float_of_nat(v___y_7904_);
                v___x_7909_ = lean_float_of_nat(v___x_7907_);
                v___x_7910_ = leanh::lean_box_float(v___x_7908_);
                v___x_7911_ = leanh::lean_box_float(v___x_7909_);
                v___x_7912_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7912_, 0, v___x_7910_);
                leanh::lean_ctor_set(v___x_7912_, 1, v___x_7911_);
                v___x_7913_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_7913_, 0, v_a_7906_);
                leanh::lean_ctor_set(v___x_7913_, 1, v___x_7912_);
                v___x_7914_ = l___private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2(v___x_7884_, v_hasTrace_7874_, v___x_7885_, v_options_7872_, v___x_7887_, v___y_7905_, v___f_7883_, v___x_7913_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_, v___y_7815_, v___y_7816_);
                v___y_7848_ = v___x_7914_;
                state = 6;
                continue;
            }
            14 => {
                v___x_7916_ = l___private_Lean_Util_Trace_0__Lean_getResetTraces___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__0___redArg(v___y_7816_);
                if leanh::lean_obj_tag(v___x_7916_) == 0 {
                    v_a_7917_ = leanh::lean_ctor_get(v___x_7916_, 0);
                    leanh::lean_inc(v_a_7917_);
                    leanh::lean_dec_ref_known(v___x_7916_, 1);
                    v___x_7918_ = l_Lean_trace_profiler_useHeartbeats;
                    v___x_7919_ =
                        l_Lean_Option_get___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__1(
                            v_options_7872_,
                            v___x_7918_,
                        );
                    if v___x_7919_ == 0 {
                        v___x_7920_ = lean_io_mono_nanos_now();
                        leanh::lean_inc_ref(v_e_7803_);
                        v___x_7921_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_7876_, v_e_7803_, v_snd_7828_, v_proc_7832_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_, v___y_7815_, v___y_7816_);
                        leanh::lean_dec(v_snd_7828_);
                        if leanh::lean_obj_tag(v___x_7921_) == 0 {
                            v_a_7922_ = leanh::lean_ctor_get(v___x_7921_, 0);
                            v_isSharedCheck_7929_ =
                                (!leanh::lean_is_exclusive(v___x_7921_)) as u8;
                            if v_isSharedCheck_7929_ == 0 {
                                v___x_7924_ = v___x_7921_;
                                v_isShared_7925_ = v_isSharedCheck_7929_;
                                state = 15;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7922_);
                                leanh::lean_dec(v___x_7921_);
                                v___x_7924_ = leanh::lean_box(0);
                                v_isShared_7925_ = v_isSharedCheck_7929_;
                                state = 15;
                                continue;
                            }
                        } else {
                            v_a_7930_ = leanh::lean_ctor_get(v___x_7921_, 0);
                            v_isSharedCheck_7937_ =
                                (!leanh::lean_is_exclusive(v___x_7921_)) as u8;
                            if v_isSharedCheck_7937_ == 0 {
                                v___x_7932_ = v___x_7921_;
                                v_isShared_7933_ = v_isSharedCheck_7937_;
                                state = 17;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7930_);
                                leanh::lean_dec(v___x_7921_);
                                v___x_7932_ = leanh::lean_box(0);
                                v_isShared_7933_ = v_isSharedCheck_7937_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        v___x_7938_ = lean_io_get_num_heartbeats();
                        leanh::lean_inc_ref(v_e_7803_);
                        v___x_7939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___lam__0(v___x_7876_, v_e_7803_, v_snd_7828_, v_proc_7832_, v___y_7808_, v___y_7809_, v___y_7810_, v___y_7811_, v___y_7812_, v___y_7813_, v___y_7814_, v___y_7815_, v___y_7816_);
                        leanh::lean_dec(v_snd_7828_);
                        if leanh::lean_obj_tag(v___x_7939_) == 0 {
                            v_a_7940_ = leanh::lean_ctor_get(v___x_7939_, 0);
                            v_isSharedCheck_7947_ =
                                (!leanh::lean_is_exclusive(v___x_7939_)) as u8;
                            if v_isSharedCheck_7947_ == 0 {
                                v___x_7942_ = v___x_7939_;
                                v_isShared_7943_ = v_isSharedCheck_7947_;
                                state = 19;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7940_);
                                leanh::lean_dec(v___x_7939_);
                                v___x_7942_ = leanh::lean_box(0);
                                v_isShared_7943_ = v_isSharedCheck_7947_;
                                state = 19;
                                continue;
                            }
                        } else {
                            v_a_7948_ = leanh::lean_ctor_get(v___x_7939_, 0);
                            v_isSharedCheck_7955_ =
                                (!leanh::lean_is_exclusive(v___x_7939_)) as u8;
                            if v_isSharedCheck_7955_ == 0 {
                                v___x_7950_ = v___x_7939_;
                                v_isShared_7951_ = v_isSharedCheck_7955_;
                                state = 21;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_7948_);
                                leanh::lean_dec(v___x_7939_);
                                v___x_7950_ = leanh::lean_box(0);
                                v_isShared_7951_ = v_isSharedCheck_7955_;
                                state = 21;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v___f_7883_);
                    leanh::lean_del_object(v___x_7834_);
                    leanh::lean_dec_ref(v_proc_7832_);
                    leanh::lean_del_object(v___x_7830_);
                    leanh::lean_dec(v_snd_7828_);
                    leanh::lean_dec_ref(v_e_7803_);
                    v_a_7956_ = leanh::lean_ctor_get(v___x_7916_, 0);
                    v_isSharedCheck_7963_ = (!leanh::lean_is_exclusive(v___x_7916_)) as u8;
                    if v_isSharedCheck_7963_ == 0 {
                        v___x_7958_ = v___x_7916_;
                        v_isShared_7959_ = v_isSharedCheck_7963_;
                        state = 23;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_7956_);
                        leanh::lean_dec(v___x_7916_);
                        v___x_7958_ = leanh::lean_box(0);
                        v_isShared_7959_ = v_isSharedCheck_7963_;
                        state = 23;
                        continue;
                    }
                }
            }
            15 => {
                if v_isShared_7925_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7924_, 1);
                    v___x_7927_ = v___x_7924_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_7928_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7928_, 0, v_a_7922_);
                    v___x_7927_ = v_reuseFailAlloc_7928_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                v___y_7889_ = v___x_7920_;
                v___y_7890_ = v_a_7917_;
                v_a_7891_ = v___x_7927_;
                state = 12;
                continue;
            }
            17 => {
                if v_isShared_7933_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7932_, 0);
                    v___x_7935_ = v___x_7932_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_7936_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7936_, 0, v_a_7930_);
                    v___x_7935_ = v_reuseFailAlloc_7936_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                v___y_7889_ = v___x_7920_;
                v___y_7890_ = v_a_7917_;
                v_a_7891_ = v___x_7935_;
                state = 12;
                continue;
            }
            19 => {
                if v_isShared_7943_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7942_, 1);
                    v___x_7945_ = v___x_7942_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_7946_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7946_, 0, v_a_7940_);
                    v___x_7945_ = v_reuseFailAlloc_7946_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                v___y_7904_ = v___x_7938_;
                v___y_7905_ = v_a_7917_;
                v_a_7906_ = v___x_7945_;
                state = 13;
                continue;
            }
            21 => {
                if v_isShared_7951_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_7950_, 0);
                    v___x_7953_ = v___x_7950_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_7954_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7954_, 0, v_a_7948_);
                    v___x_7953_ = v_reuseFailAlloc_7954_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                v___y_7904_ = v___x_7938_;
                v___y_7905_ = v_a_7917_;
                v_a_7906_ = v___x_7953_;
                state = 13;
                continue;
            }
            23 => {
                if v_isShared_7959_ == 0 {
                    v___x_7961_ = v___x_7958_;
                    state = 24;
                    continue;
                } else {
                    v_reuseFailAlloc_7962_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7962_, 0, v_a_7956_);
                    v___x_7961_ = v_reuseFailAlloc_7962_;
                    state = 24;
                    continue;
                }
            }
            24 => {
                return v___x_7961_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___boxed(
    mut v_erased_7971_: *mut leanh::LeanObject,
    mut v_e_7972_: *mut leanh::LeanObject,
    mut v_as_7973_: *mut leanh::LeanObject,
    mut v_sz_7974_: *mut leanh::LeanObject,
    mut v_i_7975_: *mut leanh::LeanObject,
    mut v_b_7976_: *mut leanh::LeanObject,
    mut v___y_7977_: *mut leanh::LeanObject,
    mut v___y_7978_: *mut leanh::LeanObject,
    mut v___y_7979_: *mut leanh::LeanObject,
    mut v___y_7980_: *mut leanh::LeanObject,
    mut v___y_7981_: *mut leanh::LeanObject,
    mut v___y_7982_: *mut leanh::LeanObject,
    mut v___y_7983_: *mut leanh::LeanObject,
    mut v___y_7984_: *mut leanh::LeanObject,
    mut v___y_7985_: *mut leanh::LeanObject,
    mut v___y_7986_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_7987_: usize = 0;
    let mut v_i_boxed_7988_: usize = 0;
    let mut v_res_7989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_7987_ = leanh::lean_unbox_usize(v_sz_7974_);
    leanh::lean_dec(v_sz_7974_);
    v_i_boxed_7988_ = leanh::lean_unbox_usize(v_i_7975_);
    leanh::lean_dec(v_i_7975_);
    v_res_7989_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_7971_, v_e_7972_, v_as_7973_, v_sz_boxed_7987_, v_i_boxed_7988_, v_b_7976_, v___y_7977_, v___y_7978_, v___y_7979_, v___y_7980_, v___y_7981_, v___y_7982_, v___y_7983_, v___y_7984_, v___y_7985_);
    leanh::lean_dec(v___y_7985_);
    leanh::lean_dec_ref(v___y_7984_);
    leanh::lean_dec(v___y_7983_);
    leanh::lean_dec_ref(v___y_7982_);
    leanh::lean_dec(v___y_7981_);
    leanh::lean_dec_ref(v___y_7980_);
    leanh::lean_dec(v___y_7979_);
    leanh::lean_dec_ref(v___y_7978_);
    leanh::lean_dec(v___y_7977_);
    leanh::lean_dec_ref(v_as_7973_);
    leanh::lean_dec_ref(v_erased_7971_);
    return v_res_7989_;
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(
    mut v_tree_7992_: *mut leanh::LeanObject,
    mut v_erased_7993_: *mut leanh::LeanObject,
    mut v_e_7994_: *mut leanh::LeanObject,
    mut v_a_7995_: *mut leanh::LeanObject,
    mut v_a_7996_: *mut leanh::LeanObject,
    mut v_a_7997_: *mut leanh::LeanObject,
    mut v_a_7998_: *mut leanh::LeanObject,
    mut v_a_7999_: *mut leanh::LeanObject,
    mut v_a_8000_: *mut leanh::LeanObject,
    mut v_a_8001_: *mut leanh::LeanObject,
    mut v_a_8002_: *mut leanh::LeanObject,
    mut v_a_8003_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_candidates_8005_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8006_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8007_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8008_: u8 = 0;
    let mut v___x_8009_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_8010_: usize = 0;
    let mut v___x_8011_: usize = 0;
    let mut v___x_8012_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_8013_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8015_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8016_: u8 = 0;
    let mut v_fst_8017_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8020_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_8022_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8026_: u8 = 0;
    let mut v_a_8027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_8030_: u8 = 0;
    let mut v___x_8032_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_8033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_8034_: u8 = 0;
    let mut v___x_8035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_8036_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_candidates_8005_ =
                    l_Lean_Meta_Sym_getMatchWithExtra___redArg(v_tree_7992_, v_e_7994_);
                v___x_8006_ = lean_array_get_size(v_candidates_8005_);
                v___x_8007_ = leanh::lean_unsigned_to_nat(0);
                v___x_8008_ = lean_nat_dec_eq(v___x_8006_, v___x_8007_);
                if v___x_8008_ == 0 {
                    v___x_8009_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3___closed__0;
                    v_sz_8010_ = lean_array_size(v_candidates_8005_);
                    v___x_8011_ = 0usize;
                    v___x_8012_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__3(v_erased_7993_, v_e_7994_, v_candidates_8005_, v_sz_8010_, v___x_8011_, v___x_8009_, v_a_7995_, v_a_7996_, v_a_7997_, v_a_7998_, v_a_7999_, v_a_8000_, v_a_8001_, v_a_8002_, v_a_8003_);
                    leanh::lean_dec_ref(v_candidates_8005_);
                    if leanh::lean_obj_tag(v___x_8012_) == 0 {
                        v_a_8013_ = leanh::lean_ctor_get(v___x_8012_, 0);
                        v_isSharedCheck_8026_ =
                            (!leanh::lean_is_exclusive(v___x_8012_)) as u8;
                        if v_isSharedCheck_8026_ == 0 {
                            v___x_8015_ = v___x_8012_;
                            v_isShared_8016_ = v_isSharedCheck_8026_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8013_);
                            leanh::lean_dec(v___x_8012_);
                            v___x_8015_ = leanh::lean_box(0);
                            v_isShared_8016_ = v_isSharedCheck_8026_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_8027_ = leanh::lean_ctor_get(v___x_8012_, 0);
                        v_isSharedCheck_8034_ =
                            (!leanh::lean_is_exclusive(v___x_8012_)) as u8;
                        if v_isSharedCheck_8034_ == 0 {
                            v___x_8029_ = v___x_8012_;
                            v_isShared_8030_ = v_isSharedCheck_8034_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_8027_);
                            leanh::lean_dec(v___x_8012_);
                            v___x_8029_ = leanh::lean_box(0);
                            v_isShared_8030_ = v_isSharedCheck_8034_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    leanh::lean_dec_ref(v_candidates_8005_);
                    leanh::lean_dec_ref(v_e_7994_);
                    v___x_8035_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___closed__0;
                    v___x_8036_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_8036_, 0, v___x_8035_);
                    return v___x_8036_;
                }
            }
            1 => {
                v_fst_8017_ = leanh::lean_ctor_get(v_a_8013_, 0);
                leanh::lean_inc(v_fst_8017_);
                leanh::lean_dec(v_a_8013_);
                if leanh::lean_obj_tag(v_fst_8017_) == 0 {
                    v___x_8018_ = leanh::lean_alloc_ctor(0, 0, (2) as u32);
                    leanh::lean_ctor_set_uint8(v___x_8018_, 0 as u32, v___x_8008_);
                    leanh::lean_ctor_set_uint8(v___x_8018_, 1 as u32, v___x_8008_);
                    if v_isShared_8016_ == 0 {
                        leanh::lean_ctor_set(v___x_8015_, 0, v___x_8018_);
                        v___x_8020_ = v___x_8015_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_8021_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8021_, 0, v___x_8018_);
                        v___x_8020_ = v_reuseFailAlloc_8021_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_val_8022_ = leanh::lean_ctor_get(v_fst_8017_, 0);
                    leanh::lean_inc(v_val_8022_);
                    leanh::lean_dec_ref_known(v_fst_8017_, 1);
                    if v_isShared_8016_ == 0 {
                        leanh::lean_ctor_set(v___x_8015_, 0, v_val_8022_);
                        v___x_8024_ = v___x_8015_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_8025_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_8025_, 0, v_val_8022_);
                        v___x_8024_ = v_reuseFailAlloc_8025_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_8020_;
            }
            3 => {
                return v___x_8024_;
            }
            4 => {
                if v_isShared_8030_ == 0 {
                    v___x_8032_ = v___x_8029_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_8033_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_8033_, 0, v_a_8027_);
                    v___x_8032_ = v_reuseFailAlloc_8033_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_8032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch___boxed(
    mut v_tree_8037_: *mut leanh::LeanObject,
    mut v_erased_8038_: *mut leanh::LeanObject,
    mut v_e_8039_: *mut leanh::LeanObject,
    mut v_a_8040_: *mut leanh::LeanObject,
    mut v_a_8041_: *mut leanh::LeanObject,
    mut v_a_8042_: *mut leanh::LeanObject,
    mut v_a_8043_: *mut leanh::LeanObject,
    mut v_a_8044_: *mut leanh::LeanObject,
    mut v_a_8045_: *mut leanh::LeanObject,
    mut v_a_8046_: *mut leanh::LeanObject,
    mut v_a_8047_: *mut leanh::LeanObject,
    mut v_a_8048_: *mut leanh::LeanObject,
    mut v_a_8049_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8050_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8050_ = l_Lean_Meta_Tactic_Cbv_cbvSimprocDispatch(
        v_tree_8037_,
        v_erased_8038_,
        v_e_8039_,
        v_a_8040_,
        v_a_8041_,
        v_a_8042_,
        v_a_8043_,
        v_a_8044_,
        v_a_8045_,
        v_a_8046_,
        v_a_8047_,
        v_a_8048_,
    );
    leanh::lean_dec(v_a_8048_);
    leanh::lean_dec_ref(v_a_8047_);
    leanh::lean_dec(v_a_8046_);
    leanh::lean_dec_ref(v_a_8045_);
    leanh::lean_dec(v_a_8044_);
    leanh::lean_dec_ref(v_a_8043_);
    leanh::lean_dec(v_a_8042_);
    leanh::lean_dec_ref(v_a_8041_);
    leanh::lean_dec(v_a_8040_);
    leanh::lean_dec_ref(v_erased_8038_);
    leanh::lean_dec_ref(v_tree_8037_);
    return v_res_8050_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(
    mut v_00_u03b1_8051_: *mut leanh::LeanObject,
    mut v_x_8052_: *mut leanh::LeanObject,
    mut v___y_8053_: *mut leanh::LeanObject,
    mut v___y_8054_: *mut leanh::LeanObject,
    mut v___y_8055_: *mut leanh::LeanObject,
    mut v___y_8056_: *mut leanh::LeanObject,
    mut v___y_8057_: *mut leanh::LeanObject,
    mut v___y_8058_: *mut leanh::LeanObject,
    mut v___y_8059_: *mut leanh::LeanObject,
    mut v___y_8060_: *mut leanh::LeanObject,
    mut v___y_8061_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8063_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8063_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___redArg(v_x_8052_);
    return v___x_8063_;
}
pub unsafe fn l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4___boxed(
    mut v_00_u03b1_8064_: *mut leanh::LeanObject,
    mut v_x_8065_: *mut leanh::LeanObject,
    mut v___y_8066_: *mut leanh::LeanObject,
    mut v___y_8067_: *mut leanh::LeanObject,
    mut v___y_8068_: *mut leanh::LeanObject,
    mut v___y_8069_: *mut leanh::LeanObject,
    mut v___y_8070_: *mut leanh::LeanObject,
    mut v___y_8071_: *mut leanh::LeanObject,
    mut v___y_8072_: *mut leanh::LeanObject,
    mut v___y_8073_: *mut leanh::LeanObject,
    mut v___y_8074_: *mut leanh::LeanObject,
    mut v___y_8075_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8076_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8076_ = l_MonadExcept_ofExcept___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__4(v_00_u03b1_8064_, v_x_8065_, v___y_8066_, v___y_8067_, v___y_8068_, v___y_8069_, v___y_8070_, v___y_8071_, v___y_8072_, v___y_8073_, v___y_8074_);
    leanh::lean_dec(v___y_8074_);
    leanh::lean_dec_ref(v___y_8073_);
    leanh::lean_dec(v___y_8072_);
    leanh::lean_dec_ref(v___y_8071_);
    leanh::lean_dec(v___y_8070_);
    leanh::lean_dec_ref(v___y_8069_);
    leanh::lean_dec(v___y_8068_);
    leanh::lean_dec_ref(v___y_8067_);
    leanh::lean_dec(v___y_8066_);
    return v_res_8076_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(
    mut v_oldTraces_8077_: *mut leanh::LeanObject,
    mut v_data_8078_: *mut leanh::LeanObject,
    mut v_ref_8079_: *mut leanh::LeanObject,
    mut v_msg_8080_: *mut leanh::LeanObject,
    mut v___y_8081_: *mut leanh::LeanObject,
    mut v___y_8082_: *mut leanh::LeanObject,
    mut v___y_8083_: *mut leanh::LeanObject,
    mut v___y_8084_: *mut leanh::LeanObject,
    mut v___y_8085_: *mut leanh::LeanObject,
    mut v___y_8086_: *mut leanh::LeanObject,
    mut v___y_8087_: *mut leanh::LeanObject,
    mut v___y_8088_: *mut leanh::LeanObject,
    mut v___y_8089_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_8091_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_8091_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___redArg(v_oldTraces_8077_, v_data_8078_, v_ref_8079_, v_msg_8080_, v___y_8086_, v___y_8087_, v___y_8088_, v___y_8089_);
    return v___x_8091_;
}
pub unsafe fn l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3___boxed(
    mut v_oldTraces_8092_: *mut leanh::LeanObject,
    mut v_data_8093_: *mut leanh::LeanObject,
    mut v_ref_8094_: *mut leanh::LeanObject,
    mut v_msg_8095_: *mut leanh::LeanObject,
    mut v___y_8096_: *mut leanh::LeanObject,
    mut v___y_8097_: *mut leanh::LeanObject,
    mut v___y_8098_: *mut leanh::LeanObject,
    mut v___y_8099_: *mut leanh::LeanObject,
    mut v___y_8100_: *mut leanh::LeanObject,
    mut v___y_8101_: *mut leanh::LeanObject,
    mut v___y_8102_: *mut leanh::LeanObject,
    mut v___y_8103_: *mut leanh::LeanObject,
    mut v___y_8104_: *mut leanh::LeanObject,
    mut v___y_8105_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_8106_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_8106_ = l___private_Lean_Util_Trace_0__Lean_addTraceNode___at___00__private_Lean_Util_Trace_0__Lean_withTraceNode_postCallback___at___00Lean_Meta_Tactic_Cbv_cbvSimprocDispatch_spec__2_spec__3(v_oldTraces_8092_, v_data_8093_, v_ref_8094_, v_msg_8095_, v___y_8096_, v___y_8097_, v___y_8098_, v___y_8099_, v___y_8100_, v___y_8101_, v___y_8102_, v___y_8103_, v___y_8104_);
    leanh::lean_dec(v___y_8104_);
    leanh::lean_dec_ref(v___y_8103_);
    leanh::lean_dec(v___y_8102_);
    leanh::lean_dec_ref(v___y_8101_);
    leanh::lean_dec(v___y_8100_);
    leanh::lean_dec_ref(v___y_8099_);
    leanh::lean_dec(v___y_8098_);
    leanh::lean_dec_ref(v___y_8097_);
    leanh::lean_dec(v___y_8096_);
    return v_res_8106_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase_default();
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocPhase();
    l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase =
        _init_l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instToExprCbvSimprocPhase);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs_default);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocs);
    l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs_default,
    );
    l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedBuiltinCbvSimprocs);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_404265556____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocDeclsRef);
    leanh::lean_dec_ref(res);
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default();
    leanh::lean_mark_persistent(
        l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState_default,
    );
    l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState =
        _init_l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState();
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_instInhabitedCbvSimprocDeclExtState);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_2237200659____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvSimprocDeclExt);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1269018163____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_builtinCbvSimprocsRef);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_1354732816____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension = leanh::lean_io_result_get_value(res);
    leanh::lean_mark_persistent(l_Lean_Meta_Tactic_Cbv_cbvSimprocExtension);
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_735115364____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = l___private_Lean_Meta_Tactic_Cbv_CbvSimproc_0__Lean_Meta_Tactic_Cbv_initFn_00___x40_Lean_Meta_Tactic_Cbv_CbvSimproc_3124561870____hygCtx___hyg_2_();
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Compiler_InitAttr(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_ScopedEnvExtension(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_Result(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_App(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Pattern(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Cbv_CbvSimproc(builtin);
}