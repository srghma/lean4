// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.OfNatModule
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Init.Grind.Module.OfNatModule Init.Grind.Module.NatModuleNorm Lean.Meta.Tactic.Grind.Diseq Lean.Meta.Tactic.Grind.Arith.Linear.ToExpr Init.Data.Nat.Order Init.Data.Order.Lemmas Lean.Data.RArray
use crate::r#gen::Init::Data::Nat::Order::{
    initialize_Init_Data_Nat_Order, runtime_initialize_Init_Data_Nat_Order,
};
use crate::r#gen::Init::Data::Order::Lemmas::{
    initialize_Init_Data_Order_Lemmas, runtime_initialize_Init_Data_Order_Lemmas,
};
use crate::r#gen::Init::Grind::Module::NatModuleNorm::{
    initialize_Init_Grind_Module_NatModuleNorm, l_Lean_Grind_Linarith_Expr_toPolyN,
    runtime_initialize_Init_Grind_Module_NatModuleNorm,
};
use crate::r#gen::Init::Grind::Module::OfNatModule::{
    initialize_Init_Grind_Module_OfNatModule, runtime_initialize_Init_Grind_Module_OfNatModule,
};
use crate::r#gen::Init::Grind::Ordered::Linarith::l_Lean_Grind_Linarith_instBEqPoly_beq;
use crate::r#gen::Lean::Data::PersistentHashMap::{
    l_Lean_PersistentHashMap_getCollisionNodeSize___redArg,
    l_Lean_PersistentHashMap_mkCollisionNode___redArg, l_Lean_PersistentHashMap_mkEmptyEntries,
};
use crate::r#gen::Lean::Data::RArray::{
    initialize_Lean_Data_RArray, l_Lean_RArray_ofFn___redArg, l_Lean_RArray_toExpr___redArg,
    runtime_initialize_Lean_Data_RArray,
};
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_app___override, l_Lean_Expr_appArg_x21, l_Lean_Expr_appFnCleanup___redArg,
    l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
    l_Lean_eagerReflBoolTrue, l_Lean_mkApp6, l_Lean_mkApp8, l_Lean_mkAppB, l_Lean_mkConst,
};
use crate::r#gen::Lean::Message::{l_Lean_indentExpr, l_Lean_stringToMessageData};
use crate::r#gen::Lean::Meta::AppBuilder::l_Lean_Meta_mkEqTrans;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_instantiateMVarsIfMVarApp___redArg, l_Lean_Meta_isDefEqD,
};
use crate::r#gen::Lean::Meta::LitValues::l_Lean_Meta_getNatValue_x3f;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Sym::SymM::{
    l_Lean_Meta_Sym_getConfig___redArg, l_Lean_Meta_Sym_reportIssue,
    l_Lean_Meta_Sym_shareCommon___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::ToExpr::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr,
    l_Lean_Meta_Grind_Arith_Linear_ofLinExpr,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::l_Lean_Meta_Grind_Arith_Linear_linearExt;
use crate::r#gen::Lean::Meta::Tactic::Grind::Diseq::{
    initialize_Lean_Meta_Tactic_Grind_Diseq, l_Lean_Meta_Grind_mkDiseqProof,
    runtime_initialize_Lean_Meta_Tactic_Grind_Diseq,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg,
    l_Lean_Meta_Grind_SolverExtension_markTerm___redArg, l_Lean_Meta_Grind_closeGoal,
};
use crate::lean_imports_rs::Init::Data::Array::Basic::{
    lean_array_uget_borrowed, lean_array_uset, lean_mk_array,
};
use crate::lean_imports_rs::Init::Data::Array::Set::lean_array_fset;
use crate::lean_imports_rs::Init::Data::UInt::Basic::{
    lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor, lean_usize_land,
    lean_usize_mul, lean_usize_shift_left, lean_usize_shift_right,
};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_le, lean_usize_of_nat, lean_usize_sub, lean_usize_to_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget, lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size,
    lean_array_push, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div,
    lean_nat_mul,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_preprocess;
pub static l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value:
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
        96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101, 114,
        114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 110, 97, 116, 83, 116, 114,
        117, 99, 116, 73, 100, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed
        as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 0,
    m_objs: [],
};
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value)
        as *mut crate::leanh::LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0_value:
    crate::leanh::LeanStringObject<69> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 69,
    m_capacity: 69,
    m_length: 68,
    m_data: [
        101, 120, 112, 114, 101, 115, 115, 105, 111, 110, 32, 105, 110, 32, 116, 119, 111, 32, 100,
        105, 102, 102, 101, 114, 101, 110, 116, 32, 110, 97, 116, 32, 109, 111, 100, 117, 108, 101,
        32, 115, 116, 114, 117, 99, 116, 117, 114, 101, 115, 32, 105, 110, 32, 108, 105, 110, 97,
        114, 105, 116, 104, 32, 109, 111, 100, 117, 108, 101, 0,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0_value
) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once:
    crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value) as *mut crate::leanh::LeanObject,18263865437487147968 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value) as *mut crate::leanh::LeanObject,2651253468108498348 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [72, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value) as *mut crate::leanh::LeanObject,15703084674812832738 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value) as *mut crate::leanh::LeanObject,13609749952674037527 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 102, 78, 97, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 100, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut crate::leanh::LeanObject,7605204649477761179 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut crate::leanh::LeanObject,11314908490917688650 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value) as *mut crate::leanh::LeanObject,5371214753348010468 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value: crate::leanh::LeanStringObject<11> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 109, 117, 108, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut crate::leanh::LeanObject,7605204649477761179 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut crate::leanh::LeanObject,11314908490917688650 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value) as *mut crate::leanh::LeanObject,15786333914169958476 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value: crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 81, 95, 122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut crate::leanh::LeanObject,7605204649477761179 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut crate::leanh::LeanObject,11314908490917688650 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value) as *mut crate::leanh::LeanObject,17599150304417000063 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value: crate::leanh::LeanArrayObject<0> = crate::leanh::LeanArrayObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [76, 105, 110, 97, 114, 105, 116, 104, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value:
    crate::leanh::LeanStringObject<9> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 9,
    m_capacity: 9,
    m_length: 8,
    m_data: [101, 113, 95, 110, 111, 114, 109, 78, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value
) as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value
        ) as *mut crate::leanh::LeanObject,
        17349746425441669063 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value:
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
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2
        ) as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value
        ) as *mut crate::leanh::LeanObject,
        13692448015376392830 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2:
    *mut crate::leanh::LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value
) as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value:
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
    m_fun: l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0:
    *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(
    mut v_natStructId_2197_: *mut crate::leanh::LeanObject,
    mut v_x_2198_: *mut crate::leanh::LeanObject,
    mut v_a_2199_: *mut crate::leanh::LeanObject,
    mut v_a_2200_: *mut crate::leanh::LeanObject,
    mut v_a_2201_: *mut crate::leanh::LeanObject,
    mut v_a_2202_: *mut crate::leanh::LeanObject,
    mut v_a_2203_: *mut crate::leanh::LeanObject,
    mut v_a_2204_: *mut crate::leanh::LeanObject,
    mut v_a_2205_: *mut crate::leanh::LeanObject,
    mut v_a_2206_: *mut crate::leanh::LeanObject,
    mut v_a_2207_: *mut crate::leanh::LeanObject,
    mut v_a_2208_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2208_);
    crate::leanh::lean_inc_ref(v_a_2207_);
    crate::leanh::lean_inc(v_a_2206_);
    crate::leanh::lean_inc_ref(v_a_2205_);
    crate::leanh::lean_inc(v_a_2204_);
    crate::leanh::lean_inc_ref(v_a_2203_);
    crate::leanh::lean_inc(v_a_2202_);
    crate::leanh::lean_inc_ref(v_a_2201_);
    crate::leanh::lean_inc(v_a_2200_);
    crate::leanh::lean_inc(v_a_2199_);
    v___x_2210_ = crate::leanh::lean_apply_12(
        v_x_2198_,
        v_natStructId_2197_,
        v_a_2199_,
        v_a_2200_,
        v_a_2201_,
        v_a_2202_,
        v_a_2203_,
        v_a_2204_,
        v_a_2205_,
        v_a_2206_,
        v_a_2207_,
        v_a_2208_,
        crate::leanh::lean_box(0),
    );
    return v___x_2210_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(
    mut v_natStructId_2211_: *mut crate::leanh::LeanObject,
    mut v_x_2212_: *mut crate::leanh::LeanObject,
    mut v_a_2213_: *mut crate::leanh::LeanObject,
    mut v_a_2214_: *mut crate::leanh::LeanObject,
    mut v_a_2215_: *mut crate::leanh::LeanObject,
    mut v_a_2216_: *mut crate::leanh::LeanObject,
    mut v_a_2217_: *mut crate::leanh::LeanObject,
    mut v_a_2218_: *mut crate::leanh::LeanObject,
    mut v_a_2219_: *mut crate::leanh::LeanObject,
    mut v_a_2220_: *mut crate::leanh::LeanObject,
    mut v_a_2221_: *mut crate::leanh::LeanObject,
    mut v_a_2222_: *mut crate::leanh::LeanObject,
    mut v_a_2223_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2224_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2224_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(
        v_natStructId_2211_,
        v_x_2212_,
        v_a_2213_,
        v_a_2214_,
        v_a_2215_,
        v_a_2216_,
        v_a_2217_,
        v_a_2218_,
        v_a_2219_,
        v_a_2220_,
        v_a_2221_,
        v_a_2222_,
    );
    crate::leanh::lean_dec(v_a_2222_);
    crate::leanh::lean_dec_ref(v_a_2221_);
    crate::leanh::lean_dec(v_a_2220_);
    crate::leanh::lean_dec_ref(v_a_2219_);
    crate::leanh::lean_dec(v_a_2218_);
    crate::leanh::lean_dec_ref(v_a_2217_);
    crate::leanh::lean_dec(v_a_2216_);
    crate::leanh::lean_dec_ref(v_a_2215_);
    crate::leanh::lean_dec(v_a_2214_);
    crate::leanh::lean_dec(v_a_2213_);
    return v_res_2224_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(
    mut v_00_u03b1_2225_: *mut crate::leanh::LeanObject,
    mut v_natStructId_2226_: *mut crate::leanh::LeanObject,
    mut v_x_2227_: *mut crate::leanh::LeanObject,
    mut v_a_2228_: *mut crate::leanh::LeanObject,
    mut v_a_2229_: *mut crate::leanh::LeanObject,
    mut v_a_2230_: *mut crate::leanh::LeanObject,
    mut v_a_2231_: *mut crate::leanh::LeanObject,
    mut v_a_2232_: *mut crate::leanh::LeanObject,
    mut v_a_2233_: *mut crate::leanh::LeanObject,
    mut v_a_2234_: *mut crate::leanh::LeanObject,
    mut v_a_2235_: *mut crate::leanh::LeanObject,
    mut v_a_2236_: *mut crate::leanh::LeanObject,
    mut v_a_2237_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2237_);
    crate::leanh::lean_inc_ref(v_a_2236_);
    crate::leanh::lean_inc(v_a_2235_);
    crate::leanh::lean_inc_ref(v_a_2234_);
    crate::leanh::lean_inc(v_a_2233_);
    crate::leanh::lean_inc_ref(v_a_2232_);
    crate::leanh::lean_inc(v_a_2231_);
    crate::leanh::lean_inc_ref(v_a_2230_);
    crate::leanh::lean_inc(v_a_2229_);
    crate::leanh::lean_inc(v_a_2228_);
    v___x_2239_ = crate::leanh::lean_apply_12(
        v_x_2227_,
        v_natStructId_2226_,
        v_a_2228_,
        v_a_2229_,
        v_a_2230_,
        v_a_2231_,
        v_a_2232_,
        v_a_2233_,
        v_a_2234_,
        v_a_2235_,
        v_a_2236_,
        v_a_2237_,
        crate::leanh::lean_box(0),
    );
    return v___x_2239_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(
    mut v_00_u03b1_2240_: *mut crate::leanh::LeanObject,
    mut v_natStructId_2241_: *mut crate::leanh::LeanObject,
    mut v_x_2242_: *mut crate::leanh::LeanObject,
    mut v_a_2243_: *mut crate::leanh::LeanObject,
    mut v_a_2244_: *mut crate::leanh::LeanObject,
    mut v_a_2245_: *mut crate::leanh::LeanObject,
    mut v_a_2246_: *mut crate::leanh::LeanObject,
    mut v_a_2247_: *mut crate::leanh::LeanObject,
    mut v_a_2248_: *mut crate::leanh::LeanObject,
    mut v_a_2249_: *mut crate::leanh::LeanObject,
    mut v_a_2250_: *mut crate::leanh::LeanObject,
    mut v_a_2251_: *mut crate::leanh::LeanObject,
    mut v_a_2252_: *mut crate::leanh::LeanObject,
    mut v_a_2253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2254_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(
        v_00_u03b1_2240_,
        v_natStructId_2241_,
        v_x_2242_,
        v_a_2243_,
        v_a_2244_,
        v_a_2245_,
        v_a_2246_,
        v_a_2247_,
        v_a_2248_,
        v_a_2249_,
        v_a_2250_,
        v_a_2251_,
        v_a_2252_,
    );
    crate::leanh::lean_dec(v_a_2252_);
    crate::leanh::lean_dec_ref(v_a_2251_);
    crate::leanh::lean_dec(v_a_2250_);
    crate::leanh::lean_dec_ref(v_a_2249_);
    crate::leanh::lean_dec(v_a_2248_);
    crate::leanh::lean_dec_ref(v_a_2247_);
    crate::leanh::lean_dec(v_a_2246_);
    crate::leanh::lean_dec_ref(v_a_2245_);
    crate::leanh::lean_dec(v_a_2244_);
    crate::leanh::lean_dec(v_a_2243_);
    return v_res_2254_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(
    mut v_a_2255_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2255_);
    v___x_2257_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2257_, 0, v_a_2255_);
    return v___x_2257_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg___boxed(
    mut v_a_2258_: *mut crate::leanh::LeanObject,
    mut v_a_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(v_a_2258_);
    crate::leanh::lean_dec(v_a_2258_);
    return v_res_2260_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId(
    mut v_a_2261_: *mut crate::leanh::LeanObject,
    mut v_a_2262_: *mut crate::leanh::LeanObject,
    mut v_a_2263_: *mut crate::leanh::LeanObject,
    mut v_a_2264_: *mut crate::leanh::LeanObject,
    mut v_a_2265_: *mut crate::leanh::LeanObject,
    mut v_a_2266_: *mut crate::leanh::LeanObject,
    mut v_a_2267_: *mut crate::leanh::LeanObject,
    mut v_a_2268_: *mut crate::leanh::LeanObject,
    mut v_a_2269_: *mut crate::leanh::LeanObject,
    mut v_a_2270_: *mut crate::leanh::LeanObject,
    mut v_a_2271_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2261_);
    v___x_2273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2273_, 0, v_a_2261_);
    return v___x_2273_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId___boxed(
    mut v_a_2274_: *mut crate::leanh::LeanObject,
    mut v_a_2275_: *mut crate::leanh::LeanObject,
    mut v_a_2276_: *mut crate::leanh::LeanObject,
    mut v_a_2277_: *mut crate::leanh::LeanObject,
    mut v_a_2278_: *mut crate::leanh::LeanObject,
    mut v_a_2279_: *mut crate::leanh::LeanObject,
    mut v_a_2280_: *mut crate::leanh::LeanObject,
    mut v_a_2281_: *mut crate::leanh::LeanObject,
    mut v_a_2282_: *mut crate::leanh::LeanObject,
    mut v_a_2283_: *mut crate::leanh::LeanObject,
    mut v_a_2284_: *mut crate::leanh::LeanObject,
    mut v_a_2285_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId(
        v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_,
        v_a_2282_, v_a_2283_, v_a_2284_,
    );
    crate::leanh::lean_dec(v_a_2284_);
    crate::leanh::lean_dec_ref(v_a_2283_);
    crate::leanh::lean_dec(v_a_2282_);
    crate::leanh::lean_dec_ref(v_a_2281_);
    crate::leanh::lean_dec(v_a_2280_);
    crate::leanh::lean_dec_ref(v_a_2279_);
    crate::leanh::lean_dec(v_a_2278_);
    crate::leanh::lean_dec_ref(v_a_2277_);
    crate::leanh::lean_dec(v_a_2276_);
    crate::leanh::lean_dec(v_a_2275_);
    crate::leanh::lean_dec(v_a_2274_);
    return v_res_2286_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(
    mut v_msgData_2287_: *mut crate::leanh::LeanObject,
    mut v___y_2288_: *mut crate::leanh::LeanObject,
    mut v___y_2289_: *mut crate::leanh::LeanObject,
    mut v___y_2290_: *mut crate::leanh::LeanObject,
    mut v___y_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_env_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_mctx_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_options_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2293_ = lean_st_ref_get(v___y_2291_);
    v_env_2294_ = crate::leanh::lean_ctor_get(v___x_2293_, 0);
    crate::leanh::lean_inc_ref(v_env_2294_);
    crate::leanh::lean_dec(v___x_2293_);
    v___x_2295_ = lean_st_ref_get(v___y_2289_);
    v_mctx_2296_ = crate::leanh::lean_ctor_get(v___x_2295_, 0);
    crate::leanh::lean_inc_ref(v_mctx_2296_);
    crate::leanh::lean_dec(v___x_2295_);
    v_lctx_2297_ = crate::leanh::lean_ctor_get(v___y_2288_, 2);
    v_options_2298_ = crate::leanh::lean_ctor_get(v___y_2290_, 2);
    crate::leanh::lean_inc_ref(v_options_2298_);
    crate::leanh::lean_inc_ref(v_lctx_2297_);
    v___x_2299_ = crate::leanh::lean_alloc_ctor(0, 4, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2299_, 0, v_env_2294_);
    crate::leanh::lean_ctor_set(v___x_2299_, 1, v_mctx_2296_);
    crate::leanh::lean_ctor_set(v___x_2299_, 2, v_lctx_2297_);
    crate::leanh::lean_ctor_set(v___x_2299_, 3, v_options_2298_);
    v___x_2300_ = crate::leanh::lean_alloc_ctor(3, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2300_, 0, v___x_2299_);
    crate::leanh::lean_ctor_set(v___x_2300_, 1, v_msgData_2287_);
    v___x_2301_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(
    mut v_msgData_2302_: *mut crate::leanh::LeanObject,
    mut v___y_2303_: *mut crate::leanh::LeanObject,
    mut v___y_2304_: *mut crate::leanh::LeanObject,
    mut v___y_2305_: *mut crate::leanh::LeanObject,
    mut v___y_2306_: *mut crate::leanh::LeanObject,
    mut v___y_2307_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2308_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msgData_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
    crate::leanh::lean_dec(v___y_2306_);
    crate::leanh::lean_dec_ref(v___y_2305_);
    crate::leanh::lean_dec(v___y_2304_);
    crate::leanh::lean_dec_ref(v___y_2303_);
    return v_res_2308_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(
    mut v_msg_2309_: *mut crate::leanh::LeanObject,
    mut v___y_2310_: *mut crate::leanh::LeanObject,
    mut v___y_2311_: *mut crate::leanh::LeanObject,
    mut v___y_2312_: *mut crate::leanh::LeanObject,
    mut v___y_2313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ref_2315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2320_: u8 = 0;
    let mut v___x_2321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2315_ = crate::leanh::lean_ctor_get(v___y_2312_, 5);
                v___x_2316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                v_a_2317_ = crate::leanh::lean_ctor_get(v___x_2316_, 0);
                v_isSharedCheck_2325_ = (!crate::leanh::lean_is_exclusive(v___x_2316_)) as u8;
                if v_isSharedCheck_2325_ == 0 {
                    v___x_2319_ = v___x_2316_;
                    v_isShared_2320_ = v_isSharedCheck_2325_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_a_2317_);
                    crate::leanh::lean_dec(v___x_2316_);
                    v___x_2319_ = crate::leanh::lean_box(0);
                    v_isShared_2320_ = v_isSharedCheck_2325_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_ref_2315_);
                v___x_2321_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2321_, 0, v_ref_2315_);
                crate::leanh::lean_ctor_set(v___x_2321_, 1, v_a_2317_);
                if v_isShared_2320_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_2319_, 1);
                    crate::leanh::lean_ctor_set(v___x_2319_, 0, v___x_2321_);
                    v___x_2323_ = v___x_2319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2324_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
                    v___x_2323_ = v_reuseFailAlloc_2324_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2323_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg___boxed(
    mut v_msg_2326_: *mut crate::leanh::LeanObject,
    mut v___y_2327_: *mut crate::leanh::LeanObject,
    mut v___y_2328_: *mut crate::leanh::LeanObject,
    mut v___y_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2332_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(
            v_msg_2326_,
            v___y_2327_,
            v___y_2328_,
            v___y_2329_,
            v___y_2330_,
        );
    crate::leanh::lean_dec(v___y_2330_);
    crate::leanh::lean_dec_ref(v___y_2329_);
    crate::leanh::lean_dec(v___y_2328_);
    crate::leanh::lean_dec_ref(v___y_2327_);
    return v_res_2332_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2334_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0;
    v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
    mut v_a_2336_: *mut crate::leanh::LeanObject,
    mut v_a_2337_: *mut crate::leanh::LeanObject,
    mut v_a_2338_: *mut crate::leanh::LeanObject,
    mut v_a_2339_: *mut crate::leanh::LeanObject,
    mut v_a_2340_: *mut crate::leanh::LeanObject,
    mut v_a_2341_: *mut crate::leanh::LeanObject,
    mut v_a_2342_: *mut crate::leanh::LeanObject,
    mut v_a_2343_: *mut crate::leanh::LeanObject,
    mut v_a_2344_: *mut crate::leanh::LeanObject,
    mut v_a_2345_: *mut crate::leanh::LeanObject,
    mut v_a_2346_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v_natStructs_2353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v_a_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2348_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_2337_, v_a_2345_);
                if crate::leanh::lean_obj_tag(v___x_2348_) == 0 {
                    v_a_2349_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                    v_isSharedCheck_2362_ = (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2362_ == 0 {
                        v___x_2351_ = v___x_2348_;
                        v_isShared_2352_ = v_isSharedCheck_2362_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2349_);
                        crate::leanh::lean_dec(v___x_2348_);
                        v___x_2351_ = crate::leanh::lean_box(0);
                        v_isShared_2352_ = v_isSharedCheck_2362_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2363_ = crate::leanh::lean_ctor_get(v___x_2348_, 0);
                    v_isSharedCheck_2370_ = (!crate::leanh::lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2365_ = v___x_2348_;
                        v_isShared_2366_ = v_isSharedCheck_2370_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2363_);
                        crate::leanh::lean_dec(v___x_2348_);
                        v___x_2365_ = crate::leanh::lean_box(0);
                        v_isShared_2366_ = v_isSharedCheck_2370_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_natStructs_2353_ = crate::leanh::lean_ctor_get(v_a_2349_, 5);
                crate::leanh::lean_inc_ref(v_natStructs_2353_);
                crate::leanh::lean_dec(v_a_2349_);
                v___x_2354_ = lean_array_get_size(v_natStructs_2353_);
                v___x_2355_ = lean_nat_dec_lt(v_a_2336_, v___x_2354_);
                if v___x_2355_ == 0 {
                    crate::leanh::lean_dec_ref(v_natStructs_2353_);
                    crate::leanh::lean_del_object(v___x_2351_);
                    v___x_2356_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1
                        ),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1,
                    );
                    v___x_2357_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(v___x_2356_, v_a_2343_, v_a_2344_, v_a_2345_, v_a_2346_);
                    return v___x_2357_;
                } else {
                    v___x_2358_ = lean_array_fget(v_natStructs_2353_, v_a_2336_);
                    crate::leanh::lean_dec_ref(v_natStructs_2353_);
                    if v_isShared_2352_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2351_, 0, v___x_2358_);
                        v___x_2360_ = v___x_2351_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2361_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
                        v___x_2360_ = v_reuseFailAlloc_2361_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2360_;
            }
            3 => {
                if v_isShared_2366_ == 0 {
                    v___x_2368_ = v___x_2365_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2369_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
                    v___x_2368_ = v_reuseFailAlloc_2369_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2368_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStruct___boxed(
    mut v_a_2371_: *mut crate::leanh::LeanObject,
    mut v_a_2372_: *mut crate::leanh::LeanObject,
    mut v_a_2373_: *mut crate::leanh::LeanObject,
    mut v_a_2374_: *mut crate::leanh::LeanObject,
    mut v_a_2375_: *mut crate::leanh::LeanObject,
    mut v_a_2376_: *mut crate::leanh::LeanObject,
    mut v_a_2377_: *mut crate::leanh::LeanObject,
    mut v_a_2378_: *mut crate::leanh::LeanObject,
    mut v_a_2379_: *mut crate::leanh::LeanObject,
    mut v_a_2380_: *mut crate::leanh::LeanObject,
    mut v_a_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
        v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_,
        v_a_2379_, v_a_2380_, v_a_2381_,
    );
    crate::leanh::lean_dec(v_a_2381_);
    crate::leanh::lean_dec_ref(v_a_2380_);
    crate::leanh::lean_dec(v_a_2379_);
    crate::leanh::lean_dec_ref(v_a_2378_);
    crate::leanh::lean_dec(v_a_2377_);
    crate::leanh::lean_dec_ref(v_a_2376_);
    crate::leanh::lean_dec(v_a_2375_);
    crate::leanh::lean_dec_ref(v_a_2374_);
    crate::leanh::lean_dec(v_a_2373_);
    crate::leanh::lean_dec(v_a_2372_);
    crate::leanh::lean_dec(v_a_2371_);
    return v_res_2383_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(
    mut v_00_u03b1_2384_: *mut crate::leanh::LeanObject,
    mut v_msg_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
    mut v___y_2391_: *mut crate::leanh::LeanObject,
    mut v___y_2392_: *mut crate::leanh::LeanObject,
    mut v___y_2393_: *mut crate::leanh::LeanObject,
    mut v___y_2394_: *mut crate::leanh::LeanObject,
    mut v___y_2395_: *mut crate::leanh::LeanObject,
    mut v___y_2396_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2398_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(
            v_msg_2385_,
            v___y_2393_,
            v___y_2394_,
            v___y_2395_,
            v___y_2396_,
        );
    return v___x_2398_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___boxed(
    mut v_00_u03b1_2399_: *mut crate::leanh::LeanObject,
    mut v_msg_2400_: *mut crate::leanh::LeanObject,
    mut v___y_2401_: *mut crate::leanh::LeanObject,
    mut v___y_2402_: *mut crate::leanh::LeanObject,
    mut v___y_2403_: *mut crate::leanh::LeanObject,
    mut v___y_2404_: *mut crate::leanh::LeanObject,
    mut v___y_2405_: *mut crate::leanh::LeanObject,
    mut v___y_2406_: *mut crate::leanh::LeanObject,
    mut v___y_2407_: *mut crate::leanh::LeanObject,
    mut v___y_2408_: *mut crate::leanh::LeanObject,
    mut v___y_2409_: *mut crate::leanh::LeanObject,
    mut v___y_2410_: *mut crate::leanh::LeanObject,
    mut v___y_2411_: *mut crate::leanh::LeanObject,
    mut v___y_2412_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2413_ = l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(
        v_00_u03b1_2399_,
        v_msg_2400_,
        v___y_2401_,
        v___y_2402_,
        v___y_2403_,
        v___y_2404_,
        v___y_2405_,
        v___y_2406_,
        v___y_2407_,
        v___y_2408_,
        v___y_2409_,
        v___y_2410_,
        v___y_2411_,
    );
    crate::leanh::lean_dec(v___y_2411_);
    crate::leanh::lean_dec_ref(v___y_2410_);
    crate::leanh::lean_dec(v___y_2409_);
    crate::leanh::lean_dec_ref(v___y_2408_);
    crate::leanh::lean_dec(v___y_2407_);
    crate::leanh::lean_dec_ref(v___y_2406_);
    crate::leanh::lean_dec(v___y_2405_);
    crate::leanh::lean_dec_ref(v___y_2404_);
    crate::leanh::lean_dec(v___y_2403_);
    crate::leanh::lean_dec(v___y_2402_);
    crate::leanh::lean_dec(v___y_2401_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(
    mut v_a_2414_: *mut crate::leanh::LeanObject,
    mut v_a_2415_: *mut crate::leanh::LeanObject,
    mut v_a_2416_: *mut crate::leanh::LeanObject,
    mut v_a_2417_: *mut crate::leanh::LeanObject,
    mut v_a_2418_: *mut crate::leanh::LeanObject,
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_a_2420_: *mut crate::leanh::LeanObject,
    mut v_a_2421_: *mut crate::leanh::LeanObject,
    mut v_a_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
    mut v_a_2424_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structId_2428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2426_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_,
                    v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_,
                );
                if crate::leanh::lean_obj_tag(v___x_2426_) == 0 {
                    v_a_2427_ = crate::leanh::lean_ctor_get(v___x_2426_, 0);
                    crate::leanh::lean_inc(v_a_2427_);
                    crate::leanh::lean_dec_ref_known(v___x_2426_, 1);
                    v_structId_2428_ = crate::leanh::lean_ctor_get(v_a_2427_, 1);
                    crate::leanh::lean_inc(v_structId_2428_);
                    crate::leanh::lean_dec(v_a_2427_);
                    v___x_2429_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                        v_structId_2428_,
                        v_a_2415_,
                        v_a_2416_,
                        v_a_2417_,
                        v_a_2418_,
                        v_a_2419_,
                        v_a_2420_,
                        v_a_2421_,
                        v_a_2422_,
                        v_a_2423_,
                        v_a_2424_,
                    );
                    crate::leanh::lean_dec(v_structId_2428_);
                    return v___x_2429_;
                } else {
                    v_a_2430_ = crate::leanh::lean_ctor_get(v___x_2426_, 0);
                    v_isSharedCheck_2437_ = (!crate::leanh::lean_is_exclusive(v___x_2426_)) as u8;
                    if v_isSharedCheck_2437_ == 0 {
                        v___x_2432_ = v___x_2426_;
                        v_isShared_2433_ = v_isSharedCheck_2437_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2430_);
                        crate::leanh::lean_dec(v___x_2426_);
                        v___x_2432_ = crate::leanh::lean_box(0);
                        v_isShared_2433_ = v_isSharedCheck_2437_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2433_ == 0 {
                    v___x_2435_ = v___x_2432_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2436_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
                    v___x_2435_ = v_reuseFailAlloc_2436_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2435_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed(
    mut v_a_2438_: *mut crate::leanh::LeanObject,
    mut v_a_2439_: *mut crate::leanh::LeanObject,
    mut v_a_2440_: *mut crate::leanh::LeanObject,
    mut v_a_2441_: *mut crate::leanh::LeanObject,
    mut v_a_2442_: *mut crate::leanh::LeanObject,
    mut v_a_2443_: *mut crate::leanh::LeanObject,
    mut v_a_2444_: *mut crate::leanh::LeanObject,
    mut v_a_2445_: *mut crate::leanh::LeanObject,
    mut v_a_2446_: *mut crate::leanh::LeanObject,
    mut v_a_2447_: *mut crate::leanh::LeanObject,
    mut v_a_2448_: *mut crate::leanh::LeanObject,
    mut v_a_2449_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2450_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(
        v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_,
        v_a_2446_, v_a_2447_, v_a_2448_,
    );
    crate::leanh::lean_dec(v_a_2448_);
    crate::leanh::lean_dec_ref(v_a_2447_);
    crate::leanh::lean_dec(v_a_2446_);
    crate::leanh::lean_dec_ref(v_a_2445_);
    crate::leanh::lean_dec(v_a_2444_);
    crate::leanh::lean_dec_ref(v_a_2443_);
    crate::leanh::lean_dec(v_a_2442_);
    crate::leanh::lean_dec_ref(v_a_2441_);
    crate::leanh::lean_dec(v_a_2440_);
    crate::leanh::lean_dec(v_a_2439_);
    crate::leanh::lean_dec(v_a_2438_);
    return v_res_2450_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(
    mut v_a_2452_: *mut crate::leanh::LeanObject,
    mut v_f_2453_: *mut crate::leanh::LeanObject,
    mut v_s_2454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_2461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u8 = 0;
    let mut v___x_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v_v_2468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v_unused_2477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_2484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2455_ = crate::leanh::lean_ctor_get(v_s_2454_, 0);
                v_typeIdOf_2456_ = crate::leanh::lean_ctor_get(v_s_2454_, 1);
                v_exprToStructId_2457_ = crate::leanh::lean_ctor_get(v_s_2454_, 2);
                v_exprToStructIdEntries_2458_ = crate::leanh::lean_ctor_get(v_s_2454_, 3);
                v_forbiddenNatModules_2459_ = crate::leanh::lean_ctor_get(v_s_2454_, 4);
                v_natStructs_2460_ = crate::leanh::lean_ctor_get(v_s_2454_, 5);
                v_natTypeIdOf_2461_ = crate::leanh::lean_ctor_get(v_s_2454_, 6);
                v_exprToNatStructId_2462_ = crate::leanh::lean_ctor_get(v_s_2454_, 7);
                v___x_2463_ = lean_array_get_size(v_natStructs_2460_);
                v___x_2464_ = lean_nat_dec_lt(v_a_2452_, v___x_2463_);
                if v___x_2464_ == 0 {
                    crate::leanh::lean_dec_ref(v_f_2453_);
                    return v_s_2454_;
                } else {
                    crate::leanh::lean_inc_ref(v_exprToNatStructId_2462_);
                    crate::leanh::lean_inc_ref(v_natTypeIdOf_2461_);
                    crate::leanh::lean_inc_ref(v_natStructs_2460_);
                    crate::leanh::lean_inc_ref(v_forbiddenNatModules_2459_);
                    crate::leanh::lean_inc_ref(v_exprToStructIdEntries_2458_);
                    crate::leanh::lean_inc_ref(v_exprToStructId_2457_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_2456_);
                    crate::leanh::lean_inc_ref(v_structs_2455_);
                    v_isSharedCheck_2476_ = (!crate::leanh::lean_is_exclusive(v_s_2454_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v_unused_2477_ = crate::leanh::lean_ctor_get(v_s_2454_, 7);
                        crate::leanh::lean_dec(v_unused_2477_);
                        v_unused_2478_ = crate::leanh::lean_ctor_get(v_s_2454_, 6);
                        crate::leanh::lean_dec(v_unused_2478_);
                        v_unused_2479_ = crate::leanh::lean_ctor_get(v_s_2454_, 5);
                        crate::leanh::lean_dec(v_unused_2479_);
                        v_unused_2480_ = crate::leanh::lean_ctor_get(v_s_2454_, 4);
                        crate::leanh::lean_dec(v_unused_2480_);
                        v_unused_2481_ = crate::leanh::lean_ctor_get(v_s_2454_, 3);
                        crate::leanh::lean_dec(v_unused_2481_);
                        v_unused_2482_ = crate::leanh::lean_ctor_get(v_s_2454_, 2);
                        crate::leanh::lean_dec(v_unused_2482_);
                        v_unused_2483_ = crate::leanh::lean_ctor_get(v_s_2454_, 1);
                        crate::leanh::lean_dec(v_unused_2483_);
                        v_unused_2484_ = crate::leanh::lean_ctor_get(v_s_2454_, 0);
                        crate::leanh::lean_dec(v_unused_2484_);
                        v___x_2466_ = v_s_2454_;
                        v_isShared_2467_ = v_isSharedCheck_2476_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_2454_);
                        v___x_2466_ = crate::leanh::lean_box(0);
                        v_isShared_2467_ = v_isSharedCheck_2476_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2468_ = lean_array_fget(v_natStructs_2460_, v_a_2452_);
                v___x_2469_ = crate::leanh::lean_box(0);
                v_xs_x27_2470_ = lean_array_fset(v_natStructs_2460_, v_a_2452_, v___x_2469_);
                v___x_2471_ = crate::leanh::lean_apply_1(v_f_2453_, v_v_2468_);
                v___x_2472_ = lean_array_fset(v_xs_x27_2470_, v_a_2452_, v___x_2471_);
                if v_isShared_2467_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2466_, 5, v___x_2472_);
                    v___x_2474_ = v___x_2466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2475_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_structs_2455_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_typeIdOf_2456_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_exprToStructId_2457_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2475_,
                        3,
                        v_exprToStructIdEntries_2458_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2475_,
                        4,
                        v_forbiddenNatModules_2459_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 5, v___x_2472_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2475_, 6, v_natTypeIdOf_2461_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2475_,
                        7,
                        v_exprToNatStructId_2462_,
                    );
                    v___x_2474_ = v_reuseFailAlloc_2475_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2474_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed(
    mut v_a_2485_: *mut crate::leanh::LeanObject,
    mut v_f_2486_: *mut crate::leanh::LeanObject,
    mut v_s_2487_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2488_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(
        v_a_2485_, v_f_2486_, v_s_2487_,
    );
    crate::leanh::lean_dec(v_a_2485_);
    return v_res_2488_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(
    mut v_f_2489_: *mut crate::leanh::LeanObject,
    mut v_a_2490_: *mut crate::leanh::LeanObject,
    mut v_a_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2490_);
    v___f_2493_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2493_, 0, v_a_2490_);
    crate::leanh::lean_closure_set(v___f_2493_, 1, v_f_2489_);
    v___x_2494_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_2495_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2494_, v___f_2493_, v_a_2491_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(
    mut v_f_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
    mut v_a_2498_: *mut crate::leanh::LeanObject,
    mut v_a_2499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2500_ =
        l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(v_f_2496_, v_a_2497_, v_a_2498_);
    crate::leanh::lean_dec(v_a_2498_);
    crate::leanh::lean_dec(v_a_2497_);
    return v_res_2500_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(
    mut v_f_2501_: *mut crate::leanh::LeanObject,
    mut v_a_2502_: *mut crate::leanh::LeanObject,
    mut v_a_2503_: *mut crate::leanh::LeanObject,
    mut v_a_2504_: *mut crate::leanh::LeanObject,
    mut v_a_2505_: *mut crate::leanh::LeanObject,
    mut v_a_2506_: *mut crate::leanh::LeanObject,
    mut v_a_2507_: *mut crate::leanh::LeanObject,
    mut v_a_2508_: *mut crate::leanh::LeanObject,
    mut v_a_2509_: *mut crate::leanh::LeanObject,
    mut v_a_2510_: *mut crate::leanh::LeanObject,
    mut v_a_2511_: *mut crate::leanh::LeanObject,
    mut v_a_2512_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    crate::leanh::lean_inc(v_a_2502_);
    v___f_2514_ = crate::leanh::lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    crate::leanh::lean_closure_set(v___f_2514_, 0, v_a_2502_);
    crate::leanh::lean_closure_set(v___f_2514_, 1, v_f_2501_);
    v___x_2515_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_2516_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2515_, v___f_2514_, v_a_2503_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(
    mut v_f_2517_: *mut crate::leanh::LeanObject,
    mut v_a_2518_: *mut crate::leanh::LeanObject,
    mut v_a_2519_: *mut crate::leanh::LeanObject,
    mut v_a_2520_: *mut crate::leanh::LeanObject,
    mut v_a_2521_: *mut crate::leanh::LeanObject,
    mut v_a_2522_: *mut crate::leanh::LeanObject,
    mut v_a_2523_: *mut crate::leanh::LeanObject,
    mut v_a_2524_: *mut crate::leanh::LeanObject,
    mut v_a_2525_: *mut crate::leanh::LeanObject,
    mut v_a_2526_: *mut crate::leanh::LeanObject,
    mut v_a_2527_: *mut crate::leanh::LeanObject,
    mut v_a_2528_: *mut crate::leanh::LeanObject,
    mut v_a_2529_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(
        v_f_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_,
        v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_,
    );
    crate::leanh::lean_dec(v_a_2528_);
    crate::leanh::lean_dec_ref(v_a_2527_);
    crate::leanh::lean_dec(v_a_2526_);
    crate::leanh::lean_dec_ref(v_a_2525_);
    crate::leanh::lean_dec(v_a_2524_);
    crate::leanh::lean_dec_ref(v_a_2523_);
    crate::leanh::lean_dec(v_a_2522_);
    crate::leanh::lean_dec_ref(v_a_2521_);
    crate::leanh::lean_dec(v_a_2520_);
    crate::leanh::lean_dec(v_a_2519_);
    crate::leanh::lean_dec(v_a_2518_);
    return v_res_2530_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2531_: *mut crate::leanh::LeanObject,
    mut v_vals_2532_: *mut crate::leanh::LeanObject,
    mut v_i_2533_: *mut crate::leanh::LeanObject,
    mut v_k_2534_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2535_ = lean_array_get_size(v_keys_2531_);
                v___x_2536_ = lean_nat_dec_lt(v_i_2533_, v___x_2535_);
                if v___x_2536_ == 0 {
                    crate::leanh::lean_dec(v_i_2533_);
                    v___x_2537_ = crate::leanh::lean_box(0);
                    return v___x_2537_;
                } else {
                    v_k_x27_2538_ = lean_array_fget_borrowed(v_keys_2531_, v_i_2533_);
                    v___x_2539_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2534_,
                            v_k_x27_2538_,
                        );
                    if v___x_2539_ == 0 {
                        v___x_2540_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2541_ = lean_nat_add(v_i_2533_, v___x_2540_);
                        crate::leanh::lean_dec(v_i_2533_);
                        v_i_2533_ = v___x_2541_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2543_ = lean_array_fget_borrowed(v_vals_2532_, v_i_2533_);
                        crate::leanh::lean_dec(v_i_2533_);
                        crate::leanh::lean_inc(v___x_2543_);
                        v___x_2544_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2544_, 0, v___x_2543_);
                        return v___x_2544_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2545_: *mut crate::leanh::LeanObject,
    mut v_vals_2546_: *mut crate::leanh::LeanObject,
    mut v_i_2547_: *mut crate::leanh::LeanObject,
    mut v_k_2548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2549_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2545_, v_vals_2546_, v_i_2547_, v_k_2548_);
    crate::leanh::lean_dec_ref(v_k_2548_);
    crate::leanh::lean_dec_ref(v_vals_2546_);
    crate::leanh::lean_dec_ref(v_keys_2545_);
    return v_res_2549_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2550_: usize = 0;
    let mut v___x_2551_: usize = 0;
    let mut v___x_2552_: usize = 0;
    v___x_2550_ = 5usize;
    v___x_2551_ = 1usize;
    v___x_2552_ = lean_usize_shift_left(v___x_2551_, v___x_2550_);
    return v___x_2552_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2553_: usize = 0;
    let mut v___x_2554_: usize = 0;
    let mut v___x_2555_: usize = 0;
    v___x_2553_ = 1usize;
    v___x_2554_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_2555_ = lean_usize_sub(v___x_2554_, v___x_2553_);
    return v___x_2555_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(
    mut v_x_2556_: *mut crate::leanh::LeanObject,
    mut v_x_2557_: usize,
    mut v_x_2558_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: usize = 0;
    let mut v___x_2562_: usize = 0;
    let mut v___x_2563_: usize = 0;
    let mut v_j_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: usize = 0;
    let mut v___x_2574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2556_) == 0 {
                    v_es_2559_ = crate::leanh::lean_ctor_get(v_x_2556_, 0);
                    v___x_2560_ = crate::leanh::lean_box(2);
                    v___x_2561_ = 5usize;
                    v___x_2562_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_2563_ = lean_usize_land(v_x_2557_, v___x_2562_);
                    v_j_2564_ = lean_usize_to_nat(v___x_2563_);
                    v___x_2565_ = lean_array_get_borrowed(v___x_2560_, v_es_2559_, v_j_2564_);
                    crate::leanh::lean_dec(v_j_2564_);
                    match crate::leanh::lean_obj_tag(v___x_2565_) {
                        0 => {
                            v_key_2566_ = crate::leanh::lean_ctor_get(v___x_2565_, 0);
                            v_val_2567_ = crate::leanh::lean_ctor_get(v___x_2565_, 1);
                            v___x_2568_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2558_, v_key_2566_);
                            if v___x_2568_ == 0 {
                                v___x_2569_ = crate::leanh::lean_box(0);
                                return v___x_2569_;
                            } else {
                                crate::leanh::lean_inc(v_val_2567_);
                                v___x_2570_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2570_, 0, v_val_2567_);
                                return v___x_2570_;
                            }
                        }
                        1 => {
                            v_node_2571_ = crate::leanh::lean_ctor_get(v___x_2565_, 0);
                            v___x_2572_ = lean_usize_shift_right(v_x_2557_, v___x_2561_);
                            v_x_2556_ = v_node_2571_;
                            v_x_2557_ = v___x_2572_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2574_ = crate::leanh::lean_box(0);
                            return v___x_2574_;
                        }
                    }
                } else {
                    v_ks_2575_ = crate::leanh::lean_ctor_get(v_x_2556_, 0);
                    v_vs_2576_ = crate::leanh::lean_ctor_get(v_x_2556_, 1);
                    v___x_2577_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2578_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2575_, v_vs_2576_, v___x_2577_, v_x_2558_);
                    return v___x_2578_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2579_: *mut crate::leanh::LeanObject,
    mut v_x_2580_: *mut crate::leanh::LeanObject,
    mut v_x_2581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_867__boxed_2582_: usize = 0;
    let mut v_res_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_867__boxed_2582_ = crate::leanh::lean_unbox_usize(v_x_2580_);
    crate::leanh::lean_dec(v_x_2580_);
    v_res_2583_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_2579_, v_x_867__boxed_2582_, v_x_2581_);
    crate::leanh::lean_dec_ref(v_x_2581_);
    crate::leanh::lean_dec_ref(v_x_2579_);
    return v_res_2583_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(
    mut v_x_2584_: *mut crate::leanh::LeanObject,
    mut v_x_2585_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2586_: u64 = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2585_);
    v___x_2587_ = lean_uint64_to_usize(v___x_2586_);
    v___x_2588_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_2584_, v___x_2587_, v_x_2585_);
    return v___x_2588_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(
    mut v_x_2589_: *mut crate::leanh::LeanObject,
    mut v_x_2590_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2591_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_2589_, v_x_2590_);
    crate::leanh::lean_dec_ref(v_x_2590_);
    crate::leanh::lean_dec_ref(v_x_2589_);
    return v_res_2591_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
    mut v_e_2592_: *mut crate::leanh::LeanObject,
    mut v_a_2593_: *mut crate::leanh::LeanObject,
    mut v_a_2594_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v_exprToNatStructId_2601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v_a_2607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2596_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_2593_, v_a_2594_);
                if crate::leanh::lean_obj_tag(v___x_2596_) == 0 {
                    v_a_2597_ = crate::leanh::lean_ctor_get(v___x_2596_, 0);
                    v_isSharedCheck_2606_ = (!crate::leanh::lean_is_exclusive(v___x_2596_)) as u8;
                    if v_isSharedCheck_2606_ == 0 {
                        v___x_2599_ = v___x_2596_;
                        v_isShared_2600_ = v_isSharedCheck_2606_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2597_);
                        crate::leanh::lean_dec(v___x_2596_);
                        v___x_2599_ = crate::leanh::lean_box(0);
                        v_isShared_2600_ = v_isSharedCheck_2606_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2607_ = crate::leanh::lean_ctor_get(v___x_2596_, 0);
                    v_isSharedCheck_2614_ = (!crate::leanh::lean_is_exclusive(v___x_2596_)) as u8;
                    if v_isSharedCheck_2614_ == 0 {
                        v___x_2609_ = v___x_2596_;
                        v_isShared_2610_ = v_isSharedCheck_2614_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2607_);
                        crate::leanh::lean_dec(v___x_2596_);
                        v___x_2609_ = crate::leanh::lean_box(0);
                        v_isShared_2610_ = v_isSharedCheck_2614_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToNatStructId_2601_ = crate::leanh::lean_ctor_get(v_a_2597_, 7);
                crate::leanh::lean_inc_ref(v_exprToNatStructId_2601_);
                crate::leanh::lean_dec(v_a_2597_);
                v___x_2602_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_exprToNatStructId_2601_, v_e_2592_);
                crate::leanh::lean_dec_ref(v_exprToNatStructId_2601_);
                if v_isShared_2600_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2599_, 0, v___x_2602_);
                    v___x_2604_ = v___x_2599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
                    v___x_2604_ = v_reuseFailAlloc_2605_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2604_;
            }
            3 => {
                if v_isShared_2610_ == 0 {
                    v___x_2612_ = v___x_2609_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
                    v___x_2612_ = v_reuseFailAlloc_2613_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2612_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg___boxed(
    mut v_e_2615_: *mut crate::leanh::LeanObject,
    mut v_a_2616_: *mut crate::leanh::LeanObject,
    mut v_a_2617_: *mut crate::leanh::LeanObject,
    mut v_a_2618_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2619_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
        v_e_2615_, v_a_2616_, v_a_2617_,
    );
    crate::leanh::lean_dec_ref(v_a_2617_);
    crate::leanh::lean_dec(v_a_2616_);
    crate::leanh::lean_dec_ref(v_e_2615_);
    return v_res_2619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(
    mut v_e_2620_: *mut crate::leanh::LeanObject,
    mut v_a_2621_: *mut crate::leanh::LeanObject,
    mut v_a_2622_: *mut crate::leanh::LeanObject,
    mut v_a_2623_: *mut crate::leanh::LeanObject,
    mut v_a_2624_: *mut crate::leanh::LeanObject,
    mut v_a_2625_: *mut crate::leanh::LeanObject,
    mut v_a_2626_: *mut crate::leanh::LeanObject,
    mut v_a_2627_: *mut crate::leanh::LeanObject,
    mut v_a_2628_: *mut crate::leanh::LeanObject,
    mut v_a_2629_: *mut crate::leanh::LeanObject,
    mut v_a_2630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2632_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
        v_e_2620_, v_a_2621_, v_a_2629_,
    );
    return v___x_2632_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(
    mut v_e_2633_: *mut crate::leanh::LeanObject,
    mut v_a_2634_: *mut crate::leanh::LeanObject,
    mut v_a_2635_: *mut crate::leanh::LeanObject,
    mut v_a_2636_: *mut crate::leanh::LeanObject,
    mut v_a_2637_: *mut crate::leanh::LeanObject,
    mut v_a_2638_: *mut crate::leanh::LeanObject,
    mut v_a_2639_: *mut crate::leanh::LeanObject,
    mut v_a_2640_: *mut crate::leanh::LeanObject,
    mut v_a_2641_: *mut crate::leanh::LeanObject,
    mut v_a_2642_: *mut crate::leanh::LeanObject,
    mut v_a_2643_: *mut crate::leanh::LeanObject,
    mut v_a_2644_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2645_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(
        v_e_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_,
        v_a_2641_, v_a_2642_, v_a_2643_,
    );
    crate::leanh::lean_dec(v_a_2643_);
    crate::leanh::lean_dec_ref(v_a_2642_);
    crate::leanh::lean_dec(v_a_2641_);
    crate::leanh::lean_dec_ref(v_a_2640_);
    crate::leanh::lean_dec(v_a_2639_);
    crate::leanh::lean_dec_ref(v_a_2638_);
    crate::leanh::lean_dec(v_a_2637_);
    crate::leanh::lean_dec_ref(v_a_2636_);
    crate::leanh::lean_dec(v_a_2635_);
    crate::leanh::lean_dec(v_a_2634_);
    crate::leanh::lean_dec_ref(v_e_2633_);
    return v_res_2645_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(
    mut v_00_u03b2_2646_: *mut crate::leanh::LeanObject,
    mut v_x_2647_: *mut crate::leanh::LeanObject,
    mut v_x_2648_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2649_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_2647_, v_x_2648_);
    return v___x_2649_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(
    mut v_00_u03b2_2650_: *mut crate::leanh::LeanObject,
    mut v_x_2651_: *mut crate::leanh::LeanObject,
    mut v_x_2652_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2653_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(v_00_u03b2_2650_, v_x_2651_, v_x_2652_);
    crate::leanh::lean_dec_ref(v_x_2652_);
    crate::leanh::lean_dec_ref(v_x_2651_);
    return v_res_2653_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(
    mut v_00_u03b2_2654_: *mut crate::leanh::LeanObject,
    mut v_x_2655_: *mut crate::leanh::LeanObject,
    mut v_x_2656_: usize,
    mut v_x_2657_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_2655_, v_x_2656_, v_x_2657_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2659_: *mut crate::leanh::LeanObject,
    mut v_x_2660_: *mut crate::leanh::LeanObject,
    mut v_x_2661_: *mut crate::leanh::LeanObject,
    mut v_x_2662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_984__boxed_2663_: usize = 0;
    let mut v_res_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_984__boxed_2663_ = crate::leanh::lean_unbox_usize(v_x_2661_);
    crate::leanh::lean_dec(v_x_2661_);
    v_res_2664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(v_00_u03b2_2659_, v_x_2660_, v_x_984__boxed_2663_, v_x_2662_);
    crate::leanh::lean_dec_ref(v_x_2662_);
    crate::leanh::lean_dec_ref(v_x_2660_);
    return v_res_2664_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2665_: *mut crate::leanh::LeanObject,
    mut v_keys_2666_: *mut crate::leanh::LeanObject,
    mut v_vals_2667_: *mut crate::leanh::LeanObject,
    mut v_heq_2668_: *mut crate::leanh::LeanObject,
    mut v_i_2669_: *mut crate::leanh::LeanObject,
    mut v_k_2670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2671_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2666_, v_vals_2667_, v_i_2669_, v_k_2670_);
    return v___x_2671_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2672_: *mut crate::leanh::LeanObject,
    mut v_keys_2673_: *mut crate::leanh::LeanObject,
    mut v_vals_2674_: *mut crate::leanh::LeanObject,
    mut v_heq_2675_: *mut crate::leanh::LeanObject,
    mut v_i_2676_: *mut crate::leanh::LeanObject,
    mut v_k_2677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2672_, v_keys_2673_, v_vals_2674_, v_heq_2675_, v_i_2676_, v_k_2677_);
    crate::leanh::lean_dec_ref(v_k_2677_);
    crate::leanh::lean_dec_ref(v_vals_2674_);
    crate::leanh::lean_dec_ref(v_keys_2673_);
    return v_res_2678_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(
    mut v_a_2679_: *mut crate::leanh::LeanObject,
    mut v_b_2680_: *mut crate::leanh::LeanObject,
    mut v_a_2681_: *mut crate::leanh::LeanObject,
    mut v_a_2682_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v_val_2689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v_val_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v___x_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2684_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
                    v_a_2679_, v_a_2681_, v_a_2682_,
                );
                if crate::leanh::lean_obj_tag(v___x_2684_) == 0 {
                    v_a_2685_ = crate::leanh::lean_ctor_get(v___x_2684_, 0);
                    v_isSharedCheck_2713_ = (!crate::leanh::lean_is_exclusive(v___x_2684_)) as u8;
                    if v_isSharedCheck_2713_ == 0 {
                        v___x_2687_ = v___x_2684_;
                        v_isShared_2688_ = v_isSharedCheck_2713_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2685_);
                        crate::leanh::lean_dec(v___x_2684_);
                        v___x_2687_ = crate::leanh::lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2713_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2684_;
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2685_) == 1 {
                    crate::leanh::lean_del_object(v___x_2687_);
                    v_val_2689_ = crate::leanh::lean_ctor_get(v_a_2685_, 0);
                    v___x_2690_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
                        v_b_2680_, v_a_2681_, v_a_2682_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_2690_) == 0 {
                        v_a_2691_ = crate::leanh::lean_ctor_get(v___x_2690_, 0);
                        v_isSharedCheck_2708_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2690_)) as u8;
                        if v_isSharedCheck_2708_ == 0 {
                            v___x_2693_ = v___x_2690_;
                            v_isShared_2694_ = v_isSharedCheck_2708_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2691_);
                            crate::leanh::lean_dec(v___x_2690_);
                            v___x_2693_ = crate::leanh::lean_box(0);
                            v_isShared_2694_ = v_isSharedCheck_2708_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref_known(v_a_2685_, 1);
                        return v___x_2690_;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2685_);
                    v___x_2709_ = crate::leanh::lean_box(0);
                    if v_isShared_2688_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2687_, 0, v___x_2709_);
                        v___x_2711_ = v___x_2687_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2712_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
                        v___x_2711_ = v_reuseFailAlloc_2712_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2691_) == 1 {
                    v_val_2695_ = crate::leanh::lean_ctor_get(v_a_2691_, 0);
                    crate::leanh::lean_inc(v_val_2695_);
                    crate::leanh::lean_dec_ref_known(v_a_2691_, 1);
                    v___x_2696_ = lean_nat_dec_eq(v_val_2689_, v_val_2695_);
                    crate::leanh::lean_dec(v_val_2695_);
                    if v___x_2696_ == 0 {
                        crate::leanh::lean_dec_ref_known(v_a_2685_, 1);
                        v___x_2697_ = crate::leanh::lean_box(0);
                        if v_isShared_2694_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2693_, 0, v___x_2697_);
                            v___x_2699_ = v___x_2693_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2700_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
                            v___x_2699_ = v_reuseFailAlloc_2700_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2694_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2693_, 0, v_a_2685_);
                            v___x_2702_ = v___x_2693_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2703_ =
                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2685_);
                            v___x_2702_ = v_reuseFailAlloc_2703_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v_a_2691_);
                    crate::leanh::lean_dec_ref_known(v_a_2685_, 1);
                    v___x_2704_ = crate::leanh::lean_box(0);
                    if v_isShared_2694_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2693_, 0, v___x_2704_);
                        v___x_2706_ = v___x_2693_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2707_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
                        v___x_2706_ = v_reuseFailAlloc_2707_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_2699_;
            }
            4 => {
                return v___x_2702_;
            }
            5 => {
                return v___x_2706_;
            }
            6 => {
                return v___x_2711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg___boxed(
    mut v_a_2714_: *mut crate::leanh::LeanObject,
    mut v_b_2715_: *mut crate::leanh::LeanObject,
    mut v_a_2716_: *mut crate::leanh::LeanObject,
    mut v_a_2717_: *mut crate::leanh::LeanObject,
    mut v_a_2718_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(
        v_a_2714_, v_b_2715_, v_a_2716_, v_a_2717_,
    );
    crate::leanh::lean_dec_ref(v_a_2717_);
    crate::leanh::lean_dec(v_a_2716_);
    crate::leanh::lean_dec_ref(v_b_2715_);
    crate::leanh::lean_dec_ref(v_a_2714_);
    return v_res_2719_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(
    mut v_a_2720_: *mut crate::leanh::LeanObject,
    mut v_b_2721_: *mut crate::leanh::LeanObject,
    mut v_a_2722_: *mut crate::leanh::LeanObject,
    mut v_a_2723_: *mut crate::leanh::LeanObject,
    mut v_a_2724_: *mut crate::leanh::LeanObject,
    mut v_a_2725_: *mut crate::leanh::LeanObject,
    mut v_a_2726_: *mut crate::leanh::LeanObject,
    mut v_a_2727_: *mut crate::leanh::LeanObject,
    mut v_a_2728_: *mut crate::leanh::LeanObject,
    mut v_a_2729_: *mut crate::leanh::LeanObject,
    mut v_a_2730_: *mut crate::leanh::LeanObject,
    mut v_a_2731_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(
        v_a_2720_, v_b_2721_, v_a_2722_, v_a_2730_,
    );
    return v___x_2733_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(
    mut v_a_2734_: *mut crate::leanh::LeanObject,
    mut v_b_2735_: *mut crate::leanh::LeanObject,
    mut v_a_2736_: *mut crate::leanh::LeanObject,
    mut v_a_2737_: *mut crate::leanh::LeanObject,
    mut v_a_2738_: *mut crate::leanh::LeanObject,
    mut v_a_2739_: *mut crate::leanh::LeanObject,
    mut v_a_2740_: *mut crate::leanh::LeanObject,
    mut v_a_2741_: *mut crate::leanh::LeanObject,
    mut v_a_2742_: *mut crate::leanh::LeanObject,
    mut v_a_2743_: *mut crate::leanh::LeanObject,
    mut v_a_2744_: *mut crate::leanh::LeanObject,
    mut v_a_2745_: *mut crate::leanh::LeanObject,
    mut v_a_2746_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2747_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(
        v_a_2734_, v_b_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_,
        v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_,
    );
    crate::leanh::lean_dec(v_a_2745_);
    crate::leanh::lean_dec_ref(v_a_2744_);
    crate::leanh::lean_dec(v_a_2743_);
    crate::leanh::lean_dec_ref(v_a_2742_);
    crate::leanh::lean_dec(v_a_2741_);
    crate::leanh::lean_dec_ref(v_a_2740_);
    crate::leanh::lean_dec(v_a_2739_);
    crate::leanh::lean_dec_ref(v_a_2738_);
    crate::leanh::lean_dec(v_a_2737_);
    crate::leanh::lean_dec(v_a_2736_);
    crate::leanh::lean_dec_ref(v_b_2735_);
    crate::leanh::lean_dec_ref(v_a_2734_);
    return v_res_2747_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2748_: *mut crate::leanh::LeanObject,
    mut v_x_2749_: *mut crate::leanh::LeanObject,
    mut v_x_2750_: *mut crate::leanh::LeanObject,
    mut v_x_2751_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_ks_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: u8 = 0;
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2752_ = crate::leanh::lean_ctor_get(v_x_2748_, 0);
                v_vs_2753_ = crate::leanh::lean_ctor_get(v_x_2748_, 1);
                v_isSharedCheck_2777_ = (!crate::leanh::lean_is_exclusive(v_x_2748_)) as u8;
                if v_isSharedCheck_2777_ == 0 {
                    v___x_2755_ = v_x_2748_;
                    v_isShared_2756_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_vs_2753_);
                    crate::leanh::lean_inc(v_ks_2752_);
                    crate::leanh::lean_dec(v_x_2748_);
                    v___x_2755_ = crate::leanh::lean_box(0);
                    v_isShared_2756_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2757_ = lean_array_get_size(v_ks_2752_);
                v___x_2758_ = lean_nat_dec_lt(v_x_2749_, v___x_2757_);
                if v___x_2758_ == 0 {
                    crate::leanh::lean_dec(v_x_2749_);
                    v___x_2759_ = lean_array_push(v_ks_2752_, v_x_2750_);
                    v___x_2760_ = lean_array_push(v_vs_2753_, v_x_2751_);
                    if v_isShared_2756_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2755_, 1, v___x_2760_);
                        crate::leanh::lean_ctor_set(v___x_2755_, 0, v___x_2759_);
                        v___x_2762_ = v___x_2755_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2763_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2759_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2760_);
                        v___x_2762_ = v_reuseFailAlloc_2763_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_k_x27_2764_ = lean_array_fget_borrowed(v_ks_2752_, v_x_2749_);
                    v___x_2765_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_x_2750_,
                            v_k_x27_2764_,
                        );
                    if v___x_2765_ == 0 {
                        if v_isShared_2756_ == 0 {
                            v___x_2767_ = v___x_2755_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2771_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_ks_2752_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_vs_2753_);
                            v___x_2767_ = v_reuseFailAlloc_2771_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2772_ = lean_array_fset(v_ks_2752_, v_x_2749_, v_x_2750_);
                        v___x_2773_ = lean_array_fset(v_vs_2753_, v_x_2749_, v_x_2751_);
                        crate::leanh::lean_dec(v_x_2749_);
                        if v_isShared_2756_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_2755_, 1, v___x_2773_);
                            crate::leanh::lean_ctor_set(v___x_2755_, 0, v___x_2772_);
                            v___x_2775_ = v___x_2755_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2776_ =
                                crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___x_2773_);
                            v___x_2775_ = v_reuseFailAlloc_2776_;
                            state = 4;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2762_;
            }
            3 => {
                v___x_2768_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_2769_ = lean_nat_add(v_x_2749_, v___x_2768_);
                crate::leanh::lean_dec(v_x_2749_);
                v_x_2748_ = v___x_2767_;
                v_x_2749_ = v___x_2769_;
                state = 0;
                continue;
            }
            4 => {
                return v___x_2775_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(
    mut v_n_2778_: *mut crate::leanh::LeanObject,
    mut v_k_2779_: *mut crate::leanh::LeanObject,
    mut v_v_2780_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2781_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2782_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2778_, v___x_2781_, v_k_2779_, v_v_2780_);
    return v___x_2782_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2783_ = l_Lean_PersistentHashMap_mkEmptyEntries(
        crate::leanh::lean_box(0),
        crate::leanh::lean_box(0),
    );
    return v___x_2783_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(
    mut v_x_2784_: *mut crate::leanh::LeanObject,
    mut v_x_2785_: usize,
    mut v_x_2786_: usize,
    mut v_x_2787_: *mut crate::leanh::LeanObject,
    mut v_x_2788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: usize = 0;
    let mut v___x_2791_: usize = 0;
    let mut v___x_2792_: usize = 0;
    let mut v___x_2793_: usize = 0;
    let mut v_j_2794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v_v_2800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_node_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2825_: usize = 0;
    let mut v___x_2826_: usize = 0;
    let mut v___x_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v___x_2832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut v_unused_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_newNode_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: u8 = 0;
    let mut v_ks_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: usize = 0;
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    let mut v_reuseFailAlloc_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2784_) == 0 {
                    v_es_2789_ = crate::leanh::lean_ctor_get(v_x_2784_, 0);
                    v___x_2790_ = 5usize;
                    v___x_2791_ = 1usize;
                    v___x_2792_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_2793_ = lean_usize_land(v_x_2785_, v___x_2792_);
                    v_j_2794_ = lean_usize_to_nat(v___x_2793_);
                    v___x_2795_ = lean_array_get_size(v_es_2789_);
                    v___x_2796_ = lean_nat_dec_lt(v_j_2794_, v___x_2795_);
                    if v___x_2796_ == 0 {
                        crate::leanh::lean_dec(v_j_2794_);
                        crate::leanh::lean_dec(v_x_2788_);
                        crate::leanh::lean_dec_ref(v_x_2787_);
                        return v_x_2784_;
                    } else {
                        crate::leanh::lean_inc_ref(v_es_2789_);
                        v_isSharedCheck_2833_ = (!crate::leanh::lean_is_exclusive(v_x_2784_)) as u8;
                        if v_isSharedCheck_2833_ == 0 {
                            v_unused_2834_ = crate::leanh::lean_ctor_get(v_x_2784_, 0);
                            crate::leanh::lean_dec(v_unused_2834_);
                            v___x_2798_ = v_x_2784_;
                            v_isShared_2799_ = v_isSharedCheck_2833_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_x_2784_);
                            v___x_2798_ = crate::leanh::lean_box(0);
                            v_isShared_2799_ = v_isSharedCheck_2833_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2835_ = crate::leanh::lean_ctor_get(v_x_2784_, 0);
                    v_vs_2836_ = crate::leanh::lean_ctor_get(v_x_2784_, 1);
                    v_isSharedCheck_2856_ = (!crate::leanh::lean_is_exclusive(v_x_2784_)) as u8;
                    if v_isSharedCheck_2856_ == 0 {
                        v___x_2838_ = v_x_2784_;
                        v_isShared_2839_ = v_isSharedCheck_2856_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vs_2836_);
                        crate::leanh::lean_inc(v_ks_2835_);
                        crate::leanh::lean_dec(v_x_2784_);
                        v___x_2838_ = crate::leanh::lean_box(0);
                        v_isShared_2839_ = v_isSharedCheck_2856_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2800_ = lean_array_fget(v_es_2789_, v_j_2794_);
                v___x_2801_ = crate::leanh::lean_box(0);
                v_xs_x27_2802_ = lean_array_fset(v_es_2789_, v_j_2794_, v___x_2801_);
                match crate::leanh::lean_obj_tag(v_v_2800_) {
                    0 => {
                        v_key_2809_ = crate::leanh::lean_ctor_get(v_v_2800_, 0);
                        v_val_2810_ = crate::leanh::lean_ctor_get(v_v_2800_, 1);
                        v_isSharedCheck_2820_ = (!crate::leanh::lean_is_exclusive(v_v_2800_)) as u8;
                        if v_isSharedCheck_2820_ == 0 {
                            v___x_2812_ = v_v_2800_;
                            v_isShared_2813_ = v_isSharedCheck_2820_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_2810_);
                            crate::leanh::lean_inc(v_key_2809_);
                            crate::leanh::lean_dec(v_v_2800_);
                            v___x_2812_ = crate::leanh::lean_box(0);
                            v_isShared_2813_ = v_isSharedCheck_2820_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2821_ = crate::leanh::lean_ctor_get(v_v_2800_, 0);
                        v_isSharedCheck_2831_ = (!crate::leanh::lean_is_exclusive(v_v_2800_)) as u8;
                        if v_isSharedCheck_2831_ == 0 {
                            v___x_2823_ = v_v_2800_;
                            v_isShared_2824_ = v_isSharedCheck_2831_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_node_2821_);
                            crate::leanh::lean_dec(v_v_2800_);
                            v___x_2823_ = crate::leanh::lean_box(0);
                            v_isShared_2824_ = v_isSharedCheck_2831_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2832_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2832_, 0, v_x_2787_);
                        crate::leanh::lean_ctor_set(v___x_2832_, 1, v_x_2788_);
                        v___y_2804_ = v___x_2832_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2805_ = lean_array_fset(v_xs_x27_2802_, v_j_2794_, v___y_2804_);
                crate::leanh::lean_dec(v_j_2794_);
                if v_isShared_2799_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2798_, 0, v___x_2805_);
                    v___x_2807_ = v___x_2798_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
                    v___x_2807_ = v_reuseFailAlloc_2808_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2807_;
            }
            4 => {
                v___x_2814_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_x_2787_,
                        v_key_2809_,
                    );
                if v___x_2814_ == 0 {
                    crate::leanh::lean_del_object(v___x_2812_);
                    v___x_2815_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2809_,
                        v_val_2810_,
                        v_x_2787_,
                        v_x_2788_,
                    );
                    v___x_2816_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2816_, 0, v___x_2815_);
                    v___y_2804_ = v___x_2816_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_val_2810_);
                    crate::leanh::lean_dec(v_key_2809_);
                    if v_isShared_2813_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2812_, 1, v_x_2788_);
                        crate::leanh::lean_ctor_set(v___x_2812_, 0, v_x_2787_);
                        v___x_2818_ = v___x_2812_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2819_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_x_2787_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_x_2788_);
                        v___x_2818_ = v_reuseFailAlloc_2819_;
                        state = 5;
                        continue;
                    }
                }
            }
            5 => {
                v___y_2804_ = v___x_2818_;
                state = 2;
                continue;
            }
            6 => {
                v___x_2825_ = lean_usize_shift_right(v_x_2785_, v___x_2790_);
                v___x_2826_ = lean_usize_add(v_x_2786_, v___x_2791_);
                v___x_2827_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_node_2821_, v___x_2825_, v___x_2826_, v_x_2787_, v_x_2788_);
                if v_isShared_2824_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2823_, 0, v___x_2827_);
                    v___x_2829_ = v___x_2823_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
                    v___x_2829_ = v_reuseFailAlloc_2830_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___y_2804_ = v___x_2829_;
                state = 2;
                continue;
            }
            8 => {
                if v_isShared_2839_ == 0 {
                    v___x_2841_ = v___x_2838_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2855_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_ks_2835_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_vs_2836_);
                    v___x_2841_ = v_reuseFailAlloc_2855_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_newNode_2842_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v___x_2841_, v_x_2787_, v_x_2788_);
                v___x_2850_ = 7usize;
                v___x_2851_ = lean_usize_dec_le(v___x_2850_, v_x_2786_);
                if v___x_2851_ == 0 {
                    v___x_2852_ =
                        l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_2842_);
                    v___x_2853_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_2854_ = lean_nat_dec_lt(v___x_2852_, v___x_2853_);
                    crate::leanh::lean_dec(v___x_2852_);
                    v___y_2844_ = v___x_2854_;
                    state = 10;
                    continue;
                } else {
                    v___y_2844_ = v___x_2851_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v___y_2844_ == 0 {
                    v_ks_2845_ = crate::leanh::lean_ctor_get(v_newNode_2842_, 0);
                    crate::leanh::lean_inc_ref(v_ks_2845_);
                    v_vs_2846_ = crate::leanh::lean_ctor_get(v_newNode_2842_, 1);
                    crate::leanh::lean_inc_ref(v_vs_2846_);
                    crate::leanh::lean_dec_ref(v_newNode_2842_);
                    v___x_2847_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2848_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0);
                    v___x_2849_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_x_2786_, v_ks_2845_, v_vs_2846_, v___x_2847_, v___x_2848_);
                    crate::leanh::lean_dec_ref(v_vs_2846_);
                    crate::leanh::lean_dec_ref(v_ks_2845_);
                    return v___x_2849_;
                } else {
                    return v_newNode_2842_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(
    mut v_depth_2857_: usize,
    mut v_keys_2858_: *mut crate::leanh::LeanObject,
    mut v_vals_2859_: *mut crate::leanh::LeanObject,
    mut v_i_2860_: *mut crate::leanh::LeanObject,
    mut v_entries_2861_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    let mut v_k_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u64 = 0;
    let mut v_h_2867_: usize = 0;
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: usize = 0;
    let mut v___x_2871_: usize = 0;
    let mut v___x_2872_: usize = 0;
    let mut v_h_2873_: usize = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2862_ = lean_array_get_size(v_keys_2858_);
                v___x_2863_ = lean_nat_dec_lt(v_i_2860_, v___x_2862_);
                if v___x_2863_ == 0 {
                    crate::leanh::lean_dec(v_i_2860_);
                    return v_entries_2861_;
                } else {
                    v_k_2864_ = lean_array_fget_borrowed(v_keys_2858_, v_i_2860_);
                    v_v_2865_ = lean_array_fget_borrowed(v_vals_2859_, v_i_2860_);
                    v___x_2866_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2864_);
                    v_h_2867_ = lean_uint64_to_usize(v___x_2866_);
                    v___x_2868_ = 5usize;
                    v___x_2869_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_2870_ = 1usize;
                    v___x_2871_ = lean_usize_sub(v_depth_2857_, v___x_2870_);
                    v___x_2872_ = lean_usize_mul(v___x_2868_, v___x_2871_);
                    v_h_2873_ = lean_usize_shift_right(v_h_2867_, v___x_2872_);
                    v___x_2874_ = lean_nat_add(v_i_2860_, v___x_2869_);
                    crate::leanh::lean_dec(v_i_2860_);
                    crate::leanh::lean_inc(v_v_2865_);
                    crate::leanh::lean_inc(v_k_2864_);
                    v___x_2875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_entries_2861_, v_h_2873_, v_depth_2857_, v_k_2864_, v_v_2865_);
                    v_i_2860_ = v___x_2874_;
                    v_entries_2861_ = v___x_2875_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg___boxed(
    mut v_depth_2877_: *mut crate::leanh::LeanObject,
    mut v_keys_2878_: *mut crate::leanh::LeanObject,
    mut v_vals_2879_: *mut crate::leanh::LeanObject,
    mut v_i_2880_: *mut crate::leanh::LeanObject,
    mut v_entries_2881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_2882_: usize = 0;
    let mut v_res_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_2882_ = crate::leanh::lean_unbox_usize(v_depth_2877_);
    crate::leanh::lean_dec(v_depth_2877_);
    v_res_2883_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2882_, v_keys_2878_, v_vals_2879_, v_i_2880_, v_entries_2881_);
    crate::leanh::lean_dec_ref(v_vals_2879_);
    crate::leanh::lean_dec_ref(v_keys_2878_);
    return v_res_2883_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(
    mut v_x_2884_: *mut crate::leanh::LeanObject,
    mut v_x_2885_: *mut crate::leanh::LeanObject,
    mut v_x_2886_: *mut crate::leanh::LeanObject,
    mut v_x_2887_: *mut crate::leanh::LeanObject,
    mut v_x_2888_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_6922__boxed_2889_: usize = 0;
    let mut v_x_6923__boxed_2890_: usize = 0;
    let mut v_res_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_6922__boxed_2889_ = crate::leanh::lean_unbox_usize(v_x_2885_);
    crate::leanh::lean_dec(v_x_2885_);
    v_x_6923__boxed_2890_ = crate::leanh::lean_unbox_usize(v_x_2886_);
    crate::leanh::lean_dec(v_x_2886_);
    v_res_2891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_2884_, v_x_6922__boxed_2889_, v_x_6923__boxed_2890_, v_x_2887_, v_x_2888_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(
    mut v_x_2892_: *mut crate::leanh::LeanObject,
    mut v_x_2893_: *mut crate::leanh::LeanObject,
    mut v_x_2894_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2895_: u64 = 0;
    let mut v___x_2896_: usize = 0;
    let mut v___x_2897_: usize = 0;
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2895_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2893_);
    v___x_2896_ = lean_uint64_to_usize(v___x_2895_);
    v___x_2897_ = 1usize;
    v___x_2898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_2892_, v___x_2896_, v___x_2897_, v_x_2893_, v_x_2894_);
    return v___x_2898_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(
    mut v_e_2899_: *mut crate::leanh::LeanObject,
    mut v_a_2900_: *mut crate::leanh::LeanObject,
    mut v_s_2901_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_2905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_2906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_2909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2902_ = crate::leanh::lean_ctor_get(v_s_2901_, 0);
                v_typeIdOf_2903_ = crate::leanh::lean_ctor_get(v_s_2901_, 1);
                v_exprToStructId_2904_ = crate::leanh::lean_ctor_get(v_s_2901_, 2);
                v_exprToStructIdEntries_2905_ = crate::leanh::lean_ctor_get(v_s_2901_, 3);
                v_forbiddenNatModules_2906_ = crate::leanh::lean_ctor_get(v_s_2901_, 4);
                v_natStructs_2907_ = crate::leanh::lean_ctor_get(v_s_2901_, 5);
                v_natTypeIdOf_2908_ = crate::leanh::lean_ctor_get(v_s_2901_, 6);
                v_exprToNatStructId_2909_ = crate::leanh::lean_ctor_get(v_s_2901_, 7);
                v_isSharedCheck_2917_ = (!crate::leanh::lean_is_exclusive(v_s_2901_)) as u8;
                if v_isSharedCheck_2917_ == 0 {
                    v___x_2911_ = v_s_2901_;
                    v_isShared_2912_ = v_isSharedCheck_2917_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_exprToNatStructId_2909_);
                    crate::leanh::lean_inc(v_natTypeIdOf_2908_);
                    crate::leanh::lean_inc(v_natStructs_2907_);
                    crate::leanh::lean_inc(v_forbiddenNatModules_2906_);
                    crate::leanh::lean_inc(v_exprToStructIdEntries_2905_);
                    crate::leanh::lean_inc(v_exprToStructId_2904_);
                    crate::leanh::lean_inc(v_typeIdOf_2903_);
                    crate::leanh::lean_inc(v_structs_2902_);
                    crate::leanh::lean_dec(v_s_2901_);
                    v___x_2911_ = crate::leanh::lean_box(0);
                    v_isShared_2912_ = v_isSharedCheck_2917_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                crate::leanh::lean_inc(v_a_2900_);
                v___x_2913_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_exprToNatStructId_2909_, v_e_2899_, v_a_2900_);
                if v_isShared_2912_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2911_, 7, v___x_2913_);
                    v___x_2915_ = v___x_2911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_structs_2902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_typeIdOf_2903_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 2, v_exprToStructId_2904_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2916_,
                        3,
                        v_exprToStructIdEntries_2905_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_2916_,
                        4,
                        v_forbiddenNatModules_2906_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 5, v_natStructs_2907_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 6, v_natTypeIdOf_2908_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 7, v___x_2913_);
                    v___x_2915_ = v_reuseFailAlloc_2916_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2915_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed(
    mut v_e_2918_: *mut crate::leanh::LeanObject,
    mut v_a_2919_: *mut crate::leanh::LeanObject,
    mut v_s_2920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(
        v_e_2918_, v_a_2919_, v_s_2920_,
    );
    crate::leanh::lean_dec(v_a_2919_);
    return v_res_2921_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2923_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0;
    v___x_2924_ = l_Lean_stringToMessageData(v___x_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
    mut v_e_2925_: *mut crate::leanh::LeanObject,
    mut v_a_2926_: *mut crate::leanh::LeanObject,
    mut v_a_2927_: *mut crate::leanh::LeanObject,
    mut v_a_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
    mut v_a_2931_: *mut crate::leanh::LeanObject,
    mut v_a_2932_: *mut crate::leanh::LeanObject,
    mut v_a_2933_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u8 = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___x_2954_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v___f_2957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2938_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
                    v_e_2925_, v_a_2927_, v_a_2932_,
                );
                if crate::leanh::lean_obj_tag(v___x_2938_) == 0 {
                    v_a_2939_ = crate::leanh::lean_ctor_get(v___x_2938_, 0);
                    crate::leanh::lean_inc(v_a_2939_);
                    crate::leanh::lean_dec_ref_known(v___x_2938_, 1);
                    if crate::leanh::lean_obj_tag(v_a_2939_) == 1 {
                        v_val_2940_ = crate::leanh::lean_ctor_get(v_a_2939_, 0);
                        crate::leanh::lean_inc(v_val_2940_);
                        crate::leanh::lean_dec_ref_known(v_a_2939_, 1);
                        v___x_2941_ = lean_nat_dec_eq(v_val_2940_, v_a_2926_);
                        crate::leanh::lean_dec(v_val_2940_);
                        if v___x_2941_ == 0 {
                            v___x_2942_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2928_);
                            if crate::leanh::lean_obj_tag(v___x_2942_) == 0 {
                                v_a_2943_ = crate::leanh::lean_ctor_get(v___x_2942_, 0);
                                crate::leanh::lean_inc(v_a_2943_);
                                crate::leanh::lean_dec_ref_known(v___x_2942_, 1);
                                v___x_2944_ = (crate::leanh::lean_unbox(v_a_2943_) as u8);
                                crate::leanh::lean_dec(v_a_2943_);
                                if v___x_2944_ == 0 {
                                    crate::leanh::lean_dec_ref(v_e_2925_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2945_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1);
                                    v___x_2946_ = l_Lean_indentExpr(v_e_2925_);
                                    v___x_2947_ = crate::leanh::lean_alloc_ctor(7, 2, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_2947_, 0, v___x_2945_);
                                    crate::leanh::lean_ctor_set(v___x_2947_, 1, v___x_2946_);
                                    v___x_2948_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_2947_,
                                        v_a_2928_,
                                        v_a_2929_,
                                        v_a_2930_,
                                        v_a_2931_,
                                        v_a_2932_,
                                        v_a_2933_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_2948_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_2948_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_2948_;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref(v_e_2925_);
                                v_a_2949_ = crate::leanh::lean_ctor_get(v___x_2942_, 0);
                                v_isSharedCheck_2956_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2942_)) as u8;
                                if v_isSharedCheck_2956_ == 0 {
                                    v___x_2951_ = v___x_2942_;
                                    v_isShared_2952_ = v_isSharedCheck_2956_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2949_);
                                    crate::leanh::lean_dec(v___x_2942_);
                                    v___x_2951_ = crate::leanh::lean_box(0);
                                    v_isShared_2952_ = v_isSharedCheck_2956_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_e_2925_);
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_2939_);
                        crate::leanh::lean_inc(v_a_2926_);
                        v___f_2957_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                        crate::leanh::lean_closure_set(v___f_2957_, 0, v_e_2925_);
                        crate::leanh::lean_closure_set(v___f_2957_, 1, v_a_2926_);
                        v___x_2958_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                        v___x_2959_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2958_, v___f_2957_, v_a_2927_);
                        return v___x_2959_;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_2925_);
                    v_a_2960_ = crate::leanh::lean_ctor_get(v___x_2938_, 0);
                    v_isSharedCheck_2967_ = (!crate::leanh::lean_is_exclusive(v___x_2938_)) as u8;
                    if v_isSharedCheck_2967_ == 0 {
                        v___x_2962_ = v___x_2938_;
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2960_);
                        crate::leanh::lean_dec(v___x_2938_);
                        v___x_2962_ = crate::leanh::lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2936_ = crate::leanh::lean_box(0);
                v___x_2937_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_2937_, 0, v___x_2936_);
                return v___x_2937_;
            }
            2 => {
                if v_isShared_2952_ == 0 {
                    v___x_2954_ = v___x_2951_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
                    v___x_2954_ = v_reuseFailAlloc_2955_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2954_;
            }
            4 => {
                if v_isShared_2963_ == 0 {
                    v___x_2965_ = v___x_2962_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2966_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
                    v___x_2965_ = v_reuseFailAlloc_2966_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2965_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___boxed(
    mut v_e_2968_: *mut crate::leanh::LeanObject,
    mut v_a_2969_: *mut crate::leanh::LeanObject,
    mut v_a_2970_: *mut crate::leanh::LeanObject,
    mut v_a_2971_: *mut crate::leanh::LeanObject,
    mut v_a_2972_: *mut crate::leanh::LeanObject,
    mut v_a_2973_: *mut crate::leanh::LeanObject,
    mut v_a_2974_: *mut crate::leanh::LeanObject,
    mut v_a_2975_: *mut crate::leanh::LeanObject,
    mut v_a_2976_: *mut crate::leanh::LeanObject,
    mut v_a_2977_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
        v_e_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_,
        v_a_2976_,
    );
    crate::leanh::lean_dec(v_a_2976_);
    crate::leanh::lean_dec_ref(v_a_2975_);
    crate::leanh::lean_dec(v_a_2974_);
    crate::leanh::lean_dec_ref(v_a_2973_);
    crate::leanh::lean_dec(v_a_2972_);
    crate::leanh::lean_dec_ref(v_a_2971_);
    crate::leanh::lean_dec(v_a_2970_);
    crate::leanh::lean_dec(v_a_2969_);
    return v_res_2978_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(
    mut v_e_2979_: *mut crate::leanh::LeanObject,
    mut v_a_2980_: *mut crate::leanh::LeanObject,
    mut v_a_2981_: *mut crate::leanh::LeanObject,
    mut v_a_2982_: *mut crate::leanh::LeanObject,
    mut v_a_2983_: *mut crate::leanh::LeanObject,
    mut v_a_2984_: *mut crate::leanh::LeanObject,
    mut v_a_2985_: *mut crate::leanh::LeanObject,
    mut v_a_2986_: *mut crate::leanh::LeanObject,
    mut v_a_2987_: *mut crate::leanh::LeanObject,
    mut v_a_2988_: *mut crate::leanh::LeanObject,
    mut v_a_2989_: *mut crate::leanh::LeanObject,
    mut v_a_2990_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2992_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
        v_e_2979_, v_a_2980_, v_a_2981_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_,
        v_a_2990_,
    );
    return v___x_2992_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(
    mut v_e_2993_: *mut crate::leanh::LeanObject,
    mut v_a_2994_: *mut crate::leanh::LeanObject,
    mut v_a_2995_: *mut crate::leanh::LeanObject,
    mut v_a_2996_: *mut crate::leanh::LeanObject,
    mut v_a_2997_: *mut crate::leanh::LeanObject,
    mut v_a_2998_: *mut crate::leanh::LeanObject,
    mut v_a_2999_: *mut crate::leanh::LeanObject,
    mut v_a_3000_: *mut crate::leanh::LeanObject,
    mut v_a_3001_: *mut crate::leanh::LeanObject,
    mut v_a_3002_: *mut crate::leanh::LeanObject,
    mut v_a_3003_: *mut crate::leanh::LeanObject,
    mut v_a_3004_: *mut crate::leanh::LeanObject,
    mut v_a_3005_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(
        v_e_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
        v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_,
    );
    crate::leanh::lean_dec(v_a_3004_);
    crate::leanh::lean_dec_ref(v_a_3003_);
    crate::leanh::lean_dec(v_a_3002_);
    crate::leanh::lean_dec_ref(v_a_3001_);
    crate::leanh::lean_dec(v_a_3000_);
    crate::leanh::lean_dec_ref(v_a_2999_);
    crate::leanh::lean_dec(v_a_2998_);
    crate::leanh::lean_dec_ref(v_a_2997_);
    crate::leanh::lean_dec(v_a_2996_);
    crate::leanh::lean_dec(v_a_2995_);
    crate::leanh::lean_dec(v_a_2994_);
    return v_res_3006_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(
    mut v_00_u03b2_3007_: *mut crate::leanh::LeanObject,
    mut v_x_3008_: *mut crate::leanh::LeanObject,
    mut v_x_3009_: *mut crate::leanh::LeanObject,
    mut v_x_3010_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3011_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_x_3008_, v_x_3009_, v_x_3010_);
    return v___x_3011_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(
    mut v_00_u03b2_3012_: *mut crate::leanh::LeanObject,
    mut v_x_3013_: *mut crate::leanh::LeanObject,
    mut v_x_3014_: usize,
    mut v_x_3015_: usize,
    mut v_x_3016_: *mut crate::leanh::LeanObject,
    mut v_x_3017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_3013_, v_x_3014_, v_x_3015_, v_x_3016_, v_x_3017_);
    return v___x_3018_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(
    mut v_00_u03b2_3019_: *mut crate::leanh::LeanObject,
    mut v_x_3020_: *mut crate::leanh::LeanObject,
    mut v_x_3021_: *mut crate::leanh::LeanObject,
    mut v_x_3022_: *mut crate::leanh::LeanObject,
    mut v_x_3023_: *mut crate::leanh::LeanObject,
    mut v_x_3024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_7201__boxed_3025_: usize = 0;
    let mut v_x_7202__boxed_3026_: usize = 0;
    let mut v_res_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_7201__boxed_3025_ = crate::leanh::lean_unbox_usize(v_x_3021_);
    crate::leanh::lean_dec(v_x_3021_);
    v_x_7202__boxed_3026_ = crate::leanh::lean_unbox_usize(v_x_3022_);
    crate::leanh::lean_dec(v_x_3022_);
    v_res_3027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(v_00_u03b2_3019_, v_x_3020_, v_x_7201__boxed_3025_, v_x_7202__boxed_3026_, v_x_3023_, v_x_3024_);
    return v_res_3027_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3028_: *mut crate::leanh::LeanObject,
    mut v_n_3029_: *mut crate::leanh::LeanObject,
    mut v_k_3030_: *mut crate::leanh::LeanObject,
    mut v_v_3031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v_n_3029_, v_k_3030_, v_v_3031_);
    return v___x_3032_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3033_: *mut crate::leanh::LeanObject,
    mut v_depth_3034_: usize,
    mut v_keys_3035_: *mut crate::leanh::LeanObject,
    mut v_vals_3036_: *mut crate::leanh::LeanObject,
    mut v_heq_3037_: *mut crate::leanh::LeanObject,
    mut v_i_3038_: *mut crate::leanh::LeanObject,
    mut v_entries_3039_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_3034_, v_keys_3035_, v_vals_3036_, v_i_3038_, v_entries_3039_);
    return v___x_3040_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3041_: *mut crate::leanh::LeanObject,
    mut v_depth_3042_: *mut crate::leanh::LeanObject,
    mut v_keys_3043_: *mut crate::leanh::LeanObject,
    mut v_vals_3044_: *mut crate::leanh::LeanObject,
    mut v_heq_3045_: *mut crate::leanh::LeanObject,
    mut v_i_3046_: *mut crate::leanh::LeanObject,
    mut v_entries_3047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_depth_boxed_3048_: usize = 0;
    let mut v_res_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_depth_boxed_3048_ = crate::leanh::lean_unbox_usize(v_depth_3042_);
    crate::leanh::lean_dec(v_depth_3042_);
    v_res_3049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(v_00_u03b2_3041_, v_depth_boxed_3048_, v_keys_3043_, v_vals_3044_, v_heq_3045_, v_i_3046_, v_entries_3047_);
    crate::leanh::lean_dec_ref(v_vals_3044_);
    crate::leanh::lean_dec_ref(v_keys_3043_);
    return v_res_3049_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3050_: *mut crate::leanh::LeanObject,
    mut v_x_3051_: *mut crate::leanh::LeanObject,
    mut v_x_3052_: *mut crate::leanh::LeanObject,
    mut v_x_3053_: *mut crate::leanh::LeanObject,
    mut v_x_3054_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3055_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3051_, v_x_3052_, v_x_3053_, v_x_3054_);
    return v___x_3055_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(
    mut v_a_3056_: *mut crate::leanh::LeanObject,
    mut v_e_3057_: *mut crate::leanh::LeanObject,
    mut v___x_3058_: *mut crate::leanh::LeanObject,
    mut v_s_3059_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_3063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v_v_3073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structId_3075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_3079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_3080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_3083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_3084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rfl__q_3086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_3087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_3088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_3089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_smulFn_3090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMap_3091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3105_: u8 = 0;
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut v_unused_3107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3060_ = crate::leanh::lean_ctor_get(v_s_3059_, 0);
                v_typeIdOf_3061_ = crate::leanh::lean_ctor_get(v_s_3059_, 1);
                v_exprToStructId_3062_ = crate::leanh::lean_ctor_get(v_s_3059_, 2);
                v_exprToStructIdEntries_3063_ = crate::leanh::lean_ctor_get(v_s_3059_, 3);
                v_forbiddenNatModules_3064_ = crate::leanh::lean_ctor_get(v_s_3059_, 4);
                v_natStructs_3065_ = crate::leanh::lean_ctor_get(v_s_3059_, 5);
                v_natTypeIdOf_3066_ = crate::leanh::lean_ctor_get(v_s_3059_, 6);
                v_exprToNatStructId_3067_ = crate::leanh::lean_ctor_get(v_s_3059_, 7);
                v___x_3068_ = lean_array_get_size(v_natStructs_3065_);
                v___x_3069_ = lean_nat_dec_lt(v_a_3056_, v___x_3068_);
                if v___x_3069_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3058_);
                    crate::leanh::lean_dec_ref(v_e_3057_);
                    return v_s_3059_;
                } else {
                    crate::leanh::lean_inc_ref(v_exprToNatStructId_3067_);
                    crate::leanh::lean_inc_ref(v_natTypeIdOf_3066_);
                    crate::leanh::lean_inc_ref(v_natStructs_3065_);
                    crate::leanh::lean_inc_ref(v_forbiddenNatModules_3064_);
                    crate::leanh::lean_inc_ref(v_exprToStructIdEntries_3063_);
                    crate::leanh::lean_inc_ref(v_exprToStructId_3062_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_3061_);
                    crate::leanh::lean_inc_ref(v_structs_3060_);
                    v_isSharedCheck_3106_ = (!crate::leanh::lean_is_exclusive(v_s_3059_)) as u8;
                    if v_isSharedCheck_3106_ == 0 {
                        v_unused_3107_ = crate::leanh::lean_ctor_get(v_s_3059_, 7);
                        crate::leanh::lean_dec(v_unused_3107_);
                        v_unused_3108_ = crate::leanh::lean_ctor_get(v_s_3059_, 6);
                        crate::leanh::lean_dec(v_unused_3108_);
                        v_unused_3109_ = crate::leanh::lean_ctor_get(v_s_3059_, 5);
                        crate::leanh::lean_dec(v_unused_3109_);
                        v_unused_3110_ = crate::leanh::lean_ctor_get(v_s_3059_, 4);
                        crate::leanh::lean_dec(v_unused_3110_);
                        v_unused_3111_ = crate::leanh::lean_ctor_get(v_s_3059_, 3);
                        crate::leanh::lean_dec(v_unused_3111_);
                        v_unused_3112_ = crate::leanh::lean_ctor_get(v_s_3059_, 2);
                        crate::leanh::lean_dec(v_unused_3112_);
                        v_unused_3113_ = crate::leanh::lean_ctor_get(v_s_3059_, 1);
                        crate::leanh::lean_dec(v_unused_3113_);
                        v_unused_3114_ = crate::leanh::lean_ctor_get(v_s_3059_, 0);
                        crate::leanh::lean_dec(v_unused_3114_);
                        v___x_3071_ = v_s_3059_;
                        v_isShared_3072_ = v_isSharedCheck_3106_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_3059_);
                        v___x_3071_ = crate::leanh::lean_box(0);
                        v_isShared_3072_ = v_isSharedCheck_3106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3073_ = lean_array_fget(v_natStructs_3065_, v_a_3056_);
                v_id_3074_ = crate::leanh::lean_ctor_get(v_v_3073_, 0);
                v_structId_3075_ = crate::leanh::lean_ctor_get(v_v_3073_, 1);
                v_type_3076_ = crate::leanh::lean_ctor_get(v_v_3073_, 2);
                v_u_3077_ = crate::leanh::lean_ctor_get(v_v_3073_, 3);
                v_natModuleInst_3078_ = crate::leanh::lean_ctor_get(v_v_3073_, 4);
                v_leInst_x3f_3079_ = crate::leanh::lean_ctor_get(v_v_3073_, 5);
                v_ltInst_x3f_3080_ = crate::leanh::lean_ctor_get(v_v_3073_, 6);
                v_lawfulOrderLTInst_x3f_3081_ = crate::leanh::lean_ctor_get(v_v_3073_, 7);
                v_isPreorderInst_x3f_3082_ = crate::leanh::lean_ctor_get(v_v_3073_, 8);
                v_orderedAddInst_x3f_3083_ = crate::leanh::lean_ctor_get(v_v_3073_, 9);
                v_isLinearInst_x3f_3084_ = crate::leanh::lean_ctor_get(v_v_3073_, 10);
                v_addRightCancelInst_x3f_3085_ = crate::leanh::lean_ctor_get(v_v_3073_, 11);
                v_rfl__q_3086_ = crate::leanh::lean_ctor_get(v_v_3073_, 12);
                v_zero_3087_ = crate::leanh::lean_ctor_get(v_v_3073_, 13);
                v_toQFn_3088_ = crate::leanh::lean_ctor_get(v_v_3073_, 14);
                v_addFn_3089_ = crate::leanh::lean_ctor_get(v_v_3073_, 15);
                v_smulFn_3090_ = crate::leanh::lean_ctor_get(v_v_3073_, 16);
                v_termMap_3091_ = crate::leanh::lean_ctor_get(v_v_3073_, 17);
                v_isSharedCheck_3105_ = (!crate::leanh::lean_is_exclusive(v_v_3073_)) as u8;
                if v_isSharedCheck_3105_ == 0 {
                    v___x_3093_ = v_v_3073_;
                    v_isShared_3094_ = v_isSharedCheck_3105_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_termMap_3091_);
                    crate::leanh::lean_inc(v_smulFn_3090_);
                    crate::leanh::lean_inc(v_addFn_3089_);
                    crate::leanh::lean_inc(v_toQFn_3088_);
                    crate::leanh::lean_inc(v_zero_3087_);
                    crate::leanh::lean_inc(v_rfl__q_3086_);
                    crate::leanh::lean_inc(v_addRightCancelInst_x3f_3085_);
                    crate::leanh::lean_inc(v_isLinearInst_x3f_3084_);
                    crate::leanh::lean_inc(v_orderedAddInst_x3f_3083_);
                    crate::leanh::lean_inc(v_isPreorderInst_x3f_3082_);
                    crate::leanh::lean_inc(v_lawfulOrderLTInst_x3f_3081_);
                    crate::leanh::lean_inc(v_ltInst_x3f_3080_);
                    crate::leanh::lean_inc(v_leInst_x3f_3079_);
                    crate::leanh::lean_inc(v_natModuleInst_3078_);
                    crate::leanh::lean_inc(v_u_3077_);
                    crate::leanh::lean_inc(v_type_3076_);
                    crate::leanh::lean_inc(v_structId_3075_);
                    crate::leanh::lean_inc(v_id_3074_);
                    crate::leanh::lean_dec(v_v_3073_);
                    v___x_3093_ = crate::leanh::lean_box(0);
                    v_isShared_3094_ = v_isSharedCheck_3105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3095_ = crate::leanh::lean_box(0);
                v_xs_x27_3096_ = lean_array_fset(v_natStructs_3065_, v_a_3056_, v___x_3095_);
                v___x_3097_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_3091_, v_e_3057_, v___x_3058_);
                if v_isShared_3094_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3093_, 17, v___x_3097_);
                    v___x_3099_ = v___x_3093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3104_ = crate::leanh::lean_alloc_ctor(0, 18, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_id_3074_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_structId_3075_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_type_3076_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_u_3077_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_natModuleInst_3078_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 5, v_leInst_x3f_3079_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_ltInst_x3f_3080_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3104_,
                        7,
                        v_lawfulOrderLTInst_x3f_3081_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3104_,
                        8,
                        v_isPreorderInst_x3f_3082_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3104_,
                        9,
                        v_orderedAddInst_x3f_3083_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3104_,
                        10,
                        v_isLinearInst_x3f_3084_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3104_,
                        11,
                        v_addRightCancelInst_x3f_3085_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 12, v_rfl__q_3086_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 13, v_zero_3087_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 14, v_toQFn_3088_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 15, v_addFn_3089_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 16, v_smulFn_3090_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3104_, 17, v___x_3097_);
                    v___x_3099_ = v_reuseFailAlloc_3104_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3100_ = lean_array_fset(v_xs_x27_3096_, v_a_3056_, v___x_3099_);
                if v_isShared_3072_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3071_, 5, v___x_3100_);
                    v___x_3102_ = v___x_3071_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3103_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_structs_3060_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_typeIdOf_3061_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_exprToStructId_3062_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3103_,
                        3,
                        v_exprToStructIdEntries_3063_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3103_,
                        4,
                        v_forbiddenNatModules_3064_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3103_, 5, v___x_3100_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3103_, 6, v_natTypeIdOf_3066_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3103_,
                        7,
                        v_exprToNatStructId_3067_,
                    );
                    v___x_3102_ = v_reuseFailAlloc_3103_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3102_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed(
    mut v_a_3115_: *mut crate::leanh::LeanObject,
    mut v_e_3116_: *mut crate::leanh::LeanObject,
    mut v___x_3117_: *mut crate::leanh::LeanObject,
    mut v_s_3118_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3119_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(v_a_3115_, v_e_3116_, v___x_3117_, v_s_3118_);
    crate::leanh::lean_dec(v_a_3115_);
    return v_res_3119_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(
    mut v_e_3120_: *mut crate::leanh::LeanObject,
    mut v_a_3121_: *mut crate::leanh::LeanObject,
    mut v_a_3122_: *mut crate::leanh::LeanObject,
    mut v_a_3123_: *mut crate::leanh::LeanObject,
    mut v_a_3124_: *mut crate::leanh::LeanObject,
    mut v_a_3125_: *mut crate::leanh::LeanObject,
    mut v_a_3126_: *mut crate::leanh::LeanObject,
    mut v_a_3127_: *mut crate::leanh::LeanObject,
    mut v_a_3128_: *mut crate::leanh::LeanObject,
    mut v_a_3129_: *mut crate::leanh::LeanObject,
    mut v_a_3130_: *mut crate::leanh::LeanObject,
    mut v_a_3131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v_termMap_3138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rfl__q_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3153_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3162_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut v_unused_3165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_a_3174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v_a_3182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3189_: u8 = 0;
    let mut v_a_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut v_a_3198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_a_3207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3133_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_,
                    v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_,
                );
                if crate::leanh::lean_obj_tag(v___x_3133_) == 0 {
                    v_a_3134_ = crate::leanh::lean_ctor_get(v___x_3133_, 0);
                    v_isSharedCheck_3206_ = (!crate::leanh::lean_is_exclusive(v___x_3133_)) as u8;
                    if v_isSharedCheck_3206_ == 0 {
                        v___x_3136_ = v___x_3133_;
                        v_isShared_3137_ = v_isSharedCheck_3206_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3134_);
                        crate::leanh::lean_dec(v___x_3133_);
                        v___x_3136_ = crate::leanh::lean_box(0);
                        v_isShared_3137_ = v_isSharedCheck_3206_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3120_);
                    v_a_3207_ = crate::leanh::lean_ctor_get(v___x_3133_, 0);
                    v_isSharedCheck_3214_ = (!crate::leanh::lean_is_exclusive(v___x_3133_)) as u8;
                    if v_isSharedCheck_3214_ == 0 {
                        v___x_3209_ = v___x_3133_;
                        v_isShared_3210_ = v_isSharedCheck_3214_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3207_);
                        crate::leanh::lean_dec(v___x_3133_);
                        v___x_3209_ = crate::leanh::lean_box(0);
                        v_isShared_3210_ = v_isSharedCheck_3214_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_termMap_3138_ = crate::leanh::lean_ctor_get(v_a_3134_, 17);
                crate::leanh::lean_inc_ref(v_termMap_3138_);
                crate::leanh::lean_dec(v_a_3134_);
                v___x_3139_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_3138_, v_e_3120_);
                crate::leanh::lean_dec_ref(v_termMap_3138_);
                if crate::leanh::lean_obj_tag(v___x_3139_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_3120_);
                    v_val_3140_ = crate::leanh::lean_ctor_get(v___x_3139_, 0);
                    crate::leanh::lean_inc(v_val_3140_);
                    crate::leanh::lean_dec_ref_known(v___x_3139_, 1);
                    if v_isShared_3137_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3136_, 0, v_val_3140_);
                        v___x_3142_ = v___x_3136_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_val_3140_);
                        v___x_3142_ = v_reuseFailAlloc_3143_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3139_);
                    crate::leanh::lean_del_object(v___x_3136_);
                    v___x_3144_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                        v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_,
                        v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3144_) == 0 {
                        v_a_3145_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                        crate::leanh::lean_inc(v_a_3145_);
                        crate::leanh::lean_dec_ref_known(v___x_3144_, 1);
                        v_rfl__q_3146_ = crate::leanh::lean_ctor_get(v_a_3145_, 12);
                        crate::leanh::lean_inc_ref(v_rfl__q_3146_);
                        v_toQFn_3147_ = crate::leanh::lean_ctor_get(v_a_3145_, 14);
                        crate::leanh::lean_inc_ref(v_toQFn_3147_);
                        crate::leanh::lean_dec(v_a_3145_);
                        crate::leanh::lean_inc_ref(v_e_3120_);
                        v___x_3148_ = l_Lean_Expr_app___override(v_toQFn_3147_, v_e_3120_);
                        v___x_3149_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_3148_, v_a_3127_);
                        if crate::leanh::lean_obj_tag(v___x_3149_) == 0 {
                            v_a_3150_ = crate::leanh::lean_ctor_get(v___x_3149_, 0);
                            crate::leanh::lean_inc_n(v_a_3150_, 2);
                            crate::leanh::lean_dec_ref_known(v___x_3149_, 1);
                            v___x_3151_ = l_Lean_Expr_app___override(v_rfl__q_3146_, v_a_3150_);
                            v___x_3152_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_3152_, 0, v_a_3150_);
                            crate::leanh::lean_ctor_set(v___x_3152_, 1, v___x_3151_);
                            crate::leanh::lean_inc_ref(v___x_3152_);
                            crate::leanh::lean_inc_ref(v_e_3120_);
                            crate::leanh::lean_inc(v_a_3121_);
                            v___f_3153_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
                            crate::leanh::lean_closure_set(v___f_3153_, 0, v_a_3121_);
                            crate::leanh::lean_closure_set(v___f_3153_, 1, v_e_3120_);
                            crate::leanh::lean_closure_set(v___f_3153_, 2, v___x_3152_);
                            v___x_3154_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                            v___x_3155_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3154_, v___f_3153_, v_a_3122_);
                            if crate::leanh::lean_obj_tag(v___x_3155_) == 0 {
                                crate::leanh::lean_dec_ref_known(v___x_3155_, 1);
                                crate::leanh::lean_inc_ref(v_e_3120_);
                                v___x_3156_ =
                                    l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
                                        v_e_3120_, v_a_3121_, v_a_3122_, v_a_3126_, v_a_3127_,
                                        v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_,
                                    );
                                if crate::leanh::lean_obj_tag(v___x_3156_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3156_, 1);
                                    v___x_3157_ =
                                        l_Lean_Meta_Grind_SolverExtension_markTerm___redArg(
                                            v___x_3154_,
                                            v_e_3120_,
                                            v_a_3122_,
                                            v_a_3123_,
                                            v_a_3124_,
                                            v_a_3125_,
                                            v_a_3126_,
                                            v_a_3127_,
                                            v_a_3128_,
                                            v_a_3129_,
                                            v_a_3130_,
                                            v_a_3131_,
                                        );
                                    if crate::leanh::lean_obj_tag(v___x_3157_) == 0 {
                                        v_isSharedCheck_3164_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3157_)) as u8;
                                        if v_isSharedCheck_3164_ == 0 {
                                            v_unused_3165_ =
                                                crate::leanh::lean_ctor_get(v___x_3157_, 0);
                                            crate::leanh::lean_dec(v_unused_3165_);
                                            v___x_3159_ = v___x_3157_;
                                            v_isShared_3160_ = v_isSharedCheck_3164_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_3157_);
                                            v___x_3159_ = crate::leanh::lean_box(0);
                                            v_isShared_3160_ = v_isSharedCheck_3164_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref_known(v___x_3152_, 2);
                                        v_a_3166_ = crate::leanh::lean_ctor_get(v___x_3157_, 0);
                                        v_isSharedCheck_3173_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3157_)) as u8;
                                        if v_isSharedCheck_3173_ == 0 {
                                            v___x_3168_ = v___x_3157_;
                                            v_isShared_3169_ = v_isSharedCheck_3173_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3166_);
                                            crate::leanh::lean_dec(v___x_3157_);
                                            v___x_3168_ = crate::leanh::lean_box(0);
                                            v_isShared_3169_ = v_isSharedCheck_3173_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref_known(v___x_3152_, 2);
                                    crate::leanh::lean_dec_ref(v_e_3120_);
                                    v_a_3174_ = crate::leanh::lean_ctor_get(v___x_3156_, 0);
                                    v_isSharedCheck_3181_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_3156_)) as u8;
                                    if v_isSharedCheck_3181_ == 0 {
                                        v___x_3176_ = v___x_3156_;
                                        v_isShared_3177_ = v_isSharedCheck_3181_;
                                        state = 7;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_3174_);
                                        crate::leanh::lean_dec(v___x_3156_);
                                        v___x_3176_ = crate::leanh::lean_box(0);
                                        v_isShared_3177_ = v_isSharedCheck_3181_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec_ref_known(v___x_3152_, 2);
                                crate::leanh::lean_dec_ref(v_e_3120_);
                                v_a_3182_ = crate::leanh::lean_ctor_get(v___x_3155_, 0);
                                v_isSharedCheck_3189_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_3155_)) as u8;
                                if v_isSharedCheck_3189_ == 0 {
                                    v___x_3184_ = v___x_3155_;
                                    v_isShared_3185_ = v_isSharedCheck_3189_;
                                    state = 9;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_3182_);
                                    crate::leanh::lean_dec(v___x_3155_);
                                    v___x_3184_ = crate::leanh::lean_box(0);
                                    v_isShared_3185_ = v_isSharedCheck_3189_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_rfl__q_3146_);
                            crate::leanh::lean_dec_ref(v_e_3120_);
                            v_a_3190_ = crate::leanh::lean_ctor_get(v___x_3149_, 0);
                            v_isSharedCheck_3197_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3149_)) as u8;
                            if v_isSharedCheck_3197_ == 0 {
                                v___x_3192_ = v___x_3149_;
                                v_isShared_3193_ = v_isSharedCheck_3197_;
                                state = 11;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3190_);
                                crate::leanh::lean_dec(v___x_3149_);
                                v___x_3192_ = crate::leanh::lean_box(0);
                                v_isShared_3193_ = v_isSharedCheck_3197_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3120_);
                        v_a_3198_ = crate::leanh::lean_ctor_get(v___x_3144_, 0);
                        v_isSharedCheck_3205_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3144_)) as u8;
                        if v_isSharedCheck_3205_ == 0 {
                            v___x_3200_ = v___x_3144_;
                            v_isShared_3201_ = v_isSharedCheck_3205_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3198_);
                            crate::leanh::lean_dec(v___x_3144_);
                            v___x_3200_ = crate::leanh::lean_box(0);
                            v_isShared_3201_ = v_isSharedCheck_3205_;
                            state = 13;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3142_;
            }
            3 => {
                if v_isShared_3160_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3159_, 0, v___x_3152_);
                    v___x_3162_ = v___x_3159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3152_);
                    v___x_3162_ = v_reuseFailAlloc_3163_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3162_;
            }
            5 => {
                if v_isShared_3169_ == 0 {
                    v___x_3171_ = v___x_3168_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3172_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
                    v___x_3171_ = v_reuseFailAlloc_3172_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3171_;
            }
            7 => {
                if v_isShared_3177_ == 0 {
                    v___x_3179_ = v___x_3176_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_3180_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
                    v___x_3179_ = v_reuseFailAlloc_3180_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_3179_;
            }
            9 => {
                if v_isShared_3185_ == 0 {
                    v___x_3187_ = v___x_3184_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3188_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
                    v___x_3187_ = v_reuseFailAlloc_3188_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3187_;
            }
            11 => {
                if v_isShared_3193_ == 0 {
                    v___x_3195_ = v___x_3192_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_3196_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
                    v___x_3195_ = v_reuseFailAlloc_3196_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_3195_;
            }
            13 => {
                if v_isShared_3201_ == 0 {
                    v___x_3203_ = v___x_3200_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_3204_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
                    v___x_3203_ = v_reuseFailAlloc_3204_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_3203_;
            }
            15 => {
                if v_isShared_3210_ == 0 {
                    v___x_3212_ = v___x_3209_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3213_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
                    v___x_3212_ = v_reuseFailAlloc_3213_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3212_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___boxed(
    mut v_e_3215_: *mut crate::leanh::LeanObject,
    mut v_a_3216_: *mut crate::leanh::LeanObject,
    mut v_a_3217_: *mut crate::leanh::LeanObject,
    mut v_a_3218_: *mut crate::leanh::LeanObject,
    mut v_a_3219_: *mut crate::leanh::LeanObject,
    mut v_a_3220_: *mut crate::leanh::LeanObject,
    mut v_a_3221_: *mut crate::leanh::LeanObject,
    mut v_a_3222_: *mut crate::leanh::LeanObject,
    mut v_a_3223_: *mut crate::leanh::LeanObject,
    mut v_a_3224_: *mut crate::leanh::LeanObject,
    mut v_a_3225_: *mut crate::leanh::LeanObject,
    mut v_a_3226_: *mut crate::leanh::LeanObject,
    mut v_a_3227_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3228_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
    crate::leanh::lean_dec(v_a_3226_);
    crate::leanh::lean_dec_ref(v_a_3225_);
    crate::leanh::lean_dec(v_a_3224_);
    crate::leanh::lean_dec_ref(v_a_3223_);
    crate::leanh::lean_dec(v_a_3222_);
    crate::leanh::lean_dec_ref(v_a_3221_);
    crate::leanh::lean_dec(v_a_3220_);
    crate::leanh::lean_dec_ref(v_a_3219_);
    crate::leanh::lean_dec(v_a_3218_);
    crate::leanh::lean_dec(v_a_3217_);
    crate::leanh::lean_dec(v_a_3216_);
    return v_res_3228_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(
    mut v_natStruct_3229_: *mut crate::leanh::LeanObject,
    mut v_inst_3230_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_addFn_3231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: u8 = 0;
    v_addFn_3231_ = crate::leanh::lean_ctor_get(v_natStruct_3229_, 15);
    v___x_3232_ = l_Lean_Expr_appArg_x21(v_addFn_3231_);
    v___x_3233_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_3232_,
        v_inst_3230_,
    );
    crate::leanh::lean_dec_ref(v___x_3232_);
    return v___x_3233_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(
    mut v_natStruct_3234_: *mut crate::leanh::LeanObject,
    mut v_inst_3235_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3236_: u8 = 0;
    let mut v_r_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3236_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_3234_, v_inst_3235_);
    crate::leanh::lean_dec_ref(v_inst_3235_);
    crate::leanh::lean_dec_ref(v_natStruct_3234_);
    v_r_3237_ = crate::leanh::lean_box((v_res_3236_) as usize);
    return v_r_3237_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(
    mut v_natStruct_3238_: *mut crate::leanh::LeanObject,
    mut v_inst_3239_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_zero_3240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: u8 = 0;
    v_zero_3240_ = crate::leanh::lean_ctor_get(v_natStruct_3238_, 13);
    v___x_3241_ = l_Lean_Expr_appArg_x21(v_zero_3240_);
    v___x_3242_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_3241_,
        v_inst_3239_,
    );
    crate::leanh::lean_dec_ref(v___x_3241_);
    return v___x_3242_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(
    mut v_natStruct_3243_: *mut crate::leanh::LeanObject,
    mut v_inst_3244_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3245_: u8 = 0;
    let mut v_r_3246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3245_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_3243_, v_inst_3244_);
    crate::leanh::lean_dec_ref(v_inst_3244_);
    crate::leanh::lean_dec_ref(v_natStruct_3243_);
    v_r_3246_ = crate::leanh::lean_box((v_res_3245_) as usize);
    return v_r_3246_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(
    mut v_natStruct_3247_: *mut crate::leanh::LeanObject,
    mut v_inst_3248_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_smulFn_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: u8 = 0;
    v_smulFn_3249_ = crate::leanh::lean_ctor_get(v_natStruct_3247_, 16);
    v___x_3250_ = l_Lean_Expr_appArg_x21(v_smulFn_3249_);
    v___x_3251_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_3250_,
        v_inst_3248_,
    );
    crate::leanh::lean_dec_ref(v___x_3250_);
    return v___x_3251_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(
    mut v_natStruct_3252_: *mut crate::leanh::LeanObject,
    mut v_inst_3253_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3254_: u8 = 0;
    let mut v_r_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3254_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_3252_, v_inst_3253_);
    crate::leanh::lean_dec_ref(v_inst_3253_);
    crate::leanh::lean_dec_ref(v_natStruct_3252_);
    v_r_3255_ = crate::leanh::lean_box((v_res_3254_) as usize);
    return v_r_3255_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(
    mut v_e_3301_: *mut crate::leanh::LeanObject,
    mut v_a_3302_: *mut crate::leanh::LeanObject,
    mut v_a_3303_: *mut crate::leanh::LeanObject,
    mut v_a_3304_: *mut crate::leanh::LeanObject,
    mut v_a_3305_: *mut crate::leanh::LeanObject,
    mut v_a_3306_: *mut crate::leanh::LeanObject,
    mut v_a_3307_: *mut crate::leanh::LeanObject,
    mut v_a_3308_: *mut crate::leanh::LeanObject,
    mut v_a_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3322_: u8 = 0;
    let mut v___x_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: u8 = 0;
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_3336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: u8 = 0;
    let mut v___x_3355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v___x_3363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v_fst_3368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v_addFn_3373_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3400_: u8 = 0;
    let mut v_fst_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3405_: u8 = 0;
    let mut v_nsmulFn_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3422_: u8 = 0;
    let mut v_isSharedCheck_3423_: u8 = 0;
    let mut v_type_3424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_3427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3432_: u8 = 0;
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_3435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3445_: u8 = 0;
    let mut v_a_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3453_: u8 = 0;
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_3456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_a_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_a_3478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_a_3486_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3314_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(
                    v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_,
                    v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_,
                );
                if crate::leanh::lean_obj_tag(v___x_3314_) == 0 {
                    v_a_3315_ = crate::leanh::lean_ctor_get(v___x_3314_, 0);
                    crate::leanh::lean_inc(v_a_3315_);
                    crate::leanh::lean_dec_ref_known(v___x_3314_, 1);
                    v___x_3316_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                        v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_,
                        v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3316_) == 0 {
                        v_a_3317_ = crate::leanh::lean_ctor_get(v___x_3316_, 0);
                        crate::leanh::lean_inc(v_a_3317_);
                        crate::leanh::lean_dec_ref_known(v___x_3316_, 1);
                        crate::leanh::lean_inc_ref(v_e_3301_);
                        v___x_3318_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3301_, v_a_3310_);
                        if crate::leanh::lean_obj_tag(v___x_3318_) == 0 {
                            v_a_3319_ = crate::leanh::lean_ctor_get(v___x_3318_, 0);
                            v_isSharedCheck_3469_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3318_)) as u8;
                            if v_isSharedCheck_3469_ == 0 {
                                v___x_3321_ = v___x_3318_;
                                v_isShared_3322_ = v_isSharedCheck_3469_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3319_);
                                crate::leanh::lean_dec(v___x_3318_);
                                v___x_3321_ = crate::leanh::lean_box(0);
                                v_isShared_3322_ = v_isSharedCheck_3469_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3317_);
                            crate::leanh::lean_dec(v_a_3315_);
                            crate::leanh::lean_dec_ref(v_e_3301_);
                            v_a_3470_ = crate::leanh::lean_ctor_get(v___x_3318_, 0);
                            v_isSharedCheck_3477_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3318_)) as u8;
                            if v_isSharedCheck_3477_ == 0 {
                                v___x_3472_ = v___x_3318_;
                                v_isShared_3473_ = v_isSharedCheck_3477_;
                                state = 17;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3470_);
                                crate::leanh::lean_dec(v___x_3318_);
                                v___x_3472_ = crate::leanh::lean_box(0);
                                v_isShared_3473_ = v_isSharedCheck_3477_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_3315_);
                        crate::leanh::lean_dec_ref(v_e_3301_);
                        v_a_3478_ = crate::leanh::lean_ctor_get(v___x_3316_, 0);
                        v_isSharedCheck_3485_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3316_)) as u8;
                        if v_isSharedCheck_3485_ == 0 {
                            v___x_3480_ = v___x_3316_;
                            v_isShared_3481_ = v_isSharedCheck_3485_;
                            state = 19;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3478_);
                            crate::leanh::lean_dec(v___x_3316_);
                            v___x_3480_ = crate::leanh::lean_box(0);
                            v_isShared_3481_ = v_isSharedCheck_3485_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3301_);
                    v_a_3486_ = crate::leanh::lean_ctor_get(v___x_3314_, 0);
                    v_isSharedCheck_3493_ = (!crate::leanh::lean_is_exclusive(v___x_3314_)) as u8;
                    if v_isSharedCheck_3493_ == 0 {
                        v___x_3488_ = v___x_3314_;
                        v_isShared_3489_ = v_isSharedCheck_3493_;
                        state = 21;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3486_);
                        crate::leanh::lean_dec(v___x_3314_);
                        v___x_3488_ = crate::leanh::lean_box(0);
                        v_isShared_3489_ = v_isSharedCheck_3493_;
                        state = 21;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3323_ = l_Lean_Expr_cleanupAnnotations(v_a_3319_);
                v___x_3324_ = l_Lean_Expr_isApp(v___x_3323_);
                if v___x_3324_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3323_);
                    crate::leanh::lean_del_object(v___x_3321_);
                    crate::leanh::lean_dec(v_a_3317_);
                    crate::leanh::lean_dec(v_a_3315_);
                    v___x_3325_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                    return v___x_3325_;
                } else {
                    v_arg_3326_ = crate::leanh::lean_ctor_get(v___x_3323_, 1);
                    crate::leanh::lean_inc_ref(v_arg_3326_);
                    v___x_3327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3323_);
                    v___x_3328_ = l_Lean_Expr_isApp(v___x_3327_);
                    if v___x_3328_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_3327_);
                        crate::leanh::lean_dec_ref(v_arg_3326_);
                        crate::leanh::lean_del_object(v___x_3321_);
                        crate::leanh::lean_dec(v_a_3317_);
                        crate::leanh::lean_dec(v_a_3315_);
                        v___x_3329_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                        return v___x_3329_;
                    } else {
                        v_arg_3330_ = crate::leanh::lean_ctor_get(v___x_3327_, 1);
                        crate::leanh::lean_inc_ref(v_arg_3330_);
                        v___x_3331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3327_);
                        v___x_3332_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2;
                        v___x_3333_ = l_Lean_Expr_isConstOf(v___x_3331_, v___x_3332_);
                        if v___x_3333_ == 0 {
                            crate::leanh::lean_del_object(v___x_3321_);
                            v___x_3334_ = l_Lean_Expr_isApp(v___x_3331_);
                            if v___x_3334_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_3331_);
                                crate::leanh::lean_dec_ref(v_arg_3330_);
                                crate::leanh::lean_dec_ref(v_arg_3326_);
                                crate::leanh::lean_dec(v_a_3317_);
                                crate::leanh::lean_dec(v_a_3315_);
                                v___x_3335_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                return v___x_3335_;
                            } else {
                                v_arg_3336_ = crate::leanh::lean_ctor_get(v___x_3331_, 1);
                                crate::leanh::lean_inc_ref(v_arg_3336_);
                                v___x_3337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3331_);
                                v___x_3338_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5;
                                v___x_3339_ = l_Lean_Expr_isConstOf(v___x_3337_, v___x_3338_);
                                if v___x_3339_ == 0 {
                                    v___x_3340_ = l_Lean_Expr_isApp(v___x_3337_);
                                    if v___x_3340_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_3337_);
                                        crate::leanh::lean_dec_ref(v_arg_3336_);
                                        crate::leanh::lean_dec_ref(v_arg_3330_);
                                        crate::leanh::lean_dec_ref(v_arg_3326_);
                                        crate::leanh::lean_dec(v_a_3317_);
                                        crate::leanh::lean_dec(v_a_3315_);
                                        v___x_3341_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                        return v___x_3341_;
                                    } else {
                                        v___x_3342_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3337_);
                                        v___x_3343_ = l_Lean_Expr_isApp(v___x_3342_);
                                        if v___x_3343_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_3342_);
                                            crate::leanh::lean_dec_ref(v_arg_3336_);
                                            crate::leanh::lean_dec_ref(v_arg_3330_);
                                            crate::leanh::lean_dec_ref(v_arg_3326_);
                                            crate::leanh::lean_dec(v_a_3317_);
                                            crate::leanh::lean_dec(v_a_3315_);
                                            v___x_3344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                            return v___x_3344_;
                                        } else {
                                            v___x_3345_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3342_);
                                            v___x_3346_ = l_Lean_Expr_isApp(v___x_3345_);
                                            if v___x_3346_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_3345_);
                                                crate::leanh::lean_dec_ref(v_arg_3336_);
                                                crate::leanh::lean_dec_ref(v_arg_3330_);
                                                crate::leanh::lean_dec_ref(v_arg_3326_);
                                                crate::leanh::lean_dec(v_a_3317_);
                                                crate::leanh::lean_dec(v_a_3315_);
                                                v___x_3347_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                return v___x_3347_;
                                            } else {
                                                v___x_3348_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_3345_);
                                                v___x_3349_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8;
                                                v___x_3350_ =
                                                    l_Lean_Expr_isConstOf(v___x_3348_, v___x_3349_);
                                                if v___x_3350_ == 0 {
                                                    v___x_3351_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11;
                                                    v___x_3352_ = l_Lean_Expr_isConstOf(
                                                        v___x_3348_,
                                                        v___x_3351_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_3348_);
                                                    if v___x_3352_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_3336_);
                                                        crate::leanh::lean_dec_ref(v_arg_3330_);
                                                        crate::leanh::lean_dec_ref(v_arg_3326_);
                                                        crate::leanh::lean_dec(v_a_3317_);
                                                        crate::leanh::lean_dec(v_a_3315_);
                                                        v___x_3353_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                        return v___x_3353_;
                                                    } else {
                                                        v___x_3354_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_3317_, v_arg_3336_);
                                                        crate::leanh::lean_dec_ref(v_arg_3336_);
                                                        if v___x_3354_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_arg_3330_);
                                                            crate::leanh::lean_dec_ref(v_arg_3326_);
                                                            crate::leanh::lean_dec(v_a_3317_);
                                                            crate::leanh::lean_dec(v_a_3315_);
                                                            v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                            return v___x_3355_;
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_e_3301_);
                                                            crate::leanh::lean_inc_ref(v_arg_3330_);
                                                            v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_3330_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_3356_,
                                                            ) == 0
                                                            {
                                                                v_a_3357_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_3356_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_3357_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_3356_,
                                                                    1,
                                                                );
                                                                v_fst_3358_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_a_3357_, 0,
                                                                    );
                                                                v_snd_3359_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_a_3357_, 1,
                                                                    );
                                                                v_isSharedCheck_3393_ = (!crate::leanh::lean_is_exclusive(v_a_3357_)) as u8;
                                                                if v_isSharedCheck_3393_ == 0 {
                                                                    v___x_3361_ = v_a_3357_;
                                                                    v_isShared_3362_ =
                                                                        v_isSharedCheck_3393_;
                                                                    state = 2;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_snd_3359_,
                                                                    );
                                                                    crate::leanh::lean_inc(
                                                                        v_fst_3358_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v_a_3357_,
                                                                    );
                                                                    v___x_3361_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_3362_ =
                                                                        v_isSharedCheck_3393_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3330_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_3326_,
                                                                );
                                                                crate::leanh::lean_dec(v_a_3317_);
                                                                crate::leanh::lean_dec(v_a_3315_);
                                                                return v___x_3356_;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_3348_);
                                                    v___x_3394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_3317_, v_arg_3336_);
                                                    crate::leanh::lean_dec_ref(v_arg_3336_);
                                                    if v___x_3394_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_3330_);
                                                        crate::leanh::lean_dec_ref(v_arg_3326_);
                                                        crate::leanh::lean_dec(v_a_3317_);
                                                        crate::leanh::lean_dec(v_a_3315_);
                                                        v___x_3395_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                        return v___x_3395_;
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v_e_3301_);
                                                        crate::leanh::lean_inc_ref(v_arg_3326_);
                                                        v___x_3396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_3326_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                        if crate::leanh::lean_obj_tag(v___x_3396_)
                                                            == 0
                                                        {
                                                            v_a_3397_ = crate::leanh::lean_ctor_get(
                                                                v___x_3396_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_3423_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_3396_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_3423_ == 0 {
                                                                v___x_3399_ = v___x_3396_;
                                                                v_isShared_3400_ =
                                                                    v_isSharedCheck_3423_;
                                                                state = 8;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_3397_);
                                                                crate::leanh::lean_dec(v___x_3396_);
                                                                v___x_3399_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_3400_ =
                                                                    v_isSharedCheck_3423_;
                                                                state = 8;
                                                                continue;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_3330_);
                                                            crate::leanh::lean_dec_ref(v_arg_3326_);
                                                            crate::leanh::lean_dec(v_a_3317_);
                                                            crate::leanh::lean_dec(v_a_3315_);
                                                            return v___x_3396_;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_3337_);
                                    crate::leanh::lean_dec_ref(v_arg_3336_);
                                    crate::leanh::lean_dec_ref(v_arg_3330_);
                                    crate::leanh::lean_dec_ref(v_arg_3326_);
                                    v_type_3424_ = crate::leanh::lean_ctor_get(v_a_3317_, 2);
                                    crate::leanh::lean_inc_ref(v_type_3424_);
                                    v_u_3425_ = crate::leanh::lean_ctor_get(v_a_3317_, 3);
                                    crate::leanh::lean_inc(v_u_3425_);
                                    v_natModuleInst_3426_ =
                                        crate::leanh::lean_ctor_get(v_a_3317_, 4);
                                    crate::leanh::lean_inc_ref(v_natModuleInst_3426_);
                                    v_zero_3427_ = crate::leanh::lean_ctor_get(v_a_3317_, 13);
                                    crate::leanh::lean_inc_ref(v_zero_3427_);
                                    crate::leanh::lean_dec(v_a_3317_);
                                    crate::leanh::lean_inc_ref(v_e_3301_);
                                    v___x_3428_ = l_Lean_Meta_isDefEqD(
                                        v_e_3301_,
                                        v_zero_3427_,
                                        v_a_3309_,
                                        v_a_3310_,
                                        v_a_3311_,
                                        v_a_3312_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_3428_) == 0 {
                                        v_a_3429_ = crate::leanh::lean_ctor_get(v___x_3428_, 0);
                                        v_isSharedCheck_3445_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3428_)) as u8;
                                        if v_isSharedCheck_3445_ == 0 {
                                            v___x_3431_ = v___x_3428_;
                                            v_isShared_3432_ = v_isSharedCheck_3445_;
                                            state = 12;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3429_);
                                            crate::leanh::lean_dec(v___x_3428_);
                                            v___x_3431_ = crate::leanh::lean_box(0);
                                            v_isShared_3432_ = v_isSharedCheck_3445_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_natModuleInst_3426_);
                                        crate::leanh::lean_dec(v_u_3425_);
                                        crate::leanh::lean_dec_ref(v_type_3424_);
                                        crate::leanh::lean_dec(v_a_3315_);
                                        crate::leanh::lean_dec_ref(v_e_3301_);
                                        v_a_3446_ = crate::leanh::lean_ctor_get(v___x_3428_, 0);
                                        v_isSharedCheck_3453_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_3428_)) as u8;
                                        if v_isSharedCheck_3453_ == 0 {
                                            v___x_3448_ = v___x_3428_;
                                            v_isShared_3449_ = v_isSharedCheck_3453_;
                                            state = 14;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_3446_);
                                            crate::leanh::lean_dec(v___x_3428_);
                                            v___x_3448_ = crate::leanh::lean_box(0);
                                            v_isShared_3449_ = v_isSharedCheck_3453_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_3331_);
                            crate::leanh::lean_dec_ref(v_arg_3330_);
                            v___x_3454_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_3317_, v_arg_3326_);
                            crate::leanh::lean_dec_ref(v_arg_3326_);
                            if v___x_3454_ == 0 {
                                crate::leanh::lean_del_object(v___x_3321_);
                                crate::leanh::lean_dec(v_a_3317_);
                                crate::leanh::lean_dec(v_a_3315_);
                                v___x_3455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                return v___x_3455_;
                            } else {
                                crate::leanh::lean_dec_ref(v_e_3301_);
                                v_zero_3456_ = crate::leanh::lean_ctor_get(v_a_3315_, 17);
                                crate::leanh::lean_inc_ref(v_zero_3456_);
                                crate::leanh::lean_dec(v_a_3315_);
                                v_type_3457_ = crate::leanh::lean_ctor_get(v_a_3317_, 2);
                                crate::leanh::lean_inc_ref(v_type_3457_);
                                v_u_3458_ = crate::leanh::lean_ctor_get(v_a_3317_, 3);
                                crate::leanh::lean_inc(v_u_3458_);
                                v_natModuleInst_3459_ = crate::leanh::lean_ctor_get(v_a_3317_, 4);
                                crate::leanh::lean_inc_ref(v_natModuleInst_3459_);
                                crate::leanh::lean_dec(v_a_3317_);
                                v___x_3460_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21;
                                v___x_3461_ = crate::leanh::lean_box(0);
                                v___x_3462_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3462_, 0, v_u_3458_);
                                crate::leanh::lean_ctor_set(v___x_3462_, 1, v___x_3461_);
                                v___x_3463_ = l_Lean_mkConst(v___x_3460_, v___x_3462_);
                                v___x_3464_ =
                                    l_Lean_mkAppB(v___x_3463_, v_type_3457_, v_natModuleInst_3459_);
                                v___x_3465_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_3465_, 0, v_zero_3456_);
                                crate::leanh::lean_ctor_set(v___x_3465_, 1, v___x_3464_);
                                if v_isShared_3322_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_3321_, 0, v___x_3465_);
                                    v___x_3467_ = v___x_3321_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3468_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_3468_,
                                        0,
                                        v___x_3465_,
                                    );
                                    v___x_3467_ = v_reuseFailAlloc_3468_;
                                    state = 16;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                crate::leanh::lean_inc_ref(v_arg_3326_);
                v___x_3363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_3326_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                if crate::leanh::lean_obj_tag(v___x_3363_) == 0 {
                    v_a_3364_ = crate::leanh::lean_ctor_get(v___x_3363_, 0);
                    v_isSharedCheck_3392_ = (!crate::leanh::lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3392_ == 0 {
                        v___x_3366_ = v___x_3363_;
                        v_isShared_3367_ = v_isSharedCheck_3392_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3364_);
                        crate::leanh::lean_dec(v___x_3363_);
                        v___x_3366_ = crate::leanh::lean_box(0);
                        v_isShared_3367_ = v_isSharedCheck_3392_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3361_);
                    crate::leanh::lean_dec(v_snd_3359_);
                    crate::leanh::lean_dec(v_fst_3358_);
                    crate::leanh::lean_dec_ref(v_arg_3330_);
                    crate::leanh::lean_dec_ref(v_arg_3326_);
                    crate::leanh::lean_dec(v_a_3317_);
                    crate::leanh::lean_dec(v_a_3315_);
                    return v___x_3363_;
                }
            }
            3 => {
                v_fst_3368_ = crate::leanh::lean_ctor_get(v_a_3364_, 0);
                v_snd_3369_ = crate::leanh::lean_ctor_get(v_a_3364_, 1);
                v_isSharedCheck_3391_ = (!crate::leanh::lean_is_exclusive(v_a_3364_)) as u8;
                if v_isSharedCheck_3391_ == 0 {
                    v___x_3371_ = v_a_3364_;
                    v_isShared_3372_ = v_isSharedCheck_3391_;
                    state = 4;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3369_);
                    crate::leanh::lean_inc(v_fst_3368_);
                    crate::leanh::lean_dec(v_a_3364_);
                    v___x_3371_ = crate::leanh::lean_box(0);
                    v_isShared_3372_ = v_isSharedCheck_3391_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_addFn_3373_ = crate::leanh::lean_ctor_get(v_a_3315_, 22);
                crate::leanh::lean_inc_ref(v_addFn_3373_);
                crate::leanh::lean_dec(v_a_3315_);
                v_type_3374_ = crate::leanh::lean_ctor_get(v_a_3317_, 2);
                crate::leanh::lean_inc_ref(v_type_3374_);
                v_u_3375_ = crate::leanh::lean_ctor_get(v_a_3317_, 3);
                crate::leanh::lean_inc(v_u_3375_);
                v_natModuleInst_3376_ = crate::leanh::lean_ctor_get(v_a_3317_, 4);
                crate::leanh::lean_inc_ref(v_natModuleInst_3376_);
                crate::leanh::lean_dec(v_a_3317_);
                crate::leanh::lean_inc(v_fst_3368_);
                crate::leanh::lean_inc(v_fst_3358_);
                v___x_3377_ = l_Lean_mkAppB(v_addFn_3373_, v_fst_3358_, v_fst_3368_);
                v___x_3378_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17;
                v___x_3379_ = crate::leanh::lean_box(0);
                if v_isShared_3362_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_3361_, 1);
                    crate::leanh::lean_ctor_set(v___x_3361_, 1, v___x_3379_);
                    crate::leanh::lean_ctor_set(v___x_3361_, 0, v_u_3375_);
                    v___x_3381_ = v___x_3361_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_u_3375_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3379_);
                    v___x_3381_ = v_reuseFailAlloc_3390_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_3382_ = l_Lean_mkConst(v___x_3378_, v___x_3381_);
                v___x_3383_ = l_Lean_mkApp8(
                    v___x_3382_,
                    v_type_3374_,
                    v_natModuleInst_3376_,
                    v_arg_3330_,
                    v_arg_3326_,
                    v_fst_3358_,
                    v_fst_3368_,
                    v_snd_3359_,
                    v_snd_3369_,
                );
                if v_isShared_3372_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3371_, 1, v___x_3383_);
                    crate::leanh::lean_ctor_set(v___x_3371_, 0, v___x_3377_);
                    v___x_3385_ = v___x_3371_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3377_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3383_);
                    v___x_3385_ = v_reuseFailAlloc_3389_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3367_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3366_, 0, v___x_3385_);
                    v___x_3387_ = v___x_3366_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3387_;
            }
            8 => {
                v_fst_3401_ = crate::leanh::lean_ctor_get(v_a_3397_, 0);
                v_snd_3402_ = crate::leanh::lean_ctor_get(v_a_3397_, 1);
                v_isSharedCheck_3422_ = (!crate::leanh::lean_is_exclusive(v_a_3397_)) as u8;
                if v_isSharedCheck_3422_ == 0 {
                    v___x_3404_ = v_a_3397_;
                    v_isShared_3405_ = v_isSharedCheck_3422_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_snd_3402_);
                    crate::leanh::lean_inc(v_fst_3401_);
                    crate::leanh::lean_dec(v_a_3397_);
                    v___x_3404_ = crate::leanh::lean_box(0);
                    v_isShared_3405_ = v_isSharedCheck_3422_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_nsmulFn_3406_ = crate::leanh::lean_ctor_get(v_a_3315_, 24);
                crate::leanh::lean_inc_ref(v_nsmulFn_3406_);
                crate::leanh::lean_dec(v_a_3315_);
                v_type_3407_ = crate::leanh::lean_ctor_get(v_a_3317_, 2);
                crate::leanh::lean_inc_ref(v_type_3407_);
                v_u_3408_ = crate::leanh::lean_ctor_get(v_a_3317_, 3);
                crate::leanh::lean_inc(v_u_3408_);
                v_natModuleInst_3409_ = crate::leanh::lean_ctor_get(v_a_3317_, 4);
                crate::leanh::lean_inc_ref(v_natModuleInst_3409_);
                crate::leanh::lean_dec(v_a_3317_);
                crate::leanh::lean_inc(v_fst_3401_);
                crate::leanh::lean_inc_ref(v_arg_3330_);
                v___x_3410_ = l_Lean_mkAppB(v_nsmulFn_3406_, v_arg_3330_, v_fst_3401_);
                v___x_3411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19;
                v___x_3412_ = crate::leanh::lean_box(0);
                v___x_3413_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3413_, 0, v_u_3408_);
                crate::leanh::lean_ctor_set(v___x_3413_, 1, v___x_3412_);
                v___x_3414_ = l_Lean_mkConst(v___x_3411_, v___x_3413_);
                v___x_3415_ = l_Lean_mkApp6(
                    v___x_3414_,
                    v_type_3407_,
                    v_natModuleInst_3409_,
                    v_arg_3330_,
                    v_arg_3326_,
                    v_fst_3401_,
                    v_snd_3402_,
                );
                if v_isShared_3405_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3404_, 1, v___x_3415_);
                    crate::leanh::lean_ctor_set(v___x_3404_, 0, v___x_3410_);
                    v___x_3417_ = v___x_3404_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3410_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3415_);
                    v___x_3417_ = v_reuseFailAlloc_3421_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3400_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3399_, 0, v___x_3417_);
                    v___x_3419_ = v___x_3399_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3420_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
                    v___x_3419_ = v_reuseFailAlloc_3420_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3419_;
            }
            12 => {
                v___x_3433_ = (crate::leanh::lean_unbox(v_a_3429_) as u8);
                crate::leanh::lean_dec(v_a_3429_);
                if v___x_3433_ == 0 {
                    crate::leanh::lean_del_object(v___x_3431_);
                    crate::leanh::lean_dec_ref(v_natModuleInst_3426_);
                    crate::leanh::lean_dec(v_u_3425_);
                    crate::leanh::lean_dec_ref(v_type_3424_);
                    crate::leanh::lean_dec(v_a_3315_);
                    v___x_3434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                    return v___x_3434_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_3301_);
                    v_zero_3435_ = crate::leanh::lean_ctor_get(v_a_3315_, 17);
                    crate::leanh::lean_inc_ref(v_zero_3435_);
                    crate::leanh::lean_dec(v_a_3315_);
                    v___x_3436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21;
                    v___x_3437_ = crate::leanh::lean_box(0);
                    v___x_3438_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3438_, 0, v_u_3425_);
                    crate::leanh::lean_ctor_set(v___x_3438_, 1, v___x_3437_);
                    v___x_3439_ = l_Lean_mkConst(v___x_3436_, v___x_3438_);
                    v___x_3440_ = l_Lean_mkAppB(v___x_3439_, v_type_3424_, v_natModuleInst_3426_);
                    v___x_3441_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3441_, 0, v_zero_3435_);
                    crate::leanh::lean_ctor_set(v___x_3441_, 1, v___x_3440_);
                    if v_isShared_3432_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3431_, 0, v___x_3441_);
                        v___x_3443_ = v___x_3431_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3444_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
                        v___x_3443_ = v_reuseFailAlloc_3444_;
                        state = 13;
                        continue;
                    }
                }
            }
            13 => {
                return v___x_3443_;
            }
            14 => {
                if v_isShared_3449_ == 0 {
                    v___x_3451_ = v___x_3448_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_3452_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
                    v___x_3451_ = v_reuseFailAlloc_3452_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_3451_;
            }
            16 => {
                return v___x_3467_;
            }
            17 => {
                if v_isShared_3473_ == 0 {
                    v___x_3475_ = v___x_3472_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3476_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
                    v___x_3475_ = v_reuseFailAlloc_3476_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3475_;
            }
            19 => {
                if v_isShared_3481_ == 0 {
                    v___x_3483_ = v___x_3480_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_3484_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
                    v___x_3483_ = v_reuseFailAlloc_3484_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                return v___x_3483_;
            }
            21 => {
                if v_isShared_3489_ == 0 {
                    v___x_3491_ = v___x_3488_;
                    state = 22;
                    continue;
                } else {
                    v_reuseFailAlloc_3492_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
                    v___x_3491_ = v_reuseFailAlloc_3492_;
                    state = 22;
                    continue;
                }
            }
            22 => {
                return v___x_3491_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___boxed(
    mut v_e_3494_: *mut crate::leanh::LeanObject,
    mut v_a_3495_: *mut crate::leanh::LeanObject,
    mut v_a_3496_: *mut crate::leanh::LeanObject,
    mut v_a_3497_: *mut crate::leanh::LeanObject,
    mut v_a_3498_: *mut crate::leanh::LeanObject,
    mut v_a_3499_: *mut crate::leanh::LeanObject,
    mut v_a_3500_: *mut crate::leanh::LeanObject,
    mut v_a_3501_: *mut crate::leanh::LeanObject,
    mut v_a_3502_: *mut crate::leanh::LeanObject,
    mut v_a_3503_: *mut crate::leanh::LeanObject,
    mut v_a_3504_: *mut crate::leanh::LeanObject,
    mut v_a_3505_: *mut crate::leanh::LeanObject,
    mut v_a_3506_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3507_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
    crate::leanh::lean_dec(v_a_3505_);
    crate::leanh::lean_dec_ref(v_a_3504_);
    crate::leanh::lean_dec(v_a_3503_);
    crate::leanh::lean_dec_ref(v_a_3502_);
    crate::leanh::lean_dec(v_a_3501_);
    crate::leanh::lean_dec_ref(v_a_3500_);
    crate::leanh::lean_dec(v_a_3499_);
    crate::leanh::lean_dec_ref(v_a_3498_);
    crate::leanh::lean_dec(v_a_3497_);
    crate::leanh::lean_dec(v_a_3496_);
    crate::leanh::lean_dec(v_a_3495_);
    return v_res_3507_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v_e_3509_: *mut crate::leanh::LeanObject,
    mut v_____x_3510_: *mut crate::leanh::LeanObject,
    mut v_s_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_structs_3512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_3516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natStructs_3517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: u8 = 0;
    let mut v___x_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v_v_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_id_3526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structId_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_3533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_3535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_3537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_rfl__q_3538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toQFn_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_addFn_3541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_smulFn_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_termMap_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3557_: u8 = 0;
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_unused_3559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_unused_3566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3512_ = crate::leanh::lean_ctor_get(v_s_3511_, 0);
                v_typeIdOf_3513_ = crate::leanh::lean_ctor_get(v_s_3511_, 1);
                v_exprToStructId_3514_ = crate::leanh::lean_ctor_get(v_s_3511_, 2);
                v_exprToStructIdEntries_3515_ = crate::leanh::lean_ctor_get(v_s_3511_, 3);
                v_forbiddenNatModules_3516_ = crate::leanh::lean_ctor_get(v_s_3511_, 4);
                v_natStructs_3517_ = crate::leanh::lean_ctor_get(v_s_3511_, 5);
                v_natTypeIdOf_3518_ = crate::leanh::lean_ctor_get(v_s_3511_, 6);
                v_exprToNatStructId_3519_ = crate::leanh::lean_ctor_get(v_s_3511_, 7);
                v___x_3520_ = lean_array_get_size(v_natStructs_3517_);
                v___x_3521_ = lean_nat_dec_lt(v___y_3508_, v___x_3520_);
                if v___x_3521_ == 0 {
                    crate::leanh::lean_dec_ref(v_____x_3510_);
                    crate::leanh::lean_dec_ref(v_e_3509_);
                    return v_s_3511_;
                } else {
                    crate::leanh::lean_inc_ref(v_exprToNatStructId_3519_);
                    crate::leanh::lean_inc_ref(v_natTypeIdOf_3518_);
                    crate::leanh::lean_inc_ref(v_natStructs_3517_);
                    crate::leanh::lean_inc_ref(v_forbiddenNatModules_3516_);
                    crate::leanh::lean_inc_ref(v_exprToStructIdEntries_3515_);
                    crate::leanh::lean_inc_ref(v_exprToStructId_3514_);
                    crate::leanh::lean_inc_ref(v_typeIdOf_3513_);
                    crate::leanh::lean_inc_ref(v_structs_3512_);
                    v_isSharedCheck_3558_ = (!crate::leanh::lean_is_exclusive(v_s_3511_)) as u8;
                    if v_isSharedCheck_3558_ == 0 {
                        v_unused_3559_ = crate::leanh::lean_ctor_get(v_s_3511_, 7);
                        crate::leanh::lean_dec(v_unused_3559_);
                        v_unused_3560_ = crate::leanh::lean_ctor_get(v_s_3511_, 6);
                        crate::leanh::lean_dec(v_unused_3560_);
                        v_unused_3561_ = crate::leanh::lean_ctor_get(v_s_3511_, 5);
                        crate::leanh::lean_dec(v_unused_3561_);
                        v_unused_3562_ = crate::leanh::lean_ctor_get(v_s_3511_, 4);
                        crate::leanh::lean_dec(v_unused_3562_);
                        v_unused_3563_ = crate::leanh::lean_ctor_get(v_s_3511_, 3);
                        crate::leanh::lean_dec(v_unused_3563_);
                        v_unused_3564_ = crate::leanh::lean_ctor_get(v_s_3511_, 2);
                        crate::leanh::lean_dec(v_unused_3564_);
                        v_unused_3565_ = crate::leanh::lean_ctor_get(v_s_3511_, 1);
                        crate::leanh::lean_dec(v_unused_3565_);
                        v_unused_3566_ = crate::leanh::lean_ctor_get(v_s_3511_, 0);
                        crate::leanh::lean_dec(v_unused_3566_);
                        v___x_3523_ = v_s_3511_;
                        v_isShared_3524_ = v_isSharedCheck_3558_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_s_3511_);
                        v___x_3523_ = crate::leanh::lean_box(0);
                        v_isShared_3524_ = v_isSharedCheck_3558_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3525_ = lean_array_fget(v_natStructs_3517_, v___y_3508_);
                v_id_3526_ = crate::leanh::lean_ctor_get(v_v_3525_, 0);
                v_structId_3527_ = crate::leanh::lean_ctor_get(v_v_3525_, 1);
                v_type_3528_ = crate::leanh::lean_ctor_get(v_v_3525_, 2);
                v_u_3529_ = crate::leanh::lean_ctor_get(v_v_3525_, 3);
                v_natModuleInst_3530_ = crate::leanh::lean_ctor_get(v_v_3525_, 4);
                v_leInst_x3f_3531_ = crate::leanh::lean_ctor_get(v_v_3525_, 5);
                v_ltInst_x3f_3532_ = crate::leanh::lean_ctor_get(v_v_3525_, 6);
                v_lawfulOrderLTInst_x3f_3533_ = crate::leanh::lean_ctor_get(v_v_3525_, 7);
                v_isPreorderInst_x3f_3534_ = crate::leanh::lean_ctor_get(v_v_3525_, 8);
                v_orderedAddInst_x3f_3535_ = crate::leanh::lean_ctor_get(v_v_3525_, 9);
                v_isLinearInst_x3f_3536_ = crate::leanh::lean_ctor_get(v_v_3525_, 10);
                v_addRightCancelInst_x3f_3537_ = crate::leanh::lean_ctor_get(v_v_3525_, 11);
                v_rfl__q_3538_ = crate::leanh::lean_ctor_get(v_v_3525_, 12);
                v_zero_3539_ = crate::leanh::lean_ctor_get(v_v_3525_, 13);
                v_toQFn_3540_ = crate::leanh::lean_ctor_get(v_v_3525_, 14);
                v_addFn_3541_ = crate::leanh::lean_ctor_get(v_v_3525_, 15);
                v_smulFn_3542_ = crate::leanh::lean_ctor_get(v_v_3525_, 16);
                v_termMap_3543_ = crate::leanh::lean_ctor_get(v_v_3525_, 17);
                v_isSharedCheck_3557_ = (!crate::leanh::lean_is_exclusive(v_v_3525_)) as u8;
                if v_isSharedCheck_3557_ == 0 {
                    v___x_3545_ = v_v_3525_;
                    v_isShared_3546_ = v_isSharedCheck_3557_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_termMap_3543_);
                    crate::leanh::lean_inc(v_smulFn_3542_);
                    crate::leanh::lean_inc(v_addFn_3541_);
                    crate::leanh::lean_inc(v_toQFn_3540_);
                    crate::leanh::lean_inc(v_zero_3539_);
                    crate::leanh::lean_inc(v_rfl__q_3538_);
                    crate::leanh::lean_inc(v_addRightCancelInst_x3f_3537_);
                    crate::leanh::lean_inc(v_isLinearInst_x3f_3536_);
                    crate::leanh::lean_inc(v_orderedAddInst_x3f_3535_);
                    crate::leanh::lean_inc(v_isPreorderInst_x3f_3534_);
                    crate::leanh::lean_inc(v_lawfulOrderLTInst_x3f_3533_);
                    crate::leanh::lean_inc(v_ltInst_x3f_3532_);
                    crate::leanh::lean_inc(v_leInst_x3f_3531_);
                    crate::leanh::lean_inc(v_natModuleInst_3530_);
                    crate::leanh::lean_inc(v_u_3529_);
                    crate::leanh::lean_inc(v_type_3528_);
                    crate::leanh::lean_inc(v_structId_3527_);
                    crate::leanh::lean_inc(v_id_3526_);
                    crate::leanh::lean_dec(v_v_3525_);
                    v___x_3545_ = crate::leanh::lean_box(0);
                    v_isShared_3546_ = v_isSharedCheck_3557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3547_ = crate::leanh::lean_box(0);
                v_xs_x27_3548_ = lean_array_fset(v_natStructs_3517_, v___y_3508_, v___x_3547_);
                v___x_3549_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_3543_, v_e_3509_, v_____x_3510_);
                if v_isShared_3546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3545_, 17, v___x_3549_);
                    v___x_3551_ = v___x_3545_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = crate::leanh::lean_alloc_ctor(0, 18, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_id_3526_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_structId_3527_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_type_3528_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 3, v_u_3529_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 4, v_natModuleInst_3530_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 5, v_leInst_x3f_3531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 6, v_ltInst_x3f_3532_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3556_,
                        7,
                        v_lawfulOrderLTInst_x3f_3533_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3556_,
                        8,
                        v_isPreorderInst_x3f_3534_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3556_,
                        9,
                        v_orderedAddInst_x3f_3535_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3556_,
                        10,
                        v_isLinearInst_x3f_3536_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3556_,
                        11,
                        v_addRightCancelInst_x3f_3537_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 12, v_rfl__q_3538_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 13, v_zero_3539_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 14, v_toQFn_3540_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 15, v_addFn_3541_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 16, v_smulFn_3542_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3556_, 17, v___x_3549_);
                    v___x_3551_ = v_reuseFailAlloc_3556_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3552_ = lean_array_fset(v_xs_x27_3548_, v___y_3508_, v___x_3551_);
                if v_isShared_3524_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3523_, 5, v___x_3552_);
                    v___x_3554_ = v___x_3523_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3555_ = crate::leanh::lean_alloc_ctor(0, 8, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_structs_3512_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_typeIdOf_3513_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_exprToStructId_3514_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3555_,
                        3,
                        v_exprToStructIdEntries_3515_,
                    );
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3555_,
                        4,
                        v_forbiddenNatModules_3516_,
                    );
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 5, v___x_3552_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3555_, 6, v_natTypeIdOf_3518_);
                    crate::leanh::lean_ctor_set(
                        v_reuseFailAlloc_3555_,
                        7,
                        v_exprToNatStructId_3519_,
                    );
                    v___x_3554_ = v_reuseFailAlloc_3555_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3554_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed(
    mut v___y_3567_: *mut crate::leanh::LeanObject,
    mut v_e_3568_: *mut crate::leanh::LeanObject,
    mut v_____x_3569_: *mut crate::leanh::LeanObject,
    mut v_s_3570_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3571_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(
        v___y_3567_,
        v_e_3568_,
        v_____x_3569_,
        v_s_3570_,
    );
    crate::leanh::lean_dec(v___y_3567_);
    return v_res_3571_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofNatModule(
    mut v_e_3572_: *mut crate::leanh::LeanObject,
    mut v_a_3573_: *mut crate::leanh::LeanObject,
    mut v_a_3574_: *mut crate::leanh::LeanObject,
    mut v_a_3575_: *mut crate::leanh::LeanObject,
    mut v_a_3576_: *mut crate::leanh::LeanObject,
    mut v_a_3577_: *mut crate::leanh::LeanObject,
    mut v_a_3578_: *mut crate::leanh::LeanObject,
    mut v_a_3579_: *mut crate::leanh::LeanObject,
    mut v_a_3580_: *mut crate::leanh::LeanObject,
    mut v_a_3581_: *mut crate::leanh::LeanObject,
    mut v_a_3582_: *mut crate::leanh::LeanObject,
    mut v_a_3583_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____x_3586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut v_unused_3606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut v_a_3615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v___x_3623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3624_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v_termMap_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_3643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_expr_3644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3658_: u8 = 0;
    let mut v_expr_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_a_3673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3623_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_,
                    v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_,
                );
                if crate::leanh::lean_obj_tag(v___x_3623_) == 0 {
                    v_a_3624_ = crate::leanh::lean_ctor_get(v___x_3623_, 0);
                    v_isSharedCheck_3672_ = (!crate::leanh::lean_is_exclusive(v___x_3623_)) as u8;
                    if v_isSharedCheck_3672_ == 0 {
                        v___x_3626_ = v___x_3623_;
                        v_isShared_3627_ = v_isSharedCheck_3672_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3624_);
                        crate::leanh::lean_dec(v___x_3623_);
                        v___x_3626_ = crate::leanh::lean_box(0);
                        v_isShared_3627_ = v_isSharedCheck_3672_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_3572_);
                    v_a_3673_ = crate::leanh::lean_ctor_get(v___x_3623_, 0);
                    v_isSharedCheck_3680_ = (!crate::leanh::lean_is_exclusive(v___x_3623_)) as u8;
                    if v_isSharedCheck_3680_ == 0 {
                        v___x_3675_ = v___x_3623_;
                        v_isShared_3676_ = v_isSharedCheck_3680_;
                        state = 17;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3673_);
                        crate::leanh::lean_dec(v___x_3623_);
                        v___x_3675_ = crate::leanh::lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3680_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                crate::leanh::lean_inc_ref(v_e_3572_);
                v___x_3595_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
                    v_e_3572_,
                    v___y_3587_,
                    v___y_3588_,
                    v___y_3589_,
                    v___y_3590_,
                    v___y_3591_,
                    v___y_3592_,
                    v___y_3593_,
                    v___y_3594_,
                );
                if crate::leanh::lean_obj_tag(v___x_3595_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_3595_, 1);
                    crate::leanh::lean_inc_ref(v_____x_3586_);
                    crate::leanh::lean_inc(v___y_3587_);
                    v___f_3596_ = crate::leanh::lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    crate::leanh::lean_closure_set(v___f_3596_, 0, v___y_3587_);
                    crate::leanh::lean_closure_set(v___f_3596_, 1, v_e_3572_);
                    crate::leanh::lean_closure_set(v___f_3596_, 2, v_____x_3586_);
                    v___x_3597_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                    v___x_3598_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3597_, v___f_3596_, v___y_3588_);
                    if crate::leanh::lean_obj_tag(v___x_3598_) == 0 {
                        v_isSharedCheck_3605_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3598_)) as u8;
                        if v_isSharedCheck_3605_ == 0 {
                            v_unused_3606_ = crate::leanh::lean_ctor_get(v___x_3598_, 0);
                            crate::leanh::lean_dec(v_unused_3606_);
                            v___x_3600_ = v___x_3598_;
                            v_isShared_3601_ = v_isSharedCheck_3605_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v___x_3598_);
                            v___x_3600_ = crate::leanh::lean_box(0);
                            v_isShared_3601_ = v_isSharedCheck_3605_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_____x_3586_);
                        v_a_3607_ = crate::leanh::lean_ctor_get(v___x_3598_, 0);
                        v_isSharedCheck_3614_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3598_)) as u8;
                        if v_isSharedCheck_3614_ == 0 {
                            v___x_3609_ = v___x_3598_;
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3607_);
                            crate::leanh::lean_dec(v___x_3598_);
                            v___x_3609_ = crate::leanh::lean_box(0);
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_____x_3586_);
                    crate::leanh::lean_dec_ref(v_e_3572_);
                    v_a_3615_ = crate::leanh::lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3622_ = (!crate::leanh::lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3622_ == 0 {
                        v___x_3617_ = v___x_3595_;
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3615_);
                        crate::leanh::lean_dec(v___x_3595_);
                        v___x_3617_ = crate::leanh::lean_box(0);
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3600_, 0, v_____x_3586_);
                    v___x_3603_ = v___x_3600_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_____x_3586_);
                    v___x_3603_ = v_reuseFailAlloc_3604_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3603_;
            }
            4 => {
                if v_isShared_3610_ == 0 {
                    v___x_3612_ = v___x_3609_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3613_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
                    v___x_3612_ = v_reuseFailAlloc_3613_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3612_;
            }
            6 => {
                if v_isShared_3618_ == 0 {
                    v___x_3620_ = v___x_3617_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3621_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
                    v___x_3620_ = v_reuseFailAlloc_3621_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3620_;
            }
            8 => {
                v_termMap_3628_ = crate::leanh::lean_ctor_get(v_a_3624_, 17);
                crate::leanh::lean_inc_ref(v_termMap_3628_);
                crate::leanh::lean_dec(v_a_3624_);
                v___x_3629_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_3628_, v_e_3572_);
                crate::leanh::lean_dec_ref(v_termMap_3628_);
                if crate::leanh::lean_obj_tag(v___x_3629_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_3572_);
                    v_val_3630_ = crate::leanh::lean_ctor_get(v___x_3629_, 0);
                    crate::leanh::lean_inc(v_val_3630_);
                    crate::leanh::lean_dec_ref_known(v___x_3629_, 1);
                    if v_isShared_3627_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3626_, 0, v_val_3630_);
                        v___x_3632_ = v___x_3626_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3633_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_val_3630_);
                        v___x_3632_ = v_reuseFailAlloc_3633_;
                        state = 9;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3629_);
                    crate::leanh::lean_del_object(v___x_3626_);
                    crate::leanh::lean_inc_ref(v_e_3572_);
                    v___x_3634_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
                    if crate::leanh::lean_obj_tag(v___x_3634_) == 0 {
                        v_a_3635_ = crate::leanh::lean_ctor_get(v___x_3634_, 0);
                        crate::leanh::lean_inc(v_a_3635_);
                        crate::leanh::lean_dec_ref_known(v___x_3634_, 1);
                        v_fst_3636_ = crate::leanh::lean_ctor_get(v_a_3635_, 0);
                        v_snd_3637_ = crate::leanh::lean_ctor_get(v_a_3635_, 1);
                        v_isSharedCheck_3671_ = (!crate::leanh::lean_is_exclusive(v_a_3635_)) as u8;
                        if v_isSharedCheck_3671_ == 0 {
                            v___x_3639_ = v_a_3635_;
                            v_isShared_3640_ = v_isSharedCheck_3671_;
                            state = 10;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_snd_3637_);
                            crate::leanh::lean_inc(v_fst_3636_);
                            crate::leanh::lean_dec(v_a_3635_);
                            v___x_3639_ = crate::leanh::lean_box(0);
                            v_isShared_3640_ = v_isSharedCheck_3671_;
                            state = 10;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_e_3572_);
                        return v___x_3634_;
                    }
                }
            }
            9 => {
                return v___x_3632_;
            }
            10 => {
                crate::leanh::lean_inc(v_a_3583_);
                crate::leanh::lean_inc_ref(v_a_3582_);
                crate::leanh::lean_inc(v_a_3581_);
                crate::leanh::lean_inc_ref(v_a_3580_);
                crate::leanh::lean_inc(v_a_3579_);
                crate::leanh::lean_inc_ref(v_a_3578_);
                crate::leanh::lean_inc(v_a_3577_);
                crate::leanh::lean_inc_ref(v_a_3576_);
                crate::leanh::lean_inc(v_a_3575_);
                crate::leanh::lean_inc(v_a_3574_);
                v___x_3641_ = lean_grind_preprocess(
                    v_fst_3636_,
                    v_a_3574_,
                    v_a_3575_,
                    v_a_3576_,
                    v_a_3577_,
                    v_a_3578_,
                    v_a_3579_,
                    v_a_3580_,
                    v_a_3581_,
                    v_a_3582_,
                    v_a_3583_,
                );
                if crate::leanh::lean_obj_tag(v___x_3641_) == 0 {
                    v_a_3642_ = crate::leanh::lean_ctor_get(v___x_3641_, 0);
                    crate::leanh::lean_inc(v_a_3642_);
                    crate::leanh::lean_dec_ref_known(v___x_3641_, 1);
                    v_proof_x3f_3643_ = crate::leanh::lean_ctor_get(v_a_3642_, 1);
                    if crate::leanh::lean_obj_tag(v_proof_x3f_3643_) == 1 {
                        crate::leanh::lean_inc_ref(v_proof_x3f_3643_);
                        v_expr_3644_ = crate::leanh::lean_ctor_get(v_a_3642_, 0);
                        crate::leanh::lean_inc_ref(v_expr_3644_);
                        crate::leanh::lean_dec(v_a_3642_);
                        v_val_3645_ = crate::leanh::lean_ctor_get(v_proof_x3f_3643_, 0);
                        crate::leanh::lean_inc(v_val_3645_);
                        crate::leanh::lean_dec_ref_known(v_proof_x3f_3643_, 1);
                        v___x_3646_ = l_Lean_Meta_mkEqTrans(
                            v_snd_3637_,
                            v_val_3645_,
                            v_a_3580_,
                            v_a_3581_,
                            v_a_3582_,
                            v_a_3583_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3646_) == 0 {
                            v_a_3647_ = crate::leanh::lean_ctor_get(v___x_3646_, 0);
                            crate::leanh::lean_inc(v_a_3647_);
                            crate::leanh::lean_dec_ref_known(v___x_3646_, 1);
                            if v_isShared_3640_ == 0 {
                                crate::leanh::lean_ctor_set(v___x_3639_, 1, v_a_3647_);
                                crate::leanh::lean_ctor_set(v___x_3639_, 0, v_expr_3644_);
                                v___x_3649_ = v___x_3639_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_3650_ =
                                    crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                                crate::leanh::lean_ctor_set(
                                    v_reuseFailAlloc_3650_,
                                    0,
                                    v_expr_3644_,
                                );
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_a_3647_);
                                v___x_3649_ = v_reuseFailAlloc_3650_;
                                state = 11;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v_expr_3644_);
                            crate::leanh::lean_del_object(v___x_3639_);
                            crate::leanh::lean_dec_ref(v_e_3572_);
                            v_a_3651_ = crate::leanh::lean_ctor_get(v___x_3646_, 0);
                            v_isSharedCheck_3658_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3646_)) as u8;
                            if v_isSharedCheck_3658_ == 0 {
                                v___x_3653_ = v___x_3646_;
                                v_isShared_3654_ = v_isSharedCheck_3658_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3651_);
                                crate::leanh::lean_dec(v___x_3646_);
                                v___x_3653_ = crate::leanh::lean_box(0);
                                v_isShared_3654_ = v_isSharedCheck_3658_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        v_expr_3659_ = crate::leanh::lean_ctor_get(v_a_3642_, 0);
                        crate::leanh::lean_inc_ref(v_expr_3659_);
                        crate::leanh::lean_dec(v_a_3642_);
                        if v_isShared_3640_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3639_, 0, v_expr_3659_);
                            v___x_3661_ = v___x_3639_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3662_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_expr_3659_);
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_snd_3637_);
                            v___x_3661_ = v_reuseFailAlloc_3662_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3639_);
                    crate::leanh::lean_dec(v_snd_3637_);
                    crate::leanh::lean_dec_ref(v_e_3572_);
                    v_a_3663_ = crate::leanh::lean_ctor_get(v___x_3641_, 0);
                    v_isSharedCheck_3670_ = (!crate::leanh::lean_is_exclusive(v___x_3641_)) as u8;
                    if v_isSharedCheck_3670_ == 0 {
                        v___x_3665_ = v___x_3641_;
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3663_);
                        crate::leanh::lean_dec(v___x_3641_);
                        v___x_3665_ = crate::leanh::lean_box(0);
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 15;
                        continue;
                    }
                }
            }
            11 => {
                v_____x_3586_ = v___x_3649_;
                v___y_3587_ = v_a_3573_;
                v___y_3588_ = v_a_3574_;
                v___y_3589_ = v_a_3578_;
                v___y_3590_ = v_a_3579_;
                v___y_3591_ = v_a_3580_;
                v___y_3592_ = v_a_3581_;
                v___y_3593_ = v_a_3582_;
                v___y_3594_ = v_a_3583_;
                state = 1;
                continue;
            }
            12 => {
                if v_isShared_3654_ == 0 {
                    v___x_3656_ = v___x_3653_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_3657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
                    v___x_3656_ = v_reuseFailAlloc_3657_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_3656_;
            }
            14 => {
                v_____x_3586_ = v___x_3661_;
                v___y_3587_ = v_a_3573_;
                v___y_3588_ = v_a_3574_;
                v___y_3589_ = v_a_3578_;
                v___y_3590_ = v_a_3579_;
                v___y_3591_ = v_a_3580_;
                v___y_3592_ = v_a_3581_;
                v___y_3593_ = v_a_3582_;
                v___y_3594_ = v_a_3583_;
                state = 1;
                continue;
            }
            15 => {
                if v_isShared_3666_ == 0 {
                    v___x_3668_ = v___x_3665_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_3669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
                    v___x_3668_ = v_reuseFailAlloc_3669_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_3668_;
            }
            17 => {
                if v_isShared_3676_ == 0 {
                    v___x_3678_ = v___x_3675_;
                    state = 18;
                    continue;
                } else {
                    v_reuseFailAlloc_3679_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
                    v___x_3678_ = v_reuseFailAlloc_3679_;
                    state = 18;
                    continue;
                }
            }
            18 => {
                return v___x_3678_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofNatModule___boxed(
    mut v_e_3681_: *mut crate::leanh::LeanObject,
    mut v_a_3682_: *mut crate::leanh::LeanObject,
    mut v_a_3683_: *mut crate::leanh::LeanObject,
    mut v_a_3684_: *mut crate::leanh::LeanObject,
    mut v_a_3685_: *mut crate::leanh::LeanObject,
    mut v_a_3686_: *mut crate::leanh::LeanObject,
    mut v_a_3687_: *mut crate::leanh::LeanObject,
    mut v_a_3688_: *mut crate::leanh::LeanObject,
    mut v_a_3689_: *mut crate::leanh::LeanObject,
    mut v_a_3690_: *mut crate::leanh::LeanObject,
    mut v_a_3691_: *mut crate::leanh::LeanObject,
    mut v_a_3692_: *mut crate::leanh::LeanObject,
    mut v_a_3693_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3694_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3694_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(
        v_e_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_,
        v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_,
    );
    crate::leanh::lean_dec(v_a_3692_);
    crate::leanh::lean_dec_ref(v_a_3691_);
    crate::leanh::lean_dec(v_a_3690_);
    crate::leanh::lean_dec_ref(v_a_3689_);
    crate::leanh::lean_dec(v_a_3688_);
    crate::leanh::lean_dec_ref(v_a_3687_);
    crate::leanh::lean_dec(v_a_3686_);
    crate::leanh::lean_dec_ref(v_a_3685_);
    crate::leanh::lean_dec(v_a_3684_);
    crate::leanh::lean_dec(v_a_3683_);
    crate::leanh::lean_dec(v_a_3682_);
    return v_res_3694_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3695_ = crate::leanh::lean_box(0);
    v___x_3696_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_3697_ = lean_mk_array(v___x_3696_, v___x_3695_);
    return v___x_3697_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3698_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0);
    v___x_3699_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3700_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3700_, 0, v___x_3699_);
    crate::leanh::lean_ctor_set(v___x_3700_, 1, v___x_3698_);
    return v___x_3700_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3703_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2;
    v___x_3704_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1);
    v___x_3705_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_3705_, 0, v___x_3704_);
    crate::leanh::lean_ctor_set(v___x_3705_, 1, v___x_3703_);
    return v___x_3705_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(
    mut v_x_3706_: *mut crate::leanh::LeanObject,
    mut v_a_3707_: *mut crate::leanh::LeanObject,
    mut v_a_3708_: *mut crate::leanh::LeanObject,
    mut v_a_3709_: *mut crate::leanh::LeanObject,
    mut v_a_3710_: *mut crate::leanh::LeanObject,
    mut v_a_3711_: *mut crate::leanh::LeanObject,
    mut v_a_3712_: *mut crate::leanh::LeanObject,
    mut v_a_3713_: *mut crate::leanh::LeanObject,
    mut v_a_3714_: *mut crate::leanh::LeanObject,
    mut v_a_3715_: *mut crate::leanh::LeanObject,
    mut v_a_3716_: *mut crate::leanh::LeanObject,
    mut v_a_3717_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3719_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
                v___x_3720_ = lean_st_mk_ref(v___x_3719_);
                crate::leanh::lean_inc(v_a_3717_);
                crate::leanh::lean_inc_ref(v_a_3716_);
                crate::leanh::lean_inc(v_a_3715_);
                crate::leanh::lean_inc_ref(v_a_3714_);
                crate::leanh::lean_inc(v_a_3713_);
                crate::leanh::lean_inc_ref(v_a_3712_);
                crate::leanh::lean_inc(v_a_3711_);
                crate::leanh::lean_inc_ref(v_a_3710_);
                crate::leanh::lean_inc(v_a_3709_);
                crate::leanh::lean_inc(v_a_3708_);
                crate::leanh::lean_inc(v_a_3707_);
                crate::leanh::lean_inc(v___x_3720_);
                v___x_3721_ = crate::leanh::lean_apply_13(
                    v_x_3706_,
                    v___x_3720_,
                    v_a_3707_,
                    v_a_3708_,
                    v_a_3709_,
                    v_a_3710_,
                    v_a_3711_,
                    v_a_3712_,
                    v_a_3713_,
                    v_a_3714_,
                    v_a_3715_,
                    v_a_3716_,
                    v_a_3717_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3721_) == 0 {
                    v_a_3722_ = crate::leanh::lean_ctor_get(v___x_3721_, 0);
                    v_isSharedCheck_3730_ = (!crate::leanh::lean_is_exclusive(v___x_3721_)) as u8;
                    if v_isSharedCheck_3730_ == 0 {
                        v___x_3724_ = v___x_3721_;
                        v_isShared_3725_ = v_isSharedCheck_3730_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3722_);
                        crate::leanh::lean_dec(v___x_3721_);
                        v___x_3724_ = crate::leanh::lean_box(0);
                        v_isShared_3725_ = v_isSharedCheck_3730_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3720_);
                    return v___x_3721_;
                }
            }
            1 => {
                v___x_3726_ = lean_st_ref_get(v___x_3720_);
                crate::leanh::lean_dec(v___x_3720_);
                crate::leanh::lean_dec(v___x_3726_);
                if v_isShared_3725_ == 0 {
                    v___x_3728_ = v___x_3724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3722_);
                    v___x_3728_ = v_reuseFailAlloc_3729_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3728_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___boxed(
    mut v_x_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
    mut v_a_3733_: *mut crate::leanh::LeanObject,
    mut v_a_3734_: *mut crate::leanh::LeanObject,
    mut v_a_3735_: *mut crate::leanh::LeanObject,
    mut v_a_3736_: *mut crate::leanh::LeanObject,
    mut v_a_3737_: *mut crate::leanh::LeanObject,
    mut v_a_3738_: *mut crate::leanh::LeanObject,
    mut v_a_3739_: *mut crate::leanh::LeanObject,
    mut v_a_3740_: *mut crate::leanh::LeanObject,
    mut v_a_3741_: *mut crate::leanh::LeanObject,
    mut v_a_3742_: *mut crate::leanh::LeanObject,
    mut v_a_3743_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
    crate::leanh::lean_dec(v_a_3742_);
    crate::leanh::lean_dec_ref(v_a_3741_);
    crate::leanh::lean_dec(v_a_3740_);
    crate::leanh::lean_dec_ref(v_a_3739_);
    crate::leanh::lean_dec(v_a_3738_);
    crate::leanh::lean_dec_ref(v_a_3737_);
    crate::leanh::lean_dec(v_a_3736_);
    crate::leanh::lean_dec_ref(v_a_3735_);
    crate::leanh::lean_dec(v_a_3734_);
    crate::leanh::lean_dec(v_a_3733_);
    crate::leanh::lean_dec(v_a_3732_);
    return v_res_3744_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(
    mut v_00_u03b1_3745_: *mut crate::leanh::LeanObject,
    mut v_x_3746_: *mut crate::leanh::LeanObject,
    mut v_a_3747_: *mut crate::leanh::LeanObject,
    mut v_a_3748_: *mut crate::leanh::LeanObject,
    mut v_a_3749_: *mut crate::leanh::LeanObject,
    mut v_a_3750_: *mut crate::leanh::LeanObject,
    mut v_a_3751_: *mut crate::leanh::LeanObject,
    mut v_a_3752_: *mut crate::leanh::LeanObject,
    mut v_a_3753_: *mut crate::leanh::LeanObject,
    mut v_a_3754_: *mut crate::leanh::LeanObject,
    mut v_a_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3759_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
                v___x_3760_ = lean_st_mk_ref(v___x_3759_);
                crate::leanh::lean_inc(v_a_3757_);
                crate::leanh::lean_inc_ref(v_a_3756_);
                crate::leanh::lean_inc(v_a_3755_);
                crate::leanh::lean_inc_ref(v_a_3754_);
                crate::leanh::lean_inc(v_a_3753_);
                crate::leanh::lean_inc_ref(v_a_3752_);
                crate::leanh::lean_inc(v_a_3751_);
                crate::leanh::lean_inc_ref(v_a_3750_);
                crate::leanh::lean_inc(v_a_3749_);
                crate::leanh::lean_inc(v_a_3748_);
                crate::leanh::lean_inc(v_a_3747_);
                crate::leanh::lean_inc(v___x_3760_);
                v___x_3761_ = crate::leanh::lean_apply_13(
                    v_x_3746_,
                    v___x_3760_,
                    v_a_3747_,
                    v_a_3748_,
                    v_a_3749_,
                    v_a_3750_,
                    v_a_3751_,
                    v_a_3752_,
                    v_a_3753_,
                    v_a_3754_,
                    v_a_3755_,
                    v_a_3756_,
                    v_a_3757_,
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_3761_) == 0 {
                    v_a_3762_ = crate::leanh::lean_ctor_get(v___x_3761_, 0);
                    v_isSharedCheck_3770_ = (!crate::leanh::lean_is_exclusive(v___x_3761_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3764_ = v___x_3761_;
                        v_isShared_3765_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3762_);
                        crate::leanh::lean_dec(v___x_3761_);
                        v___x_3764_ = crate::leanh::lean_box(0);
                        v_isShared_3765_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3760_);
                    return v___x_3761_;
                }
            }
            1 => {
                v___x_3766_ = lean_st_ref_get(v___x_3760_);
                crate::leanh::lean_dec(v___x_3760_);
                crate::leanh::lean_dec(v___x_3766_);
                if v_isShared_3765_ == 0 {
                    v___x_3768_ = v___x_3764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3762_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___boxed(
    mut v_00_u03b1_3771_: *mut crate::leanh::LeanObject,
    mut v_x_3772_: *mut crate::leanh::LeanObject,
    mut v_a_3773_: *mut crate::leanh::LeanObject,
    mut v_a_3774_: *mut crate::leanh::LeanObject,
    mut v_a_3775_: *mut crate::leanh::LeanObject,
    mut v_a_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_a_3779_: *mut crate::leanh::LeanObject,
    mut v_a_3780_: *mut crate::leanh::LeanObject,
    mut v_a_3781_: *mut crate::leanh::LeanObject,
    mut v_a_3782_: *mut crate::leanh::LeanObject,
    mut v_a_3783_: *mut crate::leanh::LeanObject,
    mut v_a_3784_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(v_00_u03b1_3771_, v_x_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
    crate::leanh::lean_dec(v_a_3783_);
    crate::leanh::lean_dec_ref(v_a_3782_);
    crate::leanh::lean_dec(v_a_3781_);
    crate::leanh::lean_dec_ref(v_a_3780_);
    crate::leanh::lean_dec(v_a_3779_);
    crate::leanh::lean_dec_ref(v_a_3778_);
    crate::leanh::lean_dec(v_a_3777_);
    crate::leanh::lean_dec_ref(v_a_3776_);
    crate::leanh::lean_dec(v_a_3775_);
    crate::leanh::lean_dec(v_a_3774_);
    crate::leanh::lean_dec(v_a_3773_);
    return v_res_3785_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(
    mut v_a_3786_: *mut crate::leanh::LeanObject,
    mut v_b_3787_: *mut crate::leanh::LeanObject,
    mut v_x_3788_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3788_) == 0 {
                    crate::leanh::lean_dec(v_b_3787_);
                    crate::leanh::lean_dec_ref(v_a_3786_);
                    return v_x_3788_;
                } else {
                    v_key_3789_ = crate::leanh::lean_ctor_get(v_x_3788_, 0);
                    v_value_3790_ = crate::leanh::lean_ctor_get(v_x_3788_, 1);
                    v_tail_3791_ = crate::leanh::lean_ctor_get(v_x_3788_, 2);
                    v_isSharedCheck_3803_ = (!crate::leanh::lean_is_exclusive(v_x_3788_)) as u8;
                    if v_isSharedCheck_3803_ == 0 {
                        v___x_3793_ = v_x_3788_;
                        v_isShared_3794_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3791_);
                        crate::leanh::lean_inc(v_value_3790_);
                        crate::leanh::lean_inc(v_key_3789_);
                        crate::leanh::lean_dec(v_x_3788_);
                        v___x_3793_ = crate::leanh::lean_box(0);
                        v_isShared_3794_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3795_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_key_3789_,
                        v_a_3786_,
                    );
                if v___x_3795_ == 0 {
                    v___x_3796_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_3786_, v_b_3787_, v_tail_3791_);
                    if v_isShared_3794_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3793_, 2, v___x_3796_);
                        v___x_3798_ = v___x_3793_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3799_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_key_3789_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_value_3790_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3799_, 2, v___x_3796_);
                        v___x_3798_ = v_reuseFailAlloc_3799_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_value_3790_);
                    crate::leanh::lean_dec(v_key_3789_);
                    if v_isShared_3794_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3793_, 1, v_b_3787_);
                        crate::leanh::lean_ctor_set(v___x_3793_, 0, v_a_3786_);
                        v___x_3801_ = v___x_3793_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3802_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3786_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_b_3787_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3802_, 2, v_tail_3791_);
                        v___x_3801_ = v_reuseFailAlloc_3802_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3798_;
            }
            3 => {
                return v___x_3801_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(
    mut v_x_3804_: *mut crate::leanh::LeanObject,
    mut v_x_3805_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_key_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: u64 = 0;
    let mut v___x_3814_: u64 = 0;
    let mut v___x_3815_: u64 = 0;
    let mut v_fold_3816_: u64 = 0;
    let mut v___x_3817_: u64 = 0;
    let mut v___x_3818_: u64 = 0;
    let mut v___x_3819_: u64 = 0;
    let mut v___x_3820_: usize = 0;
    let mut v___x_3821_: usize = 0;
    let mut v___x_3822_: usize = 0;
    let mut v___x_3823_: usize = 0;
    let mut v___x_3824_: usize = 0;
    let mut v___x_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3805_) == 0 {
                    return v_x_3804_;
                } else {
                    v_key_3806_ = crate::leanh::lean_ctor_get(v_x_3805_, 0);
                    v_value_3807_ = crate::leanh::lean_ctor_get(v_x_3805_, 1);
                    v_tail_3808_ = crate::leanh::lean_ctor_get(v_x_3805_, 2);
                    v_isSharedCheck_3831_ = (!crate::leanh::lean_is_exclusive(v_x_3805_)) as u8;
                    if v_isSharedCheck_3831_ == 0 {
                        v___x_3810_ = v_x_3805_;
                        v_isShared_3811_ = v_isSharedCheck_3831_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_tail_3808_);
                        crate::leanh::lean_inc(v_value_3807_);
                        crate::leanh::lean_inc(v_key_3806_);
                        crate::leanh::lean_dec(v_x_3805_);
                        v___x_3810_ = crate::leanh::lean_box(0);
                        v_isShared_3811_ = v_isSharedCheck_3831_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3812_ = lean_array_get_size(v_x_3804_);
                v___x_3813_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_key_3806_);
                v___x_3814_ = 32u64;
                v___x_3815_ = lean_uint64_shift_right(v___x_3813_, v___x_3814_);
                v_fold_3816_ = lean_uint64_xor(v___x_3813_, v___x_3815_);
                v___x_3817_ = 16u64;
                v___x_3818_ = lean_uint64_shift_right(v_fold_3816_, v___x_3817_);
                v___x_3819_ = lean_uint64_xor(v_fold_3816_, v___x_3818_);
                v___x_3820_ = lean_uint64_to_usize(v___x_3819_);
                v___x_3821_ = lean_usize_of_nat(v___x_3812_);
                v___x_3822_ = 1usize;
                v___x_3823_ = lean_usize_sub(v___x_3821_, v___x_3822_);
                v___x_3824_ = lean_usize_land(v___x_3820_, v___x_3823_);
                v___x_3825_ = lean_array_uget_borrowed(v_x_3804_, v___x_3824_);
                crate::leanh::lean_inc(v___x_3825_);
                if v_isShared_3811_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3810_, 2, v___x_3825_);
                    v___x_3827_ = v___x_3810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3830_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_key_3806_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_value_3807_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3830_, 2, v___x_3825_);
                    v___x_3827_ = v_reuseFailAlloc_3830_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3828_ = lean_array_uset(v_x_3804_, v___x_3824_, v___x_3827_);
                v_x_3804_ = v___x_3828_;
                v_x_3805_ = v_tail_3808_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(
    mut v_i_3832_: *mut crate::leanh::LeanObject,
    mut v_source_3833_: *mut crate::leanh::LeanObject,
    mut v_target_3834_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: u8 = 0;
    let mut v_es_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_source_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_target_3840_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3835_ = lean_array_get_size(v_source_3833_);
                v___x_3836_ = lean_nat_dec_lt(v_i_3832_, v___x_3835_);
                if v___x_3836_ == 0 {
                    crate::leanh::lean_dec_ref(v_source_3833_);
                    crate::leanh::lean_dec(v_i_3832_);
                    return v_target_3834_;
                } else {
                    v_es_3837_ = lean_array_fget(v_source_3833_, v_i_3832_);
                    v___x_3838_ = crate::leanh::lean_box(0);
                    v_source_3839_ = lean_array_fset(v_source_3833_, v_i_3832_, v___x_3838_);
                    v_target_3840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_3834_, v_es_3837_);
                    v___x_3841_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_3842_ = lean_nat_add(v_i_3832_, v___x_3841_);
                    crate::leanh::lean_dec(v_i_3832_);
                    v_i_3832_ = v___x_3842_;
                    v_source_3833_ = v_source_3839_;
                    v_target_3834_ = v_target_3840_;
                    state = 0;
                    continue;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(
    mut v_data_3844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3845_ = lean_array_get_size(v_data_3844_);
    v___x_3846_ = crate::leanh::lean_unsigned_to_nat(2);
    v_nbuckets_3847_ = lean_nat_mul(v___x_3845_, v___x_3846_);
    v___x_3848_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3849_ = crate::leanh::lean_box(0);
    v___x_3850_ = lean_mk_array(v_nbuckets_3847_, v___x_3849_);
    v___x_3851_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v___x_3848_, v_data_3844_, v___x_3850_);
    return v___x_3851_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(
    mut v_a_3852_: *mut crate::leanh::LeanObject,
    mut v_x_3853_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3854_: u8 = 0;
    let mut v_key_3855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3853_) == 0 {
                    v___x_3854_ = 0;
                    return v___x_3854_;
                } else {
                    v_key_3855_ = crate::leanh::lean_ctor_get(v_x_3853_, 0);
                    v_tail_3856_ = crate::leanh::lean_ctor_get(v_x_3853_, 2);
                    v___x_3857_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_3855_,
                            v_a_3852_,
                        );
                    if v___x_3857_ == 0 {
                        v_x_3853_ = v_tail_3856_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_3857_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg___boxed(
    mut v_a_3859_: *mut crate::leanh::LeanObject,
    mut v_x_3860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3861_: u8 = 0;
    let mut v_r_3862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_3859_, v_x_3860_);
    crate::leanh::lean_dec(v_x_3860_);
    crate::leanh::lean_dec_ref(v_a_3859_);
    v_r_3862_ = crate::leanh::lean_box((v_res_3861_) as usize);
    return v_r_3862_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(
    mut v_m_3863_: *mut crate::leanh::LeanObject,
    mut v_a_3864_: *mut crate::leanh::LeanObject,
    mut v_b_3865_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_size_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: u64 = 0;
    let mut v___x_3873_: u64 = 0;
    let mut v___x_3874_: u64 = 0;
    let mut v_fold_3875_: u64 = 0;
    let mut v___x_3876_: u64 = 0;
    let mut v___x_3877_: u64 = 0;
    let mut v___x_3878_: u64 = 0;
    let mut v___x_3879_: usize = 0;
    let mut v___x_3880_: usize = 0;
    let mut v___x_3881_: usize = 0;
    let mut v___x_3882_: usize = 0;
    let mut v___x_3883_: usize = 0;
    let mut v_bkt_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: u8 = 0;
    let mut v_val_3896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3866_ = crate::leanh::lean_ctor_get(v_m_3863_, 0);
                v_buckets_3867_ = crate::leanh::lean_ctor_get(v_m_3863_, 1);
                v_isSharedCheck_3910_ = (!crate::leanh::lean_is_exclusive(v_m_3863_)) as u8;
                if v_isSharedCheck_3910_ == 0 {
                    v___x_3869_ = v_m_3863_;
                    v_isShared_3870_ = v_isSharedCheck_3910_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_buckets_3867_);
                    crate::leanh::lean_inc(v_size_3866_);
                    crate::leanh::lean_dec(v_m_3863_);
                    v___x_3869_ = crate::leanh::lean_box(0);
                    v_isShared_3870_ = v_isSharedCheck_3910_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_3871_ = lean_array_get_size(v_buckets_3867_);
                v___x_3872_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_3864_);
                v___x_3873_ = 32u64;
                v___x_3874_ = lean_uint64_shift_right(v___x_3872_, v___x_3873_);
                v_fold_3875_ = lean_uint64_xor(v___x_3872_, v___x_3874_);
                v___x_3876_ = 16u64;
                v___x_3877_ = lean_uint64_shift_right(v_fold_3875_, v___x_3876_);
                v___x_3878_ = lean_uint64_xor(v_fold_3875_, v___x_3877_);
                v___x_3879_ = lean_uint64_to_usize(v___x_3878_);
                v___x_3880_ = lean_usize_of_nat(v___x_3871_);
                v___x_3881_ = 1usize;
                v___x_3882_ = lean_usize_sub(v___x_3880_, v___x_3881_);
                v___x_3883_ = lean_usize_land(v___x_3879_, v___x_3882_);
                v_bkt_3884_ = lean_array_uget_borrowed(v_buckets_3867_, v___x_3883_);
                v___x_3885_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_3864_, v_bkt_3884_);
                if v___x_3885_ == 0 {
                    v___x_3886_ = crate::leanh::lean_unsigned_to_nat(1);
                    v_size_x27_3887_ = lean_nat_add(v_size_3866_, v___x_3886_);
                    crate::leanh::lean_dec(v_size_3866_);
                    crate::leanh::lean_inc(v_bkt_3884_);
                    v___x_3888_ = crate::leanh::lean_alloc_ctor(1, 3, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3888_, 0, v_a_3864_);
                    crate::leanh::lean_ctor_set(v___x_3888_, 1, v_b_3865_);
                    crate::leanh::lean_ctor_set(v___x_3888_, 2, v_bkt_3884_);
                    v_buckets_x27_3889_ =
                        lean_array_uset(v_buckets_3867_, v___x_3883_, v___x_3888_);
                    v___x_3890_ = crate::leanh::lean_unsigned_to_nat(4);
                    v___x_3891_ = lean_nat_mul(v_size_x27_3887_, v___x_3890_);
                    v___x_3892_ = crate::leanh::lean_unsigned_to_nat(3);
                    v___x_3893_ = lean_nat_div(v___x_3891_, v___x_3892_);
                    crate::leanh::lean_dec(v___x_3891_);
                    v___x_3894_ = lean_array_get_size(v_buckets_x27_3889_);
                    v___x_3895_ = lean_nat_dec_le(v___x_3893_, v___x_3894_);
                    crate::leanh::lean_dec(v___x_3893_);
                    if v___x_3895_ == 0 {
                        v_val_3896_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_buckets_x27_3889_);
                        if v_isShared_3870_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3869_, 1, v_val_3896_);
                            crate::leanh::lean_ctor_set(v___x_3869_, 0, v_size_x27_3887_);
                            v___x_3898_ = v___x_3869_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3899_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3899_,
                                0,
                                v_size_x27_3887_,
                            );
                            crate::leanh::lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_val_3896_);
                            v___x_3898_ = v_reuseFailAlloc_3899_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3870_ == 0 {
                            crate::leanh::lean_ctor_set(v___x_3869_, 1, v_buckets_x27_3889_);
                            crate::leanh::lean_ctor_set(v___x_3869_, 0, v_size_x27_3887_);
                            v___x_3901_ = v___x_3869_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3902_ =
                                crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3902_,
                                0,
                                v_size_x27_3887_,
                            );
                            crate::leanh::lean_ctor_set(
                                v_reuseFailAlloc_3902_,
                                1,
                                v_buckets_x27_3889_,
                            );
                            v___x_3901_ = v_reuseFailAlloc_3902_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_inc(v_bkt_3884_);
                    v___x_3903_ = crate::leanh::lean_box(0);
                    v_buckets_x27_3904_ =
                        lean_array_uset(v_buckets_3867_, v___x_3883_, v___x_3903_);
                    v___x_3905_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_3864_, v_b_3865_, v_bkt_3884_);
                    v___x_3906_ = lean_array_uset(v_buckets_x27_3904_, v___x_3883_, v___x_3905_);
                    if v_isShared_3870_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3869_, 1, v___x_3906_);
                        v___x_3908_ = v___x_3869_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3909_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_size_3866_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3909_, 1, v___x_3906_);
                        v___x_3908_ = v_reuseFailAlloc_3909_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3898_;
            }
            3 => {
                return v___x_3901_;
            }
            4 => {
                return v___x_3908_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(
    mut v_a_3911_: *mut crate::leanh::LeanObject,
    mut v_x_3912_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3912_) == 0 {
                    v___x_3913_ = crate::leanh::lean_box(0);
                    return v___x_3913_;
                } else {
                    v_key_3914_ = crate::leanh::lean_ctor_get(v_x_3912_, 0);
                    v_value_3915_ = crate::leanh::lean_ctor_get(v_x_3912_, 1);
                    v_tail_3916_ = crate::leanh::lean_ctor_get(v_x_3912_, 2);
                    v___x_3917_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_key_3914_,
                            v_a_3911_,
                        );
                    if v___x_3917_ == 0 {
                        v_x_3912_ = v_tail_3916_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_3915_);
                        v___x_3919_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3919_, 0, v_value_3915_);
                        return v___x_3919_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(
    mut v_a_3920_: *mut crate::leanh::LeanObject,
    mut v_x_3921_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3922_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_3920_, v_x_3921_);
    crate::leanh::lean_dec(v_x_3921_);
    crate::leanh::lean_dec_ref(v_a_3920_);
    return v_res_3922_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(
    mut v_m_3923_: *mut crate::leanh::LeanObject,
    mut v_a_3924_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u64 = 0;
    let mut v___x_3928_: u64 = 0;
    let mut v___x_3929_: u64 = 0;
    let mut v_fold_3930_: u64 = 0;
    let mut v___x_3931_: u64 = 0;
    let mut v___x_3932_: u64 = 0;
    let mut v___x_3933_: u64 = 0;
    let mut v___x_3934_: usize = 0;
    let mut v___x_3935_: usize = 0;
    let mut v___x_3936_: usize = 0;
    let mut v___x_3937_: usize = 0;
    let mut v___x_3938_: usize = 0;
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_3925_ = crate::leanh::lean_ctor_get(v_m_3923_, 1);
    v___x_3926_ = lean_array_get_size(v_buckets_3925_);
    v___x_3927_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_a_3924_);
    v___x_3928_ = 32u64;
    v___x_3929_ = lean_uint64_shift_right(v___x_3927_, v___x_3928_);
    v_fold_3930_ = lean_uint64_xor(v___x_3927_, v___x_3929_);
    v___x_3931_ = 16u64;
    v___x_3932_ = lean_uint64_shift_right(v_fold_3930_, v___x_3931_);
    v___x_3933_ = lean_uint64_xor(v_fold_3930_, v___x_3932_);
    v___x_3934_ = lean_uint64_to_usize(v___x_3933_);
    v___x_3935_ = lean_usize_of_nat(v___x_3926_);
    v___x_3936_ = 1usize;
    v___x_3937_ = lean_usize_sub(v___x_3935_, v___x_3936_);
    v___x_3938_ = lean_usize_land(v___x_3934_, v___x_3937_);
    v___x_3939_ = lean_array_uget_borrowed(v_buckets_3925_, v___x_3938_);
    v___x_3940_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_3924_, v___x_3939_);
    return v___x_3940_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg___boxed(
    mut v_m_3941_: *mut crate::leanh::LeanObject,
    mut v_a_3942_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_3941_, v_a_3942_);
    crate::leanh::lean_dec_ref(v_a_3942_);
    crate::leanh::lean_dec_ref(v_m_3941_);
    return v_res_3943_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(
    mut v_e_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v___x_3959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3961_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_3962_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_3963_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3967_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3947_ = lean_st_ref_get(v_a_3945_);
                v_varMap_3948_ = crate::leanh::lean_ctor_get(v___x_3947_, 0);
                crate::leanh::lean_inc_ref(v_varMap_3948_);
                crate::leanh::lean_dec(v___x_3947_);
                v___x_3949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_varMap_3948_, v_e_3944_);
                crate::leanh::lean_dec_ref(v_varMap_3948_);
                if crate::leanh::lean_obj_tag(v___x_3949_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_3944_);
                    v_val_3950_ = crate::leanh::lean_ctor_get(v___x_3949_, 0);
                    v_isSharedCheck_3958_ = (!crate::leanh::lean_is_exclusive(v___x_3949_)) as u8;
                    if v_isSharedCheck_3958_ == 0 {
                        v___x_3952_ = v___x_3949_;
                        v_isShared_3953_ = v_isSharedCheck_3958_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_3950_);
                        crate::leanh::lean_dec(v___x_3949_);
                        v___x_3952_ = crate::leanh::lean_box(0);
                        v_isShared_3953_ = v_isSharedCheck_3958_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_3949_);
                    v___x_3959_ = lean_st_ref_get(v_a_3945_);
                    v___x_3960_ = lean_st_ref_take(v_a_3945_);
                    v_vars_3961_ = crate::leanh::lean_ctor_get(v___x_3959_, 1);
                    crate::leanh::lean_inc_ref(v_vars_3961_);
                    crate::leanh::lean_dec(v___x_3959_);
                    v_varMap_3962_ = crate::leanh::lean_ctor_get(v___x_3960_, 0);
                    v_vars_3963_ = crate::leanh::lean_ctor_get(v___x_3960_, 1);
                    v_isSharedCheck_3976_ = (!crate::leanh::lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_3976_ == 0 {
                        v___x_3965_ = v___x_3960_;
                        v_isShared_3966_ = v_isSharedCheck_3976_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_vars_3963_);
                        crate::leanh::lean_inc(v_varMap_3962_);
                        crate::leanh::lean_dec(v___x_3960_);
                        v___x_3965_ = crate::leanh::lean_box(0);
                        v_isShared_3966_ = v_isSharedCheck_3976_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3953_ == 0 {
                    v___x_3955_ = v___x_3952_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3957_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_val_3950_);
                    v___x_3955_ = v_reuseFailAlloc_3957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3956_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3956_, 0, v___x_3955_);
                return v___x_3956_;
            }
            3 => {
                v___x_3967_ = lean_array_get_size(v_vars_3961_);
                crate::leanh::lean_dec_ref(v_vars_3961_);
                crate::leanh::lean_inc_ref(v_e_3944_);
                v___x_3968_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_varMap_3962_, v_e_3944_, v___x_3967_);
                v___x_3969_ = lean_array_push(v_vars_3963_, v_e_3944_);
                if v_isShared_3966_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3965_, 1, v___x_3969_);
                    crate::leanh::lean_ctor_set(v___x_3965_, 0, v___x_3968_);
                    v___x_3971_ = v___x_3965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3968_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3969_);
                    v___x_3971_ = v_reuseFailAlloc_3975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3972_ = lean_st_ref_set(v_a_3945_, v___x_3971_);
                v___x_3973_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3973_, 0, v___x_3967_);
                v___x_3974_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3974_, 0, v___x_3973_);
                return v___x_3974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(
    mut v_e_3977_: *mut crate::leanh::LeanObject,
    mut v_a_3978_: *mut crate::leanh::LeanObject,
    mut v_a_3979_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3980_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_3977_, v_a_3978_);
    crate::leanh::lean_dec(v_a_3978_);
    return v_res_3980_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(
    mut v_e_3981_: *mut crate::leanh::LeanObject,
    mut v_a_3982_: *mut crate::leanh::LeanObject,
    mut v_a_3983_: *mut crate::leanh::LeanObject,
    mut v_a_3984_: *mut crate::leanh::LeanObject,
    mut v_a_3985_: *mut crate::leanh::LeanObject,
    mut v_a_3986_: *mut crate::leanh::LeanObject,
    mut v_a_3987_: *mut crate::leanh::LeanObject,
    mut v_a_3988_: *mut crate::leanh::LeanObject,
    mut v_a_3989_: *mut crate::leanh::LeanObject,
    mut v_a_3990_: *mut crate::leanh::LeanObject,
    mut v_a_3991_: *mut crate::leanh::LeanObject,
    mut v_a_3992_: *mut crate::leanh::LeanObject,
    mut v_a_3993_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_3981_, v_a_3982_);
    return v___x_3995_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(
    mut v_e_3996_: *mut crate::leanh::LeanObject,
    mut v_a_3997_: *mut crate::leanh::LeanObject,
    mut v_a_3998_: *mut crate::leanh::LeanObject,
    mut v_a_3999_: *mut crate::leanh::LeanObject,
    mut v_a_4000_: *mut crate::leanh::LeanObject,
    mut v_a_4001_: *mut crate::leanh::LeanObject,
    mut v_a_4002_: *mut crate::leanh::LeanObject,
    mut v_a_4003_: *mut crate::leanh::LeanObject,
    mut v_a_4004_: *mut crate::leanh::LeanObject,
    mut v_a_4005_: *mut crate::leanh::LeanObject,
    mut v_a_4006_: *mut crate::leanh::LeanObject,
    mut v_a_4007_: *mut crate::leanh::LeanObject,
    mut v_a_4008_: *mut crate::leanh::LeanObject,
    mut v_a_4009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
    crate::leanh::lean_dec(v_a_4008_);
    crate::leanh::lean_dec_ref(v_a_4007_);
    crate::leanh::lean_dec(v_a_4006_);
    crate::leanh::lean_dec_ref(v_a_4005_);
    crate::leanh::lean_dec(v_a_4004_);
    crate::leanh::lean_dec_ref(v_a_4003_);
    crate::leanh::lean_dec(v_a_4002_);
    crate::leanh::lean_dec_ref(v_a_4001_);
    crate::leanh::lean_dec(v_a_4000_);
    crate::leanh::lean_dec(v_a_3999_);
    crate::leanh::lean_dec(v_a_3998_);
    crate::leanh::lean_dec(v_a_3997_);
    return v_res_4010_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(
    mut v_00_u03b2_4011_: *mut crate::leanh::LeanObject,
    mut v_m_4012_: *mut crate::leanh::LeanObject,
    mut v_a_4013_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_4012_, v_a_4013_);
    return v___x_4014_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(
    mut v_00_u03b2_4015_: *mut crate::leanh::LeanObject,
    mut v_m_4016_: *mut crate::leanh::LeanObject,
    mut v_a_4017_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(v_00_u03b2_4015_, v_m_4016_, v_a_4017_);
    crate::leanh::lean_dec_ref(v_a_4017_);
    crate::leanh::lean_dec_ref(v_m_4016_);
    return v_res_4018_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(
    mut v_00_u03b2_4019_: *mut crate::leanh::LeanObject,
    mut v_m_4020_: *mut crate::leanh::LeanObject,
    mut v_a_4021_: *mut crate::leanh::LeanObject,
    mut v_b_4022_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_m_4020_, v_a_4021_, v_b_4022_);
    return v___x_4023_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(
    mut v_00_u03b2_4024_: *mut crate::leanh::LeanObject,
    mut v_a_4025_: *mut crate::leanh::LeanObject,
    mut v_x_4026_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_4025_, v_x_4026_);
    return v___x_4027_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_4028_: *mut crate::leanh::LeanObject,
    mut v_a_4029_: *mut crate::leanh::LeanObject,
    mut v_x_4030_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4031_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(v_00_u03b2_4028_, v_a_4029_, v_x_4030_);
    crate::leanh::lean_dec(v_x_4030_);
    crate::leanh::lean_dec_ref(v_a_4029_);
    return v_res_4031_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(
    mut v_00_u03b2_4032_: *mut crate::leanh::LeanObject,
    mut v_a_4033_: *mut crate::leanh::LeanObject,
    mut v_x_4034_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_4035_: u8 = 0;
    v___x_4035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_4033_, v_x_4034_);
    return v___x_4035_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(
    mut v_00_u03b2_4036_: *mut crate::leanh::LeanObject,
    mut v_a_4037_: *mut crate::leanh::LeanObject,
    mut v_x_4038_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4039_: u8 = 0;
    let mut v_r_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(v_00_u03b2_4036_, v_a_4037_, v_x_4038_);
    crate::leanh::lean_dec(v_x_4038_);
    crate::leanh::lean_dec_ref(v_a_4037_);
    v_r_4040_ = crate::leanh::lean_box((v_res_4039_) as usize);
    return v_r_4040_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(
    mut v_00_u03b2_4041_: *mut crate::leanh::LeanObject,
    mut v_data_4042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4043_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_data_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(
    mut v_00_u03b2_4044_: *mut crate::leanh::LeanObject,
    mut v_a_4045_: *mut crate::leanh::LeanObject,
    mut v_b_4046_: *mut crate::leanh::LeanObject,
    mut v_x_4047_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4048_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_4045_, v_b_4046_, v_x_4047_);
    return v___x_4048_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4049_: *mut crate::leanh::LeanObject,
    mut v_i_4050_: *mut crate::leanh::LeanObject,
    mut v_source_4051_: *mut crate::leanh::LeanObject,
    mut v_target_4052_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4053_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4053_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v_i_4050_, v_source_4051_, v_target_4052_);
    return v___x_4053_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_4054_: *mut crate::leanh::LeanObject,
    mut v_x_4055_: *mut crate::leanh::LeanObject,
    mut v_x_4056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_4055_, v_x_4056_);
    return v___x_4057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(
    mut v_e_4058_: *mut crate::leanh::LeanObject,
    mut v_a_4059_: *mut crate::leanh::LeanObject,
    mut v_a_4060_: *mut crate::leanh::LeanObject,
    mut v_a_4061_: *mut crate::leanh::LeanObject,
    mut v_a_4062_: *mut crate::leanh::LeanObject,
    mut v_a_4063_: *mut crate::leanh::LeanObject,
    mut v_a_4064_: *mut crate::leanh::LeanObject,
    mut v_a_4065_: *mut crate::leanh::LeanObject,
    mut v_a_4066_: *mut crate::leanh::LeanObject,
    mut v_a_4067_: *mut crate::leanh::LeanObject,
    mut v_a_4068_: *mut crate::leanh::LeanObject,
    mut v_a_4069_: *mut crate::leanh::LeanObject,
    mut v_a_4070_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4086_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_arg_4092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut v___x_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4143_: u8 = 0;
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_zero_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v_a_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v___x_4169_: u8 = 0;
    let mut v___x_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut v_a_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v___x_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_a_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4072_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_,
                    v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_,
                );
                if crate::leanh::lean_obj_tag(v___x_4072_) == 0 {
                    v_a_4073_ = crate::leanh::lean_ctor_get(v___x_4072_, 0);
                    crate::leanh::lean_inc(v_a_4073_);
                    crate::leanh::lean_dec_ref_known(v___x_4072_, 1);
                    crate::leanh::lean_inc_ref(v_e_4058_);
                    v___x_4074_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4058_, v_a_4068_);
                    if crate::leanh::lean_obj_tag(v___x_4074_) == 0 {
                        v_a_4075_ = crate::leanh::lean_ctor_get(v___x_4074_, 0);
                        v_isSharedCheck_4175_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4074_)) as u8;
                        if v_isSharedCheck_4175_ == 0 {
                            v___x_4077_ = v___x_4074_;
                            v_isShared_4078_ = v_isSharedCheck_4175_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4075_);
                            crate::leanh::lean_dec(v___x_4074_);
                            v___x_4077_ = crate::leanh::lean_box(0);
                            v_isShared_4078_ = v_isSharedCheck_4175_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4073_);
                        crate::leanh::lean_dec_ref(v_e_4058_);
                        v_a_4176_ = crate::leanh::lean_ctor_get(v___x_4074_, 0);
                        v_isSharedCheck_4183_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4074_)) as u8;
                        if v_isSharedCheck_4183_ == 0 {
                            v___x_4178_ = v___x_4074_;
                            v_isShared_4179_ = v_isSharedCheck_4183_;
                            state = 13;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4176_);
                            crate::leanh::lean_dec(v___x_4074_);
                            v___x_4178_ = crate::leanh::lean_box(0);
                            v_isShared_4179_ = v_isSharedCheck_4183_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_e_4058_);
                    v_a_4184_ = crate::leanh::lean_ctor_get(v___x_4072_, 0);
                    v_isSharedCheck_4191_ = (!crate::leanh::lean_is_exclusive(v___x_4072_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4186_ = v___x_4072_;
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 15;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4184_);
                        crate::leanh::lean_dec(v___x_4072_);
                        v___x_4186_ = crate::leanh::lean_box(0);
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4079_ = l_Lean_Expr_cleanupAnnotations(v_a_4075_);
                v___x_4080_ = l_Lean_Expr_isApp(v___x_4079_);
                if v___x_4080_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_4079_);
                    crate::leanh::lean_del_object(v___x_4077_);
                    crate::leanh::lean_dec(v_a_4073_);
                    v___x_4081_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                    return v___x_4081_;
                } else {
                    v_arg_4082_ = crate::leanh::lean_ctor_get(v___x_4079_, 1);
                    crate::leanh::lean_inc_ref(v_arg_4082_);
                    v___x_4083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4079_);
                    v___x_4084_ = l_Lean_Expr_isApp(v___x_4083_);
                    if v___x_4084_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_4083_);
                        crate::leanh::lean_dec_ref(v_arg_4082_);
                        crate::leanh::lean_del_object(v___x_4077_);
                        crate::leanh::lean_dec(v_a_4073_);
                        v___x_4085_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                        return v___x_4085_;
                    } else {
                        v_arg_4086_ = crate::leanh::lean_ctor_get(v___x_4083_, 1);
                        crate::leanh::lean_inc_ref(v_arg_4086_);
                        v___x_4087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4083_);
                        v___x_4088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2;
                        v___x_4089_ = l_Lean_Expr_isConstOf(v___x_4087_, v___x_4088_);
                        if v___x_4089_ == 0 {
                            crate::leanh::lean_del_object(v___x_4077_);
                            v___x_4090_ = l_Lean_Expr_isApp(v___x_4087_);
                            if v___x_4090_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_4087_);
                                crate::leanh::lean_dec_ref(v_arg_4086_);
                                crate::leanh::lean_dec_ref(v_arg_4082_);
                                crate::leanh::lean_dec(v_a_4073_);
                                v___x_4091_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                return v___x_4091_;
                            } else {
                                v_arg_4092_ = crate::leanh::lean_ctor_get(v___x_4087_, 1);
                                crate::leanh::lean_inc_ref(v_arg_4092_);
                                v___x_4093_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4087_);
                                v___x_4094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5;
                                v___x_4095_ = l_Lean_Expr_isConstOf(v___x_4093_, v___x_4094_);
                                if v___x_4095_ == 0 {
                                    v___x_4096_ = l_Lean_Expr_isApp(v___x_4093_);
                                    if v___x_4096_ == 0 {
                                        crate::leanh::lean_dec_ref(v___x_4093_);
                                        crate::leanh::lean_dec_ref(v_arg_4092_);
                                        crate::leanh::lean_dec_ref(v_arg_4086_);
                                        crate::leanh::lean_dec_ref(v_arg_4082_);
                                        crate::leanh::lean_dec(v_a_4073_);
                                        v___x_4097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                        return v___x_4097_;
                                    } else {
                                        v___x_4098_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4093_);
                                        v___x_4099_ = l_Lean_Expr_isApp(v___x_4098_);
                                        if v___x_4099_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_4098_);
                                            crate::leanh::lean_dec_ref(v_arg_4092_);
                                            crate::leanh::lean_dec_ref(v_arg_4086_);
                                            crate::leanh::lean_dec_ref(v_arg_4082_);
                                            crate::leanh::lean_dec(v_a_4073_);
                                            v___x_4100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                            return v___x_4100_;
                                        } else {
                                            v___x_4101_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_4098_);
                                            v___x_4102_ = l_Lean_Expr_isApp(v___x_4101_);
                                            if v___x_4102_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_4101_);
                                                crate::leanh::lean_dec_ref(v_arg_4092_);
                                                crate::leanh::lean_dec_ref(v_arg_4086_);
                                                crate::leanh::lean_dec_ref(v_arg_4082_);
                                                crate::leanh::lean_dec(v_a_4073_);
                                                v___x_4103_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                return v___x_4103_;
                                            } else {
                                                v___x_4104_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_4101_);
                                                v___x_4105_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8;
                                                v___x_4106_ =
                                                    l_Lean_Expr_isConstOf(v___x_4104_, v___x_4105_);
                                                if v___x_4106_ == 0 {
                                                    v___x_4107_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11;
                                                    v___x_4108_ = l_Lean_Expr_isConstOf(
                                                        v___x_4104_,
                                                        v___x_4107_,
                                                    );
                                                    crate::leanh::lean_dec_ref(v___x_4104_);
                                                    if v___x_4108_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_4092_);
                                                        crate::leanh::lean_dec_ref(v_arg_4086_);
                                                        crate::leanh::lean_dec_ref(v_arg_4082_);
                                                        crate::leanh::lean_dec(v_a_4073_);
                                                        v___x_4109_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                        return v___x_4109_;
                                                    } else {
                                                        v___x_4110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_4073_, v_arg_4092_);
                                                        crate::leanh::lean_dec_ref(v_arg_4092_);
                                                        crate::leanh::lean_dec(v_a_4073_);
                                                        if v___x_4110_ == 0 {
                                                            crate::leanh::lean_dec_ref(v_arg_4086_);
                                                            crate::leanh::lean_dec_ref(v_arg_4082_);
                                                            v___x_4111_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                            return v___x_4111_;
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_e_4058_);
                                                            v___x_4112_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_4086_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_4112_,
                                                            ) == 0
                                                            {
                                                                v_a_4113_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_4112_,
                                                                        0,
                                                                    );
                                                                crate::leanh::lean_inc(v_a_4113_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v___x_4112_,
                                                                    1,
                                                                );
                                                                v___x_4114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_4082_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_4114_,
                                                                ) == 0
                                                                {
                                                                    v_a_4115_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_4114_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4123_ = (!crate::leanh::lean_is_exclusive(v___x_4114_)) as u8;
                                                                    if v_isSharedCheck_4123_ == 0 {
                                                                        v___x_4117_ = v___x_4114_;
                                                                        v_isShared_4118_ =
                                                                            v_isSharedCheck_4123_;
                                                                        state = 2;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_4115_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_4114_,
                                                                        );
                                                                        v___x_4117_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_4118_ =
                                                                            v_isSharedCheck_4123_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_a_4113_,
                                                                    );
                                                                    return v___x_4114_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_4082_,
                                                                );
                                                                return v___x_4112_;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    crate::leanh::lean_dec_ref(v___x_4104_);
                                                    v___x_4124_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_4073_, v_arg_4092_);
                                                    crate::leanh::lean_dec_ref(v_arg_4092_);
                                                    crate::leanh::lean_dec(v_a_4073_);
                                                    if v___x_4124_ == 0 {
                                                        crate::leanh::lean_dec_ref(v_arg_4086_);
                                                        crate::leanh::lean_dec_ref(v_arg_4082_);
                                                        v___x_4125_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                        return v___x_4125_;
                                                    } else {
                                                        v___x_4126_ = l_Lean_Meta_getNatValue_x3f(
                                                            v_arg_4086_,
                                                            v_a_4067_,
                                                            v_a_4068_,
                                                            v_a_4069_,
                                                            v_a_4070_,
                                                        );
                                                        crate::leanh::lean_dec_ref(v_arg_4086_);
                                                        if crate::leanh::lean_obj_tag(v___x_4126_)
                                                            == 0
                                                        {
                                                            v_a_4127_ = crate::leanh::lean_ctor_get(
                                                                v___x_4126_,
                                                                0,
                                                            );
                                                            crate::leanh::lean_inc(v_a_4127_);
                                                            crate::leanh::lean_dec_ref_known(
                                                                v___x_4126_,
                                                                1,
                                                            );
                                                            if crate::leanh::lean_obj_tag(v_a_4127_)
                                                                == 1
                                                            {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_e_4058_,
                                                                );
                                                                v_val_4128_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v_a_4127_, 0,
                                                                    );
                                                                crate::leanh::lean_inc(v_val_4128_);
                                                                crate::leanh::lean_dec_ref_known(
                                                                    v_a_4127_, 1,
                                                                );
                                                                v___x_4129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_4082_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_4129_,
                                                                ) == 0
                                                                {
                                                                    v_a_4130_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_4129_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_4138_ = (!crate::leanh::lean_is_exclusive(v___x_4129_)) as u8;
                                                                    if v_isSharedCheck_4138_ == 0 {
                                                                        v___x_4132_ = v___x_4129_;
                                                                        v_isShared_4133_ =
                                                                            v_isSharedCheck_4138_;
                                                                        state = 4;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_4130_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_4129_,
                                                                        );
                                                                        v___x_4132_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_4133_ =
                                                                            v_isSharedCheck_4138_;
                                                                        state = 4;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec(
                                                                        v_val_4128_,
                                                                    );
                                                                    return v___x_4129_;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec(v_a_4127_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_4082_,
                                                                );
                                                                v___x_4139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                                return v___x_4139_;
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_4082_);
                                                            crate::leanh::lean_dec_ref(v_e_4058_);
                                                            v_a_4140_ = crate::leanh::lean_ctor_get(
                                                                v___x_4126_,
                                                                0,
                                                            );
                                                            v_isSharedCheck_4147_ =
                                                                (!crate::leanh::lean_is_exclusive(
                                                                    v___x_4126_,
                                                                ))
                                                                    as u8;
                                                            if v_isSharedCheck_4147_ == 0 {
                                                                v___x_4142_ = v___x_4126_;
                                                                v_isShared_4143_ =
                                                                    v_isSharedCheck_4147_;
                                                                state = 6;
                                                                continue;
                                                            } else {
                                                                crate::leanh::lean_inc(v_a_4140_);
                                                                crate::leanh::lean_dec(v___x_4126_);
                                                                v___x_4142_ =
                                                                    crate::leanh::lean_box(0);
                                                                v_isShared_4143_ =
                                                                    v_isSharedCheck_4147_;
                                                                state = 6;
                                                                continue;
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_4093_);
                                    crate::leanh::lean_dec_ref(v_arg_4092_);
                                    crate::leanh::lean_dec_ref(v_arg_4086_);
                                    crate::leanh::lean_dec_ref(v_arg_4082_);
                                    v_zero_4148_ = crate::leanh::lean_ctor_get(v_a_4073_, 13);
                                    crate::leanh::lean_inc_ref(v_zero_4148_);
                                    crate::leanh::lean_dec(v_a_4073_);
                                    crate::leanh::lean_inc_ref(v_e_4058_);
                                    v___x_4149_ = l_Lean_Meta_isDefEqD(
                                        v_e_4058_,
                                        v_zero_4148_,
                                        v_a_4067_,
                                        v_a_4068_,
                                        v_a_4069_,
                                        v_a_4070_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4149_) == 0 {
                                        v_a_4150_ = crate::leanh::lean_ctor_get(v___x_4149_, 0);
                                        v_isSharedCheck_4160_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4149_)) as u8;
                                        if v_isSharedCheck_4160_ == 0 {
                                            v___x_4152_ = v___x_4149_;
                                            v_isShared_4153_ = v_isSharedCheck_4160_;
                                            state = 8;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4150_);
                                            crate::leanh::lean_dec(v___x_4149_);
                                            v___x_4152_ = crate::leanh::lean_box(0);
                                            v_isShared_4153_ = v_isSharedCheck_4160_;
                                            state = 8;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v_e_4058_);
                                        v_a_4161_ = crate::leanh::lean_ctor_get(v___x_4149_, 0);
                                        v_isSharedCheck_4168_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4149_)) as u8;
                                        if v_isSharedCheck_4168_ == 0 {
                                            v___x_4163_ = v___x_4149_;
                                            v_isShared_4164_ = v_isSharedCheck_4168_;
                                            state = 10;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4161_);
                                            crate::leanh::lean_dec(v___x_4149_);
                                            v___x_4163_ = crate::leanh::lean_box(0);
                                            v_isShared_4164_ = v_isSharedCheck_4168_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_4087_);
                            crate::leanh::lean_dec_ref(v_arg_4086_);
                            v___x_4169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_4073_, v_arg_4082_);
                            crate::leanh::lean_dec_ref(v_arg_4082_);
                            crate::leanh::lean_dec(v_a_4073_);
                            if v___x_4169_ == 0 {
                                crate::leanh::lean_del_object(v___x_4077_);
                                v___x_4170_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                return v___x_4170_;
                            } else {
                                crate::leanh::lean_dec_ref(v_e_4058_);
                                v___x_4171_ = crate::leanh::lean_box(0);
                                if v_isShared_4078_ == 0 {
                                    crate::leanh::lean_ctor_set(v___x_4077_, 0, v___x_4171_);
                                    v___x_4173_ = v___x_4077_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4174_ =
                                        crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(
                                        v_reuseFailAlloc_4174_,
                                        0,
                                        v___x_4171_,
                                    );
                                    v___x_4173_ = v_reuseFailAlloc_4174_;
                                    state = 12;
                                    continue;
                                }
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_4119_ = crate::leanh::lean_alloc_ctor(2, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4119_, 0, v_a_4113_);
                crate::leanh::lean_ctor_set(v___x_4119_, 1, v_a_4115_);
                if v_isShared_4118_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4117_, 0, v___x_4119_);
                    v___x_4121_ = v___x_4117_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4122_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4119_);
                    v___x_4121_ = v_reuseFailAlloc_4122_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4121_;
            }
            4 => {
                v___x_4134_ = crate::leanh::lean_alloc_ctor(5, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4134_, 0, v_val_4128_);
                crate::leanh::lean_ctor_set(v___x_4134_, 1, v_a_4130_);
                if v_isShared_4133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4132_, 0, v___x_4134_);
                    v___x_4136_ = v___x_4132_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
                    v___x_4136_ = v_reuseFailAlloc_4137_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4136_;
            }
            6 => {
                if v_isShared_4143_ == 0 {
                    v___x_4145_ = v___x_4142_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4145_;
            }
            8 => {
                v___x_4154_ = (crate::leanh::lean_unbox(v_a_4150_) as u8);
                crate::leanh::lean_dec(v_a_4150_);
                if v___x_4154_ == 0 {
                    crate::leanh::lean_del_object(v___x_4152_);
                    v___x_4155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                    return v___x_4155_;
                } else {
                    crate::leanh::lean_dec_ref(v_e_4058_);
                    v___x_4156_ = crate::leanh::lean_box(0);
                    if v_isShared_4153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4152_, 0, v___x_4156_);
                        v___x_4158_ = v___x_4152_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4159_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
                        v___x_4158_ = v_reuseFailAlloc_4159_;
                        state = 9;
                        continue;
                    }
                }
            }
            9 => {
                return v___x_4158_;
            }
            10 => {
                if v_isShared_4164_ == 0 {
                    v___x_4166_ = v___x_4163_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
                    v___x_4166_ = v_reuseFailAlloc_4167_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4166_;
            }
            12 => {
                return v___x_4173_;
            }
            13 => {
                if v_isShared_4179_ == 0 {
                    v___x_4181_ = v___x_4178_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
                    v___x_4181_ = v_reuseFailAlloc_4182_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                return v___x_4181_;
            }
            15 => {
                if v_isShared_4187_ == 0 {
                    v___x_4189_ = v___x_4186_;
                    state = 16;
                    continue;
                } else {
                    v_reuseFailAlloc_4190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
                    v___x_4189_ = v_reuseFailAlloc_4190_;
                    state = 16;
                    continue;
                }
            }
            16 => {
                return v___x_4189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify___boxed(
    mut v_e_4192_: *mut crate::leanh::LeanObject,
    mut v_a_4193_: *mut crate::leanh::LeanObject,
    mut v_a_4194_: *mut crate::leanh::LeanObject,
    mut v_a_4195_: *mut crate::leanh::LeanObject,
    mut v_a_4196_: *mut crate::leanh::LeanObject,
    mut v_a_4197_: *mut crate::leanh::LeanObject,
    mut v_a_4198_: *mut crate::leanh::LeanObject,
    mut v_a_4199_: *mut crate::leanh::LeanObject,
    mut v_a_4200_: *mut crate::leanh::LeanObject,
    mut v_a_4201_: *mut crate::leanh::LeanObject,
    mut v_a_4202_: *mut crate::leanh::LeanObject,
    mut v_a_4203_: *mut crate::leanh::LeanObject,
    mut v_a_4204_: *mut crate::leanh::LeanObject,
    mut v_a_4205_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
    crate::leanh::lean_dec(v_a_4204_);
    crate::leanh::lean_dec_ref(v_a_4203_);
    crate::leanh::lean_dec(v_a_4202_);
    crate::leanh::lean_dec_ref(v_a_4201_);
    crate::leanh::lean_dec(v_a_4200_);
    crate::leanh::lean_dec_ref(v_a_4199_);
    crate::leanh::lean_dec(v_a_4198_);
    crate::leanh::lean_dec_ref(v_a_4197_);
    crate::leanh::lean_dec(v_a_4196_);
    crate::leanh::lean_dec(v_a_4195_);
    crate::leanh::lean_dec(v_a_4194_);
    crate::leanh::lean_dec(v_a_4193_);
    return v_res_4206_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(
    mut v_a_4214_: *mut crate::leanh::LeanObject,
    mut v_b_4215_: *mut crate::leanh::LeanObject,
    mut v_a_4216_: *mut crate::leanh::LeanObject,
    mut v_a_4217_: *mut crate::leanh::LeanObject,
    mut v_a_4218_: *mut crate::leanh::LeanObject,
    mut v_ctx_4219_: *mut crate::leanh::LeanObject,
    mut v___y_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
    mut v___y_4225_: *mut crate::leanh::LeanObject,
    mut v___y_4226_: *mut crate::leanh::LeanObject,
    mut v___y_4227_: *mut crate::leanh::LeanObject,
    mut v___y_4228_: *mut crate::leanh::LeanObject,
    mut v___y_4229_: *mut crate::leanh::LeanObject,
    mut v___y_4230_: *mut crate::leanh::LeanObject,
    mut v___y_4231_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_u_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4251_: u8 = 0;
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4255_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4233_ = l_Lean_Meta_Grind_mkDiseqProof(
                    v_a_4214_,
                    v_b_4215_,
                    v___y_4222_,
                    v___y_4223_,
                    v___y_4224_,
                    v___y_4225_,
                    v___y_4226_,
                    v___y_4227_,
                    v___y_4228_,
                    v___y_4229_,
                    v___y_4230_,
                    v___y_4231_,
                );
                if crate::leanh::lean_obj_tag(v___x_4233_) == 0 {
                    v_a_4234_ = crate::leanh::lean_ctor_get(v___x_4233_, 0);
                    crate::leanh::lean_inc(v_a_4234_);
                    crate::leanh::lean_dec_ref_known(v___x_4233_, 1);
                    v_type_4235_ = crate::leanh::lean_ctor_get(v_a_4216_, 2);
                    crate::leanh::lean_inc_ref(v_type_4235_);
                    v_u_4236_ = crate::leanh::lean_ctor_get(v_a_4216_, 3);
                    crate::leanh::lean_inc(v_u_4236_);
                    v_natModuleInst_4237_ = crate::leanh::lean_ctor_get(v_a_4216_, 4);
                    crate::leanh::lean_inc_ref(v_natModuleInst_4237_);
                    crate::leanh::lean_dec_ref(v_a_4216_);
                    v___x_4238_ =
                        l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2;
                    v___x_4239_ = crate::leanh::lean_box(0);
                    v___x_4240_ = crate::leanh::lean_alloc_ctor(1, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4240_, 0, v_u_4236_);
                    crate::leanh::lean_ctor_set(v___x_4240_, 1, v___x_4239_);
                    v___x_4241_ = l_Lean_mkConst(v___x_4238_, v___x_4240_);
                    v___x_4242_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_4217_);
                    v___x_4243_ = l_Lean_Meta_Grind_Arith_Linear_ofLinExpr(v_a_4218_);
                    v___x_4244_ = l_Lean_eagerReflBoolTrue;
                    v___x_4245_ = l_Lean_mkApp6(
                        v___x_4241_,
                        v_type_4235_,
                        v_natModuleInst_4237_,
                        v_ctx_4219_,
                        v___x_4242_,
                        v___x_4243_,
                        v___x_4244_,
                    );
                    v___x_4246_ = l_Lean_Expr_app___override(v_a_4234_, v___x_4245_);
                    v___x_4247_ = l_Lean_Meta_Grind_closeGoal(
                        v___x_4246_,
                        v___y_4222_,
                        v___y_4223_,
                        v___y_4224_,
                        v___y_4225_,
                        v___y_4226_,
                        v___y_4227_,
                        v___y_4228_,
                        v___y_4229_,
                        v___y_4230_,
                        v___y_4231_,
                    );
                    return v___x_4247_;
                } else {
                    crate::leanh::lean_dec_ref(v_ctx_4219_);
                    crate::leanh::lean_dec(v_a_4218_);
                    crate::leanh::lean_dec(v_a_4217_);
                    crate::leanh::lean_dec_ref(v_a_4216_);
                    v_a_4248_ = crate::leanh::lean_ctor_get(v___x_4233_, 0);
                    v_isSharedCheck_4255_ = (!crate::leanh::lean_is_exclusive(v___x_4233_)) as u8;
                    if v_isSharedCheck_4255_ == 0 {
                        v___x_4250_ = v___x_4233_;
                        v_isShared_4251_ = v_isSharedCheck_4255_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4248_);
                        crate::leanh::lean_dec(v___x_4233_);
                        v___x_4250_ = crate::leanh::lean_box(0);
                        v_isShared_4251_ = v_isSharedCheck_4255_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4251_ == 0 {
                    v___x_4253_ = v___x_4250_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4254_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
                    v___x_4253_ = v_reuseFailAlloc_4254_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4253_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_4256_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_b_4257_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_a_4258_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_4259_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_a_4260_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_ctx_4261_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4262_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4263_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4264_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4265_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4266_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4267_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4268_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4269_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4270_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4271_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4272_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4273_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4274_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_4275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4275_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(
        v_a_4256_,
        v_b_4257_,
        v_a_4258_,
        v_a_4259_,
        v_a_4260_,
        v_ctx_4261_,
        v___y_4262_,
        v___y_4263_,
        v___y_4264_,
        v___y_4265_,
        v___y_4266_,
        v___y_4267_,
        v___y_4268_,
        v___y_4269_,
        v___y_4270_,
        v___y_4271_,
        v___y_4272_,
        v___y_4273_,
    );
    crate::leanh::lean_dec(v___y_4273_);
    crate::leanh::lean_dec_ref(v___y_4272_);
    crate::leanh::lean_dec(v___y_4271_);
    crate::leanh::lean_dec_ref(v___y_4270_);
    crate::leanh::lean_dec(v___y_4269_);
    crate::leanh::lean_dec_ref(v___y_4268_);
    crate::leanh::lean_dec(v___y_4267_);
    crate::leanh::lean_dec_ref(v___y_4266_);
    crate::leanh::lean_dec(v___y_4265_);
    crate::leanh::lean_dec(v___y_4264_);
    crate::leanh::lean_dec(v___y_4263_);
    crate::leanh::lean_dec(v___y_4262_);
    return v_res_4275_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(
    mut v___y_4276_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    crate::leanh::lean_inc_ref(v___y_4276_);
    return v___y_4276_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(
    mut v___y_4277_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4278_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(v___y_4277_);
    crate::leanh::lean_dec_ref(v___y_4277_);
    return v_res_4278_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(
    mut v_vars_4279_: *mut crate::leanh::LeanObject,
    mut v_x_4280_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4281_ = lean_array_fget_borrowed(v_vars_4279_, v_x_4280_);
    crate::leanh::lean_inc(v___x_4281_);
    return v___x_4281_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed(
    mut v_vars_4282_: *mut crate::leanh::LeanObject,
    mut v_x_4283_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4284_ =
        l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(v_vars_4282_, v_x_4283_);
    crate::leanh::lean_dec(v_x_4283_);
    crate::leanh::lean_dec_ref(v_vars_4282_);
    return v_res_4284_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(
    mut v_a_4286_: *mut crate::leanh::LeanObject,
    mut v_b_4287_: *mut crate::leanh::LeanObject,
    mut v_a_4288_: *mut crate::leanh::LeanObject,
    mut v_a_4289_: *mut crate::leanh::LeanObject,
    mut v_a_4290_: *mut crate::leanh::LeanObject,
    mut v_a_4291_: *mut crate::leanh::LeanObject,
    mut v_a_4292_: *mut crate::leanh::LeanObject,
    mut v_a_4293_: *mut crate::leanh::LeanObject,
    mut v_a_4294_: *mut crate::leanh::LeanObject,
    mut v_a_4295_: *mut crate::leanh::LeanObject,
    mut v_a_4296_: *mut crate::leanh::LeanObject,
    mut v_a_4297_: *mut crate::leanh::LeanObject,
    mut v_a_4298_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: u8 = 0;
    let mut v_type_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_zero_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_type_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_4341_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v___x_4351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4353_: u8 = 0;
    let mut v_a_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4357_: u8 = 0;
    let mut v___x_4359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4361_: u8 = 0;
    let mut v_a_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_a_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4373_: u8 = 0;
    let mut v___x_4375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4300_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_4301_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
                v___x_4302_ = lean_st_mk_ref(v___x_4301_);
                crate::leanh::lean_inc_ref(v_a_4286_);
                v___x_4310_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_a_4286_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                if crate::leanh::lean_obj_tag(v___x_4310_) == 0 {
                    v_a_4311_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                    crate::leanh::lean_inc(v_a_4311_);
                    crate::leanh::lean_dec_ref_known(v___x_4310_, 1);
                    crate::leanh::lean_inc_ref(v_b_4287_);
                    v___x_4312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_b_4287_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                    if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                        v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                        crate::leanh::lean_inc_n(v_a_4313_, 2);
                        crate::leanh::lean_dec_ref_known(v___x_4312_, 1);
                        crate::leanh::lean_inc(v_a_4311_);
                        v___x_4314_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_4311_);
                        v___x_4315_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_4313_);
                        v___x_4316_ =
                            l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4314_, v___x_4315_);
                        crate::leanh::lean_dec(v___x_4315_);
                        crate::leanh::lean_dec(v___x_4314_);
                        if v___x_4316_ == 0 {
                            crate::leanh::lean_dec(v_a_4313_);
                            crate::leanh::lean_dec(v_a_4311_);
                            crate::leanh::lean_dec_ref(v_b_4287_);
                            crate::leanh::lean_dec_ref(v_a_4286_);
                            v___x_4317_ = crate::leanh::lean_box(0);
                            v_a_4304_ = v___x_4317_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4318_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                                v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_,
                                v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_4318_) == 0 {
                                v_a_4319_ = crate::leanh::lean_ctor_get(v___x_4318_, 0);
                                crate::leanh::lean_inc(v_a_4319_);
                                crate::leanh::lean_dec_ref_known(v___x_4318_, 1);
                                v___x_4320_ = lean_st_ref_get(v___x_4302_);
                                v_vars_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 1);
                                crate::leanh::lean_inc_ref(v_vars_4321_);
                                crate::leanh::lean_dec(v___x_4320_);
                                v___x_4322_ = lean_array_get_size(v_vars_4321_);
                                v___x_4323_ = lean_nat_dec_lt(v___x_4300_, v___x_4322_);
                                if v___x_4323_ == 0 {
                                    crate::leanh::lean_dec_ref(v_vars_4321_);
                                    v_type_4324_ = crate::leanh::lean_ctor_get(v_a_4319_, 2);
                                    v_zero_4325_ = crate::leanh::lean_ctor_get(v_a_4319_, 13);
                                    v___f_4326_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0;
                                    crate::leanh::lean_inc_ref(v_zero_4325_);
                                    v___x_4327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                    crate::leanh::lean_ctor_set(v___x_4327_, 0, v_zero_4325_);
                                    crate::leanh::lean_inc_ref(v_type_4324_);
                                    v___x_4328_ = l_Lean_RArray_toExpr___redArg(
                                        v_type_4324_,
                                        v___f_4326_,
                                        v___x_4327_,
                                        v_a_4295_,
                                        v_a_4296_,
                                        v_a_4297_,
                                        v_a_4298_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4328_) == 0 {
                                        v_a_4329_ = crate::leanh::lean_ctor_get(v___x_4328_, 0);
                                        crate::leanh::lean_inc(v_a_4329_);
                                        crate::leanh::lean_dec_ref_known(v___x_4328_, 1);
                                        v___x_4330_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_4286_, v_b_4287_, v_a_4319_, v_a_4311_, v_a_4313_, v_a_4329_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                                        v___y_4308_ = v___x_4330_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_4319_);
                                        crate::leanh::lean_dec(v_a_4313_);
                                        crate::leanh::lean_dec(v_a_4311_);
                                        crate::leanh::lean_dec(v___x_4302_);
                                        crate::leanh::lean_dec_ref(v_b_4287_);
                                        crate::leanh::lean_dec_ref(v_a_4286_);
                                        v_a_4331_ = crate::leanh::lean_ctor_get(v___x_4328_, 0);
                                        v_isSharedCheck_4338_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4328_)) as u8;
                                        if v_isSharedCheck_4338_ == 0 {
                                            v___x_4333_ = v___x_4328_;
                                            v_isShared_4334_ = v_isSharedCheck_4338_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4331_);
                                            crate::leanh::lean_dec(v___x_4328_);
                                            v___x_4333_ = crate::leanh::lean_box(0);
                                            v_isShared_4334_ = v_isSharedCheck_4338_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_type_4339_ = crate::leanh::lean_ctor_get(v_a_4319_, 2);
                                    v___f_4340_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0;
                                    v___f_4341_ = crate::leanh::lean_alloc_closure(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed as *mut core::ffi::c_void, 2, 1);
                                    crate::leanh::lean_closure_set(v___f_4341_, 0, v_vars_4321_);
                                    v___x_4342_ =
                                        l_Lean_RArray_ofFn___redArg(v___x_4322_, v___f_4341_);
                                    crate::leanh::lean_inc_ref(v_type_4339_);
                                    v___x_4343_ = l_Lean_RArray_toExpr___redArg(
                                        v_type_4339_,
                                        v___f_4340_,
                                        v___x_4342_,
                                        v_a_4295_,
                                        v_a_4296_,
                                        v_a_4297_,
                                        v_a_4298_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4343_) == 0 {
                                        v_a_4344_ = crate::leanh::lean_ctor_get(v___x_4343_, 0);
                                        crate::leanh::lean_inc(v_a_4344_);
                                        crate::leanh::lean_dec_ref_known(v___x_4343_, 1);
                                        v___x_4345_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_4286_, v_b_4287_, v_a_4319_, v_a_4311_, v_a_4313_, v_a_4344_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                                        v___y_4308_ = v___x_4345_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_4319_);
                                        crate::leanh::lean_dec(v_a_4313_);
                                        crate::leanh::lean_dec(v_a_4311_);
                                        crate::leanh::lean_dec(v___x_4302_);
                                        crate::leanh::lean_dec_ref(v_b_4287_);
                                        crate::leanh::lean_dec_ref(v_a_4286_);
                                        v_a_4346_ = crate::leanh::lean_ctor_get(v___x_4343_, 0);
                                        v_isSharedCheck_4353_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4343_)) as u8;
                                        if v_isSharedCheck_4353_ == 0 {
                                            v___x_4348_ = v___x_4343_;
                                            v_isShared_4349_ = v_isSharedCheck_4353_;
                                            state = 5;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4346_);
                                            crate::leanh::lean_dec(v___x_4343_);
                                            v___x_4348_ = crate::leanh::lean_box(0);
                                            v_isShared_4349_ = v_isSharedCheck_4353_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_4313_);
                                crate::leanh::lean_dec(v_a_4311_);
                                crate::leanh::lean_dec(v___x_4302_);
                                crate::leanh::lean_dec_ref(v_b_4287_);
                                crate::leanh::lean_dec_ref(v_a_4286_);
                                v_a_4354_ = crate::leanh::lean_ctor_get(v___x_4318_, 0);
                                v_isSharedCheck_4361_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4318_)) as u8;
                                if v_isSharedCheck_4361_ == 0 {
                                    v___x_4356_ = v___x_4318_;
                                    v_isShared_4357_ = v_isSharedCheck_4361_;
                                    state = 7;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4354_);
                                    crate::leanh::lean_dec(v___x_4318_);
                                    v___x_4356_ = crate::leanh::lean_box(0);
                                    v_isShared_4357_ = v_isSharedCheck_4361_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_4311_);
                        crate::leanh::lean_dec(v___x_4302_);
                        crate::leanh::lean_dec_ref(v_b_4287_);
                        crate::leanh::lean_dec_ref(v_a_4286_);
                        v_a_4362_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4369_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4369_ == 0 {
                            v___x_4364_ = v___x_4312_;
                            v_isShared_4365_ = v_isSharedCheck_4369_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4362_);
                            crate::leanh::lean_dec(v___x_4312_);
                            v___x_4364_ = crate::leanh::lean_box(0);
                            v_isShared_4365_ = v_isSharedCheck_4369_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    crate::leanh::lean_dec(v___x_4302_);
                    crate::leanh::lean_dec_ref(v_b_4287_);
                    crate::leanh::lean_dec_ref(v_a_4286_);
                    v_a_4370_ = crate::leanh::lean_ctor_get(v___x_4310_, 0);
                    v_isSharedCheck_4377_ = (!crate::leanh::lean_is_exclusive(v___x_4310_)) as u8;
                    if v_isSharedCheck_4377_ == 0 {
                        v___x_4372_ = v___x_4310_;
                        v_isShared_4373_ = v_isSharedCheck_4377_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4370_);
                        crate::leanh::lean_dec(v___x_4310_);
                        v___x_4372_ = crate::leanh::lean_box(0);
                        v_isShared_4373_ = v_isSharedCheck_4377_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4305_ = lean_st_ref_get(v___x_4302_);
                crate::leanh::lean_dec(v___x_4302_);
                crate::leanh::lean_dec(v___x_4305_);
                v___x_4306_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4306_, 0, v_a_4304_);
                return v___x_4306_;
            }
            2 => {
                if crate::leanh::lean_obj_tag(v___y_4308_) == 0 {
                    v_a_4309_ = crate::leanh::lean_ctor_get(v___y_4308_, 0);
                    crate::leanh::lean_inc(v_a_4309_);
                    crate::leanh::lean_dec_ref_known(v___y_4308_, 1);
                    v_a_4304_ = v_a_4309_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_4302_);
                    return v___y_4308_;
                }
            }
            3 => {
                if v_isShared_4334_ == 0 {
                    v___x_4336_ = v___x_4333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4336_;
            }
            5 => {
                if v_isShared_4349_ == 0 {
                    v___x_4351_ = v___x_4348_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4352_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4352_, 0, v_a_4346_);
                    v___x_4351_ = v_reuseFailAlloc_4352_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4351_;
            }
            7 => {
                if v_isShared_4357_ == 0 {
                    v___x_4359_ = v___x_4356_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4360_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
                    v___x_4359_ = v_reuseFailAlloc_4360_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4359_;
            }
            9 => {
                if v_isShared_4365_ == 0 {
                    v___x_4367_ = v___x_4364_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4368_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
                    v___x_4367_ = v_reuseFailAlloc_4368_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4367_;
            }
            11 => {
                if v_isShared_4373_ == 0 {
                    v___x_4375_ = v___x_4372_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4376_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
                    v___x_4375_ = v_reuseFailAlloc_4376_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4375_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___boxed(
    mut v_a_4378_: *mut crate::leanh::LeanObject,
    mut v_b_4379_: *mut crate::leanh::LeanObject,
    mut v_a_4380_: *mut crate::leanh::LeanObject,
    mut v_a_4381_: *mut crate::leanh::LeanObject,
    mut v_a_4382_: *mut crate::leanh::LeanObject,
    mut v_a_4383_: *mut crate::leanh::LeanObject,
    mut v_a_4384_: *mut crate::leanh::LeanObject,
    mut v_a_4385_: *mut crate::leanh::LeanObject,
    mut v_a_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_a_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4392_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(
        v_a_4378_, v_b_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_,
        v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_,
    );
    crate::leanh::lean_dec(v_a_4390_);
    crate::leanh::lean_dec_ref(v_a_4389_);
    crate::leanh::lean_dec(v_a_4388_);
    crate::leanh::lean_dec_ref(v_a_4387_);
    crate::leanh::lean_dec(v_a_4386_);
    crate::leanh::lean_dec_ref(v_a_4385_);
    crate::leanh::lean_dec(v_a_4384_);
    crate::leanh::lean_dec_ref(v_a_4383_);
    crate::leanh::lean_dec(v_a_4382_);
    crate::leanh::lean_dec(v_a_4381_);
    crate::leanh::lean_dec(v_a_4380_);
    return v_res_4392_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_OfNatModule(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_NatModuleNorm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Module_OfNatModule(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Module_NatModuleNorm(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Data_RArray(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
}
