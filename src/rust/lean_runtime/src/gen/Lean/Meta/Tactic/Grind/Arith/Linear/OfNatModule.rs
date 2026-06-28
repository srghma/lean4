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
use crate::r#gen::Init::Prelude::{l_Lean_Name_mkStr2, l_Lean_Name_mkStr4, l_Lean_Name_mkStr5};
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
    lean_array_push, lean_mk_empty_array_with_capacity, lean_nat_add, lean_nat_dec_eq,
    lean_nat_dec_le, lean_nat_dec_lt, lean_nat_div, lean_nat_mul,
};
use crate::lean_imports_rs::Init::System::ST::{
    lean_st_mk_ref, lean_st_ref_get, lean_st_ref_set, lean_st_ref_take,
};
use crate::lean_imports_rs::Lean::Meta::Tactic::Grind::Types::lean_grind_preprocess;
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_1,
    lean_apply_12, lean_apply_13, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_set,
    lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object, lean_inc,
    lean_inc_n, lean_inc_ref, lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive,
    lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize, lean_unsigned_to_nat,
    lean_usize_once,
};
pub static l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value: LeanStringObject<44> =
    LeanStringObject {
        m_header: LeanObject {
            rc: 0,
            cs_size: (0) as u16,
            other: 0,
            tag: 249,
        },
        m_size: 44,
        m_capacity: 44,
        m_length: 43,
        m_data: [
            96, 103, 114, 105, 110, 100, 96, 32, 105, 110, 116, 101, 114, 110, 97, 108, 32, 101,
            114, 114, 111, 114, 44, 32, 105, 110, 118, 97, 108, 105, 100, 32, 110, 97, 116, 83,
            116, 114, 117, 99, 116, 73, 100, 0,
        ],
    };
static mut l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0_value)
        as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1_once: LeanOnceCell =
    LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct___boxed
        as *const core::ffi::c_void,
    m_arity: 12,
    m_num_fixed: 0,
    m_objs: [],
};
pub static mut l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_instMonadGetStructOfNatModuleM_value)
        as *mut LeanObject;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0_value:
    LeanStringObject<69> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0_value
)
    as *mut LeanObject;
static mut l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once:
    LeanOnceCell = LeanOnceCell {
    state: core::sync::atomic::AtomicI32::new(0),
    lock: core::sync::atomic::AtomicI32::new(0),
};
static mut l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1: *mut LeanObject =
    core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__0_value) as *mut LeanObject,18263865437487147968 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__1_value) as *mut LeanObject,2651253468108498348 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__3_value) as *mut LeanObject,17636616155771105671 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__4_value) as *mut LeanObject,15578568367168711682 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [72, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__6_value) as *mut LeanObject,15703084674812832738 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__7_value) as *mut LeanObject,13609749952674037527 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__8_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__9_value) as *mut LeanObject,10393083817453678557 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__10_value) as *mut LeanObject,10680564408669940870 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__11_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value: LeanStringObject<5> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value: LeanStringObject<6> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value: LeanStringObject<12> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 102, 78, 97, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value: LeanStringObject<10> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [97, 100, 100, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut LeanObject,7605204649477761179 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut LeanObject,11314908490917688650 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__16_value) as *mut LeanObject,5371214753348010468 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value: LeanStringObject<11> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 11, m_capacity: 11, m_length: 10, m_data: [115, 109, 117, 108, 95, 99, 111, 110, 103, 114, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut LeanObject,7605204649477761179 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut LeanObject,11314908490917688650 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__18_value) as *mut LeanObject,15786333914169958476 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value: LeanStringObject<9> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 9, m_capacity: 9, m_length: 8, m_data: [116, 111, 81, 95, 122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value) as *mut LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__14_value) as *mut LeanObject,7605204649477761179 as *mut LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_2) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__15_value) as *mut LeanObject,11314908490917688650 as *mut LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value_aux_3) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__20_value) as *mut LeanObject,17599150304417000063 as *mut LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value: LeanArrayObject<0> = LeanArrayObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<usize>()*2 + core::mem::size_of::<*mut LeanObject>()*0) as u16, other: 0, tag: 246 }, m_size: 0, m_capacity: 0, m_data: [] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value:
    LeanStringObject<9> = LeanStringObject {
    m_header: LeanObject {
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
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value
)
    as *mut LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__12_value) as *mut LeanObject,11948124481539785030 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1: LeanCtorObject<3> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_0) as *mut LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__13_value) as *mut LeanObject,13563742693681136756 as *mut LeanObject] };
static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_1
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__0_value
        ) as *mut LeanObject,
        17349746425441669063 as *mut LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value:
    LeanCtorObject<3> = LeanCtorObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*mut LeanObject>() * 2
            + 8) as u16,
        other: 2,
        tag: 1,
    },
    m_objs: [
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value_aux_2
        ) as *mut LeanObject,
        core::ptr::addr_of!(
            l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__1_value
        ) as *mut LeanObject,
        13692448015376392830 as *mut LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(
    l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2_value
)
    as *mut LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value: LeanClosureObject<
    0,
> = LeanClosureObject {
    m_header: LeanObject {
        rc: 0,
        cs_size: (core::mem::size_of::<LeanObject>()
            + core::mem::size_of::<*const core::ffi::c_void>()
            + 4
            + core::mem::size_of::<*mut LeanObject>() * 0) as u16,
        other: 0,
        tag: 245,
    },
    m_fun: l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed
        as *const core::ffi::c_void,
    m_arity: 1,
    m_num_fixed: 0,
    m_objs: [],
};
static mut l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0: *mut LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0_value)
        as *mut LeanObject;
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg(
    mut v_natStructId_2197_: *mut LeanObject,
    mut v_x_2198_: *mut LeanObject,
    mut v_a_2199_: *mut LeanObject,
    mut v_a_2200_: *mut LeanObject,
    mut v_a_2201_: *mut LeanObject,
    mut v_a_2202_: *mut LeanObject,
    mut v_a_2203_: *mut LeanObject,
    mut v_a_2204_: *mut LeanObject,
    mut v_a_2205_: *mut LeanObject,
    mut v_a_2206_: *mut LeanObject,
    mut v_a_2207_: *mut LeanObject,
    mut v_a_2208_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2210_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2208_);
    lean_inc_ref(v_a_2207_);
    lean_inc(v_a_2206_);
    lean_inc_ref(v_a_2205_);
    lean_inc(v_a_2204_);
    lean_inc_ref(v_a_2203_);
    lean_inc(v_a_2202_);
    lean_inc_ref(v_a_2201_);
    lean_inc(v_a_2200_);
    lean_inc(v_a_2199_);
    v___x_2210_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_2210_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___redArg___boxed(
    mut v_natStructId_2211_: *mut LeanObject,
    mut v_x_2212_: *mut LeanObject,
    mut v_a_2213_: *mut LeanObject,
    mut v_a_2214_: *mut LeanObject,
    mut v_a_2215_: *mut LeanObject,
    mut v_a_2216_: *mut LeanObject,
    mut v_a_2217_: *mut LeanObject,
    mut v_a_2218_: *mut LeanObject,
    mut v_a_2219_: *mut LeanObject,
    mut v_a_2220_: *mut LeanObject,
    mut v_a_2221_: *mut LeanObject,
    mut v_a_2222_: *mut LeanObject,
    mut v_a_2223_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2224_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2222_);
    lean_dec_ref(v_a_2221_);
    lean_dec(v_a_2220_);
    lean_dec_ref(v_a_2219_);
    lean_dec(v_a_2218_);
    lean_dec_ref(v_a_2217_);
    lean_dec(v_a_2216_);
    lean_dec_ref(v_a_2215_);
    lean_dec(v_a_2214_);
    lean_dec(v_a_2213_);
    return v_res_2224_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run(
    mut v_00_u03b1_2225_: *mut LeanObject,
    mut v_natStructId_2226_: *mut LeanObject,
    mut v_x_2227_: *mut LeanObject,
    mut v_a_2228_: *mut LeanObject,
    mut v_a_2229_: *mut LeanObject,
    mut v_a_2230_: *mut LeanObject,
    mut v_a_2231_: *mut LeanObject,
    mut v_a_2232_: *mut LeanObject,
    mut v_a_2233_: *mut LeanObject,
    mut v_a_2234_: *mut LeanObject,
    mut v_a_2235_: *mut LeanObject,
    mut v_a_2236_: *mut LeanObject,
    mut v_a_2237_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2239_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2237_);
    lean_inc_ref(v_a_2236_);
    lean_inc(v_a_2235_);
    lean_inc_ref(v_a_2234_);
    lean_inc(v_a_2233_);
    lean_inc_ref(v_a_2232_);
    lean_inc(v_a_2231_);
    lean_inc_ref(v_a_2230_);
    lean_inc(v_a_2229_);
    lean_inc(v_a_2228_);
    v___x_2239_ = lean_apply_12(
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
        lean_box(0),
    );
    return v___x_2239_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_run___boxed(
    mut v_00_u03b1_2240_: *mut LeanObject,
    mut v_natStructId_2241_: *mut LeanObject,
    mut v_x_2242_: *mut LeanObject,
    mut v_a_2243_: *mut LeanObject,
    mut v_a_2244_: *mut LeanObject,
    mut v_a_2245_: *mut LeanObject,
    mut v_a_2246_: *mut LeanObject,
    mut v_a_2247_: *mut LeanObject,
    mut v_a_2248_: *mut LeanObject,
    mut v_a_2249_: *mut LeanObject,
    mut v_a_2250_: *mut LeanObject,
    mut v_a_2251_: *mut LeanObject,
    mut v_a_2252_: *mut LeanObject,
    mut v_a_2253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2254_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v_a_2252_);
    lean_dec_ref(v_a_2251_);
    lean_dec(v_a_2250_);
    lean_dec_ref(v_a_2249_);
    lean_dec(v_a_2248_);
    lean_dec_ref(v_a_2247_);
    lean_dec(v_a_2246_);
    lean_dec_ref(v_a_2245_);
    lean_dec(v_a_2244_);
    lean_dec(v_a_2243_);
    return v_res_2254_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(
    mut v_a_2255_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2257_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2255_);
    v___x_2257_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2257_, 0, v_a_2255_);
    return v___x_2257_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg___boxed(
    mut v_a_2258_: *mut LeanObject,
    mut v_a_2259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2260_: *mut LeanObject = core::ptr::null_mut();
    v_res_2260_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId___redArg(v_a_2258_);
    lean_dec(v_a_2258_);
    return v_res_2260_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId(
    mut v_a_2261_: *mut LeanObject,
    mut v_a_2262_: *mut LeanObject,
    mut v_a_2263_: *mut LeanObject,
    mut v_a_2264_: *mut LeanObject,
    mut v_a_2265_: *mut LeanObject,
    mut v_a_2266_: *mut LeanObject,
    mut v_a_2267_: *mut LeanObject,
    mut v_a_2268_: *mut LeanObject,
    mut v_a_2269_: *mut LeanObject,
    mut v_a_2270_: *mut LeanObject,
    mut v_a_2271_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2273_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2261_);
    v___x_2273_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2273_, 0, v_a_2261_);
    return v___x_2273_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStructId___boxed(
    mut v_a_2274_: *mut LeanObject,
    mut v_a_2275_: *mut LeanObject,
    mut v_a_2276_: *mut LeanObject,
    mut v_a_2277_: *mut LeanObject,
    mut v_a_2278_: *mut LeanObject,
    mut v_a_2279_: *mut LeanObject,
    mut v_a_2280_: *mut LeanObject,
    mut v_a_2281_: *mut LeanObject,
    mut v_a_2282_: *mut LeanObject,
    mut v_a_2283_: *mut LeanObject,
    mut v_a_2284_: *mut LeanObject,
    mut v_a_2285_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2286_: *mut LeanObject = core::ptr::null_mut();
    v_res_2286_ = l_Lean_Meta_Grind_Arith_Linear_getNatStructId(
        v_a_2274_, v_a_2275_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_, v_a_2280_, v_a_2281_,
        v_a_2282_, v_a_2283_, v_a_2284_,
    );
    lean_dec(v_a_2284_);
    lean_dec_ref(v_a_2283_);
    lean_dec(v_a_2282_);
    lean_dec_ref(v_a_2281_);
    lean_dec(v_a_2280_);
    lean_dec_ref(v_a_2279_);
    lean_dec(v_a_2278_);
    lean_dec_ref(v_a_2277_);
    lean_dec(v_a_2276_);
    lean_dec(v_a_2275_);
    lean_dec(v_a_2274_);
    return v_res_2286_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(
    mut v_msgData_2287_: *mut LeanObject,
    mut v___y_2288_: *mut LeanObject,
    mut v___y_2289_: *mut LeanObject,
    mut v___y_2290_: *mut LeanObject,
    mut v___y_2291_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_env_2294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2295_: *mut LeanObject = core::ptr::null_mut();
    let mut v_mctx_2296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lctx_2297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_options_2298_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2299_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2301_: *mut LeanObject = core::ptr::null_mut();
    v___x_2293_ = lean_st_ref_get(v___y_2291_);
    v_env_2294_ = lean_ctor_get(v___x_2293_, 0);
    lean_inc_ref(v_env_2294_);
    lean_dec(v___x_2293_);
    v___x_2295_ = lean_st_ref_get(v___y_2289_);
    v_mctx_2296_ = lean_ctor_get(v___x_2295_, 0);
    lean_inc_ref(v_mctx_2296_);
    lean_dec(v___x_2295_);
    v_lctx_2297_ = lean_ctor_get(v___y_2288_, 2);
    v_options_2298_ = lean_ctor_get(v___y_2290_, 2);
    lean_inc_ref(v_options_2298_);
    lean_inc_ref(v_lctx_2297_);
    v___x_2299_ = lean_alloc_ctor(0, 4, (0) as u32);
    lean_ctor_set(v___x_2299_, 0, v_env_2294_);
    lean_ctor_set(v___x_2299_, 1, v_mctx_2296_);
    lean_ctor_set(v___x_2299_, 2, v_lctx_2297_);
    lean_ctor_set(v___x_2299_, 3, v_options_2298_);
    v___x_2300_ = lean_alloc_ctor(3, 2, (0) as u32);
    lean_ctor_set(v___x_2300_, 0, v___x_2299_);
    lean_ctor_set(v___x_2300_, 1, v_msgData_2287_);
    v___x_2301_ = lean_alloc_ctor(0, 1, (0) as u32);
    lean_ctor_set(v___x_2301_, 0, v___x_2300_);
    return v___x_2301_;
}
pub unsafe fn l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0___boxed(
    mut v_msgData_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
    mut v___y_2307_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2308_: *mut LeanObject = core::ptr::null_mut();
    v_res_2308_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msgData_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
    lean_dec(v___y_2306_);
    lean_dec_ref(v___y_2305_);
    lean_dec(v___y_2304_);
    lean_dec_ref(v___y_2303_);
    return v_res_2308_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(
    mut v_msg_2309_: *mut LeanObject,
    mut v___y_2310_: *mut LeanObject,
    mut v___y_2311_: *mut LeanObject,
    mut v___y_2312_: *mut LeanObject,
    mut v___y_2313_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ref_2315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2319_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2320_: u8 = 0;
    let mut v___x_2321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2325_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ref_2315_ = lean_ctor_get(v___y_2312_, 5);
                v___x_2316_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0_spec__0(v_msg_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
                v_a_2317_ = lean_ctor_get(v___x_2316_, 0);
                v_isSharedCheck_2325_ = (!lean_is_exclusive(v___x_2316_)) as u8;
                if v_isSharedCheck_2325_ == 0 {
                    v___x_2319_ = v___x_2316_;
                    v_isShared_2320_ = v_isSharedCheck_2325_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_a_2317_);
                    lean_dec(v___x_2316_);
                    v___x_2319_ = lean_box(0);
                    v_isShared_2320_ = v_isSharedCheck_2325_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_ref_2315_);
                v___x_2321_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2321_, 0, v_ref_2315_);
                lean_ctor_set(v___x_2321_, 1, v_a_2317_);
                if v_isShared_2320_ == 0 {
                    lean_ctor_set_tag(v___x_2319_, 1);
                    lean_ctor_set(v___x_2319_, 0, v___x_2321_);
                    v___x_2323_ = v___x_2319_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2324_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2324_, 0, v___x_2321_);
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
    mut v_msg_2326_: *mut LeanObject,
    mut v___y_2327_: *mut LeanObject,
    mut v___y_2328_: *mut LeanObject,
    mut v___y_2329_: *mut LeanObject,
    mut v___y_2330_: *mut LeanObject,
    mut v___y_2331_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2332_: *mut LeanObject = core::ptr::null_mut();
    v_res_2332_ =
        l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0___redArg(
            v_msg_2326_,
            v___y_2327_,
            v___y_2328_,
            v___y_2329_,
            v___y_2330_,
        );
    lean_dec(v___y_2330_);
    lean_dec_ref(v___y_2329_);
    lean_dec(v___y_2328_);
    lean_dec_ref(v___y_2327_);
    return v_res_2332_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__1() -> *mut LeanObject {
    let mut v___x_2334_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2335_: *mut LeanObject = core::ptr::null_mut();
    v___x_2334_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct___closed__0;
    v___x_2335_ = l_Lean_stringToMessageData(v___x_2334_);
    return v___x_2335_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
    mut v_a_2336_: *mut LeanObject,
    mut v_a_2337_: *mut LeanObject,
    mut v_a_2338_: *mut LeanObject,
    mut v_a_2339_: *mut LeanObject,
    mut v_a_2340_: *mut LeanObject,
    mut v_a_2341_: *mut LeanObject,
    mut v_a_2342_: *mut LeanObject,
    mut v_a_2343_: *mut LeanObject,
    mut v_a_2344_: *mut LeanObject,
    mut v_a_2345_: *mut LeanObject,
    mut v_a_2346_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2352_: u8 = 0;
    let mut v_natStructs_2353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2355_: u8 = 0;
    let mut v___x_2356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2357_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2362_: u8 = 0;
    let mut v_a_2363_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2366_: u8 = 0;
    let mut v___x_2368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2369_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2370_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2348_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_2337_, v_a_2345_);
                if lean_obj_tag(v___x_2348_) == 0 {
                    v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
                    v_isSharedCheck_2362_ = (!lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2362_ == 0 {
                        v___x_2351_ = v___x_2348_;
                        v_isShared_2352_ = v_isSharedCheck_2362_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2349_);
                        lean_dec(v___x_2348_);
                        v___x_2351_ = lean_box(0);
                        v_isShared_2352_ = v_isSharedCheck_2362_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2363_ = lean_ctor_get(v___x_2348_, 0);
                    v_isSharedCheck_2370_ = (!lean_is_exclusive(v___x_2348_)) as u8;
                    if v_isSharedCheck_2370_ == 0 {
                        v___x_2365_ = v___x_2348_;
                        v_isShared_2366_ = v_isSharedCheck_2370_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2363_);
                        lean_dec(v___x_2348_);
                        v___x_2365_ = lean_box(0);
                        v_isShared_2366_ = v_isSharedCheck_2370_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_natStructs_2353_ = lean_ctor_get(v_a_2349_, 5);
                lean_inc_ref(v_natStructs_2353_);
                lean_dec(v_a_2349_);
                v___x_2354_ = lean_array_get_size(v_natStructs_2353_);
                v___x_2355_ = lean_nat_dec_lt(v_a_2336_, v___x_2354_);
                if v___x_2355_ == 0 {
                    lean_dec_ref(v_natStructs_2353_);
                    lean_del_object(v___x_2351_);
                    v___x_2356_ = lean_obj_once(
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
                    lean_dec_ref(v_natStructs_2353_);
                    if v_isShared_2352_ == 0 {
                        lean_ctor_set(v___x_2351_, 0, v___x_2358_);
                        v___x_2360_ = v___x_2351_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2361_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2361_, 0, v___x_2358_);
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
                    v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
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
    mut v_a_2371_: *mut LeanObject,
    mut v_a_2372_: *mut LeanObject,
    mut v_a_2373_: *mut LeanObject,
    mut v_a_2374_: *mut LeanObject,
    mut v_a_2375_: *mut LeanObject,
    mut v_a_2376_: *mut LeanObject,
    mut v_a_2377_: *mut LeanObject,
    mut v_a_2378_: *mut LeanObject,
    mut v_a_2379_: *mut LeanObject,
    mut v_a_2380_: *mut LeanObject,
    mut v_a_2381_: *mut LeanObject,
    mut v_a_2382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2383_: *mut LeanObject = core::ptr::null_mut();
    v_res_2383_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
        v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_,
        v_a_2379_, v_a_2380_, v_a_2381_,
    );
    lean_dec(v_a_2381_);
    lean_dec_ref(v_a_2380_);
    lean_dec(v_a_2379_);
    lean_dec_ref(v_a_2378_);
    lean_dec(v_a_2377_);
    lean_dec_ref(v_a_2376_);
    lean_dec(v_a_2375_);
    lean_dec_ref(v_a_2374_);
    lean_dec(v_a_2373_);
    lean_dec(v_a_2372_);
    lean_dec(v_a_2371_);
    return v_res_2383_;
}
pub unsafe fn l_Lean_throwError___at___00Lean_Meta_Grind_Arith_Linear_getNatStruct_spec__0(
    mut v_00_u03b1_2384_: *mut LeanObject,
    mut v_msg_2385_: *mut LeanObject,
    mut v___y_2386_: *mut LeanObject,
    mut v___y_2387_: *mut LeanObject,
    mut v___y_2388_: *mut LeanObject,
    mut v___y_2389_: *mut LeanObject,
    mut v___y_2390_: *mut LeanObject,
    mut v___y_2391_: *mut LeanObject,
    mut v___y_2392_: *mut LeanObject,
    mut v___y_2393_: *mut LeanObject,
    mut v___y_2394_: *mut LeanObject,
    mut v___y_2395_: *mut LeanObject,
    mut v___y_2396_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2398_: *mut LeanObject = core::ptr::null_mut();
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
    mut v_00_u03b1_2399_: *mut LeanObject,
    mut v_msg_2400_: *mut LeanObject,
    mut v___y_2401_: *mut LeanObject,
    mut v___y_2402_: *mut LeanObject,
    mut v___y_2403_: *mut LeanObject,
    mut v___y_2404_: *mut LeanObject,
    mut v___y_2405_: *mut LeanObject,
    mut v___y_2406_: *mut LeanObject,
    mut v___y_2407_: *mut LeanObject,
    mut v___y_2408_: *mut LeanObject,
    mut v___y_2409_: *mut LeanObject,
    mut v___y_2410_: *mut LeanObject,
    mut v___y_2411_: *mut LeanObject,
    mut v___y_2412_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2413_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_2411_);
    lean_dec_ref(v___y_2410_);
    lean_dec(v___y_2409_);
    lean_dec_ref(v___y_2408_);
    lean_dec(v___y_2407_);
    lean_dec_ref(v___y_2406_);
    lean_dec(v___y_2405_);
    lean_dec_ref(v___y_2404_);
    lean_dec(v___y_2403_);
    lean_dec(v___y_2402_);
    lean_dec(v___y_2401_);
    return v_res_2413_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(
    mut v_a_2414_: *mut LeanObject,
    mut v_a_2415_: *mut LeanObject,
    mut v_a_2416_: *mut LeanObject,
    mut v_a_2417_: *mut LeanObject,
    mut v_a_2418_: *mut LeanObject,
    mut v_a_2419_: *mut LeanObject,
    mut v_a_2420_: *mut LeanObject,
    mut v_a_2421_: *mut LeanObject,
    mut v_a_2422_: *mut LeanObject,
    mut v_a_2423_: *mut LeanObject,
    mut v_a_2424_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structId_2428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2429_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2433_: u8 = 0;
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2436_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2437_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2426_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_2414_, v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_,
                    v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_,
                );
                if lean_obj_tag(v___x_2426_) == 0 {
                    v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
                    lean_inc(v_a_2427_);
                    lean_dec_ref_known(v___x_2426_, 1);
                    v_structId_2428_ = lean_ctor_get(v_a_2427_, 1);
                    lean_inc(v_structId_2428_);
                    lean_dec(v_a_2427_);
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
                    lean_dec(v_structId_2428_);
                    return v___x_2429_;
                } else {
                    v_a_2430_ = lean_ctor_get(v___x_2426_, 0);
                    v_isSharedCheck_2437_ = (!lean_is_exclusive(v___x_2426_)) as u8;
                    if v_isSharedCheck_2437_ == 0 {
                        v___x_2432_ = v___x_2426_;
                        v_isShared_2433_ = v_isSharedCheck_2437_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2430_);
                        lean_dec(v___x_2426_);
                        v___x_2432_ = lean_box(0);
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
                    v_reuseFailAlloc_2436_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2436_, 0, v_a_2430_);
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
    mut v_a_2438_: *mut LeanObject,
    mut v_a_2439_: *mut LeanObject,
    mut v_a_2440_: *mut LeanObject,
    mut v_a_2441_: *mut LeanObject,
    mut v_a_2442_: *mut LeanObject,
    mut v_a_2443_: *mut LeanObject,
    mut v_a_2444_: *mut LeanObject,
    mut v_a_2445_: *mut LeanObject,
    mut v_a_2446_: *mut LeanObject,
    mut v_a_2447_: *mut LeanObject,
    mut v_a_2448_: *mut LeanObject,
    mut v_a_2449_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2450_: *mut LeanObject = core::ptr::null_mut();
    v_res_2450_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(
        v_a_2438_, v_a_2439_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_,
        v_a_2446_, v_a_2447_, v_a_2448_,
    );
    lean_dec(v_a_2448_);
    lean_dec_ref(v_a_2447_);
    lean_dec(v_a_2446_);
    lean_dec_ref(v_a_2445_);
    lean_dec(v_a_2444_);
    lean_dec_ref(v_a_2443_);
    lean_dec(v_a_2442_);
    lean_dec_ref(v_a_2441_);
    lean_dec(v_a_2440_);
    lean_dec(v_a_2439_);
    lean_dec(v_a_2438_);
    return v_res_2450_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(
    mut v_a_2452_: *mut LeanObject,
    mut v_f_2453_: *mut LeanObject,
    mut v_s_2454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_2455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_2457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_2458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_2459_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_2460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_2461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_2462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2464_: u8 = 0;
    let mut v___x_2466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2467_: u8 = 0;
    let mut v_v_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2476_: u8 = 0;
    let mut v_unused_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2478_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2479_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2481_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2482_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_2484_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2455_ = lean_ctor_get(v_s_2454_, 0);
                v_typeIdOf_2456_ = lean_ctor_get(v_s_2454_, 1);
                v_exprToStructId_2457_ = lean_ctor_get(v_s_2454_, 2);
                v_exprToStructIdEntries_2458_ = lean_ctor_get(v_s_2454_, 3);
                v_forbiddenNatModules_2459_ = lean_ctor_get(v_s_2454_, 4);
                v_natStructs_2460_ = lean_ctor_get(v_s_2454_, 5);
                v_natTypeIdOf_2461_ = lean_ctor_get(v_s_2454_, 6);
                v_exprToNatStructId_2462_ = lean_ctor_get(v_s_2454_, 7);
                v___x_2463_ = lean_array_get_size(v_natStructs_2460_);
                v___x_2464_ = lean_nat_dec_lt(v_a_2452_, v___x_2463_);
                if v___x_2464_ == 0 {
                    lean_dec_ref(v_f_2453_);
                    return v_s_2454_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_2462_);
                    lean_inc_ref(v_natTypeIdOf_2461_);
                    lean_inc_ref(v_natStructs_2460_);
                    lean_inc_ref(v_forbiddenNatModules_2459_);
                    lean_inc_ref(v_exprToStructIdEntries_2458_);
                    lean_inc_ref(v_exprToStructId_2457_);
                    lean_inc_ref(v_typeIdOf_2456_);
                    lean_inc_ref(v_structs_2455_);
                    v_isSharedCheck_2476_ = (!lean_is_exclusive(v_s_2454_)) as u8;
                    if v_isSharedCheck_2476_ == 0 {
                        v_unused_2477_ = lean_ctor_get(v_s_2454_, 7);
                        lean_dec(v_unused_2477_);
                        v_unused_2478_ = lean_ctor_get(v_s_2454_, 6);
                        lean_dec(v_unused_2478_);
                        v_unused_2479_ = lean_ctor_get(v_s_2454_, 5);
                        lean_dec(v_unused_2479_);
                        v_unused_2480_ = lean_ctor_get(v_s_2454_, 4);
                        lean_dec(v_unused_2480_);
                        v_unused_2481_ = lean_ctor_get(v_s_2454_, 3);
                        lean_dec(v_unused_2481_);
                        v_unused_2482_ = lean_ctor_get(v_s_2454_, 2);
                        lean_dec(v_unused_2482_);
                        v_unused_2483_ = lean_ctor_get(v_s_2454_, 1);
                        lean_dec(v_unused_2483_);
                        v_unused_2484_ = lean_ctor_get(v_s_2454_, 0);
                        lean_dec(v_unused_2484_);
                        v___x_2466_ = v_s_2454_;
                        v_isShared_2467_ = v_isSharedCheck_2476_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_2454_);
                        v___x_2466_ = lean_box(0);
                        v_isShared_2467_ = v_isSharedCheck_2476_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2468_ = lean_array_fget(v_natStructs_2460_, v_a_2452_);
                v___x_2469_ = lean_box(0);
                v_xs_x27_2470_ = lean_array_fset(v_natStructs_2460_, v_a_2452_, v___x_2469_);
                v___x_2471_ = lean_apply_1(v_f_2453_, v_v_2468_);
                v___x_2472_ = lean_array_fset(v_xs_x27_2470_, v_a_2452_, v___x_2471_);
                if v_isShared_2467_ == 0 {
                    lean_ctor_set(v___x_2466_, 5, v___x_2472_);
                    v___x_2474_ = v___x_2466_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2475_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_structs_2455_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 1, v_typeIdOf_2456_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 2, v_exprToStructId_2457_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 3, v_exprToStructIdEntries_2458_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 4, v_forbiddenNatModules_2459_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 5, v___x_2472_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 6, v_natTypeIdOf_2461_);
                    lean_ctor_set(v_reuseFailAlloc_2475_, 7, v_exprToNatStructId_2462_);
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
    mut v_a_2485_: *mut LeanObject,
    mut v_f_2486_: *mut LeanObject,
    mut v_s_2487_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2488_: *mut LeanObject = core::ptr::null_mut();
    v_res_2488_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0(
        v_a_2485_, v_f_2486_, v_s_2487_,
    );
    lean_dec(v_a_2485_);
    return v_res_2488_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(
    mut v_f_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
    mut v_a_2491_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2493_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2494_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2495_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2490_);
    v___f_2493_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2493_, 0, v_a_2490_);
    lean_closure_set(v___f_2493_, 1, v_f_2489_);
    v___x_2494_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_2495_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2494_, v___f_2493_, v_a_2491_);
    return v___x_2495_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___boxed(
    mut v_f_2496_: *mut LeanObject,
    mut v_a_2497_: *mut LeanObject,
    mut v_a_2498_: *mut LeanObject,
    mut v_a_2499_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2500_: *mut LeanObject = core::ptr::null_mut();
    v_res_2500_ =
        l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg(v_f_2496_, v_a_2497_, v_a_2498_);
    lean_dec(v_a_2498_);
    lean_dec(v_a_2497_);
    return v_res_2500_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(
    mut v_f_2501_: *mut LeanObject,
    mut v_a_2502_: *mut LeanObject,
    mut v_a_2503_: *mut LeanObject,
    mut v_a_2504_: *mut LeanObject,
    mut v_a_2505_: *mut LeanObject,
    mut v_a_2506_: *mut LeanObject,
    mut v_a_2507_: *mut LeanObject,
    mut v_a_2508_: *mut LeanObject,
    mut v_a_2509_: *mut LeanObject,
    mut v_a_2510_: *mut LeanObject,
    mut v_a_2511_: *mut LeanObject,
    mut v_a_2512_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    lean_inc(v_a_2502_);
    v___f_2514_ = lean_alloc_closure(
        l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___redArg___lam__0___boxed
            as *mut core::ffi::c_void,
        3,
        2,
    );
    lean_closure_set(v___f_2514_, 0, v_a_2502_);
    lean_closure_set(v___f_2514_, 1, v_f_2501_);
    v___x_2515_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
    v___x_2516_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2515_, v___f_2514_, v_a_2503_);
    return v___x_2516_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct___boxed(
    mut v_f_2517_: *mut LeanObject,
    mut v_a_2518_: *mut LeanObject,
    mut v_a_2519_: *mut LeanObject,
    mut v_a_2520_: *mut LeanObject,
    mut v_a_2521_: *mut LeanObject,
    mut v_a_2522_: *mut LeanObject,
    mut v_a_2523_: *mut LeanObject,
    mut v_a_2524_: *mut LeanObject,
    mut v_a_2525_: *mut LeanObject,
    mut v_a_2526_: *mut LeanObject,
    mut v_a_2527_: *mut LeanObject,
    mut v_a_2528_: *mut LeanObject,
    mut v_a_2529_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2530_: *mut LeanObject = core::ptr::null_mut();
    v_res_2530_ = l_Lean_Meta_Grind_Arith_Linear_modifyNatStruct(
        v_f_2517_, v_a_2518_, v_a_2519_, v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_,
        v_a_2525_, v_a_2526_, v_a_2527_, v_a_2528_,
    );
    lean_dec(v_a_2528_);
    lean_dec_ref(v_a_2527_);
    lean_dec(v_a_2526_);
    lean_dec_ref(v_a_2525_);
    lean_dec(v_a_2524_);
    lean_dec_ref(v_a_2523_);
    lean_dec(v_a_2522_);
    lean_dec_ref(v_a_2521_);
    lean_dec(v_a_2520_);
    lean_dec(v_a_2519_);
    lean_dec(v_a_2518_);
    return v_res_2530_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2531_: *mut LeanObject,
    mut v_vals_2532_: *mut LeanObject,
    mut v_i_2533_: *mut LeanObject,
    mut v_k_2534_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    let mut v___x_2537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2538_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2539_: u8 = 0;
    let mut v___x_2540_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2535_ = lean_array_get_size(v_keys_2531_);
                v___x_2536_ = lean_nat_dec_lt(v_i_2533_, v___x_2535_);
                if v___x_2536_ == 0 {
                    lean_dec(v_i_2533_);
                    v___x_2537_ = lean_box(0);
                    return v___x_2537_;
                } else {
                    v_k_x27_2538_ = lean_array_fget_borrowed(v_keys_2531_, v_i_2533_);
                    v___x_2539_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2534_,
                            v_k_x27_2538_,
                        );
                    if v___x_2539_ == 0 {
                        v___x_2540_ = lean_unsigned_to_nat(1);
                        v___x_2541_ = lean_nat_add(v_i_2533_, v___x_2540_);
                        lean_dec(v_i_2533_);
                        v_i_2533_ = v___x_2541_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2543_ = lean_array_fget_borrowed(v_vals_2532_, v_i_2533_);
                        lean_dec(v_i_2533_);
                        lean_inc(v___x_2543_);
                        v___x_2544_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_2544_, 0, v___x_2543_);
                        return v___x_2544_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2545_: *mut LeanObject,
    mut v_vals_2546_: *mut LeanObject,
    mut v_i_2547_: *mut LeanObject,
    mut v_k_2548_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2549_: *mut LeanObject = core::ptr::null_mut();
    v_res_2549_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2545_, v_vals_2546_, v_i_2547_, v_k_2548_);
    lean_dec_ref(v_k_2548_);
    lean_dec_ref(v_vals_2546_);
    lean_dec_ref(v_keys_2545_);
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
    v___x_2554_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_2555_ = lean_usize_sub(v___x_2554_, v___x_2553_);
    return v___x_2555_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(
    mut v_x_2556_: *mut LeanObject,
    mut v_x_2557_: usize,
    mut v_x_2558_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2561_: usize = 0;
    let mut v___x_2562_: usize = 0;
    let mut v___x_2563_: usize = 0;
    let mut v_j_2564_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2567_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: u8 = 0;
    let mut v___x_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2570_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: usize = 0;
    let mut v___x_2574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2578_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2556_) == 0 {
                    v_es_2559_ = lean_ctor_get(v_x_2556_, 0);
                    v___x_2560_ = lean_box(2);
                    v___x_2561_ = 5usize;
                    v___x_2562_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_2563_ = lean_usize_land(v_x_2557_, v___x_2562_);
                    v_j_2564_ = lean_usize_to_nat(v___x_2563_);
                    v___x_2565_ = lean_array_get_borrowed(v___x_2560_, v_es_2559_, v_j_2564_);
                    lean_dec(v_j_2564_);
                    match lean_obj_tag(v___x_2565_) {
                        0 => {
                            v_key_2566_ = lean_ctor_get(v___x_2565_, 0);
                            v_val_2567_ = lean_ctor_get(v___x_2565_, 1);
                            v___x_2568_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2558_, v_key_2566_);
                            if v___x_2568_ == 0 {
                                v___x_2569_ = lean_box(0);
                                return v___x_2569_;
                            } else {
                                lean_inc(v_val_2567_);
                                v___x_2570_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v___x_2570_, 0, v_val_2567_);
                                return v___x_2570_;
                            }
                        }
                        1 => {
                            v_node_2571_ = lean_ctor_get(v___x_2565_, 0);
                            v___x_2572_ = lean_usize_shift_right(v_x_2557_, v___x_2561_);
                            v_x_2556_ = v_node_2571_;
                            v_x_2557_ = v___x_2572_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2574_ = lean_box(0);
                            return v___x_2574_;
                        }
                    }
                } else {
                    v_ks_2575_ = lean_ctor_get(v_x_2556_, 0);
                    v_vs_2576_ = lean_ctor_get(v_x_2556_, 1);
                    v___x_2577_ = lean_unsigned_to_nat(0);
                    v___x_2578_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2575_, v_vs_2576_, v___x_2577_, v_x_2558_);
                    return v___x_2578_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2579_: *mut LeanObject,
    mut v_x_2580_: *mut LeanObject,
    mut v_x_2581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_867__boxed_2582_: usize = 0;
    let mut v_res_2583_: *mut LeanObject = core::ptr::null_mut();
    v_x_867__boxed_2582_ = lean_unbox_usize(v_x_2580_);
    lean_dec(v_x_2580_);
    v_res_2583_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_2579_, v_x_867__boxed_2582_, v_x_2581_);
    lean_dec_ref(v_x_2581_);
    lean_dec_ref(v_x_2579_);
    return v_res_2583_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(
    mut v_x_2584_: *mut LeanObject,
    mut v_x_2585_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2586_: u64 = 0;
    let mut v___x_2587_: usize = 0;
    let mut v___x_2588_: *mut LeanObject = core::ptr::null_mut();
    v___x_2586_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2585_);
    v___x_2587_ = lean_uint64_to_usize(v___x_2586_);
    v___x_2588_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_2584_, v___x_2587_, v_x_2585_);
    return v___x_2588_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg___boxed(
    mut v_x_2589_: *mut LeanObject,
    mut v_x_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2591_: *mut LeanObject = core::ptr::null_mut();
    v_res_2591_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_2589_, v_x_2590_);
    lean_dec_ref(v_x_2590_);
    lean_dec_ref(v_x_2589_);
    return v_res_2591_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
    mut v_e_2592_: *mut LeanObject,
    mut v_a_2593_: *mut LeanObject,
    mut v_a_2594_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2596_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2599_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2600_: u8 = 0;
    let mut v_exprToNatStructId_2601_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2605_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2606_: u8 = 0;
    let mut v_a_2607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2610_: u8 = 0;
    let mut v___x_2612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2596_ = l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_2593_, v_a_2594_);
                if lean_obj_tag(v___x_2596_) == 0 {
                    v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
                    v_isSharedCheck_2606_ = (!lean_is_exclusive(v___x_2596_)) as u8;
                    if v_isSharedCheck_2606_ == 0 {
                        v___x_2599_ = v___x_2596_;
                        v_isShared_2600_ = v_isSharedCheck_2606_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2597_);
                        lean_dec(v___x_2596_);
                        v___x_2599_ = lean_box(0);
                        v_isShared_2600_ = v_isSharedCheck_2606_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2607_ = lean_ctor_get(v___x_2596_, 0);
                    v_isSharedCheck_2614_ = (!lean_is_exclusive(v___x_2596_)) as u8;
                    if v_isSharedCheck_2614_ == 0 {
                        v___x_2609_ = v___x_2596_;
                        v_isShared_2610_ = v_isSharedCheck_2614_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2607_);
                        lean_dec(v___x_2596_);
                        v___x_2609_ = lean_box(0);
                        v_isShared_2610_ = v_isSharedCheck_2614_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_exprToNatStructId_2601_ = lean_ctor_get(v_a_2597_, 7);
                lean_inc_ref(v_exprToNatStructId_2601_);
                lean_dec(v_a_2597_);
                v___x_2602_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_exprToNatStructId_2601_, v_e_2592_);
                lean_dec_ref(v_exprToNatStructId_2601_);
                if v_isShared_2600_ == 0 {
                    lean_ctor_set(v___x_2599_, 0, v___x_2602_);
                    v___x_2604_ = v___x_2599_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2605_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2605_, 0, v___x_2602_);
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
                    v_reuseFailAlloc_2613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_a_2607_);
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
    mut v_e_2615_: *mut LeanObject,
    mut v_a_2616_: *mut LeanObject,
    mut v_a_2617_: *mut LeanObject,
    mut v_a_2618_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2619_: *mut LeanObject = core::ptr::null_mut();
    v_res_2619_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
        v_e_2615_, v_a_2616_, v_a_2617_,
    );
    lean_dec_ref(v_a_2617_);
    lean_dec(v_a_2616_);
    lean_dec_ref(v_e_2615_);
    return v_res_2619_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(
    mut v_e_2620_: *mut LeanObject,
    mut v_a_2621_: *mut LeanObject,
    mut v_a_2622_: *mut LeanObject,
    mut v_a_2623_: *mut LeanObject,
    mut v_a_2624_: *mut LeanObject,
    mut v_a_2625_: *mut LeanObject,
    mut v_a_2626_: *mut LeanObject,
    mut v_a_2627_: *mut LeanObject,
    mut v_a_2628_: *mut LeanObject,
    mut v_a_2629_: *mut LeanObject,
    mut v_a_2630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2632_: *mut LeanObject = core::ptr::null_mut();
    v___x_2632_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
        v_e_2620_, v_a_2621_, v_a_2629_,
    );
    return v___x_2632_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___boxed(
    mut v_e_2633_: *mut LeanObject,
    mut v_a_2634_: *mut LeanObject,
    mut v_a_2635_: *mut LeanObject,
    mut v_a_2636_: *mut LeanObject,
    mut v_a_2637_: *mut LeanObject,
    mut v_a_2638_: *mut LeanObject,
    mut v_a_2639_: *mut LeanObject,
    mut v_a_2640_: *mut LeanObject,
    mut v_a_2641_: *mut LeanObject,
    mut v_a_2642_: *mut LeanObject,
    mut v_a_2643_: *mut LeanObject,
    mut v_a_2644_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2645_: *mut LeanObject = core::ptr::null_mut();
    v_res_2645_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f(
        v_e_2633_, v_a_2634_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_, v_a_2639_, v_a_2640_,
        v_a_2641_, v_a_2642_, v_a_2643_,
    );
    lean_dec(v_a_2643_);
    lean_dec_ref(v_a_2642_);
    lean_dec(v_a_2641_);
    lean_dec_ref(v_a_2640_);
    lean_dec(v_a_2639_);
    lean_dec_ref(v_a_2638_);
    lean_dec(v_a_2637_);
    lean_dec_ref(v_a_2636_);
    lean_dec(v_a_2635_);
    lean_dec(v_a_2634_);
    lean_dec_ref(v_e_2633_);
    return v_res_2645_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(
    mut v_00_u03b2_2646_: *mut LeanObject,
    mut v_x_2647_: *mut LeanObject,
    mut v_x_2648_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2649_: *mut LeanObject = core::ptr::null_mut();
    v___x_2649_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_x_2647_, v_x_2648_);
    return v___x_2649_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___boxed(
    mut v_00_u03b2_2650_: *mut LeanObject,
    mut v_x_2651_: *mut LeanObject,
    mut v_x_2652_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2653_: *mut LeanObject = core::ptr::null_mut();
    v_res_2653_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0(v_00_u03b2_2650_, v_x_2651_, v_x_2652_);
    lean_dec_ref(v_x_2652_);
    lean_dec_ref(v_x_2651_);
    return v_res_2653_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(
    mut v_00_u03b2_2654_: *mut LeanObject,
    mut v_x_2655_: *mut LeanObject,
    mut v_x_2656_: usize,
    mut v_x_2657_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2658_: *mut LeanObject = core::ptr::null_mut();
    v___x_2658_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg(v_x_2655_, v_x_2656_, v_x_2657_);
    return v___x_2658_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2659_: *mut LeanObject,
    mut v_x_2660_: *mut LeanObject,
    mut v_x_2661_: *mut LeanObject,
    mut v_x_2662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_984__boxed_2663_: usize = 0;
    let mut v_res_2664_: *mut LeanObject = core::ptr::null_mut();
    v_x_984__boxed_2663_ = lean_unbox_usize(v_x_2661_);
    lean_dec(v_x_2661_);
    v_res_2664_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0(v_00_u03b2_2659_, v_x_2660_, v_x_984__boxed_2663_, v_x_2662_);
    lean_dec_ref(v_x_2662_);
    lean_dec_ref(v_x_2660_);
    return v_res_2664_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2665_: *mut LeanObject,
    mut v_keys_2666_: *mut LeanObject,
    mut v_vals_2667_: *mut LeanObject,
    mut v_heq_2668_: *mut LeanObject,
    mut v_i_2669_: *mut LeanObject,
    mut v_k_2670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2671_: *mut LeanObject = core::ptr::null_mut();
    v___x_2671_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2666_, v_vals_2667_, v_i_2669_, v_k_2670_);
    return v___x_2671_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2672_: *mut LeanObject,
    mut v_keys_2673_: *mut LeanObject,
    mut v_vals_2674_: *mut LeanObject,
    mut v_heq_2675_: *mut LeanObject,
    mut v_i_2676_: *mut LeanObject,
    mut v_k_2677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2678_: *mut LeanObject = core::ptr::null_mut();
    v_res_2678_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2672_, v_keys_2673_, v_vals_2674_, v_heq_2675_, v_i_2676_, v_k_2677_);
    lean_dec_ref(v_k_2677_);
    lean_dec_ref(v_vals_2674_);
    lean_dec_ref(v_keys_2673_);
    return v_res_2678_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(
    mut v_a_2679_: *mut LeanObject,
    mut v_b_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2684_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2688_: u8 = 0;
    let mut v_val_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2690_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2693_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2694_: u8 = 0;
    let mut v_val_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2696_: u8 = 0;
    let mut v___x_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2702_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2707_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2708_: u8 = 0;
    let mut v___x_2709_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2684_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
                    v_a_2679_, v_a_2681_, v_a_2682_,
                );
                if lean_obj_tag(v___x_2684_) == 0 {
                    v_a_2685_ = lean_ctor_get(v___x_2684_, 0);
                    v_isSharedCheck_2713_ = (!lean_is_exclusive(v___x_2684_)) as u8;
                    if v_isSharedCheck_2713_ == 0 {
                        v___x_2687_ = v___x_2684_;
                        v_isShared_2688_ = v_isSharedCheck_2713_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2685_);
                        lean_dec(v___x_2684_);
                        v___x_2687_ = lean_box(0);
                        v_isShared_2688_ = v_isSharedCheck_2713_;
                        state = 1;
                        continue;
                    }
                } else {
                    return v___x_2684_;
                }
            }
            1 => {
                if lean_obj_tag(v_a_2685_) == 1 {
                    lean_del_object(v___x_2687_);
                    v_val_2689_ = lean_ctor_get(v_a_2685_, 0);
                    v___x_2690_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
                        v_b_2680_, v_a_2681_, v_a_2682_,
                    );
                    if lean_obj_tag(v___x_2690_) == 0 {
                        v_a_2691_ = lean_ctor_get(v___x_2690_, 0);
                        v_isSharedCheck_2708_ = (!lean_is_exclusive(v___x_2690_)) as u8;
                        if v_isSharedCheck_2708_ == 0 {
                            v___x_2693_ = v___x_2690_;
                            v_isShared_2694_ = v_isSharedCheck_2708_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_2691_);
                            lean_dec(v___x_2690_);
                            v___x_2693_ = lean_box(0);
                            v_isShared_2694_ = v_isSharedCheck_2708_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref_known(v_a_2685_, 1);
                        return v___x_2690_;
                    }
                } else {
                    lean_dec(v_a_2685_);
                    v___x_2709_ = lean_box(0);
                    if v_isShared_2688_ == 0 {
                        lean_ctor_set(v___x_2687_, 0, v___x_2709_);
                        v___x_2711_ = v___x_2687_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_2712_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2712_, 0, v___x_2709_);
                        v___x_2711_ = v_reuseFailAlloc_2712_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2691_) == 1 {
                    v_val_2695_ = lean_ctor_get(v_a_2691_, 0);
                    lean_inc(v_val_2695_);
                    lean_dec_ref_known(v_a_2691_, 1);
                    v___x_2696_ = lean_nat_dec_eq(v_val_2689_, v_val_2695_);
                    lean_dec(v_val_2695_);
                    if v___x_2696_ == 0 {
                        lean_dec_ref_known(v_a_2685_, 1);
                        v___x_2697_ = lean_box(0);
                        if v_isShared_2694_ == 0 {
                            lean_ctor_set(v___x_2693_, 0, v___x_2697_);
                            v___x_2699_ = v___x_2693_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_2700_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2700_, 0, v___x_2697_);
                            v___x_2699_ = v_reuseFailAlloc_2700_;
                            state = 3;
                            continue;
                        }
                    } else {
                        if v_isShared_2694_ == 0 {
                            lean_ctor_set(v___x_2693_, 0, v_a_2685_);
                            v___x_2702_ = v___x_2693_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2703_ = lean_alloc_ctor(0, 1, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2703_, 0, v_a_2685_);
                            v___x_2702_ = v_reuseFailAlloc_2703_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v_a_2691_);
                    lean_dec_ref_known(v_a_2685_, 1);
                    v___x_2704_ = lean_box(0);
                    if v_isShared_2694_ == 0 {
                        lean_ctor_set(v___x_2693_, 0, v___x_2704_);
                        v___x_2706_ = v___x_2693_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2707_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2707_, 0, v___x_2704_);
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
    mut v_a_2714_: *mut LeanObject,
    mut v_b_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2719_: *mut LeanObject = core::ptr::null_mut();
    v_res_2719_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(
        v_a_2714_, v_b_2715_, v_a_2716_, v_a_2717_,
    );
    lean_dec_ref(v_a_2717_);
    lean_dec(v_a_2716_);
    lean_dec_ref(v_b_2715_);
    lean_dec_ref(v_a_2714_);
    return v_res_2719_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(
    mut v_a_2720_: *mut LeanObject,
    mut v_b_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v_a_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
    mut v_a_2726_: *mut LeanObject,
    mut v_a_2727_: *mut LeanObject,
    mut v_a_2728_: *mut LeanObject,
    mut v_a_2729_: *mut LeanObject,
    mut v_a_2730_: *mut LeanObject,
    mut v_a_2731_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2733_: *mut LeanObject = core::ptr::null_mut();
    v___x_2733_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___redArg(
        v_a_2720_, v_b_2721_, v_a_2722_, v_a_2730_,
    );
    return v___x_2733_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f___boxed(
    mut v_a_2734_: *mut LeanObject,
    mut v_b_2735_: *mut LeanObject,
    mut v_a_2736_: *mut LeanObject,
    mut v_a_2737_: *mut LeanObject,
    mut v_a_2738_: *mut LeanObject,
    mut v_a_2739_: *mut LeanObject,
    mut v_a_2740_: *mut LeanObject,
    mut v_a_2741_: *mut LeanObject,
    mut v_a_2742_: *mut LeanObject,
    mut v_a_2743_: *mut LeanObject,
    mut v_a_2744_: *mut LeanObject,
    mut v_a_2745_: *mut LeanObject,
    mut v_a_2746_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2747_: *mut LeanObject = core::ptr::null_mut();
    v_res_2747_ = l_Lean_Meta_Grind_Arith_Linear_inSameNatStruct_x3f(
        v_a_2734_, v_b_2735_, v_a_2736_, v_a_2737_, v_a_2738_, v_a_2739_, v_a_2740_, v_a_2741_,
        v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_,
    );
    lean_dec(v_a_2745_);
    lean_dec_ref(v_a_2744_);
    lean_dec(v_a_2743_);
    lean_dec_ref(v_a_2742_);
    lean_dec(v_a_2741_);
    lean_dec_ref(v_a_2740_);
    lean_dec(v_a_2739_);
    lean_dec_ref(v_a_2738_);
    lean_dec(v_a_2737_);
    lean_dec(v_a_2736_);
    lean_dec_ref(v_b_2735_);
    lean_dec_ref(v_a_2734_);
    return v_res_2747_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(
    mut v_x_2748_: *mut LeanObject,
    mut v_x_2749_: *mut LeanObject,
    mut v_x_2750_: *mut LeanObject,
    mut v_x_2751_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_ks_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2753_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2755_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2756_: u8 = 0;
    let mut v___x_2757_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: u8 = 0;
    let mut v___x_2759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2763_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2764_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2765_: u8 = 0;
    let mut v___x_2767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2771_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2775_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2776_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2777_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_ks_2752_ = lean_ctor_get(v_x_2748_, 0);
                v_vs_2753_ = lean_ctor_get(v_x_2748_, 1);
                v_isSharedCheck_2777_ = (!lean_is_exclusive(v_x_2748_)) as u8;
                if v_isSharedCheck_2777_ == 0 {
                    v___x_2755_ = v_x_2748_;
                    v_isShared_2756_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_vs_2753_);
                    lean_inc(v_ks_2752_);
                    lean_dec(v_x_2748_);
                    v___x_2755_ = lean_box(0);
                    v_isShared_2756_ = v_isSharedCheck_2777_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v___x_2757_ = lean_array_get_size(v_ks_2752_);
                v___x_2758_ = lean_nat_dec_lt(v_x_2749_, v___x_2757_);
                if v___x_2758_ == 0 {
                    lean_dec(v_x_2749_);
                    v___x_2759_ = lean_array_push(v_ks_2752_, v_x_2750_);
                    v___x_2760_ = lean_array_push(v_vs_2753_, v_x_2751_);
                    if v_isShared_2756_ == 0 {
                        lean_ctor_set(v___x_2755_, 1, v___x_2760_);
                        lean_ctor_set(v___x_2755_, 0, v___x_2759_);
                        v___x_2762_ = v___x_2755_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2763_ = lean_alloc_ctor(1, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2763_, 0, v___x_2759_);
                        lean_ctor_set(v_reuseFailAlloc_2763_, 1, v___x_2760_);
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
                            v_reuseFailAlloc_2771_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2771_, 0, v_ks_2752_);
                            lean_ctor_set(v_reuseFailAlloc_2771_, 1, v_vs_2753_);
                            v___x_2767_ = v_reuseFailAlloc_2771_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v___x_2772_ = lean_array_fset(v_ks_2752_, v_x_2749_, v_x_2750_);
                        v___x_2773_ = lean_array_fset(v_vs_2753_, v_x_2749_, v_x_2751_);
                        lean_dec(v_x_2749_);
                        if v_isShared_2756_ == 0 {
                            lean_ctor_set(v___x_2755_, 1, v___x_2773_);
                            lean_ctor_set(v___x_2755_, 0, v___x_2772_);
                            v___x_2775_ = v___x_2755_;
                            state = 4;
                            continue;
                        } else {
                            v_reuseFailAlloc_2776_ = lean_alloc_ctor(1, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2772_);
                            lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___x_2773_);
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
                v___x_2768_ = lean_unsigned_to_nat(1);
                v___x_2769_ = lean_nat_add(v_x_2749_, v___x_2768_);
                lean_dec(v_x_2749_);
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
    mut v_n_2778_: *mut LeanObject,
    mut v_k_2779_: *mut LeanObject,
    mut v_v_2780_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2782_: *mut LeanObject = core::ptr::null_mut();
    v___x_2781_ = lean_unsigned_to_nat(0);
    v___x_2782_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_n_2778_, v___x_2781_, v_k_2779_, v_v_2780_);
    return v___x_2782_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_2783_: *mut LeanObject = core::ptr::null_mut();
    v___x_2783_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
    return v___x_2783_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(
    mut v_x_2784_: *mut LeanObject,
    mut v_x_2785_: usize,
    mut v_x_2786_: usize,
    mut v_x_2787_: *mut LeanObject,
    mut v_x_2788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_2789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2790_: usize = 0;
    let mut v___x_2791_: usize = 0;
    let mut v___x_2792_: usize = 0;
    let mut v___x_2793_: usize = 0;
    let mut v_j_2794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2796_: u8 = 0;
    let mut v___x_2798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2799_: u8 = 0;
    let mut v_v_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2813_: u8 = 0;
    let mut v___x_2814_: u8 = 0;
    let mut v___x_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2819_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2820_: u8 = 0;
    let mut v_node_2821_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2824_: u8 = 0;
    let mut v___x_2825_: usize = 0;
    let mut v___x_2826_: usize = 0;
    let mut v___x_2827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2831_: u8 = 0;
    let mut v___x_2832_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2833_: u8 = 0;
    let mut v_unused_2834_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ks_2835_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2836_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2841_: *mut LeanObject = core::ptr::null_mut();
    let mut v_newNode_2842_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_2844_: u8 = 0;
    let mut v_ks_2845_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_2846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2850_: usize = 0;
    let mut v___x_2851_: u8 = 0;
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2854_: u8 = 0;
    let mut v_reuseFailAlloc_2855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2856_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2784_) == 0 {
                    v_es_2789_ = lean_ctor_get(v_x_2784_, 0);
                    v___x_2790_ = 5usize;
                    v___x_2791_ = 1usize;
                    v___x_2792_ = lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_2793_ = lean_usize_land(v_x_2785_, v___x_2792_);
                    v_j_2794_ = lean_usize_to_nat(v___x_2793_);
                    v___x_2795_ = lean_array_get_size(v_es_2789_);
                    v___x_2796_ = lean_nat_dec_lt(v_j_2794_, v___x_2795_);
                    if v___x_2796_ == 0 {
                        lean_dec(v_j_2794_);
                        lean_dec(v_x_2788_);
                        lean_dec_ref(v_x_2787_);
                        return v_x_2784_;
                    } else {
                        lean_inc_ref(v_es_2789_);
                        v_isSharedCheck_2833_ = (!lean_is_exclusive(v_x_2784_)) as u8;
                        if v_isSharedCheck_2833_ == 0 {
                            v_unused_2834_ = lean_ctor_get(v_x_2784_, 0);
                            lean_dec(v_unused_2834_);
                            v___x_2798_ = v_x_2784_;
                            v_isShared_2799_ = v_isSharedCheck_2833_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v_x_2784_);
                            v___x_2798_ = lean_box(0);
                            v_isShared_2799_ = v_isSharedCheck_2833_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v_ks_2835_ = lean_ctor_get(v_x_2784_, 0);
                    v_vs_2836_ = lean_ctor_get(v_x_2784_, 1);
                    v_isSharedCheck_2856_ = (!lean_is_exclusive(v_x_2784_)) as u8;
                    if v_isSharedCheck_2856_ == 0 {
                        v___x_2838_ = v_x_2784_;
                        v_isShared_2839_ = v_isSharedCheck_2856_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_vs_2836_);
                        lean_inc(v_ks_2835_);
                        lean_dec(v_x_2784_);
                        v___x_2838_ = lean_box(0);
                        v_isShared_2839_ = v_isSharedCheck_2856_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                v_v_2800_ = lean_array_fget(v_es_2789_, v_j_2794_);
                v___x_2801_ = lean_box(0);
                v_xs_x27_2802_ = lean_array_fset(v_es_2789_, v_j_2794_, v___x_2801_);
                match lean_obj_tag(v_v_2800_) {
                    0 => {
                        v_key_2809_ = lean_ctor_get(v_v_2800_, 0);
                        v_val_2810_ = lean_ctor_get(v_v_2800_, 1);
                        v_isSharedCheck_2820_ = (!lean_is_exclusive(v_v_2800_)) as u8;
                        if v_isSharedCheck_2820_ == 0 {
                            v___x_2812_ = v_v_2800_;
                            v_isShared_2813_ = v_isSharedCheck_2820_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_val_2810_);
                            lean_inc(v_key_2809_);
                            lean_dec(v_v_2800_);
                            v___x_2812_ = lean_box(0);
                            v_isShared_2813_ = v_isSharedCheck_2820_;
                            state = 4;
                            continue;
                        }
                    }
                    1 => {
                        v_node_2821_ = lean_ctor_get(v_v_2800_, 0);
                        v_isSharedCheck_2831_ = (!lean_is_exclusive(v_v_2800_)) as u8;
                        if v_isSharedCheck_2831_ == 0 {
                            v___x_2823_ = v_v_2800_;
                            v_isShared_2824_ = v_isSharedCheck_2831_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_node_2821_);
                            lean_dec(v_v_2800_);
                            v___x_2823_ = lean_box(0);
                            v_isShared_2824_ = v_isSharedCheck_2831_;
                            state = 6;
                            continue;
                        }
                    }
                    _ => {
                        v___x_2832_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v___x_2832_, 0, v_x_2787_);
                        lean_ctor_set(v___x_2832_, 1, v_x_2788_);
                        v___y_2804_ = v___x_2832_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v___x_2805_ = lean_array_fset(v_xs_x27_2802_, v_j_2794_, v___y_2804_);
                lean_dec(v_j_2794_);
                if v_isShared_2799_ == 0 {
                    lean_ctor_set(v___x_2798_, 0, v___x_2805_);
                    v___x_2807_ = v___x_2798_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2808_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2808_, 0, v___x_2805_);
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
                    lean_del_object(v___x_2812_);
                    v___x_2815_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(
                        v_key_2809_,
                        v_val_2810_,
                        v_x_2787_,
                        v_x_2788_,
                    );
                    v___x_2816_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2816_, 0, v___x_2815_);
                    v___y_2804_ = v___x_2816_;
                    state = 2;
                    continue;
                } else {
                    lean_dec(v_val_2810_);
                    lean_dec(v_key_2809_);
                    if v_isShared_2813_ == 0 {
                        lean_ctor_set(v___x_2812_, 1, v_x_2788_);
                        lean_ctor_set(v___x_2812_, 0, v_x_2787_);
                        v___x_2818_ = v___x_2812_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_x_2787_);
                        lean_ctor_set(v_reuseFailAlloc_2819_, 1, v_x_2788_);
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
                    lean_ctor_set(v___x_2823_, 0, v___x_2827_);
                    v___x_2829_ = v___x_2823_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2830_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2827_);
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
                    v_reuseFailAlloc_2855_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 0, v_ks_2835_);
                    lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_vs_2836_);
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
                    v___x_2853_ = lean_unsigned_to_nat(4);
                    v___x_2854_ = lean_nat_dec_lt(v___x_2852_, v___x_2853_);
                    lean_dec(v___x_2852_);
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
                    v_ks_2845_ = lean_ctor_get(v_newNode_2842_, 0);
                    lean_inc_ref(v_ks_2845_);
                    v_vs_2846_ = lean_ctor_get(v_newNode_2842_, 1);
                    lean_inc_ref(v_vs_2846_);
                    lean_dec_ref(v_newNode_2842_);
                    v___x_2847_ = lean_unsigned_to_nat(0);
                    v___x_2848_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___closed__0);
                    v___x_2849_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_x_2786_, v_ks_2845_, v_vs_2846_, v___x_2847_, v___x_2848_);
                    lean_dec_ref(v_vs_2846_);
                    lean_dec_ref(v_ks_2845_);
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
    mut v_keys_2858_: *mut LeanObject,
    mut v_vals_2859_: *mut LeanObject,
    mut v_i_2860_: *mut LeanObject,
    mut v_entries_2861_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: u8 = 0;
    let mut v_k_2864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: u64 = 0;
    let mut v_h_2867_: usize = 0;
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2870_: usize = 0;
    let mut v___x_2871_: usize = 0;
    let mut v___x_2872_: usize = 0;
    let mut v_h_2873_: usize = 0;
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2875_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2862_ = lean_array_get_size(v_keys_2858_);
                v___x_2863_ = lean_nat_dec_lt(v_i_2860_, v___x_2862_);
                if v___x_2863_ == 0 {
                    lean_dec(v_i_2860_);
                    return v_entries_2861_;
                } else {
                    v_k_2864_ = lean_array_fget_borrowed(v_keys_2858_, v_i_2860_);
                    v_v_2865_ = lean_array_fget_borrowed(v_vals_2859_, v_i_2860_);
                    v___x_2866_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_k_2864_);
                    v_h_2867_ = lean_uint64_to_usize(v___x_2866_);
                    v___x_2868_ = 5usize;
                    v___x_2869_ = lean_unsigned_to_nat(1);
                    v___x_2870_ = 1usize;
                    v___x_2871_ = lean_usize_sub(v_depth_2857_, v___x_2870_);
                    v___x_2872_ = lean_usize_mul(v___x_2868_, v___x_2871_);
                    v_h_2873_ = lean_usize_shift_right(v_h_2867_, v___x_2872_);
                    v___x_2874_ = lean_nat_add(v_i_2860_, v___x_2869_);
                    lean_dec(v_i_2860_);
                    lean_inc(v_v_2865_);
                    lean_inc(v_k_2864_);
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
    mut v_depth_2877_: *mut LeanObject,
    mut v_keys_2878_: *mut LeanObject,
    mut v_vals_2879_: *mut LeanObject,
    mut v_i_2880_: *mut LeanObject,
    mut v_entries_2881_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_2882_: usize = 0;
    let mut v_res_2883_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_2882_ = lean_unbox_usize(v_depth_2877_);
    lean_dec(v_depth_2877_);
    v_res_2883_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_boxed_2882_, v_keys_2878_, v_vals_2879_, v_i_2880_, v_entries_2881_);
    lean_dec_ref(v_vals_2879_);
    lean_dec_ref(v_keys_2878_);
    return v_res_2883_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg___boxed(
    mut v_x_2884_: *mut LeanObject,
    mut v_x_2885_: *mut LeanObject,
    mut v_x_2886_: *mut LeanObject,
    mut v_x_2887_: *mut LeanObject,
    mut v_x_2888_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_6922__boxed_2889_: usize = 0;
    let mut v_x_6923__boxed_2890_: usize = 0;
    let mut v_res_2891_: *mut LeanObject = core::ptr::null_mut();
    v_x_6922__boxed_2889_ = lean_unbox_usize(v_x_2885_);
    lean_dec(v_x_2885_);
    v_x_6923__boxed_2890_ = lean_unbox_usize(v_x_2886_);
    lean_dec(v_x_2886_);
    v_res_2891_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_2884_, v_x_6922__boxed_2889_, v_x_6923__boxed_2890_, v_x_2887_, v_x_2888_);
    return v_res_2891_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(
    mut v_x_2892_: *mut LeanObject,
    mut v_x_2893_: *mut LeanObject,
    mut v_x_2894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2895_: u64 = 0;
    let mut v___x_2896_: usize = 0;
    let mut v___x_2897_: usize = 0;
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    v___x_2895_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2893_);
    v___x_2896_ = lean_uint64_to_usize(v___x_2895_);
    v___x_2897_ = 1usize;
    v___x_2898_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_2892_, v___x_2896_, v___x_2897_, v_x_2893_, v_x_2894_);
    return v___x_2898_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(
    mut v_e_2899_: *mut LeanObject,
    mut v_a_2900_: *mut LeanObject,
    mut v_s_2901_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_2902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_2904_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_2905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_2908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_2909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2911_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2912_: u8 = 0;
    let mut v___x_2913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_2902_ = lean_ctor_get(v_s_2901_, 0);
                v_typeIdOf_2903_ = lean_ctor_get(v_s_2901_, 1);
                v_exprToStructId_2904_ = lean_ctor_get(v_s_2901_, 2);
                v_exprToStructIdEntries_2905_ = lean_ctor_get(v_s_2901_, 3);
                v_forbiddenNatModules_2906_ = lean_ctor_get(v_s_2901_, 4);
                v_natStructs_2907_ = lean_ctor_get(v_s_2901_, 5);
                v_natTypeIdOf_2908_ = lean_ctor_get(v_s_2901_, 6);
                v_exprToNatStructId_2909_ = lean_ctor_get(v_s_2901_, 7);
                v_isSharedCheck_2917_ = (!lean_is_exclusive(v_s_2901_)) as u8;
                if v_isSharedCheck_2917_ == 0 {
                    v___x_2911_ = v_s_2901_;
                    v_isShared_2912_ = v_isSharedCheck_2917_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_exprToNatStructId_2909_);
                    lean_inc(v_natTypeIdOf_2908_);
                    lean_inc(v_natStructs_2907_);
                    lean_inc(v_forbiddenNatModules_2906_);
                    lean_inc(v_exprToStructIdEntries_2905_);
                    lean_inc(v_exprToStructId_2904_);
                    lean_inc(v_typeIdOf_2903_);
                    lean_inc(v_structs_2902_);
                    lean_dec(v_s_2901_);
                    v___x_2911_ = lean_box(0);
                    v_isShared_2912_ = v_isSharedCheck_2917_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                lean_inc(v_a_2900_);
                v___x_2913_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_exprToNatStructId_2909_, v_e_2899_, v_a_2900_);
                if v_isShared_2912_ == 0 {
                    lean_ctor_set(v___x_2911_, 7, v___x_2913_);
                    v___x_2915_ = v___x_2911_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_structs_2902_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 1, v_typeIdOf_2903_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 2, v_exprToStructId_2904_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 3, v_exprToStructIdEntries_2905_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 4, v_forbiddenNatModules_2906_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 5, v_natStructs_2907_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 6, v_natTypeIdOf_2908_);
                    lean_ctor_set(v_reuseFailAlloc_2916_, 7, v___x_2913_);
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
    mut v_e_2918_: *mut LeanObject,
    mut v_a_2919_: *mut LeanObject,
    mut v_s_2920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2921_: *mut LeanObject = core::ptr::null_mut();
    v_res_2921_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0(
        v_e_2918_, v_a_2919_, v_s_2920_,
    );
    lean_dec(v_a_2919_);
    return v_res_2921_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_2923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2924_: *mut LeanObject = core::ptr::null_mut();
    v___x_2923_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__0;
    v___x_2924_ = l_Lean_stringToMessageData(v___x_2923_);
    return v___x_2924_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
    mut v_e_2925_: *mut LeanObject,
    mut v_a_2926_: *mut LeanObject,
    mut v_a_2927_: *mut LeanObject,
    mut v_a_2928_: *mut LeanObject,
    mut v_a_2929_: *mut LeanObject,
    mut v_a_2930_: *mut LeanObject,
    mut v_a_2931_: *mut LeanObject,
    mut v_a_2932_: *mut LeanObject,
    mut v_a_2933_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2937_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2941_: u8 = 0;
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2944_: u8 = 0;
    let mut v___x_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2947_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2949_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2952_: u8 = 0;
    let mut v___x_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2956_: u8 = 0;
    let mut v___f_2957_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2958_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2963_: u8 = 0;
    let mut v___x_2965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2966_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2967_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2938_ = l_Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f___redArg(
                    v_e_2925_, v_a_2927_, v_a_2932_,
                );
                if lean_obj_tag(v___x_2938_) == 0 {
                    v_a_2939_ = lean_ctor_get(v___x_2938_, 0);
                    lean_inc(v_a_2939_);
                    lean_dec_ref_known(v___x_2938_, 1);
                    if lean_obj_tag(v_a_2939_) == 1 {
                        v_val_2940_ = lean_ctor_get(v_a_2939_, 0);
                        lean_inc(v_val_2940_);
                        lean_dec_ref_known(v_a_2939_, 1);
                        v___x_2941_ = lean_nat_dec_eq(v_val_2940_, v_a_2926_);
                        lean_dec(v_val_2940_);
                        if v___x_2941_ == 0 {
                            v___x_2942_ = l_Lean_Meta_Sym_getConfig___redArg(v_a_2928_);
                            if lean_obj_tag(v___x_2942_) == 0 {
                                v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
                                lean_inc(v_a_2943_);
                                lean_dec_ref_known(v___x_2942_, 1);
                                v___x_2944_ = (lean_unbox(v_a_2943_) as u8);
                                lean_dec(v_a_2943_);
                                if v___x_2944_ == 0 {
                                    lean_dec_ref(v_e_2925_);
                                    state = 1;
                                    continue;
                                } else {
                                    v___x_2945_ = lean_obj_once(core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1_once), _init_l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___closed__1);
                                    v___x_2946_ = l_Lean_indentExpr(v_e_2925_);
                                    v___x_2947_ = lean_alloc_ctor(7, 2, (0) as u32);
                                    lean_ctor_set(v___x_2947_, 0, v___x_2945_);
                                    lean_ctor_set(v___x_2947_, 1, v___x_2946_);
                                    v___x_2948_ = l_Lean_Meta_Sym_reportIssue(
                                        v___x_2947_,
                                        v_a_2928_,
                                        v_a_2929_,
                                        v_a_2930_,
                                        v_a_2931_,
                                        v_a_2932_,
                                        v_a_2933_,
                                    );
                                    if lean_obj_tag(v___x_2948_) == 0 {
                                        lean_dec_ref_known(v___x_2948_, 1);
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_2948_;
                                    }
                                }
                            } else {
                                lean_dec_ref(v_e_2925_);
                                v_a_2949_ = lean_ctor_get(v___x_2942_, 0);
                                v_isSharedCheck_2956_ = (!lean_is_exclusive(v___x_2942_)) as u8;
                                if v_isSharedCheck_2956_ == 0 {
                                    v___x_2951_ = v___x_2942_;
                                    v_isShared_2952_ = v_isSharedCheck_2956_;
                                    state = 2;
                                    continue;
                                } else {
                                    lean_inc(v_a_2949_);
                                    lean_dec(v___x_2942_);
                                    v___x_2951_ = lean_box(0);
                                    v_isShared_2952_ = v_isSharedCheck_2956_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_e_2925_);
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_2939_);
                        lean_inc(v_a_2926_);
                        v___f_2957_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg___lam__0___boxed as *mut core::ffi::c_void, 3, 2);
                        lean_closure_set(v___f_2957_, 0, v_e_2925_);
                        lean_closure_set(v___f_2957_, 1, v_a_2926_);
                        v___x_2958_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                        v___x_2959_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_2958_, v___f_2957_, v_a_2927_);
                        return v___x_2959_;
                    }
                } else {
                    lean_dec_ref(v_e_2925_);
                    v_a_2960_ = lean_ctor_get(v___x_2938_, 0);
                    v_isSharedCheck_2967_ = (!lean_is_exclusive(v___x_2938_)) as u8;
                    if v_isSharedCheck_2967_ == 0 {
                        v___x_2962_ = v___x_2938_;
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 4;
                        continue;
                    } else {
                        lean_inc(v_a_2960_);
                        lean_dec(v___x_2938_);
                        v___x_2962_ = lean_box(0);
                        v_isShared_2963_ = v_isSharedCheck_2967_;
                        state = 4;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2936_ = lean_box(0);
                v___x_2937_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_2937_, 0, v___x_2936_);
                return v___x_2937_;
            }
            2 => {
                if v_isShared_2952_ == 0 {
                    v___x_2954_ = v___x_2951_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
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
                    v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
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
    mut v_e_2968_: *mut LeanObject,
    mut v_a_2969_: *mut LeanObject,
    mut v_a_2970_: *mut LeanObject,
    mut v_a_2971_: *mut LeanObject,
    mut v_a_2972_: *mut LeanObject,
    mut v_a_2973_: *mut LeanObject,
    mut v_a_2974_: *mut LeanObject,
    mut v_a_2975_: *mut LeanObject,
    mut v_a_2976_: *mut LeanObject,
    mut v_a_2977_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2978_: *mut LeanObject = core::ptr::null_mut();
    v_res_2978_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
        v_e_2968_, v_a_2969_, v_a_2970_, v_a_2971_, v_a_2972_, v_a_2973_, v_a_2974_, v_a_2975_,
        v_a_2976_,
    );
    lean_dec(v_a_2976_);
    lean_dec_ref(v_a_2975_);
    lean_dec(v_a_2974_);
    lean_dec_ref(v_a_2973_);
    lean_dec(v_a_2972_);
    lean_dec_ref(v_a_2971_);
    lean_dec(v_a_2970_);
    lean_dec(v_a_2969_);
    return v_res_2978_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(
    mut v_e_2979_: *mut LeanObject,
    mut v_a_2980_: *mut LeanObject,
    mut v_a_2981_: *mut LeanObject,
    mut v_a_2982_: *mut LeanObject,
    mut v_a_2983_: *mut LeanObject,
    mut v_a_2984_: *mut LeanObject,
    mut v_a_2985_: *mut LeanObject,
    mut v_a_2986_: *mut LeanObject,
    mut v_a_2987_: *mut LeanObject,
    mut v_a_2988_: *mut LeanObject,
    mut v_a_2989_: *mut LeanObject,
    mut v_a_2990_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2992_: *mut LeanObject = core::ptr::null_mut();
    v___x_2992_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
        v_e_2979_, v_a_2980_, v_a_2981_, v_a_2985_, v_a_2986_, v_a_2987_, v_a_2988_, v_a_2989_,
        v_a_2990_,
    );
    return v___x_2992_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___boxed(
    mut v_e_2993_: *mut LeanObject,
    mut v_a_2994_: *mut LeanObject,
    mut v_a_2995_: *mut LeanObject,
    mut v_a_2996_: *mut LeanObject,
    mut v_a_2997_: *mut LeanObject,
    mut v_a_2998_: *mut LeanObject,
    mut v_a_2999_: *mut LeanObject,
    mut v_a_3000_: *mut LeanObject,
    mut v_a_3001_: *mut LeanObject,
    mut v_a_3002_: *mut LeanObject,
    mut v_a_3003_: *mut LeanObject,
    mut v_a_3004_: *mut LeanObject,
    mut v_a_3005_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3006_: *mut LeanObject = core::ptr::null_mut();
    v_res_3006_ = l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId(
        v_e_2993_, v_a_2994_, v_a_2995_, v_a_2996_, v_a_2997_, v_a_2998_, v_a_2999_, v_a_3000_,
        v_a_3001_, v_a_3002_, v_a_3003_, v_a_3004_,
    );
    lean_dec(v_a_3004_);
    lean_dec_ref(v_a_3003_);
    lean_dec(v_a_3002_);
    lean_dec_ref(v_a_3001_);
    lean_dec(v_a_3000_);
    lean_dec_ref(v_a_2999_);
    lean_dec(v_a_2998_);
    lean_dec_ref(v_a_2997_);
    lean_dec(v_a_2996_);
    lean_dec(v_a_2995_);
    lean_dec(v_a_2994_);
    return v_res_3006_;
}
pub unsafe fn l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0(
    mut v_00_u03b2_3007_: *mut LeanObject,
    mut v_x_3008_: *mut LeanObject,
    mut v_x_3009_: *mut LeanObject,
    mut v_x_3010_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3011_: *mut LeanObject = core::ptr::null_mut();
    v___x_3011_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_x_3008_, v_x_3009_, v_x_3010_);
    return v___x_3011_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(
    mut v_00_u03b2_3012_: *mut LeanObject,
    mut v_x_3013_: *mut LeanObject,
    mut v_x_3014_: usize,
    mut v_x_3015_: usize,
    mut v_x_3016_: *mut LeanObject,
    mut v_x_3017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3018_: *mut LeanObject = core::ptr::null_mut();
    v___x_3018_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___redArg(v_x_3013_, v_x_3014_, v_x_3015_, v_x_3016_, v_x_3017_);
    return v___x_3018_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0___boxed(
    mut v_00_u03b2_3019_: *mut LeanObject,
    mut v_x_3020_: *mut LeanObject,
    mut v_x_3021_: *mut LeanObject,
    mut v_x_3022_: *mut LeanObject,
    mut v_x_3023_: *mut LeanObject,
    mut v_x_3024_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_7201__boxed_3025_: usize = 0;
    let mut v_x_7202__boxed_3026_: usize = 0;
    let mut v_res_3027_: *mut LeanObject = core::ptr::null_mut();
    v_x_7201__boxed_3025_ = lean_unbox_usize(v_x_3021_);
    lean_dec(v_x_3021_);
    v_x_7202__boxed_3026_ = lean_unbox_usize(v_x_3022_);
    lean_dec(v_x_3022_);
    v_res_3027_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0(v_00_u03b2_3019_, v_x_3020_, v_x_7201__boxed_3025_, v_x_7202__boxed_3026_, v_x_3023_, v_x_3024_);
    return v_res_3027_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1(
    mut v_00_u03b2_3028_: *mut LeanObject,
    mut v_n_3029_: *mut LeanObject,
    mut v_k_3030_: *mut LeanObject,
    mut v_v_3031_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3032_: *mut LeanObject = core::ptr::null_mut();
    v___x_3032_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1___redArg(v_n_3029_, v_k_3030_, v_v_3031_);
    return v___x_3032_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(
    mut v_00_u03b2_3033_: *mut LeanObject,
    mut v_depth_3034_: usize,
    mut v_keys_3035_: *mut LeanObject,
    mut v_vals_3036_: *mut LeanObject,
    mut v_heq_3037_: *mut LeanObject,
    mut v_i_3038_: *mut LeanObject,
    mut v_entries_3039_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3040_: *mut LeanObject = core::ptr::null_mut();
    v___x_3040_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___redArg(v_depth_3034_, v_keys_3035_, v_vals_3036_, v_i_3038_, v_entries_3039_);
    return v___x_3040_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2___boxed(
    mut v_00_u03b2_3041_: *mut LeanObject,
    mut v_depth_3042_: *mut LeanObject,
    mut v_keys_3043_: *mut LeanObject,
    mut v_vals_3044_: *mut LeanObject,
    mut v_heq_3045_: *mut LeanObject,
    mut v_i_3046_: *mut LeanObject,
    mut v_entries_3047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_depth_boxed_3048_: usize = 0;
    let mut v_res_3049_: *mut LeanObject = core::ptr::null_mut();
    v_depth_boxed_3048_ = lean_unbox_usize(v_depth_3042_);
    lean_dec(v_depth_3042_);
    v_res_3049_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__2(v_00_u03b2_3041_, v_depth_boxed_3048_, v_keys_3043_, v_vals_3044_, v_heq_3045_, v_i_3046_, v_entries_3047_);
    lean_dec_ref(v_vals_3044_);
    lean_dec_ref(v_keys_3043_);
    return v_res_3049_;
}
pub unsafe fn l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2(
    mut v_00_u03b2_3050_: *mut LeanObject,
    mut v_x_3051_: *mut LeanObject,
    mut v_x_3052_: *mut LeanObject,
    mut v_x_3053_: *mut LeanObject,
    mut v_x_3054_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3055_: *mut LeanObject = core::ptr::null_mut();
    v___x_3055_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0_spec__0_spec__1_spec__2___redArg(v_x_3051_, v_x_3052_, v_x_3053_, v_x_3054_);
    return v___x_3055_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(
    mut v_a_3056_: *mut LeanObject,
    mut v_e_3057_: *mut LeanObject,
    mut v___x_3058_: *mut LeanObject,
    mut v_s_3059_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_3060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_3062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_3063_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_3064_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_3065_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_3066_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_3067_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3069_: u8 = 0;
    let mut v___x_3071_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3072_: u8 = 0;
    let mut v_v_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structId_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_3079_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_3080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_3083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_3085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rfl__q_3086_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toQFn_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_3089_: *mut LeanObject = core::ptr::null_mut();
    let mut v_smulFn_3090_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termMap_3091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3093_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3094_: u8 = 0;
    let mut v___x_3095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3099_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3104_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3105_: u8 = 0;
    let mut v_isSharedCheck_3106_: u8 = 0;
    let mut v_unused_3107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3109_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3111_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3113_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3114_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3060_ = lean_ctor_get(v_s_3059_, 0);
                v_typeIdOf_3061_ = lean_ctor_get(v_s_3059_, 1);
                v_exprToStructId_3062_ = lean_ctor_get(v_s_3059_, 2);
                v_exprToStructIdEntries_3063_ = lean_ctor_get(v_s_3059_, 3);
                v_forbiddenNatModules_3064_ = lean_ctor_get(v_s_3059_, 4);
                v_natStructs_3065_ = lean_ctor_get(v_s_3059_, 5);
                v_natTypeIdOf_3066_ = lean_ctor_get(v_s_3059_, 6);
                v_exprToNatStructId_3067_ = lean_ctor_get(v_s_3059_, 7);
                v___x_3068_ = lean_array_get_size(v_natStructs_3065_);
                v___x_3069_ = lean_nat_dec_lt(v_a_3056_, v___x_3068_);
                if v___x_3069_ == 0 {
                    lean_dec_ref(v___x_3058_);
                    lean_dec_ref(v_e_3057_);
                    return v_s_3059_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_3067_);
                    lean_inc_ref(v_natTypeIdOf_3066_);
                    lean_inc_ref(v_natStructs_3065_);
                    lean_inc_ref(v_forbiddenNatModules_3064_);
                    lean_inc_ref(v_exprToStructIdEntries_3063_);
                    lean_inc_ref(v_exprToStructId_3062_);
                    lean_inc_ref(v_typeIdOf_3061_);
                    lean_inc_ref(v_structs_3060_);
                    v_isSharedCheck_3106_ = (!lean_is_exclusive(v_s_3059_)) as u8;
                    if v_isSharedCheck_3106_ == 0 {
                        v_unused_3107_ = lean_ctor_get(v_s_3059_, 7);
                        lean_dec(v_unused_3107_);
                        v_unused_3108_ = lean_ctor_get(v_s_3059_, 6);
                        lean_dec(v_unused_3108_);
                        v_unused_3109_ = lean_ctor_get(v_s_3059_, 5);
                        lean_dec(v_unused_3109_);
                        v_unused_3110_ = lean_ctor_get(v_s_3059_, 4);
                        lean_dec(v_unused_3110_);
                        v_unused_3111_ = lean_ctor_get(v_s_3059_, 3);
                        lean_dec(v_unused_3111_);
                        v_unused_3112_ = lean_ctor_get(v_s_3059_, 2);
                        lean_dec(v_unused_3112_);
                        v_unused_3113_ = lean_ctor_get(v_s_3059_, 1);
                        lean_dec(v_unused_3113_);
                        v_unused_3114_ = lean_ctor_get(v_s_3059_, 0);
                        lean_dec(v_unused_3114_);
                        v___x_3071_ = v_s_3059_;
                        v_isShared_3072_ = v_isSharedCheck_3106_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_3059_);
                        v___x_3071_ = lean_box(0);
                        v_isShared_3072_ = v_isSharedCheck_3106_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3073_ = lean_array_fget(v_natStructs_3065_, v_a_3056_);
                v_id_3074_ = lean_ctor_get(v_v_3073_, 0);
                v_structId_3075_ = lean_ctor_get(v_v_3073_, 1);
                v_type_3076_ = lean_ctor_get(v_v_3073_, 2);
                v_u_3077_ = lean_ctor_get(v_v_3073_, 3);
                v_natModuleInst_3078_ = lean_ctor_get(v_v_3073_, 4);
                v_leInst_x3f_3079_ = lean_ctor_get(v_v_3073_, 5);
                v_ltInst_x3f_3080_ = lean_ctor_get(v_v_3073_, 6);
                v_lawfulOrderLTInst_x3f_3081_ = lean_ctor_get(v_v_3073_, 7);
                v_isPreorderInst_x3f_3082_ = lean_ctor_get(v_v_3073_, 8);
                v_orderedAddInst_x3f_3083_ = lean_ctor_get(v_v_3073_, 9);
                v_isLinearInst_x3f_3084_ = lean_ctor_get(v_v_3073_, 10);
                v_addRightCancelInst_x3f_3085_ = lean_ctor_get(v_v_3073_, 11);
                v_rfl__q_3086_ = lean_ctor_get(v_v_3073_, 12);
                v_zero_3087_ = lean_ctor_get(v_v_3073_, 13);
                v_toQFn_3088_ = lean_ctor_get(v_v_3073_, 14);
                v_addFn_3089_ = lean_ctor_get(v_v_3073_, 15);
                v_smulFn_3090_ = lean_ctor_get(v_v_3073_, 16);
                v_termMap_3091_ = lean_ctor_get(v_v_3073_, 17);
                v_isSharedCheck_3105_ = (!lean_is_exclusive(v_v_3073_)) as u8;
                if v_isSharedCheck_3105_ == 0 {
                    v___x_3093_ = v_v_3073_;
                    v_isShared_3094_ = v_isSharedCheck_3105_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_termMap_3091_);
                    lean_inc(v_smulFn_3090_);
                    lean_inc(v_addFn_3089_);
                    lean_inc(v_toQFn_3088_);
                    lean_inc(v_zero_3087_);
                    lean_inc(v_rfl__q_3086_);
                    lean_inc(v_addRightCancelInst_x3f_3085_);
                    lean_inc(v_isLinearInst_x3f_3084_);
                    lean_inc(v_orderedAddInst_x3f_3083_);
                    lean_inc(v_isPreorderInst_x3f_3082_);
                    lean_inc(v_lawfulOrderLTInst_x3f_3081_);
                    lean_inc(v_ltInst_x3f_3080_);
                    lean_inc(v_leInst_x3f_3079_);
                    lean_inc(v_natModuleInst_3078_);
                    lean_inc(v_u_3077_);
                    lean_inc(v_type_3076_);
                    lean_inc(v_structId_3075_);
                    lean_inc(v_id_3074_);
                    lean_dec(v_v_3073_);
                    v___x_3093_ = lean_box(0);
                    v_isShared_3094_ = v_isSharedCheck_3105_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3095_ = lean_box(0);
                v_xs_x27_3096_ = lean_array_fset(v_natStructs_3065_, v_a_3056_, v___x_3095_);
                v___x_3097_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_3091_, v_e_3057_, v___x_3058_);
                if v_isShared_3094_ == 0 {
                    lean_ctor_set(v___x_3093_, 17, v___x_3097_);
                    v___x_3099_ = v___x_3093_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3104_ = lean_alloc_ctor(0, 18, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 0, v_id_3074_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 1, v_structId_3075_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 2, v_type_3076_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 3, v_u_3077_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 4, v_natModuleInst_3078_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 5, v_leInst_x3f_3079_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 6, v_ltInst_x3f_3080_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 7, v_lawfulOrderLTInst_x3f_3081_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 8, v_isPreorderInst_x3f_3082_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 9, v_orderedAddInst_x3f_3083_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 10, v_isLinearInst_x3f_3084_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 11, v_addRightCancelInst_x3f_3085_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 12, v_rfl__q_3086_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 13, v_zero_3087_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 14, v_toQFn_3088_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 15, v_addFn_3089_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 16, v_smulFn_3090_);
                    lean_ctor_set(v_reuseFailAlloc_3104_, 17, v___x_3097_);
                    v___x_3099_ = v_reuseFailAlloc_3104_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3100_ = lean_array_fset(v_xs_x27_3096_, v_a_3056_, v___x_3099_);
                if v_isShared_3072_ == 0 {
                    lean_ctor_set(v___x_3071_, 5, v___x_3100_);
                    v___x_3102_ = v___x_3071_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3103_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_structs_3060_);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 1, v_typeIdOf_3061_);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 2, v_exprToStructId_3062_);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 3, v_exprToStructIdEntries_3063_);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 4, v_forbiddenNatModules_3064_);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 5, v___x_3100_);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 6, v_natTypeIdOf_3066_);
                    lean_ctor_set(v_reuseFailAlloc_3103_, 7, v_exprToNatStructId_3067_);
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
    mut v_a_3115_: *mut LeanObject,
    mut v_e_3116_: *mut LeanObject,
    mut v___x_3117_: *mut LeanObject,
    mut v_s_3118_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3119_: *mut LeanObject = core::ptr::null_mut();
    v_res_3119_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0(v_a_3115_, v_e_3116_, v___x_3117_, v_s_3118_);
    lean_dec(v_a_3115_);
    return v_res_3119_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(
    mut v_e_3120_: *mut LeanObject,
    mut v_a_3121_: *mut LeanObject,
    mut v_a_3122_: *mut LeanObject,
    mut v_a_3123_: *mut LeanObject,
    mut v_a_3124_: *mut LeanObject,
    mut v_a_3125_: *mut LeanObject,
    mut v_a_3126_: *mut LeanObject,
    mut v_a_3127_: *mut LeanObject,
    mut v_a_3128_: *mut LeanObject,
    mut v_a_3129_: *mut LeanObject,
    mut v_a_3130_: *mut LeanObject,
    mut v_a_3131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3137_: u8 = 0;
    let mut v_termMap_3138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rfl__q_3146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toQFn_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3153_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3157_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3160_: u8 = 0;
    let mut v___x_3162_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3164_: u8 = 0;
    let mut v_unused_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3166_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3169_: u8 = 0;
    let mut v___x_3171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3173_: u8 = 0;
    let mut v_a_3174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3177_: u8 = 0;
    let mut v___x_3179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3181_: u8 = 0;
    let mut v_a_3182_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3185_: u8 = 0;
    let mut v___x_3187_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3189_: u8 = 0;
    let mut v_a_3190_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3193_: u8 = 0;
    let mut v___x_3195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3196_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3197_: u8 = 0;
    let mut v_a_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3201_: u8 = 0;
    let mut v___x_3203_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3205_: u8 = 0;
    let mut v_isSharedCheck_3206_: u8 = 0;
    let mut v_a_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3210_: u8 = 0;
    let mut v___x_3212_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3214_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3133_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_, v_a_3127_,
                    v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_,
                );
                if lean_obj_tag(v___x_3133_) == 0 {
                    v_a_3134_ = lean_ctor_get(v___x_3133_, 0);
                    v_isSharedCheck_3206_ = (!lean_is_exclusive(v___x_3133_)) as u8;
                    if v_isSharedCheck_3206_ == 0 {
                        v___x_3136_ = v___x_3133_;
                        v_isShared_3137_ = v_isSharedCheck_3206_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3134_);
                        lean_dec(v___x_3133_);
                        v___x_3136_ = lean_box(0);
                        v_isShared_3137_ = v_isSharedCheck_3206_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3120_);
                    v_a_3207_ = lean_ctor_get(v___x_3133_, 0);
                    v_isSharedCheck_3214_ = (!lean_is_exclusive(v___x_3133_)) as u8;
                    if v_isSharedCheck_3214_ == 0 {
                        v___x_3209_ = v___x_3133_;
                        v_isShared_3210_ = v_isSharedCheck_3214_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3207_);
                        lean_dec(v___x_3133_);
                        v___x_3209_ = lean_box(0);
                        v_isShared_3210_ = v_isSharedCheck_3214_;
                        state = 15;
                        continue;
                    }
                }
            }
            1 => {
                v_termMap_3138_ = lean_ctor_get(v_a_3134_, 17);
                lean_inc_ref(v_termMap_3138_);
                lean_dec(v_a_3134_);
                v___x_3139_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_3138_, v_e_3120_);
                lean_dec_ref(v_termMap_3138_);
                if lean_obj_tag(v___x_3139_) == 1 {
                    lean_dec_ref(v_e_3120_);
                    v_val_3140_ = lean_ctor_get(v___x_3139_, 0);
                    lean_inc(v_val_3140_);
                    lean_dec_ref_known(v___x_3139_, 1);
                    if v_isShared_3137_ == 0 {
                        lean_ctor_set(v___x_3136_, 0, v_val_3140_);
                        v___x_3142_ = v___x_3136_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3143_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3143_, 0, v_val_3140_);
                        v___x_3142_ = v_reuseFailAlloc_3143_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3139_);
                    lean_del_object(v___x_3136_);
                    v___x_3144_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                        v_a_3121_, v_a_3122_, v_a_3123_, v_a_3124_, v_a_3125_, v_a_3126_,
                        v_a_3127_, v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_,
                    );
                    if lean_obj_tag(v___x_3144_) == 0 {
                        v_a_3145_ = lean_ctor_get(v___x_3144_, 0);
                        lean_inc(v_a_3145_);
                        lean_dec_ref_known(v___x_3144_, 1);
                        v_rfl__q_3146_ = lean_ctor_get(v_a_3145_, 12);
                        lean_inc_ref(v_rfl__q_3146_);
                        v_toQFn_3147_ = lean_ctor_get(v_a_3145_, 14);
                        lean_inc_ref(v_toQFn_3147_);
                        lean_dec(v_a_3145_);
                        lean_inc_ref(v_e_3120_);
                        v___x_3148_ = l_Lean_Expr_app___override(v_toQFn_3147_, v_e_3120_);
                        v___x_3149_ = l_Lean_Meta_Sym_shareCommon___redArg(v___x_3148_, v_a_3127_);
                        if lean_obj_tag(v___x_3149_) == 0 {
                            v_a_3150_ = lean_ctor_get(v___x_3149_, 0);
                            lean_inc_n(v_a_3150_, 2);
                            lean_dec_ref_known(v___x_3149_, 1);
                            v___x_3151_ = l_Lean_Expr_app___override(v_rfl__q_3146_, v_a_3150_);
                            v___x_3152_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v___x_3152_, 0, v_a_3150_);
                            lean_ctor_set(v___x_3152_, 1, v___x_3151_);
                            lean_inc_ref(v___x_3152_);
                            lean_inc_ref(v_e_3120_);
                            lean_inc(v_a_3121_);
                            v___f_3153_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar___lam__0___boxed as *mut core::ffi::c_void, 4, 3);
                            lean_closure_set(v___f_3153_, 0, v_a_3121_);
                            lean_closure_set(v___f_3153_, 1, v_e_3120_);
                            lean_closure_set(v___f_3153_, 2, v___x_3152_);
                            v___x_3154_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                            v___x_3155_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3154_, v___f_3153_, v_a_3122_);
                            if lean_obj_tag(v___x_3155_) == 0 {
                                lean_dec_ref_known(v___x_3155_, 1);
                                lean_inc_ref(v_e_3120_);
                                v___x_3156_ =
                                    l_Lean_Meta_Grind_Arith_Linear_setTermNatStructId___redArg(
                                        v_e_3120_, v_a_3121_, v_a_3122_, v_a_3126_, v_a_3127_,
                                        v_a_3128_, v_a_3129_, v_a_3130_, v_a_3131_,
                                    );
                                if lean_obj_tag(v___x_3156_) == 0 {
                                    lean_dec_ref_known(v___x_3156_, 1);
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
                                    if lean_obj_tag(v___x_3157_) == 0 {
                                        v_isSharedCheck_3164_ =
                                            (!lean_is_exclusive(v___x_3157_)) as u8;
                                        if v_isSharedCheck_3164_ == 0 {
                                            v_unused_3165_ = lean_ctor_get(v___x_3157_, 0);
                                            lean_dec(v_unused_3165_);
                                            v___x_3159_ = v___x_3157_;
                                            v_isShared_3160_ = v_isSharedCheck_3164_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_dec(v___x_3157_);
                                            v___x_3159_ = lean_box(0);
                                            v_isShared_3160_ = v_isSharedCheck_3164_;
                                            state = 3;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref_known(v___x_3152_, 2);
                                        v_a_3166_ = lean_ctor_get(v___x_3157_, 0);
                                        v_isSharedCheck_3173_ =
                                            (!lean_is_exclusive(v___x_3157_)) as u8;
                                        if v_isSharedCheck_3173_ == 0 {
                                            v___x_3168_ = v___x_3157_;
                                            v_isShared_3169_ = v_isSharedCheck_3173_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3166_);
                                            lean_dec(v___x_3157_);
                                            v___x_3168_ = lean_box(0);
                                            v_isShared_3169_ = v_isSharedCheck_3173_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                } else {
                                    lean_dec_ref_known(v___x_3152_, 2);
                                    lean_dec_ref(v_e_3120_);
                                    v_a_3174_ = lean_ctor_get(v___x_3156_, 0);
                                    v_isSharedCheck_3181_ = (!lean_is_exclusive(v___x_3156_)) as u8;
                                    if v_isSharedCheck_3181_ == 0 {
                                        v___x_3176_ = v___x_3156_;
                                        v_isShared_3177_ = v_isSharedCheck_3181_;
                                        state = 7;
                                        continue;
                                    } else {
                                        lean_inc(v_a_3174_);
                                        lean_dec(v___x_3156_);
                                        v___x_3176_ = lean_box(0);
                                        v_isShared_3177_ = v_isSharedCheck_3181_;
                                        state = 7;
                                        continue;
                                    }
                                }
                            } else {
                                lean_dec_ref_known(v___x_3152_, 2);
                                lean_dec_ref(v_e_3120_);
                                v_a_3182_ = lean_ctor_get(v___x_3155_, 0);
                                v_isSharedCheck_3189_ = (!lean_is_exclusive(v___x_3155_)) as u8;
                                if v_isSharedCheck_3189_ == 0 {
                                    v___x_3184_ = v___x_3155_;
                                    v_isShared_3185_ = v_isSharedCheck_3189_;
                                    state = 9;
                                    continue;
                                } else {
                                    lean_inc(v_a_3182_);
                                    lean_dec(v___x_3155_);
                                    v___x_3184_ = lean_box(0);
                                    v_isShared_3185_ = v_isSharedCheck_3189_;
                                    state = 9;
                                    continue;
                                }
                            }
                        } else {
                            lean_dec_ref(v_rfl__q_3146_);
                            lean_dec_ref(v_e_3120_);
                            v_a_3190_ = lean_ctor_get(v___x_3149_, 0);
                            v_isSharedCheck_3197_ = (!lean_is_exclusive(v___x_3149_)) as u8;
                            if v_isSharedCheck_3197_ == 0 {
                                v___x_3192_ = v___x_3149_;
                                v_isShared_3193_ = v_isSharedCheck_3197_;
                                state = 11;
                                continue;
                            } else {
                                lean_inc(v_a_3190_);
                                lean_dec(v___x_3149_);
                                v___x_3192_ = lean_box(0);
                                v_isShared_3193_ = v_isSharedCheck_3197_;
                                state = 11;
                                continue;
                            }
                        }
                    } else {
                        lean_dec_ref(v_e_3120_);
                        v_a_3198_ = lean_ctor_get(v___x_3144_, 0);
                        v_isSharedCheck_3205_ = (!lean_is_exclusive(v___x_3144_)) as u8;
                        if v_isSharedCheck_3205_ == 0 {
                            v___x_3200_ = v___x_3144_;
                            v_isShared_3201_ = v_isSharedCheck_3205_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_3198_);
                            lean_dec(v___x_3144_);
                            v___x_3200_ = lean_box(0);
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
                    lean_ctor_set(v___x_3159_, 0, v___x_3152_);
                    v___x_3162_ = v___x_3159_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3163_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3163_, 0, v___x_3152_);
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
                    v_reuseFailAlloc_3172_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3172_, 0, v_a_3166_);
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
                    v_reuseFailAlloc_3180_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3180_, 0, v_a_3174_);
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
                    v_reuseFailAlloc_3188_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3188_, 0, v_a_3182_);
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
                    v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3190_);
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
                    v_reuseFailAlloc_3204_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3204_, 0, v_a_3198_);
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
                    v_reuseFailAlloc_3213_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3213_, 0, v_a_3207_);
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
    mut v_e_3215_: *mut LeanObject,
    mut v_a_3216_: *mut LeanObject,
    mut v_a_3217_: *mut LeanObject,
    mut v_a_3218_: *mut LeanObject,
    mut v_a_3219_: *mut LeanObject,
    mut v_a_3220_: *mut LeanObject,
    mut v_a_3221_: *mut LeanObject,
    mut v_a_3222_: *mut LeanObject,
    mut v_a_3223_: *mut LeanObject,
    mut v_a_3224_: *mut LeanObject,
    mut v_a_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3228_: *mut LeanObject = core::ptr::null_mut();
    v_res_3228_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3215_, v_a_3216_, v_a_3217_, v_a_3218_, v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_);
    lean_dec(v_a_3226_);
    lean_dec_ref(v_a_3225_);
    lean_dec(v_a_3224_);
    lean_dec_ref(v_a_3223_);
    lean_dec(v_a_3222_);
    lean_dec_ref(v_a_3221_);
    lean_dec(v_a_3220_);
    lean_dec_ref(v_a_3219_);
    lean_dec(v_a_3218_);
    lean_dec(v_a_3217_);
    lean_dec(v_a_3216_);
    return v_res_3228_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(
    mut v_natStruct_3229_: *mut LeanObject,
    mut v_inst_3230_: *mut LeanObject,
) -> u8 {
    let mut v_addFn_3231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3232_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3233_: u8 = 0;
    v_addFn_3231_ = lean_ctor_get(v_natStruct_3229_, 15);
    v___x_3232_ = l_Lean_Expr_appArg_x21(v_addFn_3231_);
    v___x_3233_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_3232_,
        v_inst_3230_,
    );
    lean_dec_ref(v___x_3232_);
    return v___x_3233_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst___boxed(
    mut v_natStruct_3234_: *mut LeanObject,
    mut v_inst_3235_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3236_: u8 = 0;
    let mut v_r_3237_: *mut LeanObject = core::ptr::null_mut();
    v_res_3236_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_natStruct_3234_, v_inst_3235_);
    lean_dec_ref(v_inst_3235_);
    lean_dec_ref(v_natStruct_3234_);
    v_r_3237_ = lean_box((v_res_3236_) as usize);
    return v_r_3237_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(
    mut v_natStruct_3238_: *mut LeanObject,
    mut v_inst_3239_: *mut LeanObject,
) -> u8 {
    let mut v_zero_3240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3242_: u8 = 0;
    v_zero_3240_ = lean_ctor_get(v_natStruct_3238_, 13);
    v___x_3241_ = l_Lean_Expr_appArg_x21(v_zero_3240_);
    v___x_3242_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_3241_,
        v_inst_3239_,
    );
    lean_dec_ref(v___x_3241_);
    return v___x_3242_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst___boxed(
    mut v_natStruct_3243_: *mut LeanObject,
    mut v_inst_3244_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3245_: u8 = 0;
    let mut v_r_3246_: *mut LeanObject = core::ptr::null_mut();
    v_res_3245_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_natStruct_3243_, v_inst_3244_);
    lean_dec_ref(v_inst_3244_);
    lean_dec_ref(v_natStruct_3243_);
    v_r_3246_ = lean_box((v_res_3245_) as usize);
    return v_r_3246_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(
    mut v_natStruct_3247_: *mut LeanObject,
    mut v_inst_3248_: *mut LeanObject,
) -> u8 {
    let mut v_smulFn_3249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3251_: u8 = 0;
    v_smulFn_3249_ = lean_ctor_get(v_natStruct_3247_, 16);
    v___x_3250_ = l_Lean_Expr_appArg_x21(v_smulFn_3249_);
    v___x_3251_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
        v___x_3250_,
        v_inst_3248_,
    );
    lean_dec_ref(v___x_3250_);
    return v___x_3251_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst___boxed(
    mut v_natStruct_3252_: *mut LeanObject,
    mut v_inst_3253_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3254_: u8 = 0;
    let mut v_r_3255_: *mut LeanObject = core::ptr::null_mut();
    v_res_3254_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_natStruct_3252_, v_inst_3253_);
    lean_dec_ref(v_inst_3253_);
    lean_dec_ref(v_natStruct_3252_);
    v_r_3255_ = lean_box((v_res_3254_) as usize);
    return v_r_3255_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(
    mut v_e_3301_: *mut LeanObject,
    mut v_a_3302_: *mut LeanObject,
    mut v_a_3303_: *mut LeanObject,
    mut v_a_3304_: *mut LeanObject,
    mut v_a_3305_: *mut LeanObject,
    mut v_a_3306_: *mut LeanObject,
    mut v_a_3307_: *mut LeanObject,
    mut v_a_3308_: *mut LeanObject,
    mut v_a_3309_: *mut LeanObject,
    mut v_a_3310_: *mut LeanObject,
    mut v_a_3311_: *mut LeanObject,
    mut v_a_3312_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3322_: u8 = 0;
    let mut v___x_3323_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3324_: u8 = 0;
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: u8 = 0;
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: u8 = 0;
    let mut v___x_3334_: u8 = 0;
    let mut v___x_3335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_3336_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3339_: u8 = 0;
    let mut v___x_3340_: u8 = 0;
    let mut v___x_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: u8 = 0;
    let mut v___x_3344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3345_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3346_: u8 = 0;
    let mut v___x_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3348_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3349_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3350_: u8 = 0;
    let mut v___x_3351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3352_: u8 = 0;
    let mut v___x_3353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3354_: u8 = 0;
    let mut v___x_3355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3357_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3359_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3361_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3362_: u8 = 0;
    let mut v___x_3363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3364_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3366_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3367_: u8 = 0;
    let mut v_fst_3368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3369_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3372_: u8 = 0;
    let mut v_addFn_3373_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3374_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3376_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3377_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3379_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3382_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3385_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3388_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3389_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3390_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3391_: u8 = 0;
    let mut v_isSharedCheck_3392_: u8 = 0;
    let mut v_isSharedCheck_3393_: u8 = 0;
    let mut v___x_3394_: u8 = 0;
    let mut v___x_3395_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3397_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3400_: u8 = 0;
    let mut v_fst_3401_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3402_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3404_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3405_: u8 = 0;
    let mut v_nsmulFn_3406_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3407_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3408_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3412_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3413_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3414_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3417_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3419_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3420_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3421_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3422_: u8 = 0;
    let mut v_isSharedCheck_3423_: u8 = 0;
    let mut v_type_3424_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3425_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3426_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_3427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3432_: u8 = 0;
    let mut v___x_3433_: u8 = 0;
    let mut v___x_3434_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_3435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3444_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3445_: u8 = 0;
    let mut v_a_3446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v___x_3451_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3453_: u8 = 0;
    let mut v___x_3454_: u8 = 0;
    let mut v___x_3455_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_3456_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3457_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3458_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3460_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3467_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3469_: u8 = 0;
    let mut v_a_3470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3473_: u8 = 0;
    let mut v___x_3475_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3477_: u8 = 0;
    let mut v_a_3478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3480_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3481_: u8 = 0;
    let mut v___x_3483_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3484_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3485_: u8 = 0;
    let mut v_a_3486_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3488_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3489_: u8 = 0;
    let mut v___x_3491_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3492_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3493_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3314_ = l_Lean_Meta_Grind_Arith_Linear_OfNatModuleM_getStruct(
                    v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_,
                    v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_,
                );
                if lean_obj_tag(v___x_3314_) == 0 {
                    v_a_3315_ = lean_ctor_get(v___x_3314_, 0);
                    lean_inc(v_a_3315_);
                    lean_dec_ref_known(v___x_3314_, 1);
                    v___x_3316_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                        v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_,
                        v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_,
                    );
                    if lean_obj_tag(v___x_3316_) == 0 {
                        v_a_3317_ = lean_ctor_get(v___x_3316_, 0);
                        lean_inc(v_a_3317_);
                        lean_dec_ref_known(v___x_3316_, 1);
                        lean_inc_ref(v_e_3301_);
                        v___x_3318_ =
                            l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_3301_, v_a_3310_);
                        if lean_obj_tag(v___x_3318_) == 0 {
                            v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
                            v_isSharedCheck_3469_ = (!lean_is_exclusive(v___x_3318_)) as u8;
                            if v_isSharedCheck_3469_ == 0 {
                                v___x_3321_ = v___x_3318_;
                                v_isShared_3322_ = v_isSharedCheck_3469_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_3319_);
                                lean_dec(v___x_3318_);
                                v___x_3321_ = lean_box(0);
                                v_isShared_3322_ = v_isSharedCheck_3469_;
                                state = 1;
                                continue;
                            }
                        } else {
                            lean_dec(v_a_3317_);
                            lean_dec(v_a_3315_);
                            lean_dec_ref(v_e_3301_);
                            v_a_3470_ = lean_ctor_get(v___x_3318_, 0);
                            v_isSharedCheck_3477_ = (!lean_is_exclusive(v___x_3318_)) as u8;
                            if v_isSharedCheck_3477_ == 0 {
                                v___x_3472_ = v___x_3318_;
                                v_isShared_3473_ = v_isSharedCheck_3477_;
                                state = 17;
                                continue;
                            } else {
                                lean_inc(v_a_3470_);
                                lean_dec(v___x_3318_);
                                v___x_3472_ = lean_box(0);
                                v_isShared_3473_ = v_isSharedCheck_3477_;
                                state = 17;
                                continue;
                            }
                        }
                    } else {
                        lean_dec(v_a_3315_);
                        lean_dec_ref(v_e_3301_);
                        v_a_3478_ = lean_ctor_get(v___x_3316_, 0);
                        v_isSharedCheck_3485_ = (!lean_is_exclusive(v___x_3316_)) as u8;
                        if v_isSharedCheck_3485_ == 0 {
                            v___x_3480_ = v___x_3316_;
                            v_isShared_3481_ = v_isSharedCheck_3485_;
                            state = 19;
                            continue;
                        } else {
                            lean_inc(v_a_3478_);
                            lean_dec(v___x_3316_);
                            v___x_3480_ = lean_box(0);
                            v_isShared_3481_ = v_isSharedCheck_3485_;
                            state = 19;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_3301_);
                    v_a_3486_ = lean_ctor_get(v___x_3314_, 0);
                    v_isSharedCheck_3493_ = (!lean_is_exclusive(v___x_3314_)) as u8;
                    if v_isSharedCheck_3493_ == 0 {
                        v___x_3488_ = v___x_3314_;
                        v_isShared_3489_ = v_isSharedCheck_3493_;
                        state = 21;
                        continue;
                    } else {
                        lean_inc(v_a_3486_);
                        lean_dec(v___x_3314_);
                        v___x_3488_ = lean_box(0);
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
                    lean_dec_ref(v___x_3323_);
                    lean_del_object(v___x_3321_);
                    lean_dec(v_a_3317_);
                    lean_dec(v_a_3315_);
                    v___x_3325_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                    return v___x_3325_;
                } else {
                    v_arg_3326_ = lean_ctor_get(v___x_3323_, 1);
                    lean_inc_ref(v_arg_3326_);
                    v___x_3327_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3323_);
                    v___x_3328_ = l_Lean_Expr_isApp(v___x_3327_);
                    if v___x_3328_ == 0 {
                        lean_dec_ref(v___x_3327_);
                        lean_dec_ref(v_arg_3326_);
                        lean_del_object(v___x_3321_);
                        lean_dec(v_a_3317_);
                        lean_dec(v_a_3315_);
                        v___x_3329_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                        return v___x_3329_;
                    } else {
                        v_arg_3330_ = lean_ctor_get(v___x_3327_, 1);
                        lean_inc_ref(v_arg_3330_);
                        v___x_3331_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3327_);
                        v___x_3332_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2;
                        v___x_3333_ = l_Lean_Expr_isConstOf(v___x_3331_, v___x_3332_);
                        if v___x_3333_ == 0 {
                            lean_del_object(v___x_3321_);
                            v___x_3334_ = l_Lean_Expr_isApp(v___x_3331_);
                            if v___x_3334_ == 0 {
                                lean_dec_ref(v___x_3331_);
                                lean_dec_ref(v_arg_3330_);
                                lean_dec_ref(v_arg_3326_);
                                lean_dec(v_a_3317_);
                                lean_dec(v_a_3315_);
                                v___x_3335_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                return v___x_3335_;
                            } else {
                                v_arg_3336_ = lean_ctor_get(v___x_3331_, 1);
                                lean_inc_ref(v_arg_3336_);
                                v___x_3337_ = l_Lean_Expr_appFnCleanup___redArg(v___x_3331_);
                                v___x_3338_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5;
                                v___x_3339_ = l_Lean_Expr_isConstOf(v___x_3337_, v___x_3338_);
                                if v___x_3339_ == 0 {
                                    v___x_3340_ = l_Lean_Expr_isApp(v___x_3337_);
                                    if v___x_3340_ == 0 {
                                        lean_dec_ref(v___x_3337_);
                                        lean_dec_ref(v_arg_3336_);
                                        lean_dec_ref(v_arg_3330_);
                                        lean_dec_ref(v_arg_3326_);
                                        lean_dec(v_a_3317_);
                                        lean_dec(v_a_3315_);
                                        v___x_3341_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                        return v___x_3341_;
                                    } else {
                                        v___x_3342_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_3337_);
                                        v___x_3343_ = l_Lean_Expr_isApp(v___x_3342_);
                                        if v___x_3343_ == 0 {
                                            lean_dec_ref(v___x_3342_);
                                            lean_dec_ref(v_arg_3336_);
                                            lean_dec_ref(v_arg_3330_);
                                            lean_dec_ref(v_arg_3326_);
                                            lean_dec(v_a_3317_);
                                            lean_dec(v_a_3315_);
                                            v___x_3344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                            return v___x_3344_;
                                        } else {
                                            v___x_3345_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_3342_);
                                            v___x_3346_ = l_Lean_Expr_isApp(v___x_3345_);
                                            if v___x_3346_ == 0 {
                                                lean_dec_ref(v___x_3345_);
                                                lean_dec_ref(v_arg_3336_);
                                                lean_dec_ref(v_arg_3330_);
                                                lean_dec_ref(v_arg_3326_);
                                                lean_dec(v_a_3317_);
                                                lean_dec(v_a_3315_);
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
                                                    lean_dec_ref(v___x_3348_);
                                                    if v___x_3352_ == 0 {
                                                        lean_dec_ref(v_arg_3336_);
                                                        lean_dec_ref(v_arg_3330_);
                                                        lean_dec_ref(v_arg_3326_);
                                                        lean_dec(v_a_3317_);
                                                        lean_dec(v_a_3315_);
                                                        v___x_3353_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                        return v___x_3353_;
                                                    } else {
                                                        v___x_3354_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_3317_, v_arg_3336_);
                                                        lean_dec_ref(v_arg_3336_);
                                                        if v___x_3354_ == 0 {
                                                            lean_dec_ref(v_arg_3330_);
                                                            lean_dec_ref(v_arg_3326_);
                                                            lean_dec(v_a_3317_);
                                                            lean_dec(v_a_3315_);
                                                            v___x_3355_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                            return v___x_3355_;
                                                        } else {
                                                            lean_dec_ref(v_e_3301_);
                                                            lean_inc_ref(v_arg_3330_);
                                                            v___x_3356_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_3330_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                            if lean_obj_tag(v___x_3356_) == 0 {
                                                                v_a_3357_ =
                                                                    lean_ctor_get(v___x_3356_, 0);
                                                                lean_inc(v_a_3357_);
                                                                lean_dec_ref_known(v___x_3356_, 1);
                                                                v_fst_3358_ =
                                                                    lean_ctor_get(v_a_3357_, 0);
                                                                v_snd_3359_ =
                                                                    lean_ctor_get(v_a_3357_, 1);
                                                                v_isSharedCheck_3393_ =
                                                                    (!lean_is_exclusive(v_a_3357_))
                                                                        as u8;
                                                                if v_isSharedCheck_3393_ == 0 {
                                                                    v___x_3361_ = v_a_3357_;
                                                                    v_isShared_3362_ =
                                                                        v_isSharedCheck_3393_;
                                                                    state = 2;
                                                                    continue;
                                                                } else {
                                                                    lean_inc(v_snd_3359_);
                                                                    lean_inc(v_fst_3358_);
                                                                    lean_dec(v_a_3357_);
                                                                    v___x_3361_ = lean_box(0);
                                                                    v_isShared_3362_ =
                                                                        v_isSharedCheck_3393_;
                                                                    state = 2;
                                                                    continue;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_3330_);
                                                                lean_dec_ref(v_arg_3326_);
                                                                lean_dec(v_a_3317_);
                                                                lean_dec(v_a_3315_);
                                                                return v___x_3356_;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_3348_);
                                                    v___x_3394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_3317_, v_arg_3336_);
                                                    lean_dec_ref(v_arg_3336_);
                                                    if v___x_3394_ == 0 {
                                                        lean_dec_ref(v_arg_3330_);
                                                        lean_dec_ref(v_arg_3326_);
                                                        lean_dec(v_a_3317_);
                                                        lean_dec(v_a_3315_);
                                                        v___x_3395_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                        return v___x_3395_;
                                                    } else {
                                                        lean_dec_ref(v_e_3301_);
                                                        lean_inc_ref(v_arg_3326_);
                                                        v___x_3396_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_3326_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                                        if lean_obj_tag(v___x_3396_) == 0 {
                                                            v_a_3397_ =
                                                                lean_ctor_get(v___x_3396_, 0);
                                                            v_isSharedCheck_3423_ =
                                                                (!lean_is_exclusive(v___x_3396_))
                                                                    as u8;
                                                            if v_isSharedCheck_3423_ == 0 {
                                                                v___x_3399_ = v___x_3396_;
                                                                v_isShared_3400_ =
                                                                    v_isSharedCheck_3423_;
                                                                state = 8;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_3397_);
                                                                lean_dec(v___x_3396_);
                                                                v___x_3399_ = lean_box(0);
                                                                v_isShared_3400_ =
                                                                    v_isSharedCheck_3423_;
                                                                state = 8;
                                                                continue;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_3330_);
                                                            lean_dec_ref(v_arg_3326_);
                                                            lean_dec(v_a_3317_);
                                                            lean_dec(v_a_3315_);
                                                            return v___x_3396_;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                } else {
                                    lean_dec_ref(v___x_3337_);
                                    lean_dec_ref(v_arg_3336_);
                                    lean_dec_ref(v_arg_3330_);
                                    lean_dec_ref(v_arg_3326_);
                                    v_type_3424_ = lean_ctor_get(v_a_3317_, 2);
                                    lean_inc_ref(v_type_3424_);
                                    v_u_3425_ = lean_ctor_get(v_a_3317_, 3);
                                    lean_inc(v_u_3425_);
                                    v_natModuleInst_3426_ = lean_ctor_get(v_a_3317_, 4);
                                    lean_inc_ref(v_natModuleInst_3426_);
                                    v_zero_3427_ = lean_ctor_get(v_a_3317_, 13);
                                    lean_inc_ref(v_zero_3427_);
                                    lean_dec(v_a_3317_);
                                    lean_inc_ref(v_e_3301_);
                                    v___x_3428_ = l_Lean_Meta_isDefEqD(
                                        v_e_3301_,
                                        v_zero_3427_,
                                        v_a_3309_,
                                        v_a_3310_,
                                        v_a_3311_,
                                        v_a_3312_,
                                    );
                                    if lean_obj_tag(v___x_3428_) == 0 {
                                        v_a_3429_ = lean_ctor_get(v___x_3428_, 0);
                                        v_isSharedCheck_3445_ =
                                            (!lean_is_exclusive(v___x_3428_)) as u8;
                                        if v_isSharedCheck_3445_ == 0 {
                                            v___x_3431_ = v___x_3428_;
                                            v_isShared_3432_ = v_isSharedCheck_3445_;
                                            state = 12;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3429_);
                                            lean_dec(v___x_3428_);
                                            v___x_3431_ = lean_box(0);
                                            v_isShared_3432_ = v_isSharedCheck_3445_;
                                            state = 12;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_natModuleInst_3426_);
                                        lean_dec(v_u_3425_);
                                        lean_dec_ref(v_type_3424_);
                                        lean_dec(v_a_3315_);
                                        lean_dec_ref(v_e_3301_);
                                        v_a_3446_ = lean_ctor_get(v___x_3428_, 0);
                                        v_isSharedCheck_3453_ =
                                            (!lean_is_exclusive(v___x_3428_)) as u8;
                                        if v_isSharedCheck_3453_ == 0 {
                                            v___x_3448_ = v___x_3428_;
                                            v_isShared_3449_ = v_isSharedCheck_3453_;
                                            state = 14;
                                            continue;
                                        } else {
                                            lean_inc(v_a_3446_);
                                            lean_dec(v___x_3428_);
                                            v___x_3448_ = lean_box(0);
                                            v_isShared_3449_ = v_isSharedCheck_3453_;
                                            state = 14;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_3331_);
                            lean_dec_ref(v_arg_3330_);
                            v___x_3454_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_3317_, v_arg_3326_);
                            lean_dec_ref(v_arg_3326_);
                            if v___x_3454_ == 0 {
                                lean_del_object(v___x_3321_);
                                lean_dec(v_a_3317_);
                                lean_dec(v_a_3315_);
                                v___x_3455_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                                return v___x_3455_;
                            } else {
                                lean_dec_ref(v_e_3301_);
                                v_zero_3456_ = lean_ctor_get(v_a_3315_, 17);
                                lean_inc_ref(v_zero_3456_);
                                lean_dec(v_a_3315_);
                                v_type_3457_ = lean_ctor_get(v_a_3317_, 2);
                                lean_inc_ref(v_type_3457_);
                                v_u_3458_ = lean_ctor_get(v_a_3317_, 3);
                                lean_inc(v_u_3458_);
                                v_natModuleInst_3459_ = lean_ctor_get(v_a_3317_, 4);
                                lean_inc_ref(v_natModuleInst_3459_);
                                lean_dec(v_a_3317_);
                                v___x_3460_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21;
                                v___x_3461_ = lean_box(0);
                                v___x_3462_ = lean_alloc_ctor(1, 2, (0) as u32);
                                lean_ctor_set(v___x_3462_, 0, v_u_3458_);
                                lean_ctor_set(v___x_3462_, 1, v___x_3461_);
                                v___x_3463_ = l_Lean_mkConst(v___x_3460_, v___x_3462_);
                                v___x_3464_ =
                                    l_Lean_mkAppB(v___x_3463_, v_type_3457_, v_natModuleInst_3459_);
                                v___x_3465_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v___x_3465_, 0, v_zero_3456_);
                                lean_ctor_set(v___x_3465_, 1, v___x_3464_);
                                if v_isShared_3322_ == 0 {
                                    lean_ctor_set(v___x_3321_, 0, v___x_3465_);
                                    v___x_3467_ = v___x_3321_;
                                    state = 16;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_3468_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_3468_, 0, v___x_3465_);
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
                lean_inc_ref(v_arg_3326_);
                v___x_3363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_arg_3326_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                if lean_obj_tag(v___x_3363_) == 0 {
                    v_a_3364_ = lean_ctor_get(v___x_3363_, 0);
                    v_isSharedCheck_3392_ = (!lean_is_exclusive(v___x_3363_)) as u8;
                    if v_isSharedCheck_3392_ == 0 {
                        v___x_3366_ = v___x_3363_;
                        v_isShared_3367_ = v_isSharedCheck_3392_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3364_);
                        lean_dec(v___x_3363_);
                        v___x_3366_ = lean_box(0);
                        v_isShared_3367_ = v_isSharedCheck_3392_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3361_);
                    lean_dec(v_snd_3359_);
                    lean_dec(v_fst_3358_);
                    lean_dec_ref(v_arg_3330_);
                    lean_dec_ref(v_arg_3326_);
                    lean_dec(v_a_3317_);
                    lean_dec(v_a_3315_);
                    return v___x_3363_;
                }
            }
            3 => {
                v_fst_3368_ = lean_ctor_get(v_a_3364_, 0);
                v_snd_3369_ = lean_ctor_get(v_a_3364_, 1);
                v_isSharedCheck_3391_ = (!lean_is_exclusive(v_a_3364_)) as u8;
                if v_isSharedCheck_3391_ == 0 {
                    v___x_3371_ = v_a_3364_;
                    v_isShared_3372_ = v_isSharedCheck_3391_;
                    state = 4;
                    continue;
                } else {
                    lean_inc(v_snd_3369_);
                    lean_inc(v_fst_3368_);
                    lean_dec(v_a_3364_);
                    v___x_3371_ = lean_box(0);
                    v_isShared_3372_ = v_isSharedCheck_3391_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v_addFn_3373_ = lean_ctor_get(v_a_3315_, 22);
                lean_inc_ref(v_addFn_3373_);
                lean_dec(v_a_3315_);
                v_type_3374_ = lean_ctor_get(v_a_3317_, 2);
                lean_inc_ref(v_type_3374_);
                v_u_3375_ = lean_ctor_get(v_a_3317_, 3);
                lean_inc(v_u_3375_);
                v_natModuleInst_3376_ = lean_ctor_get(v_a_3317_, 4);
                lean_inc_ref(v_natModuleInst_3376_);
                lean_dec(v_a_3317_);
                lean_inc(v_fst_3368_);
                lean_inc(v_fst_3358_);
                v___x_3377_ = l_Lean_mkAppB(v_addFn_3373_, v_fst_3358_, v_fst_3368_);
                v___x_3378_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__17;
                v___x_3379_ = lean_box(0);
                if v_isShared_3362_ == 0 {
                    lean_ctor_set_tag(v___x_3361_, 1);
                    lean_ctor_set(v___x_3361_, 1, v___x_3379_);
                    lean_ctor_set(v___x_3361_, 0, v_u_3375_);
                    v___x_3381_ = v___x_3361_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3390_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 0, v_u_3375_);
                    lean_ctor_set(v_reuseFailAlloc_3390_, 1, v___x_3379_);
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
                    lean_ctor_set(v___x_3371_, 1, v___x_3383_);
                    lean_ctor_set(v___x_3371_, 0, v___x_3377_);
                    v___x_3385_ = v___x_3371_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3389_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3389_, 0, v___x_3377_);
                    lean_ctor_set(v_reuseFailAlloc_3389_, 1, v___x_3383_);
                    v___x_3385_ = v_reuseFailAlloc_3389_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_3367_ == 0 {
                    lean_ctor_set(v___x_3366_, 0, v___x_3385_);
                    v___x_3387_ = v___x_3366_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3388_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3388_, 0, v___x_3385_);
                    v___x_3387_ = v_reuseFailAlloc_3388_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3387_;
            }
            8 => {
                v_fst_3401_ = lean_ctor_get(v_a_3397_, 0);
                v_snd_3402_ = lean_ctor_get(v_a_3397_, 1);
                v_isSharedCheck_3422_ = (!lean_is_exclusive(v_a_3397_)) as u8;
                if v_isSharedCheck_3422_ == 0 {
                    v___x_3404_ = v_a_3397_;
                    v_isShared_3405_ = v_isSharedCheck_3422_;
                    state = 9;
                    continue;
                } else {
                    lean_inc(v_snd_3402_);
                    lean_inc(v_fst_3401_);
                    lean_dec(v_a_3397_);
                    v___x_3404_ = lean_box(0);
                    v_isShared_3405_ = v_isSharedCheck_3422_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v_nsmulFn_3406_ = lean_ctor_get(v_a_3315_, 24);
                lean_inc_ref(v_nsmulFn_3406_);
                lean_dec(v_a_3315_);
                v_type_3407_ = lean_ctor_get(v_a_3317_, 2);
                lean_inc_ref(v_type_3407_);
                v_u_3408_ = lean_ctor_get(v_a_3317_, 3);
                lean_inc(v_u_3408_);
                v_natModuleInst_3409_ = lean_ctor_get(v_a_3317_, 4);
                lean_inc_ref(v_natModuleInst_3409_);
                lean_dec(v_a_3317_);
                lean_inc(v_fst_3401_);
                lean_inc_ref(v_arg_3330_);
                v___x_3410_ = l_Lean_mkAppB(v_nsmulFn_3406_, v_arg_3330_, v_fst_3401_);
                v___x_3411_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__19;
                v___x_3412_ = lean_box(0);
                v___x_3413_ = lean_alloc_ctor(1, 2, (0) as u32);
                lean_ctor_set(v___x_3413_, 0, v_u_3408_);
                lean_ctor_set(v___x_3413_, 1, v___x_3412_);
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
                    lean_ctor_set(v___x_3404_, 1, v___x_3415_);
                    lean_ctor_set(v___x_3404_, 0, v___x_3410_);
                    v___x_3417_ = v___x_3404_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3421_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3421_, 0, v___x_3410_);
                    lean_ctor_set(v_reuseFailAlloc_3421_, 1, v___x_3415_);
                    v___x_3417_ = v_reuseFailAlloc_3421_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_3400_ == 0 {
                    lean_ctor_set(v___x_3399_, 0, v___x_3417_);
                    v___x_3419_ = v___x_3399_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_3420_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3420_, 0, v___x_3417_);
                    v___x_3419_ = v_reuseFailAlloc_3420_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_3419_;
            }
            12 => {
                v___x_3433_ = (lean_unbox(v_a_3429_) as u8);
                lean_dec(v_a_3429_);
                if v___x_3433_ == 0 {
                    lean_del_object(v___x_3431_);
                    lean_dec_ref(v_natModuleInst_3426_);
                    lean_dec(v_u_3425_);
                    lean_dec_ref(v_type_3424_);
                    lean_dec(v_a_3315_);
                    v___x_3434_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_mkOfNatModuleVar(v_e_3301_, v_a_3302_, v_a_3303_, v_a_3304_, v_a_3305_, v_a_3306_, v_a_3307_, v_a_3308_, v_a_3309_, v_a_3310_, v_a_3311_, v_a_3312_);
                    return v___x_3434_;
                } else {
                    lean_dec_ref(v_e_3301_);
                    v_zero_3435_ = lean_ctor_get(v_a_3315_, 17);
                    lean_inc_ref(v_zero_3435_);
                    lean_dec(v_a_3315_);
                    v___x_3436_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__21;
                    v___x_3437_ = lean_box(0);
                    v___x_3438_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_3438_, 0, v_u_3425_);
                    lean_ctor_set(v___x_3438_, 1, v___x_3437_);
                    v___x_3439_ = l_Lean_mkConst(v___x_3436_, v___x_3438_);
                    v___x_3440_ = l_Lean_mkAppB(v___x_3439_, v_type_3424_, v_natModuleInst_3426_);
                    v___x_3441_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3441_, 0, v_zero_3435_);
                    lean_ctor_set(v___x_3441_, 1, v___x_3440_);
                    if v_isShared_3432_ == 0 {
                        lean_ctor_set(v___x_3431_, 0, v___x_3441_);
                        v___x_3443_ = v___x_3431_;
                        state = 13;
                        continue;
                    } else {
                        v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
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
                    v_reuseFailAlloc_3452_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3452_, 0, v_a_3446_);
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
                    v_reuseFailAlloc_3476_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3476_, 0, v_a_3470_);
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
                    v_reuseFailAlloc_3484_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3484_, 0, v_a_3478_);
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
                    v_reuseFailAlloc_3492_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3492_, 0, v_a_3486_);
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
    mut v_e_3494_: *mut LeanObject,
    mut v_a_3495_: *mut LeanObject,
    mut v_a_3496_: *mut LeanObject,
    mut v_a_3497_: *mut LeanObject,
    mut v_a_3498_: *mut LeanObject,
    mut v_a_3499_: *mut LeanObject,
    mut v_a_3500_: *mut LeanObject,
    mut v_a_3501_: *mut LeanObject,
    mut v_a_3502_: *mut LeanObject,
    mut v_a_3503_: *mut LeanObject,
    mut v_a_3504_: *mut LeanObject,
    mut v_a_3505_: *mut LeanObject,
    mut v_a_3506_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3507_: *mut LeanObject = core::ptr::null_mut();
    v_res_3507_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_3494_, v_a_3495_, v_a_3496_, v_a_3497_, v_a_3498_, v_a_3499_, v_a_3500_, v_a_3501_, v_a_3502_, v_a_3503_, v_a_3504_, v_a_3505_);
    lean_dec(v_a_3505_);
    lean_dec_ref(v_a_3504_);
    lean_dec(v_a_3503_);
    lean_dec_ref(v_a_3502_);
    lean_dec(v_a_3501_);
    lean_dec_ref(v_a_3500_);
    lean_dec(v_a_3499_);
    lean_dec_ref(v_a_3498_);
    lean_dec(v_a_3497_);
    lean_dec(v_a_3496_);
    lean_dec(v_a_3495_);
    return v_res_3507_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(
    mut v___y_3508_: *mut LeanObject,
    mut v_e_3509_: *mut LeanObject,
    mut v_____x_3510_: *mut LeanObject,
    mut v_s_3511_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_structs_3512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_typeIdOf_3513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructId_3514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_3515_: *mut LeanObject = core::ptr::null_mut();
    let mut v_forbiddenNatModules_3516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natStructs_3517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natTypeIdOf_3518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_exprToNatStructId_3519_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: u8 = 0;
    let mut v___x_3523_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3524_: u8 = 0;
    let mut v_v_3525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_id_3526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structId_3527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_3528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_3529_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_3530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_leInst_x3f_3531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_ltInst_x3f_3532_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lawfulOrderLTInst_x3f_3533_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isPreorderInst_x3f_3534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_orderedAddInst_x3f_3535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isLinearInst_x3f_3536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addRightCancelInst_x3f_3537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rfl__q_3538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_3539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toQFn_3540_: *mut LeanObject = core::ptr::null_mut();
    let mut v_addFn_3541_: *mut LeanObject = core::ptr::null_mut();
    let mut v_smulFn_3542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_termMap_3543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3546_: u8 = 0;
    let mut v___x_3547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_xs_x27_3548_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3549_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3551_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3557_: u8 = 0;
    let mut v_isSharedCheck_3558_: u8 = 0;
    let mut v_unused_3559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3561_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3564_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_unused_3566_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_structs_3512_ = lean_ctor_get(v_s_3511_, 0);
                v_typeIdOf_3513_ = lean_ctor_get(v_s_3511_, 1);
                v_exprToStructId_3514_ = lean_ctor_get(v_s_3511_, 2);
                v_exprToStructIdEntries_3515_ = lean_ctor_get(v_s_3511_, 3);
                v_forbiddenNatModules_3516_ = lean_ctor_get(v_s_3511_, 4);
                v_natStructs_3517_ = lean_ctor_get(v_s_3511_, 5);
                v_natTypeIdOf_3518_ = lean_ctor_get(v_s_3511_, 6);
                v_exprToNatStructId_3519_ = lean_ctor_get(v_s_3511_, 7);
                v___x_3520_ = lean_array_get_size(v_natStructs_3517_);
                v___x_3521_ = lean_nat_dec_lt(v___y_3508_, v___x_3520_);
                if v___x_3521_ == 0 {
                    lean_dec_ref(v_____x_3510_);
                    lean_dec_ref(v_e_3509_);
                    return v_s_3511_;
                } else {
                    lean_inc_ref(v_exprToNatStructId_3519_);
                    lean_inc_ref(v_natTypeIdOf_3518_);
                    lean_inc_ref(v_natStructs_3517_);
                    lean_inc_ref(v_forbiddenNatModules_3516_);
                    lean_inc_ref(v_exprToStructIdEntries_3515_);
                    lean_inc_ref(v_exprToStructId_3514_);
                    lean_inc_ref(v_typeIdOf_3513_);
                    lean_inc_ref(v_structs_3512_);
                    v_isSharedCheck_3558_ = (!lean_is_exclusive(v_s_3511_)) as u8;
                    if v_isSharedCheck_3558_ == 0 {
                        v_unused_3559_ = lean_ctor_get(v_s_3511_, 7);
                        lean_dec(v_unused_3559_);
                        v_unused_3560_ = lean_ctor_get(v_s_3511_, 6);
                        lean_dec(v_unused_3560_);
                        v_unused_3561_ = lean_ctor_get(v_s_3511_, 5);
                        lean_dec(v_unused_3561_);
                        v_unused_3562_ = lean_ctor_get(v_s_3511_, 4);
                        lean_dec(v_unused_3562_);
                        v_unused_3563_ = lean_ctor_get(v_s_3511_, 3);
                        lean_dec(v_unused_3563_);
                        v_unused_3564_ = lean_ctor_get(v_s_3511_, 2);
                        lean_dec(v_unused_3564_);
                        v_unused_3565_ = lean_ctor_get(v_s_3511_, 1);
                        lean_dec(v_unused_3565_);
                        v_unused_3566_ = lean_ctor_get(v_s_3511_, 0);
                        lean_dec(v_unused_3566_);
                        v___x_3523_ = v_s_3511_;
                        v_isShared_3524_ = v_isSharedCheck_3558_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v_s_3511_);
                        v___x_3523_ = lean_box(0);
                        v_isShared_3524_ = v_isSharedCheck_3558_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_v_3525_ = lean_array_fget(v_natStructs_3517_, v___y_3508_);
                v_id_3526_ = lean_ctor_get(v_v_3525_, 0);
                v_structId_3527_ = lean_ctor_get(v_v_3525_, 1);
                v_type_3528_ = lean_ctor_get(v_v_3525_, 2);
                v_u_3529_ = lean_ctor_get(v_v_3525_, 3);
                v_natModuleInst_3530_ = lean_ctor_get(v_v_3525_, 4);
                v_leInst_x3f_3531_ = lean_ctor_get(v_v_3525_, 5);
                v_ltInst_x3f_3532_ = lean_ctor_get(v_v_3525_, 6);
                v_lawfulOrderLTInst_x3f_3533_ = lean_ctor_get(v_v_3525_, 7);
                v_isPreorderInst_x3f_3534_ = lean_ctor_get(v_v_3525_, 8);
                v_orderedAddInst_x3f_3535_ = lean_ctor_get(v_v_3525_, 9);
                v_isLinearInst_x3f_3536_ = lean_ctor_get(v_v_3525_, 10);
                v_addRightCancelInst_x3f_3537_ = lean_ctor_get(v_v_3525_, 11);
                v_rfl__q_3538_ = lean_ctor_get(v_v_3525_, 12);
                v_zero_3539_ = lean_ctor_get(v_v_3525_, 13);
                v_toQFn_3540_ = lean_ctor_get(v_v_3525_, 14);
                v_addFn_3541_ = lean_ctor_get(v_v_3525_, 15);
                v_smulFn_3542_ = lean_ctor_get(v_v_3525_, 16);
                v_termMap_3543_ = lean_ctor_get(v_v_3525_, 17);
                v_isSharedCheck_3557_ = (!lean_is_exclusive(v_v_3525_)) as u8;
                if v_isSharedCheck_3557_ == 0 {
                    v___x_3545_ = v_v_3525_;
                    v_isShared_3546_ = v_isSharedCheck_3557_;
                    state = 2;
                    continue;
                } else {
                    lean_inc(v_termMap_3543_);
                    lean_inc(v_smulFn_3542_);
                    lean_inc(v_addFn_3541_);
                    lean_inc(v_toQFn_3540_);
                    lean_inc(v_zero_3539_);
                    lean_inc(v_rfl__q_3538_);
                    lean_inc(v_addRightCancelInst_x3f_3537_);
                    lean_inc(v_isLinearInst_x3f_3536_);
                    lean_inc(v_orderedAddInst_x3f_3535_);
                    lean_inc(v_isPreorderInst_x3f_3534_);
                    lean_inc(v_lawfulOrderLTInst_x3f_3533_);
                    lean_inc(v_ltInst_x3f_3532_);
                    lean_inc(v_leInst_x3f_3531_);
                    lean_inc(v_natModuleInst_3530_);
                    lean_inc(v_u_3529_);
                    lean_inc(v_type_3528_);
                    lean_inc(v_structId_3527_);
                    lean_inc(v_id_3526_);
                    lean_dec(v_v_3525_);
                    v___x_3545_ = lean_box(0);
                    v_isShared_3546_ = v_isSharedCheck_3557_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3547_ = lean_box(0);
                v_xs_x27_3548_ = lean_array_fset(v_natStructs_3517_, v___y_3508_, v___x_3547_);
                v___x_3549_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_Grind_Arith_Linear_setTermNatStructId_spec__0___redArg(v_termMap_3543_, v_e_3509_, v_____x_3510_);
                if v_isShared_3546_ == 0 {
                    lean_ctor_set(v___x_3545_, 17, v___x_3549_);
                    v___x_3551_ = v___x_3545_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3556_ = lean_alloc_ctor(0, 18, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 0, v_id_3526_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 1, v_structId_3527_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 2, v_type_3528_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 3, v_u_3529_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 4, v_natModuleInst_3530_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 5, v_leInst_x3f_3531_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 6, v_ltInst_x3f_3532_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 7, v_lawfulOrderLTInst_x3f_3533_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 8, v_isPreorderInst_x3f_3534_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 9, v_orderedAddInst_x3f_3535_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 10, v_isLinearInst_x3f_3536_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 11, v_addRightCancelInst_x3f_3537_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 12, v_rfl__q_3538_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 13, v_zero_3539_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 14, v_toQFn_3540_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 15, v_addFn_3541_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 16, v_smulFn_3542_);
                    lean_ctor_set(v_reuseFailAlloc_3556_, 17, v___x_3549_);
                    v___x_3551_ = v_reuseFailAlloc_3556_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3552_ = lean_array_fset(v_xs_x27_3548_, v___y_3508_, v___x_3551_);
                if v_isShared_3524_ == 0 {
                    lean_ctor_set(v___x_3523_, 5, v___x_3552_);
                    v___x_3554_ = v___x_3523_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3555_ = lean_alloc_ctor(0, 8, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 0, v_structs_3512_);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 1, v_typeIdOf_3513_);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 2, v_exprToStructId_3514_);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 3, v_exprToStructIdEntries_3515_);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 4, v_forbiddenNatModules_3516_);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 5, v___x_3552_);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 6, v_natTypeIdOf_3518_);
                    lean_ctor_set(v_reuseFailAlloc_3555_, 7, v_exprToNatStructId_3519_);
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
    mut v___y_3567_: *mut LeanObject,
    mut v_e_3568_: *mut LeanObject,
    mut v_____x_3569_: *mut LeanObject,
    mut v_s_3570_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3571_: *mut LeanObject = core::ptr::null_mut();
    v_res_3571_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0(
        v___y_3567_,
        v_e_3568_,
        v_____x_3569_,
        v_s_3570_,
    );
    lean_dec(v___y_3567_);
    return v_res_3571_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_ofNatModule(
    mut v_e_3572_: *mut LeanObject,
    mut v_a_3573_: *mut LeanObject,
    mut v_a_3574_: *mut LeanObject,
    mut v_a_3575_: *mut LeanObject,
    mut v_a_3576_: *mut LeanObject,
    mut v_a_3577_: *mut LeanObject,
    mut v_a_3578_: *mut LeanObject,
    mut v_a_3579_: *mut LeanObject,
    mut v_a_3580_: *mut LeanObject,
    mut v_a_3581_: *mut LeanObject,
    mut v_a_3582_: *mut LeanObject,
    mut v_a_3583_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____x_3586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3590_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3593_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3594_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3596_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3598_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3601_: u8 = 0;
    let mut v___x_3603_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3604_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3605_: u8 = 0;
    let mut v_unused_3606_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3607_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3609_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3610_: u8 = 0;
    let mut v___x_3612_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3613_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3614_: u8 = 0;
    let mut v_a_3615_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3617_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3618_: u8 = 0;
    let mut v___x_3620_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3621_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3622_: u8 = 0;
    let mut v___x_3623_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3624_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3627_: u8 = 0;
    let mut v_termMap_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3629_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3635_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_3636_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3637_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3639_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3640_: u8 = 0;
    let mut v___x_3641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_proof_x3f_3643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_expr_3644_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3651_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3654_: u8 = 0;
    let mut v___x_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3658_: u8 = 0;
    let mut v_expr_3659_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3662_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3666_: u8 = 0;
    let mut v___x_3668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3670_: u8 = 0;
    let mut v_isSharedCheck_3671_: u8 = 0;
    let mut v_isSharedCheck_3672_: u8 = 0;
    let mut v_a_3673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3675_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3676_: u8 = 0;
    let mut v___x_3678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3680_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3623_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_,
                    v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_,
                );
                if lean_obj_tag(v___x_3623_) == 0 {
                    v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
                    v_isSharedCheck_3672_ = (!lean_is_exclusive(v___x_3623_)) as u8;
                    if v_isSharedCheck_3672_ == 0 {
                        v___x_3626_ = v___x_3623_;
                        v_isShared_3627_ = v_isSharedCheck_3672_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3624_);
                        lean_dec(v___x_3623_);
                        v___x_3626_ = lean_box(0);
                        v_isShared_3627_ = v_isSharedCheck_3672_;
                        state = 8;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_e_3572_);
                    v_a_3673_ = lean_ctor_get(v___x_3623_, 0);
                    v_isSharedCheck_3680_ = (!lean_is_exclusive(v___x_3623_)) as u8;
                    if v_isSharedCheck_3680_ == 0 {
                        v___x_3675_ = v___x_3623_;
                        v_isShared_3676_ = v_isSharedCheck_3680_;
                        state = 17;
                        continue;
                    } else {
                        lean_inc(v_a_3673_);
                        lean_dec(v___x_3623_);
                        v___x_3675_ = lean_box(0);
                        v_isShared_3676_ = v_isSharedCheck_3680_;
                        state = 17;
                        continue;
                    }
                }
            }
            1 => {
                lean_inc_ref(v_e_3572_);
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
                if lean_obj_tag(v___x_3595_) == 0 {
                    lean_dec_ref_known(v___x_3595_, 1);
                    lean_inc_ref(v_____x_3586_);
                    lean_inc(v___y_3587_);
                    v___f_3596_ = lean_alloc_closure(
                        l_Lean_Meta_Grind_Arith_Linear_ofNatModule___lam__0___boxed
                            as *mut core::ffi::c_void,
                        4,
                        3,
                    );
                    lean_closure_set(v___f_3596_, 0, v___y_3587_);
                    lean_closure_set(v___f_3596_, 1, v_e_3572_);
                    lean_closure_set(v___f_3596_, 2, v_____x_3586_);
                    v___x_3597_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                    v___x_3598_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_modifyStateImpl___redArg(v___x_3597_, v___f_3596_, v___y_3588_);
                    if lean_obj_tag(v___x_3598_) == 0 {
                        v_isSharedCheck_3605_ = (!lean_is_exclusive(v___x_3598_)) as u8;
                        if v_isSharedCheck_3605_ == 0 {
                            v_unused_3606_ = lean_ctor_get(v___x_3598_, 0);
                            lean_dec(v_unused_3606_);
                            v___x_3600_ = v___x_3598_;
                            v_isShared_3601_ = v_isSharedCheck_3605_;
                            state = 2;
                            continue;
                        } else {
                            lean_dec(v___x_3598_);
                            v___x_3600_ = lean_box(0);
                            v_isShared_3601_ = v_isSharedCheck_3605_;
                            state = 2;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_____x_3586_);
                        v_a_3607_ = lean_ctor_get(v___x_3598_, 0);
                        v_isSharedCheck_3614_ = (!lean_is_exclusive(v___x_3598_)) as u8;
                        if v_isSharedCheck_3614_ == 0 {
                            v___x_3609_ = v___x_3598_;
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_3607_);
                            lean_dec(v___x_3598_);
                            v___x_3609_ = lean_box(0);
                            v_isShared_3610_ = v_isSharedCheck_3614_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_____x_3586_);
                    lean_dec_ref(v_e_3572_);
                    v_a_3615_ = lean_ctor_get(v___x_3595_, 0);
                    v_isSharedCheck_3622_ = (!lean_is_exclusive(v___x_3595_)) as u8;
                    if v_isSharedCheck_3622_ == 0 {
                        v___x_3617_ = v___x_3595_;
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_3615_);
                        lean_dec(v___x_3595_);
                        v___x_3617_ = lean_box(0);
                        v_isShared_3618_ = v_isSharedCheck_3622_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3601_ == 0 {
                    lean_ctor_set(v___x_3600_, 0, v_____x_3586_);
                    v___x_3603_ = v___x_3600_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3604_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3604_, 0, v_____x_3586_);
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
                    v_reuseFailAlloc_3613_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3613_, 0, v_a_3607_);
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
                    v_reuseFailAlloc_3621_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_a_3615_);
                    v___x_3620_ = v_reuseFailAlloc_3621_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3620_;
            }
            8 => {
                v_termMap_3628_ = lean_ctor_get(v_a_3624_, 17);
                lean_inc_ref(v_termMap_3628_);
                lean_dec(v_a_3624_);
                v___x_3629_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getTermNatStructId_x3f_spec__0___redArg(v_termMap_3628_, v_e_3572_);
                lean_dec_ref(v_termMap_3628_);
                if lean_obj_tag(v___x_3629_) == 1 {
                    lean_dec_ref(v_e_3572_);
                    v_val_3630_ = lean_ctor_get(v___x_3629_, 0);
                    lean_inc(v_val_3630_);
                    lean_dec_ref_known(v___x_3629_, 1);
                    if v_isShared_3627_ == 0 {
                        lean_ctor_set(v___x_3626_, 0, v_val_3630_);
                        v___x_3632_ = v___x_3626_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_3633_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3633_, 0, v_val_3630_);
                        v___x_3632_ = v_reuseFailAlloc_3633_;
                        state = 9;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3629_);
                    lean_del_object(v___x_3626_);
                    lean_inc_ref(v_e_3572_);
                    v___x_3634_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27(v_e_3572_, v_a_3573_, v_a_3574_, v_a_3575_, v_a_3576_, v_a_3577_, v_a_3578_, v_a_3579_, v_a_3580_, v_a_3581_, v_a_3582_, v_a_3583_);
                    if lean_obj_tag(v___x_3634_) == 0 {
                        v_a_3635_ = lean_ctor_get(v___x_3634_, 0);
                        lean_inc(v_a_3635_);
                        lean_dec_ref_known(v___x_3634_, 1);
                        v_fst_3636_ = lean_ctor_get(v_a_3635_, 0);
                        v_snd_3637_ = lean_ctor_get(v_a_3635_, 1);
                        v_isSharedCheck_3671_ = (!lean_is_exclusive(v_a_3635_)) as u8;
                        if v_isSharedCheck_3671_ == 0 {
                            v___x_3639_ = v_a_3635_;
                            v_isShared_3640_ = v_isSharedCheck_3671_;
                            state = 10;
                            continue;
                        } else {
                            lean_inc(v_snd_3637_);
                            lean_inc(v_fst_3636_);
                            lean_dec(v_a_3635_);
                            v___x_3639_ = lean_box(0);
                            v_isShared_3640_ = v_isSharedCheck_3671_;
                            state = 10;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_e_3572_);
                        return v___x_3634_;
                    }
                }
            }
            9 => {
                return v___x_3632_;
            }
            10 => {
                lean_inc(v_a_3583_);
                lean_inc_ref(v_a_3582_);
                lean_inc(v_a_3581_);
                lean_inc_ref(v_a_3580_);
                lean_inc(v_a_3579_);
                lean_inc_ref(v_a_3578_);
                lean_inc(v_a_3577_);
                lean_inc_ref(v_a_3576_);
                lean_inc(v_a_3575_);
                lean_inc(v_a_3574_);
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
                if lean_obj_tag(v___x_3641_) == 0 {
                    v_a_3642_ = lean_ctor_get(v___x_3641_, 0);
                    lean_inc(v_a_3642_);
                    lean_dec_ref_known(v___x_3641_, 1);
                    v_proof_x3f_3643_ = lean_ctor_get(v_a_3642_, 1);
                    if lean_obj_tag(v_proof_x3f_3643_) == 1 {
                        lean_inc_ref(v_proof_x3f_3643_);
                        v_expr_3644_ = lean_ctor_get(v_a_3642_, 0);
                        lean_inc_ref(v_expr_3644_);
                        lean_dec(v_a_3642_);
                        v_val_3645_ = lean_ctor_get(v_proof_x3f_3643_, 0);
                        lean_inc(v_val_3645_);
                        lean_dec_ref_known(v_proof_x3f_3643_, 1);
                        v___x_3646_ = l_Lean_Meta_mkEqTrans(
                            v_snd_3637_,
                            v_val_3645_,
                            v_a_3580_,
                            v_a_3581_,
                            v_a_3582_,
                            v_a_3583_,
                        );
                        if lean_obj_tag(v___x_3646_) == 0 {
                            v_a_3647_ = lean_ctor_get(v___x_3646_, 0);
                            lean_inc(v_a_3647_);
                            lean_dec_ref_known(v___x_3646_, 1);
                            if v_isShared_3640_ == 0 {
                                lean_ctor_set(v___x_3639_, 1, v_a_3647_);
                                lean_ctor_set(v___x_3639_, 0, v_expr_3644_);
                                v___x_3649_ = v___x_3639_;
                                state = 11;
                                continue;
                            } else {
                                v_reuseFailAlloc_3650_ = lean_alloc_ctor(0, 2, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_3650_, 0, v_expr_3644_);
                                lean_ctor_set(v_reuseFailAlloc_3650_, 1, v_a_3647_);
                                v___x_3649_ = v_reuseFailAlloc_3650_;
                                state = 11;
                                continue;
                            }
                        } else {
                            lean_dec_ref(v_expr_3644_);
                            lean_del_object(v___x_3639_);
                            lean_dec_ref(v_e_3572_);
                            v_a_3651_ = lean_ctor_get(v___x_3646_, 0);
                            v_isSharedCheck_3658_ = (!lean_is_exclusive(v___x_3646_)) as u8;
                            if v_isSharedCheck_3658_ == 0 {
                                v___x_3653_ = v___x_3646_;
                                v_isShared_3654_ = v_isSharedCheck_3658_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_3651_);
                                lean_dec(v___x_3646_);
                                v___x_3653_ = lean_box(0);
                                v_isShared_3654_ = v_isSharedCheck_3658_;
                                state = 12;
                                continue;
                            }
                        }
                    } else {
                        v_expr_3659_ = lean_ctor_get(v_a_3642_, 0);
                        lean_inc_ref(v_expr_3659_);
                        lean_dec(v_a_3642_);
                        if v_isShared_3640_ == 0 {
                            lean_ctor_set(v___x_3639_, 0, v_expr_3659_);
                            v___x_3661_ = v___x_3639_;
                            state = 14;
                            continue;
                        } else {
                            v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3662_, 0, v_expr_3659_);
                            lean_ctor_set(v_reuseFailAlloc_3662_, 1, v_snd_3637_);
                            v___x_3661_ = v_reuseFailAlloc_3662_;
                            state = 14;
                            continue;
                        }
                    }
                } else {
                    lean_del_object(v___x_3639_);
                    lean_dec(v_snd_3637_);
                    lean_dec_ref(v_e_3572_);
                    v_a_3663_ = lean_ctor_get(v___x_3641_, 0);
                    v_isSharedCheck_3670_ = (!lean_is_exclusive(v___x_3641_)) as u8;
                    if v_isSharedCheck_3670_ == 0 {
                        v___x_3665_ = v___x_3641_;
                        v_isShared_3666_ = v_isSharedCheck_3670_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_3663_);
                        lean_dec(v___x_3641_);
                        v___x_3665_ = lean_box(0);
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
                    v_reuseFailAlloc_3657_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3657_, 0, v_a_3651_);
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
                    v_reuseFailAlloc_3669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3669_, 0, v_a_3663_);
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
                    v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3679_, 0, v_a_3673_);
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
    mut v_e_3681_: *mut LeanObject,
    mut v_a_3682_: *mut LeanObject,
    mut v_a_3683_: *mut LeanObject,
    mut v_a_3684_: *mut LeanObject,
    mut v_a_3685_: *mut LeanObject,
    mut v_a_3686_: *mut LeanObject,
    mut v_a_3687_: *mut LeanObject,
    mut v_a_3688_: *mut LeanObject,
    mut v_a_3689_: *mut LeanObject,
    mut v_a_3690_: *mut LeanObject,
    mut v_a_3691_: *mut LeanObject,
    mut v_a_3692_: *mut LeanObject,
    mut v_a_3693_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3694_: *mut LeanObject = core::ptr::null_mut();
    v_res_3694_ = l_Lean_Meta_Grind_Arith_Linear_ofNatModule(
        v_e_3681_, v_a_3682_, v_a_3683_, v_a_3684_, v_a_3685_, v_a_3686_, v_a_3687_, v_a_3688_,
        v_a_3689_, v_a_3690_, v_a_3691_, v_a_3692_,
    );
    lean_dec(v_a_3692_);
    lean_dec_ref(v_a_3691_);
    lean_dec(v_a_3690_);
    lean_dec_ref(v_a_3689_);
    lean_dec(v_a_3688_);
    lean_dec_ref(v_a_3687_);
    lean_dec(v_a_3686_);
    lean_dec_ref(v_a_3685_);
    lean_dec(v_a_3684_);
    lean_dec(v_a_3683_);
    lean_dec(v_a_3682_);
    return v_res_3694_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0()
-> *mut LeanObject {
    let mut v___x_3695_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3696_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3697_: *mut LeanObject = core::ptr::null_mut();
    v___x_3695_ = lean_box(0);
    v___x_3696_ = lean_unsigned_to_nat(16);
    v___x_3697_ = lean_mk_array(v___x_3696_, v___x_3695_);
    return v___x_3697_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1()
-> *mut LeanObject {
    let mut v___x_3698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3700_: *mut LeanObject = core::ptr::null_mut();
    v___x_3698_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__0);
    v___x_3699_ = lean_unsigned_to_nat(0);
    v___x_3700_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3700_, 0, v___x_3699_);
    lean_ctor_set(v___x_3700_, 1, v___x_3698_);
    return v___x_3700_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3()
-> *mut LeanObject {
    let mut v___x_3703_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3704_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3705_: *mut LeanObject = core::ptr::null_mut();
    v___x_3703_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__2;
    v___x_3704_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__1);
    v___x_3705_ = lean_alloc_ctor(0, 2, (0) as u32);
    lean_ctor_set(v___x_3705_, 0, v___x_3704_);
    lean_ctor_set(v___x_3705_, 1, v___x_3703_);
    return v___x_3705_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(
    mut v_x_3706_: *mut LeanObject,
    mut v_a_3707_: *mut LeanObject,
    mut v_a_3708_: *mut LeanObject,
    mut v_a_3709_: *mut LeanObject,
    mut v_a_3710_: *mut LeanObject,
    mut v_a_3711_: *mut LeanObject,
    mut v_a_3712_: *mut LeanObject,
    mut v_a_3713_: *mut LeanObject,
    mut v_a_3714_: *mut LeanObject,
    mut v_a_3715_: *mut LeanObject,
    mut v_a_3716_: *mut LeanObject,
    mut v_a_3717_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3721_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3724_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3725_: u8 = 0;
    let mut v___x_3726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3729_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3730_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3719_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
                v___x_3720_ = lean_st_mk_ref(v___x_3719_);
                lean_inc(v_a_3717_);
                lean_inc_ref(v_a_3716_);
                lean_inc(v_a_3715_);
                lean_inc_ref(v_a_3714_);
                lean_inc(v_a_3713_);
                lean_inc_ref(v_a_3712_);
                lean_inc(v_a_3711_);
                lean_inc_ref(v_a_3710_);
                lean_inc(v_a_3709_);
                lean_inc(v_a_3708_);
                lean_inc(v_a_3707_);
                lean_inc(v___x_3720_);
                v___x_3721_ = lean_apply_13(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3721_) == 0 {
                    v_a_3722_ = lean_ctor_get(v___x_3721_, 0);
                    v_isSharedCheck_3730_ = (!lean_is_exclusive(v___x_3721_)) as u8;
                    if v_isSharedCheck_3730_ == 0 {
                        v___x_3724_ = v___x_3721_;
                        v_isShared_3725_ = v_isSharedCheck_3730_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3722_);
                        lean_dec(v___x_3721_);
                        v___x_3724_ = lean_box(0);
                        v_isShared_3725_ = v_isSharedCheck_3730_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3720_);
                    return v___x_3721_;
                }
            }
            1 => {
                v___x_3726_ = lean_st_ref_get(v___x_3720_);
                lean_dec(v___x_3720_);
                lean_dec(v___x_3726_);
                if v_isShared_3725_ == 0 {
                    v___x_3728_ = v___x_3724_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3729_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3729_, 0, v_a_3722_);
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
    mut v_x_3731_: *mut LeanObject,
    mut v_a_3732_: *mut LeanObject,
    mut v_a_3733_: *mut LeanObject,
    mut v_a_3734_: *mut LeanObject,
    mut v_a_3735_: *mut LeanObject,
    mut v_a_3736_: *mut LeanObject,
    mut v_a_3737_: *mut LeanObject,
    mut v_a_3738_: *mut LeanObject,
    mut v_a_3739_: *mut LeanObject,
    mut v_a_3740_: *mut LeanObject,
    mut v_a_3741_: *mut LeanObject,
    mut v_a_3742_: *mut LeanObject,
    mut v_a_3743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3744_: *mut LeanObject = core::ptr::null_mut();
    v_res_3744_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg(v_x_3731_, v_a_3732_, v_a_3733_, v_a_3734_, v_a_3735_, v_a_3736_, v_a_3737_, v_a_3738_, v_a_3739_, v_a_3740_, v_a_3741_, v_a_3742_);
    lean_dec(v_a_3742_);
    lean_dec_ref(v_a_3741_);
    lean_dec(v_a_3740_);
    lean_dec_ref(v_a_3739_);
    lean_dec(v_a_3738_);
    lean_dec_ref(v_a_3737_);
    lean_dec(v_a_3736_);
    lean_dec_ref(v_a_3735_);
    lean_dec(v_a_3734_);
    lean_dec(v_a_3733_);
    lean_dec(v_a_3732_);
    return v_res_3744_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(
    mut v_00_u03b1_3745_: *mut LeanObject,
    mut v_x_3746_: *mut LeanObject,
    mut v_a_3747_: *mut LeanObject,
    mut v_a_3748_: *mut LeanObject,
    mut v_a_3749_: *mut LeanObject,
    mut v_a_3750_: *mut LeanObject,
    mut v_a_3751_: *mut LeanObject,
    mut v_a_3752_: *mut LeanObject,
    mut v_a_3753_: *mut LeanObject,
    mut v_a_3754_: *mut LeanObject,
    mut v_a_3755_: *mut LeanObject,
    mut v_a_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3759_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3760_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3762_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3764_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3765_: u8 = 0;
    let mut v___x_3766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3768_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3759_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
                v___x_3760_ = lean_st_mk_ref(v___x_3759_);
                lean_inc(v_a_3757_);
                lean_inc_ref(v_a_3756_);
                lean_inc(v_a_3755_);
                lean_inc_ref(v_a_3754_);
                lean_inc(v_a_3753_);
                lean_inc_ref(v_a_3752_);
                lean_inc(v_a_3751_);
                lean_inc_ref(v_a_3750_);
                lean_inc(v_a_3749_);
                lean_inc(v_a_3748_);
                lean_inc(v_a_3747_);
                lean_inc(v___x_3760_);
                v___x_3761_ = lean_apply_13(
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
                    lean_box(0),
                );
                if lean_obj_tag(v___x_3761_) == 0 {
                    v_a_3762_ = lean_ctor_get(v___x_3761_, 0);
                    v_isSharedCheck_3770_ = (!lean_is_exclusive(v___x_3761_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3764_ = v___x_3761_;
                        v_isShared_3765_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3762_);
                        lean_dec(v___x_3761_);
                        v___x_3764_ = lean_box(0);
                        v_isShared_3765_ = v_isSharedCheck_3770_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3760_);
                    return v___x_3761_;
                }
            }
            1 => {
                v___x_3766_ = lean_st_ref_get(v___x_3760_);
                lean_dec(v___x_3760_);
                lean_dec(v___x_3766_);
                if v_isShared_3765_ == 0 {
                    v___x_3768_ = v___x_3764_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3762_);
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
    mut v_00_u03b1_3771_: *mut LeanObject,
    mut v_x_3772_: *mut LeanObject,
    mut v_a_3773_: *mut LeanObject,
    mut v_a_3774_: *mut LeanObject,
    mut v_a_3775_: *mut LeanObject,
    mut v_a_3776_: *mut LeanObject,
    mut v_a_3777_: *mut LeanObject,
    mut v_a_3778_: *mut LeanObject,
    mut v_a_3779_: *mut LeanObject,
    mut v_a_3780_: *mut LeanObject,
    mut v_a_3781_: *mut LeanObject,
    mut v_a_3782_: *mut LeanObject,
    mut v_a_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3785_: *mut LeanObject = core::ptr::null_mut();
    v_res_3785_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run(v_00_u03b1_3771_, v_x_3772_, v_a_3773_, v_a_3774_, v_a_3775_, v_a_3776_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_);
    lean_dec(v_a_3783_);
    lean_dec_ref(v_a_3782_);
    lean_dec(v_a_3781_);
    lean_dec_ref(v_a_3780_);
    lean_dec(v_a_3779_);
    lean_dec_ref(v_a_3778_);
    lean_dec(v_a_3777_);
    lean_dec_ref(v_a_3776_);
    lean_dec(v_a_3775_);
    lean_dec(v_a_3774_);
    lean_dec(v_a_3773_);
    return v_res_3785_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(
    mut v_a_3786_: *mut LeanObject,
    mut v_b_3787_: *mut LeanObject,
    mut v_x_3788_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3789_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3794_: u8 = 0;
    let mut v___x_3795_: u8 = 0;
    let mut v___x_3796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3803_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3788_) == 0 {
                    lean_dec(v_b_3787_);
                    lean_dec_ref(v_a_3786_);
                    return v_x_3788_;
                } else {
                    v_key_3789_ = lean_ctor_get(v_x_3788_, 0);
                    v_value_3790_ = lean_ctor_get(v_x_3788_, 1);
                    v_tail_3791_ = lean_ctor_get(v_x_3788_, 2);
                    v_isSharedCheck_3803_ = (!lean_is_exclusive(v_x_3788_)) as u8;
                    if v_isSharedCheck_3803_ == 0 {
                        v___x_3793_ = v_x_3788_;
                        v_isShared_3794_ = v_isSharedCheck_3803_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3791_);
                        lean_inc(v_value_3790_);
                        lean_inc(v_key_3789_);
                        lean_dec(v_x_3788_);
                        v___x_3793_ = lean_box(0);
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
                        lean_ctor_set(v___x_3793_, 2, v___x_3796_);
                        v___x_3798_ = v___x_3793_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_key_3789_);
                        lean_ctor_set(v_reuseFailAlloc_3799_, 1, v_value_3790_);
                        lean_ctor_set(v_reuseFailAlloc_3799_, 2, v___x_3796_);
                        v___x_3798_ = v_reuseFailAlloc_3799_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_dec(v_value_3790_);
                    lean_dec(v_key_3789_);
                    if v_isShared_3794_ == 0 {
                        lean_ctor_set(v___x_3793_, 1, v_b_3787_);
                        lean_ctor_set(v___x_3793_, 0, v_a_3786_);
                        v___x_3801_ = v___x_3793_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 3, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3786_);
                        lean_ctor_set(v_reuseFailAlloc_3802_, 1, v_b_3787_);
                        lean_ctor_set(v_reuseFailAlloc_3802_, 2, v_tail_3791_);
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
    mut v_x_3804_: *mut LeanObject,
    mut v_x_3805_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_key_3806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3811_: u8 = 0;
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3825_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3827_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3831_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3805_) == 0 {
                    return v_x_3804_;
                } else {
                    v_key_3806_ = lean_ctor_get(v_x_3805_, 0);
                    v_value_3807_ = lean_ctor_get(v_x_3805_, 1);
                    v_tail_3808_ = lean_ctor_get(v_x_3805_, 2);
                    v_isSharedCheck_3831_ = (!lean_is_exclusive(v_x_3805_)) as u8;
                    if v_isSharedCheck_3831_ == 0 {
                        v___x_3810_ = v_x_3805_;
                        v_isShared_3811_ = v_isSharedCheck_3831_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_tail_3808_);
                        lean_inc(v_value_3807_);
                        lean_inc(v_key_3806_);
                        lean_dec(v_x_3805_);
                        v___x_3810_ = lean_box(0);
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
                lean_inc(v___x_3825_);
                if v_isShared_3811_ == 0 {
                    lean_ctor_set(v___x_3810_, 2, v___x_3825_);
                    v___x_3827_ = v___x_3810_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_key_3806_);
                    lean_ctor_set(v_reuseFailAlloc_3830_, 1, v_value_3807_);
                    lean_ctor_set(v_reuseFailAlloc_3830_, 2, v___x_3825_);
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
    mut v_i_3832_: *mut LeanObject,
    mut v_source_3833_: *mut LeanObject,
    mut v_target_3834_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: u8 = 0;
    let mut v_es_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut LeanObject = core::ptr::null_mut();
    let mut v_source_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_target_3840_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3841_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3835_ = lean_array_get_size(v_source_3833_);
                v___x_3836_ = lean_nat_dec_lt(v_i_3832_, v___x_3835_);
                if v___x_3836_ == 0 {
                    lean_dec_ref(v_source_3833_);
                    lean_dec(v_i_3832_);
                    return v_target_3834_;
                } else {
                    v_es_3837_ = lean_array_fget(v_source_3833_, v_i_3832_);
                    v___x_3838_ = lean_box(0);
                    v_source_3839_ = lean_array_fset(v_source_3833_, v_i_3832_, v___x_3838_);
                    v_target_3840_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_target_3834_, v_es_3837_);
                    v___x_3841_ = lean_unsigned_to_nat(1);
                    v___x_3842_ = lean_nat_add(v_i_3832_, v___x_3841_);
                    lean_dec(v_i_3832_);
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
    mut v_data_3844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut v_nbuckets_3847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3848_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3849_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3850_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3851_: *mut LeanObject = core::ptr::null_mut();
    v___x_3845_ = lean_array_get_size(v_data_3844_);
    v___x_3846_ = lean_unsigned_to_nat(2);
    v_nbuckets_3847_ = lean_nat_mul(v___x_3845_, v___x_3846_);
    v___x_3848_ = lean_unsigned_to_nat(0);
    v___x_3849_ = lean_box(0);
    v___x_3850_ = lean_mk_array(v_nbuckets_3847_, v___x_3849_);
    v___x_3851_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v___x_3848_, v_data_3844_, v___x_3850_);
    return v___x_3851_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(
    mut v_a_3852_: *mut LeanObject,
    mut v_x_3853_: *mut LeanObject,
) -> u8 {
    let mut v___x_3854_: u8 = 0;
    let mut v_key_3855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3857_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3853_) == 0 {
                    v___x_3854_ = 0;
                    return v___x_3854_;
                } else {
                    v_key_3855_ = lean_ctor_get(v_x_3853_, 0);
                    v_tail_3856_ = lean_ctor_get(v_x_3853_, 2);
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
    mut v_a_3859_: *mut LeanObject,
    mut v_x_3860_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3861_: u8 = 0;
    let mut v_r_3862_: *mut LeanObject = core::ptr::null_mut();
    v_res_3861_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_3859_, v_x_3860_);
    lean_dec(v_x_3860_);
    lean_dec_ref(v_a_3859_);
    v_r_3862_ = lean_box((v_res_3861_) as usize);
    return v_r_3862_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(
    mut v_m_3863_: *mut LeanObject,
    mut v_a_3864_: *mut LeanObject,
    mut v_b_3865_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_size_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3870_: u8 = 0;
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_bkt_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: u8 = 0;
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_x27_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3889_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3890_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3893_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3894_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3895_: u8 = 0;
    let mut v_val_3896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3899_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3902_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_buckets_x27_3904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3910_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_size_3866_ = lean_ctor_get(v_m_3863_, 0);
                v_buckets_3867_ = lean_ctor_get(v_m_3863_, 1);
                v_isSharedCheck_3910_ = (!lean_is_exclusive(v_m_3863_)) as u8;
                if v_isSharedCheck_3910_ == 0 {
                    v___x_3869_ = v_m_3863_;
                    v_isShared_3870_ = v_isSharedCheck_3910_;
                    state = 1;
                    continue;
                } else {
                    lean_inc(v_buckets_3867_);
                    lean_inc(v_size_3866_);
                    lean_dec(v_m_3863_);
                    v___x_3869_ = lean_box(0);
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
                    v___x_3886_ = lean_unsigned_to_nat(1);
                    v_size_x27_3887_ = lean_nat_add(v_size_3866_, v___x_3886_);
                    lean_dec(v_size_3866_);
                    lean_inc(v_bkt_3884_);
                    v___x_3888_ = lean_alloc_ctor(1, 3, (0) as u32);
                    lean_ctor_set(v___x_3888_, 0, v_a_3864_);
                    lean_ctor_set(v___x_3888_, 1, v_b_3865_);
                    lean_ctor_set(v___x_3888_, 2, v_bkt_3884_);
                    v_buckets_x27_3889_ =
                        lean_array_uset(v_buckets_3867_, v___x_3883_, v___x_3888_);
                    v___x_3890_ = lean_unsigned_to_nat(4);
                    v___x_3891_ = lean_nat_mul(v_size_x27_3887_, v___x_3890_);
                    v___x_3892_ = lean_unsigned_to_nat(3);
                    v___x_3893_ = lean_nat_div(v___x_3891_, v___x_3892_);
                    lean_dec(v___x_3891_);
                    v___x_3894_ = lean_array_get_size(v_buckets_x27_3889_);
                    v___x_3895_ = lean_nat_dec_le(v___x_3893_, v___x_3894_);
                    lean_dec(v___x_3893_);
                    if v___x_3895_ == 0 {
                        v_val_3896_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_buckets_x27_3889_);
                        if v_isShared_3870_ == 0 {
                            lean_ctor_set(v___x_3869_, 1, v_val_3896_);
                            lean_ctor_set(v___x_3869_, 0, v_size_x27_3887_);
                            v___x_3898_ = v___x_3869_;
                            state = 2;
                            continue;
                        } else {
                            v_reuseFailAlloc_3899_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3899_, 0, v_size_x27_3887_);
                            lean_ctor_set(v_reuseFailAlloc_3899_, 1, v_val_3896_);
                            v___x_3898_ = v_reuseFailAlloc_3899_;
                            state = 2;
                            continue;
                        }
                    } else {
                        if v_isShared_3870_ == 0 {
                            lean_ctor_set(v___x_3869_, 1, v_buckets_x27_3889_);
                            lean_ctor_set(v___x_3869_, 0, v_size_x27_3887_);
                            v___x_3901_ = v___x_3869_;
                            state = 3;
                            continue;
                        } else {
                            v_reuseFailAlloc_3902_ = lean_alloc_ctor(0, 2, (0) as u32);
                            lean_ctor_set(v_reuseFailAlloc_3902_, 0, v_size_x27_3887_);
                            lean_ctor_set(v_reuseFailAlloc_3902_, 1, v_buckets_x27_3889_);
                            v___x_3901_ = v_reuseFailAlloc_3902_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    lean_inc(v_bkt_3884_);
                    v___x_3903_ = lean_box(0);
                    v_buckets_x27_3904_ =
                        lean_array_uset(v_buckets_3867_, v___x_3883_, v___x_3903_);
                    v___x_3905_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_3864_, v_b_3865_, v_bkt_3884_);
                    v___x_3906_ = lean_array_uset(v_buckets_x27_3904_, v___x_3883_, v___x_3905_);
                    if v_isShared_3870_ == 0 {
                        lean_ctor_set(v___x_3869_, 1, v___x_3906_);
                        v___x_3908_ = v___x_3869_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3909_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3909_, 0, v_size_3866_);
                        lean_ctor_set(v_reuseFailAlloc_3909_, 1, v___x_3906_);
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
    mut v_a_3911_: *mut LeanObject,
    mut v_x_3912_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v_value_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3912_) == 0 {
                    v___x_3913_ = lean_box(0);
                    return v___x_3913_;
                } else {
                    v_key_3914_ = lean_ctor_get(v_x_3912_, 0);
                    v_value_3915_ = lean_ctor_get(v_x_3912_, 1);
                    v_tail_3916_ = lean_ctor_get(v_x_3912_, 2);
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
                        lean_inc(v_value_3915_);
                        v___x_3919_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3919_, 0, v_value_3915_);
                        return v___x_3919_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg___boxed(
    mut v_a_3920_: *mut LeanObject,
    mut v_x_3921_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3922_: *mut LeanObject = core::ptr::null_mut();
    v_res_3922_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_3920_, v_x_3921_);
    lean_dec(v_x_3921_);
    lean_dec_ref(v_a_3920_);
    return v_res_3922_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(
    mut v_m_3923_: *mut LeanObject,
    mut v_a_3924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_buckets_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v___x_3939_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    v_buckets_3925_ = lean_ctor_get(v_m_3923_, 1);
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
    mut v_m_3941_: *mut LeanObject,
    mut v_a_3942_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3943_: *mut LeanObject = core::ptr::null_mut();
    v_res_3943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_3941_, v_a_3942_);
    lean_dec_ref(v_a_3942_);
    lean_dec_ref(v_m_3941_);
    return v_res_3943_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(
    mut v_e_3944_: *mut LeanObject,
    mut v_a_3945_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3953_: u8 = 0;
    let mut v___x_3955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3957_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3958_: u8 = 0;
    let mut v___x_3959_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3961_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_3962_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_3963_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3965_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3966_: u8 = 0;
    let mut v___x_3967_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3968_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3969_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3971_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3975_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3976_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3947_ = lean_st_ref_get(v_a_3945_);
                v_varMap_3948_ = lean_ctor_get(v___x_3947_, 0);
                lean_inc_ref(v_varMap_3948_);
                lean_dec(v___x_3947_);
                v___x_3949_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_varMap_3948_, v_e_3944_);
                lean_dec_ref(v_varMap_3948_);
                if lean_obj_tag(v___x_3949_) == 1 {
                    lean_dec_ref(v_e_3944_);
                    v_val_3950_ = lean_ctor_get(v___x_3949_, 0);
                    v_isSharedCheck_3958_ = (!lean_is_exclusive(v___x_3949_)) as u8;
                    if v_isSharedCheck_3958_ == 0 {
                        v___x_3952_ = v___x_3949_;
                        v_isShared_3953_ = v_isSharedCheck_3958_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_val_3950_);
                        lean_dec(v___x_3949_);
                        v___x_3952_ = lean_box(0);
                        v_isShared_3953_ = v_isSharedCheck_3958_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec(v___x_3949_);
                    v___x_3959_ = lean_st_ref_get(v_a_3945_);
                    v___x_3960_ = lean_st_ref_take(v_a_3945_);
                    v_vars_3961_ = lean_ctor_get(v___x_3959_, 1);
                    lean_inc_ref(v_vars_3961_);
                    lean_dec(v___x_3959_);
                    v_varMap_3962_ = lean_ctor_get(v___x_3960_, 0);
                    v_vars_3963_ = lean_ctor_get(v___x_3960_, 1);
                    v_isSharedCheck_3976_ = (!lean_is_exclusive(v___x_3960_)) as u8;
                    if v_isSharedCheck_3976_ == 0 {
                        v___x_3965_ = v___x_3960_;
                        v_isShared_3966_ = v_isSharedCheck_3976_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_vars_3963_);
                        lean_inc(v_varMap_3962_);
                        lean_dec(v___x_3960_);
                        v___x_3965_ = lean_box(0);
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
                    v_reuseFailAlloc_3957_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3957_, 0, v_val_3950_);
                    v___x_3955_ = v_reuseFailAlloc_3957_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                v___x_3956_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3956_, 0, v___x_3955_);
                return v___x_3956_;
            }
            3 => {
                v___x_3967_ = lean_array_get_size(v_vars_3961_);
                lean_dec_ref(v_vars_3961_);
                lean_inc_ref(v_e_3944_);
                v___x_3968_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_varMap_3962_, v_e_3944_, v___x_3967_);
                v___x_3969_ = lean_array_push(v_vars_3963_, v_e_3944_);
                if v_isShared_3966_ == 0 {
                    lean_ctor_set(v___x_3965_, 1, v___x_3969_);
                    lean_ctor_set(v___x_3965_, 0, v___x_3968_);
                    v___x_3971_ = v___x_3965_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3975_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3975_, 0, v___x_3968_);
                    lean_ctor_set(v_reuseFailAlloc_3975_, 1, v___x_3969_);
                    v___x_3971_ = v_reuseFailAlloc_3975_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                v___x_3972_ = lean_st_ref_set(v_a_3945_, v___x_3971_);
                v___x_3973_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_3973_, 0, v___x_3967_);
                v___x_3974_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_3974_, 0, v___x_3973_);
                return v___x_3974_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg___boxed(
    mut v_e_3977_: *mut LeanObject,
    mut v_a_3978_: *mut LeanObject,
    mut v_a_3979_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3980_: *mut LeanObject = core::ptr::null_mut();
    v_res_3980_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_3977_, v_a_3978_);
    lean_dec(v_a_3978_);
    return v_res_3980_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(
    mut v_e_3981_: *mut LeanObject,
    mut v_a_3982_: *mut LeanObject,
    mut v_a_3983_: *mut LeanObject,
    mut v_a_3984_: *mut LeanObject,
    mut v_a_3985_: *mut LeanObject,
    mut v_a_3986_: *mut LeanObject,
    mut v_a_3987_: *mut LeanObject,
    mut v_a_3988_: *mut LeanObject,
    mut v_a_3989_: *mut LeanObject,
    mut v_a_3990_: *mut LeanObject,
    mut v_a_3991_: *mut LeanObject,
    mut v_a_3992_: *mut LeanObject,
    mut v_a_3993_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    v___x_3995_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_3981_, v_a_3982_);
    return v___x_3995_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___boxed(
    mut v_e_3996_: *mut LeanObject,
    mut v_a_3997_: *mut LeanObject,
    mut v_a_3998_: *mut LeanObject,
    mut v_a_3999_: *mut LeanObject,
    mut v_a_4000_: *mut LeanObject,
    mut v_a_4001_: *mut LeanObject,
    mut v_a_4002_: *mut LeanObject,
    mut v_a_4003_: *mut LeanObject,
    mut v_a_4004_: *mut LeanObject,
    mut v_a_4005_: *mut LeanObject,
    mut v_a_4006_: *mut LeanObject,
    mut v_a_4007_: *mut LeanObject,
    mut v_a_4008_: *mut LeanObject,
    mut v_a_4009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4010_: *mut LeanObject = core::ptr::null_mut();
    v_res_4010_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar(v_e_3996_, v_a_3997_, v_a_3998_, v_a_3999_, v_a_4000_, v_a_4001_, v_a_4002_, v_a_4003_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_, v_a_4008_);
    lean_dec(v_a_4008_);
    lean_dec_ref(v_a_4007_);
    lean_dec(v_a_4006_);
    lean_dec_ref(v_a_4005_);
    lean_dec(v_a_4004_);
    lean_dec_ref(v_a_4003_);
    lean_dec(v_a_4002_);
    lean_dec_ref(v_a_4001_);
    lean_dec(v_a_4000_);
    lean_dec(v_a_3999_);
    lean_dec(v_a_3998_);
    lean_dec(v_a_3997_);
    return v_res_4010_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(
    mut v_00_u03b2_4011_: *mut LeanObject,
    mut v_m_4012_: *mut LeanObject,
    mut v_a_4013_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4014_: *mut LeanObject = core::ptr::null_mut();
    v___x_4014_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___redArg(v_m_4012_, v_a_4013_);
    return v___x_4014_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0___boxed(
    mut v_00_u03b2_4015_: *mut LeanObject,
    mut v_m_4016_: *mut LeanObject,
    mut v_a_4017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4018_: *mut LeanObject = core::ptr::null_mut();
    v_res_4018_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0(v_00_u03b2_4015_, v_m_4016_, v_a_4017_);
    lean_dec_ref(v_a_4017_);
    lean_dec_ref(v_m_4016_);
    return v_res_4018_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1(
    mut v_00_u03b2_4019_: *mut LeanObject,
    mut v_m_4020_: *mut LeanObject,
    mut v_a_4021_: *mut LeanObject,
    mut v_b_4022_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    v___x_4023_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1___redArg(v_m_4020_, v_a_4021_, v_b_4022_);
    return v___x_4023_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(
    mut v_00_u03b2_4024_: *mut LeanObject,
    mut v_a_4025_: *mut LeanObject,
    mut v_x_4026_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4027_: *mut LeanObject = core::ptr::null_mut();
    v___x_4027_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___redArg(v_a_4025_, v_x_4026_);
    return v___x_4027_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0___boxed(
    mut v_00_u03b2_4028_: *mut LeanObject,
    mut v_a_4029_: *mut LeanObject,
    mut v_x_4030_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4031_: *mut LeanObject = core::ptr::null_mut();
    v_res_4031_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__0_spec__0(v_00_u03b2_4028_, v_a_4029_, v_x_4030_);
    lean_dec(v_x_4030_);
    lean_dec_ref(v_a_4029_);
    return v_res_4031_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(
    mut v_00_u03b2_4032_: *mut LeanObject,
    mut v_a_4033_: *mut LeanObject,
    mut v_x_4034_: *mut LeanObject,
) -> u8 {
    let mut v___x_4035_: u8 = 0;
    v___x_4035_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___redArg(v_a_4033_, v_x_4034_);
    return v___x_4035_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2___boxed(
    mut v_00_u03b2_4036_: *mut LeanObject,
    mut v_a_4037_: *mut LeanObject,
    mut v_x_4038_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4039_: u8 = 0;
    let mut v_r_4040_: *mut LeanObject = core::ptr::null_mut();
    v_res_4039_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__2(v_00_u03b2_4036_, v_a_4037_, v_x_4038_);
    lean_dec(v_x_4038_);
    lean_dec_ref(v_a_4037_);
    v_r_4040_ = lean_box((v_res_4039_) as usize);
    return v_r_4040_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3(
    mut v_00_u03b2_4041_: *mut LeanObject,
    mut v_data_4042_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4043_: *mut LeanObject = core::ptr::null_mut();
    v___x_4043_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3___redArg(v_data_4042_);
    return v___x_4043_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4(
    mut v_00_u03b2_4044_: *mut LeanObject,
    mut v_a_4045_: *mut LeanObject,
    mut v_b_4046_: *mut LeanObject,
    mut v_x_4047_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    v___x_4048_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__4___redArg(v_a_4045_, v_b_4046_, v_x_4047_);
    return v___x_4048_;
}
pub unsafe fn l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4(
    mut v_00_u03b2_4049_: *mut LeanObject,
    mut v_i_4050_: *mut LeanObject,
    mut v_source_4051_: *mut LeanObject,
    mut v_target_4052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4053_: *mut LeanObject = core::ptr::null_mut();
    v___x_4053_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4___redArg(v_i_4050_, v_source_4051_, v_target_4052_);
    return v___x_4053_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5(
    mut v_00_u03b2_4054_: *mut LeanObject,
    mut v_x_4055_: *mut LeanObject,
    mut v_x_4056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4057_: *mut LeanObject = core::ptr::null_mut();
    v___x_4057_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar_spec__1_spec__3_spec__4_spec__5___redArg(v_x_4055_, v_x_4056_);
    return v___x_4057_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(
    mut v_e_4058_: *mut LeanObject,
    mut v_a_4059_: *mut LeanObject,
    mut v_a_4060_: *mut LeanObject,
    mut v_a_4061_: *mut LeanObject,
    mut v_a_4062_: *mut LeanObject,
    mut v_a_4063_: *mut LeanObject,
    mut v_a_4064_: *mut LeanObject,
    mut v_a_4065_: *mut LeanObject,
    mut v_a_4066_: *mut LeanObject,
    mut v_a_4067_: *mut LeanObject,
    mut v_a_4068_: *mut LeanObject,
    mut v_a_4069_: *mut LeanObject,
    mut v_a_4070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4073_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4077_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4078_: u8 = 0;
    let mut v___x_4079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: u8 = 0;
    let mut v___x_4081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4084_: u8 = 0;
    let mut v___x_4085_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4086_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4088_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4089_: u8 = 0;
    let mut v___x_4090_: u8 = 0;
    let mut v___x_4091_: *mut LeanObject = core::ptr::null_mut();
    let mut v_arg_4092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4095_: u8 = 0;
    let mut v___x_4096_: u8 = 0;
    let mut v___x_4097_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4098_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4099_: u8 = 0;
    let mut v___x_4100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4102_: u8 = 0;
    let mut v___x_4103_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4104_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4105_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4106_: u8 = 0;
    let mut v___x_4107_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4108_: u8 = 0;
    let mut v___x_4109_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4110_: u8 = 0;
    let mut v___x_4111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4112_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4117_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4118_: u8 = 0;
    let mut v___x_4119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4121_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v___x_4124_: u8 = 0;
    let mut v___x_4125_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4128_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v___x_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4138_: u8 = 0;
    let mut v___x_4139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4143_: u8 = 0;
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4147_: u8 = 0;
    let mut v_zero_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4154_: u8 = 0;
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4156_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v_a_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v___x_4169_: u8 = 0;
    let mut v___x_4170_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4175_: u8 = 0;
    let mut v_a_4176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v___x_4181_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_a_4184_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4190_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4191_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4072_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                    v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_,
                    v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_,
                );
                if lean_obj_tag(v___x_4072_) == 0 {
                    v_a_4073_ = lean_ctor_get(v___x_4072_, 0);
                    lean_inc(v_a_4073_);
                    lean_dec_ref_known(v___x_4072_, 1);
                    lean_inc_ref(v_e_4058_);
                    v___x_4074_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_4058_, v_a_4068_);
                    if lean_obj_tag(v___x_4074_) == 0 {
                        v_a_4075_ = lean_ctor_get(v___x_4074_, 0);
                        v_isSharedCheck_4175_ = (!lean_is_exclusive(v___x_4074_)) as u8;
                        if v_isSharedCheck_4175_ == 0 {
                            v___x_4077_ = v___x_4074_;
                            v_isShared_4078_ = v_isSharedCheck_4175_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4075_);
                            lean_dec(v___x_4074_);
                            v___x_4077_ = lean_box(0);
                            v_isShared_4078_ = v_isSharedCheck_4175_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec(v_a_4073_);
                        lean_dec_ref(v_e_4058_);
                        v_a_4176_ = lean_ctor_get(v___x_4074_, 0);
                        v_isSharedCheck_4183_ = (!lean_is_exclusive(v___x_4074_)) as u8;
                        if v_isSharedCheck_4183_ == 0 {
                            v___x_4178_ = v___x_4074_;
                            v_isShared_4179_ = v_isSharedCheck_4183_;
                            state = 13;
                            continue;
                        } else {
                            lean_inc(v_a_4176_);
                            lean_dec(v___x_4074_);
                            v___x_4178_ = lean_box(0);
                            v_isShared_4179_ = v_isSharedCheck_4183_;
                            state = 13;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_e_4058_);
                    v_a_4184_ = lean_ctor_get(v___x_4072_, 0);
                    v_isSharedCheck_4191_ = (!lean_is_exclusive(v___x_4072_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4186_ = v___x_4072_;
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 15;
                        continue;
                    } else {
                        lean_inc(v_a_4184_);
                        lean_dec(v___x_4072_);
                        v___x_4186_ = lean_box(0);
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
                    lean_dec_ref(v___x_4079_);
                    lean_del_object(v___x_4077_);
                    lean_dec(v_a_4073_);
                    v___x_4081_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                    return v___x_4081_;
                } else {
                    v_arg_4082_ = lean_ctor_get(v___x_4079_, 1);
                    lean_inc_ref(v_arg_4082_);
                    v___x_4083_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4079_);
                    v___x_4084_ = l_Lean_Expr_isApp(v___x_4083_);
                    if v___x_4084_ == 0 {
                        lean_dec_ref(v___x_4083_);
                        lean_dec_ref(v_arg_4082_);
                        lean_del_object(v___x_4077_);
                        lean_dec(v_a_4073_);
                        v___x_4085_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                        return v___x_4085_;
                    } else {
                        v_arg_4086_ = lean_ctor_get(v___x_4083_, 1);
                        lean_inc_ref(v_arg_4086_);
                        v___x_4087_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4083_);
                        v___x_4088_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__2;
                        v___x_4089_ = l_Lean_Expr_isConstOf(v___x_4087_, v___x_4088_);
                        if v___x_4089_ == 0 {
                            lean_del_object(v___x_4077_);
                            v___x_4090_ = l_Lean_Expr_isApp(v___x_4087_);
                            if v___x_4090_ == 0 {
                                lean_dec_ref(v___x_4087_);
                                lean_dec_ref(v_arg_4086_);
                                lean_dec_ref(v_arg_4082_);
                                lean_dec(v_a_4073_);
                                v___x_4091_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                return v___x_4091_;
                            } else {
                                v_arg_4092_ = lean_ctor_get(v___x_4087_, 1);
                                lean_inc_ref(v_arg_4092_);
                                v___x_4093_ = l_Lean_Expr_appFnCleanup___redArg(v___x_4087_);
                                v___x_4094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ofNatModule_x27___closed__5;
                                v___x_4095_ = l_Lean_Expr_isConstOf(v___x_4093_, v___x_4094_);
                                if v___x_4095_ == 0 {
                                    v___x_4096_ = l_Lean_Expr_isApp(v___x_4093_);
                                    if v___x_4096_ == 0 {
                                        lean_dec_ref(v___x_4093_);
                                        lean_dec_ref(v_arg_4092_);
                                        lean_dec_ref(v_arg_4086_);
                                        lean_dec_ref(v_arg_4082_);
                                        lean_dec(v_a_4073_);
                                        v___x_4097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                        return v___x_4097_;
                                    } else {
                                        v___x_4098_ =
                                            l_Lean_Expr_appFnCleanup___redArg(v___x_4093_);
                                        v___x_4099_ = l_Lean_Expr_isApp(v___x_4098_);
                                        if v___x_4099_ == 0 {
                                            lean_dec_ref(v___x_4098_);
                                            lean_dec_ref(v_arg_4092_);
                                            lean_dec_ref(v_arg_4086_);
                                            lean_dec_ref(v_arg_4082_);
                                            lean_dec(v_a_4073_);
                                            v___x_4100_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                            return v___x_4100_;
                                        } else {
                                            v___x_4101_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_4098_);
                                            v___x_4102_ = l_Lean_Expr_isApp(v___x_4101_);
                                            if v___x_4102_ == 0 {
                                                lean_dec_ref(v___x_4101_);
                                                lean_dec_ref(v_arg_4092_);
                                                lean_dec_ref(v_arg_4086_);
                                                lean_dec_ref(v_arg_4082_);
                                                lean_dec(v_a_4073_);
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
                                                    lean_dec_ref(v___x_4104_);
                                                    if v___x_4108_ == 0 {
                                                        lean_dec_ref(v_arg_4092_);
                                                        lean_dec_ref(v_arg_4086_);
                                                        lean_dec_ref(v_arg_4082_);
                                                        lean_dec(v_a_4073_);
                                                        v___x_4109_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                        return v___x_4109_;
                                                    } else {
                                                        v___x_4110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isAddInst(v_a_4073_, v_arg_4092_);
                                                        lean_dec_ref(v_arg_4092_);
                                                        lean_dec(v_a_4073_);
                                                        if v___x_4110_ == 0 {
                                                            lean_dec_ref(v_arg_4086_);
                                                            lean_dec_ref(v_arg_4082_);
                                                            v___x_4111_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                            return v___x_4111_;
                                                        } else {
                                                            lean_dec_ref(v_e_4058_);
                                                            v___x_4112_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_4086_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                                            if lean_obj_tag(v___x_4112_) == 0 {
                                                                v_a_4113_ =
                                                                    lean_ctor_get(v___x_4112_, 0);
                                                                lean_inc(v_a_4113_);
                                                                lean_dec_ref_known(v___x_4112_, 1);
                                                                v___x_4114_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_4082_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                                                if lean_obj_tag(v___x_4114_) == 0 {
                                                                    v_a_4115_ = lean_ctor_get(
                                                                        v___x_4114_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_4123_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_4114_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_4123_ == 0 {
                                                                        v___x_4117_ = v___x_4114_;
                                                                        v_isShared_4118_ =
                                                                            v_isSharedCheck_4123_;
                                                                        state = 2;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_4115_);
                                                                        lean_dec(v___x_4114_);
                                                                        v___x_4117_ = lean_box(0);
                                                                        v_isShared_4118_ =
                                                                            v_isSharedCheck_4123_;
                                                                        state = 2;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec(v_a_4113_);
                                                                    return v___x_4114_;
                                                                }
                                                            } else {
                                                                lean_dec_ref(v_arg_4082_);
                                                                return v___x_4112_;
                                                            }
                                                        }
                                                    }
                                                } else {
                                                    lean_dec_ref(v___x_4104_);
                                                    v___x_4124_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isSMulInst(v_a_4073_, v_arg_4092_);
                                                    lean_dec_ref(v_arg_4092_);
                                                    lean_dec(v_a_4073_);
                                                    if v___x_4124_ == 0 {
                                                        lean_dec_ref(v_arg_4086_);
                                                        lean_dec_ref(v_arg_4082_);
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
                                                        lean_dec_ref(v_arg_4086_);
                                                        if lean_obj_tag(v___x_4126_) == 0 {
                                                            v_a_4127_ =
                                                                lean_ctor_get(v___x_4126_, 0);
                                                            lean_inc(v_a_4127_);
                                                            lean_dec_ref_known(v___x_4126_, 1);
                                                            if lean_obj_tag(v_a_4127_) == 1 {
                                                                lean_dec_ref(v_e_4058_);
                                                                v_val_4128_ =
                                                                    lean_ctor_get(v_a_4127_, 0);
                                                                lean_inc(v_val_4128_);
                                                                lean_dec_ref_known(v_a_4127_, 1);
                                                                v___x_4129_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_arg_4082_, v_a_4059_, v_a_4060_, v_a_4061_, v_a_4062_, v_a_4063_, v_a_4064_, v_a_4065_, v_a_4066_, v_a_4067_, v_a_4068_, v_a_4069_, v_a_4070_);
                                                                if lean_obj_tag(v___x_4129_) == 0 {
                                                                    v_a_4130_ = lean_ctor_get(
                                                                        v___x_4129_,
                                                                        0,
                                                                    );
                                                                    v_isSharedCheck_4138_ =
                                                                        (!lean_is_exclusive(
                                                                            v___x_4129_,
                                                                        ))
                                                                            as u8;
                                                                    if v_isSharedCheck_4138_ == 0 {
                                                                        v___x_4132_ = v___x_4129_;
                                                                        v_isShared_4133_ =
                                                                            v_isSharedCheck_4138_;
                                                                        state = 4;
                                                                        continue;
                                                                    } else {
                                                                        lean_inc(v_a_4130_);
                                                                        lean_dec(v___x_4129_);
                                                                        v___x_4132_ = lean_box(0);
                                                                        v_isShared_4133_ =
                                                                            v_isSharedCheck_4138_;
                                                                        state = 4;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    lean_dec(v_val_4128_);
                                                                    return v___x_4129_;
                                                                }
                                                            } else {
                                                                lean_dec(v_a_4127_);
                                                                lean_dec_ref(v_arg_4082_);
                                                                v___x_4139_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                                                return v___x_4139_;
                                                            }
                                                        } else {
                                                            lean_dec_ref(v_arg_4082_);
                                                            lean_dec_ref(v_e_4058_);
                                                            v_a_4140_ =
                                                                lean_ctor_get(v___x_4126_, 0);
                                                            v_isSharedCheck_4147_ =
                                                                (!lean_is_exclusive(v___x_4126_))
                                                                    as u8;
                                                            if v_isSharedCheck_4147_ == 0 {
                                                                v___x_4142_ = v___x_4126_;
                                                                v_isShared_4143_ =
                                                                    v_isSharedCheck_4147_;
                                                                state = 6;
                                                                continue;
                                                            } else {
                                                                lean_inc(v_a_4140_);
                                                                lean_dec(v___x_4126_);
                                                                v___x_4142_ = lean_box(0);
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
                                    lean_dec_ref(v___x_4093_);
                                    lean_dec_ref(v_arg_4092_);
                                    lean_dec_ref(v_arg_4086_);
                                    lean_dec_ref(v_arg_4082_);
                                    v_zero_4148_ = lean_ctor_get(v_a_4073_, 13);
                                    lean_inc_ref(v_zero_4148_);
                                    lean_dec(v_a_4073_);
                                    lean_inc_ref(v_e_4058_);
                                    v___x_4149_ = l_Lean_Meta_isDefEqD(
                                        v_e_4058_,
                                        v_zero_4148_,
                                        v_a_4067_,
                                        v_a_4068_,
                                        v_a_4069_,
                                        v_a_4070_,
                                    );
                                    if lean_obj_tag(v___x_4149_) == 0 {
                                        v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
                                        v_isSharedCheck_4160_ =
                                            (!lean_is_exclusive(v___x_4149_)) as u8;
                                        if v_isSharedCheck_4160_ == 0 {
                                            v___x_4152_ = v___x_4149_;
                                            v_isShared_4153_ = v_isSharedCheck_4160_;
                                            state = 8;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4150_);
                                            lean_dec(v___x_4149_);
                                            v___x_4152_ = lean_box(0);
                                            v_isShared_4153_ = v_isSharedCheck_4160_;
                                            state = 8;
                                            continue;
                                        }
                                    } else {
                                        lean_dec_ref(v_e_4058_);
                                        v_a_4161_ = lean_ctor_get(v___x_4149_, 0);
                                        v_isSharedCheck_4168_ =
                                            (!lean_is_exclusive(v___x_4149_)) as u8;
                                        if v_isSharedCheck_4168_ == 0 {
                                            v___x_4163_ = v___x_4149_;
                                            v_isShared_4164_ = v_isSharedCheck_4168_;
                                            state = 10;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4161_);
                                            lean_dec(v___x_4149_);
                                            v___x_4163_ = lean_box(0);
                                            v_isShared_4164_ = v_isSharedCheck_4168_;
                                            state = 10;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            lean_dec_ref(v___x_4087_);
                            lean_dec_ref(v_arg_4086_);
                            v___x_4169_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_isZeroInst(v_a_4073_, v_arg_4082_);
                            lean_dec_ref(v_arg_4082_);
                            lean_dec(v_a_4073_);
                            if v___x_4169_ == 0 {
                                lean_del_object(v___x_4077_);
                                v___x_4170_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                                return v___x_4170_;
                            } else {
                                lean_dec_ref(v_e_4058_);
                                v___x_4171_ = lean_box(0);
                                if v_isShared_4078_ == 0 {
                                    lean_ctor_set(v___x_4077_, 0, v___x_4171_);
                                    v___x_4173_ = v___x_4077_;
                                    state = 12;
                                    continue;
                                } else {
                                    v_reuseFailAlloc_4174_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v_reuseFailAlloc_4174_, 0, v___x_4171_);
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
                v___x_4119_ = lean_alloc_ctor(2, 2, (0) as u32);
                lean_ctor_set(v___x_4119_, 0, v_a_4113_);
                lean_ctor_set(v___x_4119_, 1, v_a_4115_);
                if v_isShared_4118_ == 0 {
                    lean_ctor_set(v___x_4117_, 0, v___x_4119_);
                    v___x_4121_ = v___x_4117_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4122_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4122_, 0, v___x_4119_);
                    v___x_4121_ = v_reuseFailAlloc_4122_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_4121_;
            }
            4 => {
                v___x_4134_ = lean_alloc_ctor(5, 2, (0) as u32);
                lean_ctor_set(v___x_4134_, 0, v_val_4128_);
                lean_ctor_set(v___x_4134_, 1, v_a_4130_);
                if v_isShared_4133_ == 0 {
                    lean_ctor_set(v___x_4132_, 0, v___x_4134_);
                    v___x_4136_ = v___x_4132_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4137_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4137_, 0, v___x_4134_);
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
                    v_reuseFailAlloc_4146_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 0, v_a_4140_);
                    v___x_4145_ = v_reuseFailAlloc_4146_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4145_;
            }
            8 => {
                v___x_4154_ = (lean_unbox(v_a_4150_) as u8);
                lean_dec(v_a_4150_);
                if v___x_4154_ == 0 {
                    lean_del_object(v___x_4152_);
                    v___x_4155_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reifyVar___redArg(v_e_4058_, v_a_4059_);
                    return v___x_4155_;
                } else {
                    lean_dec_ref(v_e_4058_);
                    v___x_4156_ = lean_box(0);
                    if v_isShared_4153_ == 0 {
                        lean_ctor_set(v___x_4152_, 0, v___x_4156_);
                        v___x_4158_ = v___x_4152_;
                        state = 9;
                        continue;
                    } else {
                        v_reuseFailAlloc_4159_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4159_, 0, v___x_4156_);
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
                    v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
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
                    v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
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
                    v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
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
    mut v_e_4192_: *mut LeanObject,
    mut v_a_4193_: *mut LeanObject,
    mut v_a_4194_: *mut LeanObject,
    mut v_a_4195_: *mut LeanObject,
    mut v_a_4196_: *mut LeanObject,
    mut v_a_4197_: *mut LeanObject,
    mut v_a_4198_: *mut LeanObject,
    mut v_a_4199_: *mut LeanObject,
    mut v_a_4200_: *mut LeanObject,
    mut v_a_4201_: *mut LeanObject,
    mut v_a_4202_: *mut LeanObject,
    mut v_a_4203_: *mut LeanObject,
    mut v_a_4204_: *mut LeanObject,
    mut v_a_4205_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4206_: *mut LeanObject = core::ptr::null_mut();
    v_res_4206_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_e_4192_, v_a_4193_, v_a_4194_, v_a_4195_, v_a_4196_, v_a_4197_, v_a_4198_, v_a_4199_, v_a_4200_, v_a_4201_, v_a_4202_, v_a_4203_, v_a_4204_);
    lean_dec(v_a_4204_);
    lean_dec_ref(v_a_4203_);
    lean_dec(v_a_4202_);
    lean_dec_ref(v_a_4201_);
    lean_dec(v_a_4200_);
    lean_dec_ref(v_a_4199_);
    lean_dec(v_a_4198_);
    lean_dec_ref(v_a_4197_);
    lean_dec(v_a_4196_);
    lean_dec(v_a_4195_);
    lean_dec(v_a_4194_);
    lean_dec(v_a_4193_);
    return v_res_4206_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(
    mut v_a_4214_: *mut LeanObject,
    mut v_b_4215_: *mut LeanObject,
    mut v_a_4216_: *mut LeanObject,
    mut v_a_4217_: *mut LeanObject,
    mut v_a_4218_: *mut LeanObject,
    mut v_ctx_4219_: *mut LeanObject,
    mut v___y_4220_: *mut LeanObject,
    mut v___y_4221_: *mut LeanObject,
    mut v___y_4222_: *mut LeanObject,
    mut v___y_4223_: *mut LeanObject,
    mut v___y_4224_: *mut LeanObject,
    mut v___y_4225_: *mut LeanObject,
    mut v___y_4226_: *mut LeanObject,
    mut v___y_4227_: *mut LeanObject,
    mut v___y_4228_: *mut LeanObject,
    mut v___y_4229_: *mut LeanObject,
    mut v___y_4230_: *mut LeanObject,
    mut v___y_4231_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_type_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_u_4236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_natModuleInst_4237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4240_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4242_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4250_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4251_: u8 = 0;
    let mut v___x_4253_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4254_: *mut LeanObject = core::ptr::null_mut();
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
                if lean_obj_tag(v___x_4233_) == 0 {
                    v_a_4234_ = lean_ctor_get(v___x_4233_, 0);
                    lean_inc(v_a_4234_);
                    lean_dec_ref_known(v___x_4233_, 1);
                    v_type_4235_ = lean_ctor_get(v_a_4216_, 2);
                    lean_inc_ref(v_type_4235_);
                    v_u_4236_ = lean_ctor_get(v_a_4216_, 3);
                    lean_inc(v_u_4236_);
                    v_natModuleInst_4237_ = lean_ctor_get(v_a_4216_, 4);
                    lean_inc_ref(v_natModuleInst_4237_);
                    lean_dec_ref(v_a_4216_);
                    v___x_4238_ =
                        l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0___closed__2;
                    v___x_4239_ = lean_box(0);
                    v___x_4240_ = lean_alloc_ctor(1, 2, (0) as u32);
                    lean_ctor_set(v___x_4240_, 0, v_u_4236_);
                    lean_ctor_set(v___x_4240_, 1, v___x_4239_);
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
                    lean_dec_ref(v_ctx_4219_);
                    lean_dec(v_a_4218_);
                    lean_dec(v_a_4217_);
                    lean_dec_ref(v_a_4216_);
                    v_a_4248_ = lean_ctor_get(v___x_4233_, 0);
                    v_isSharedCheck_4255_ = (!lean_is_exclusive(v___x_4233_)) as u8;
                    if v_isSharedCheck_4255_ == 0 {
                        v___x_4250_ = v___x_4233_;
                        v_isShared_4251_ = v_isSharedCheck_4255_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4248_);
                        lean_dec(v___x_4233_);
                        v___x_4250_ = lean_box(0);
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
                    v_reuseFailAlloc_4254_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4254_, 0, v_a_4248_);
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
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_4256_: *mut LeanObject = *_args.add(0);
    let mut v_b_4257_: *mut LeanObject = *_args.add(1);
    let mut v_a_4258_: *mut LeanObject = *_args.add(2);
    let mut v_a_4259_: *mut LeanObject = *_args.add(3);
    let mut v_a_4260_: *mut LeanObject = *_args.add(4);
    let mut v_ctx_4261_: *mut LeanObject = *_args.add(5);
    let mut v___y_4262_: *mut LeanObject = *_args.add(6);
    let mut v___y_4263_: *mut LeanObject = *_args.add(7);
    let mut v___y_4264_: *mut LeanObject = *_args.add(8);
    let mut v___y_4265_: *mut LeanObject = *_args.add(9);
    let mut v___y_4266_: *mut LeanObject = *_args.add(10);
    let mut v___y_4267_: *mut LeanObject = *_args.add(11);
    let mut v___y_4268_: *mut LeanObject = *_args.add(12);
    let mut v___y_4269_: *mut LeanObject = *_args.add(13);
    let mut v___y_4270_: *mut LeanObject = *_args.add(14);
    let mut v___y_4271_: *mut LeanObject = *_args.add(15);
    let mut v___y_4272_: *mut LeanObject = *_args.add(16);
    let mut v___y_4273_: *mut LeanObject = *_args.add(17);
    let mut v___y_4274_: *mut LeanObject = *_args.add(18);
    let mut v_res_4275_: *mut LeanObject = core::ptr::null_mut();
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
    lean_dec(v___y_4273_);
    lean_dec_ref(v___y_4272_);
    lean_dec(v___y_4271_);
    lean_dec_ref(v___y_4270_);
    lean_dec(v___y_4269_);
    lean_dec_ref(v___y_4268_);
    lean_dec(v___y_4267_);
    lean_dec_ref(v___y_4266_);
    lean_dec(v___y_4265_);
    lean_dec(v___y_4264_);
    lean_dec(v___y_4263_);
    lean_dec(v___y_4262_);
    return v_res_4275_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(
    mut v___y_4276_: *mut LeanObject,
) -> *mut LeanObject {
    lean_inc_ref(v___y_4276_);
    return v___y_4276_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1___boxed(
    mut v___y_4277_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4278_: *mut LeanObject = core::ptr::null_mut();
    v_res_4278_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__1(v___y_4277_);
    lean_dec_ref(v___y_4277_);
    return v_res_4278_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(
    mut v_vars_4279_: *mut LeanObject,
    mut v_x_4280_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4281_: *mut LeanObject = core::ptr::null_mut();
    v___x_4281_ = lean_array_fget_borrowed(v_vars_4279_, v_x_4280_);
    lean_inc(v___x_4281_);
    return v___x_4281_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed(
    mut v_vars_4282_: *mut LeanObject,
    mut v_x_4283_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4284_: *mut LeanObject = core::ptr::null_mut();
    v_res_4284_ =
        l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3(v_vars_4282_, v_x_4283_);
    lean_dec(v_x_4283_);
    lean_dec_ref(v_vars_4282_);
    return v_res_4284_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(
    mut v_a_4286_: *mut LeanObject,
    mut v_b_4287_: *mut LeanObject,
    mut v_a_4288_: *mut LeanObject,
    mut v_a_4289_: *mut LeanObject,
    mut v_a_4290_: *mut LeanObject,
    mut v_a_4291_: *mut LeanObject,
    mut v_a_4292_: *mut LeanObject,
    mut v_a_4293_: *mut LeanObject,
    mut v_a_4294_: *mut LeanObject,
    mut v_a_4295_: *mut LeanObject,
    mut v_a_4296_: *mut LeanObject,
    mut v_a_4297_: *mut LeanObject,
    mut v_a_4298_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4300_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4301_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4302_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4304_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4305_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4306_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4309_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4310_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4316_: u8 = 0;
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4319_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_4321_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4323_: u8 = 0;
    let mut v_type_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v_zero_4325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_type_4339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_4341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4346_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4349_: u8 = 0;
    let mut v___x_4351_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4352_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4353_: u8 = 0;
    let mut v_a_4354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4356_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4357_: u8 = 0;
    let mut v___x_4359_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4360_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4361_: u8 = 0;
    let mut v_a_4362_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4364_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4365_: u8 = 0;
    let mut v___x_4367_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4369_: u8 = 0;
    let mut v_a_4370_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4373_: u8 = 0;
    let mut v___x_4375_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4377_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4300_ = lean_unsigned_to_nat(0);
                v___x_4301_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_ReifyM_run___redArg___closed__3);
                v___x_4302_ = lean_st_mk_ref(v___x_4301_);
                lean_inc_ref(v_a_4286_);
                v___x_4310_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_a_4286_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                if lean_obj_tag(v___x_4310_) == 0 {
                    v_a_4311_ = lean_ctor_get(v___x_4310_, 0);
                    lean_inc(v_a_4311_);
                    lean_dec_ref_known(v___x_4310_, 1);
                    lean_inc_ref(v_b_4287_);
                    v___x_4312_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule_0__Lean_Meta_Grind_Arith_Linear_reify(v_b_4287_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                    if lean_obj_tag(v___x_4312_) == 0 {
                        v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
                        lean_inc_n(v_a_4313_, 2);
                        lean_dec_ref_known(v___x_4312_, 1);
                        lean_inc(v_a_4311_);
                        v___x_4314_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_4311_);
                        v___x_4315_ = l_Lean_Grind_Linarith_Expr_toPolyN(v_a_4313_);
                        v___x_4316_ =
                            l_Lean_Grind_Linarith_instBEqPoly_beq(v___x_4314_, v___x_4315_);
                        lean_dec(v___x_4315_);
                        lean_dec(v___x_4314_);
                        if v___x_4316_ == 0 {
                            lean_dec(v_a_4313_);
                            lean_dec(v_a_4311_);
                            lean_dec_ref(v_b_4287_);
                            lean_dec_ref(v_a_4286_);
                            v___x_4317_ = lean_box(0);
                            v_a_4304_ = v___x_4317_;
                            state = 1;
                            continue;
                        } else {
                            v___x_4318_ = l_Lean_Meta_Grind_Arith_Linear_getNatStruct(
                                v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_,
                                v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_,
                            );
                            if lean_obj_tag(v___x_4318_) == 0 {
                                v_a_4319_ = lean_ctor_get(v___x_4318_, 0);
                                lean_inc(v_a_4319_);
                                lean_dec_ref_known(v___x_4318_, 1);
                                v___x_4320_ = lean_st_ref_get(v___x_4302_);
                                v_vars_4321_ = lean_ctor_get(v___x_4320_, 1);
                                lean_inc_ref(v_vars_4321_);
                                lean_dec(v___x_4320_);
                                v___x_4322_ = lean_array_get_size(v_vars_4321_);
                                v___x_4323_ = lean_nat_dec_lt(v___x_4300_, v___x_4322_);
                                if v___x_4323_ == 0 {
                                    lean_dec_ref(v_vars_4321_);
                                    v_type_4324_ = lean_ctor_get(v_a_4319_, 2);
                                    v_zero_4325_ = lean_ctor_get(v_a_4319_, 13);
                                    v___f_4326_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0;
                                    lean_inc_ref(v_zero_4325_);
                                    v___x_4327_ = lean_alloc_ctor(0, 1, (0) as u32);
                                    lean_ctor_set(v___x_4327_, 0, v_zero_4325_);
                                    lean_inc_ref(v_type_4324_);
                                    v___x_4328_ = l_Lean_RArray_toExpr___redArg(
                                        v_type_4324_,
                                        v___f_4326_,
                                        v___x_4327_,
                                        v_a_4295_,
                                        v_a_4296_,
                                        v_a_4297_,
                                        v_a_4298_,
                                    );
                                    if lean_obj_tag(v___x_4328_) == 0 {
                                        v_a_4329_ = lean_ctor_get(v___x_4328_, 0);
                                        lean_inc(v_a_4329_);
                                        lean_dec_ref_known(v___x_4328_, 1);
                                        v___x_4330_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_4286_, v_b_4287_, v_a_4319_, v_a_4311_, v_a_4313_, v_a_4329_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                                        v___y_4308_ = v___x_4330_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_a_4319_);
                                        lean_dec(v_a_4313_);
                                        lean_dec(v_a_4311_);
                                        lean_dec(v___x_4302_);
                                        lean_dec_ref(v_b_4287_);
                                        lean_dec_ref(v_a_4286_);
                                        v_a_4331_ = lean_ctor_get(v___x_4328_, 0);
                                        v_isSharedCheck_4338_ =
                                            (!lean_is_exclusive(v___x_4328_)) as u8;
                                        if v_isSharedCheck_4338_ == 0 {
                                            v___x_4333_ = v___x_4328_;
                                            v_isShared_4334_ = v_isSharedCheck_4338_;
                                            state = 3;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4331_);
                                            lean_dec(v___x_4328_);
                                            v___x_4333_ = lean_box(0);
                                            v_isShared_4334_ = v_isSharedCheck_4338_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    v_type_4339_ = lean_ctor_get(v_a_4319_, 2);
                                    v___f_4340_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___closed__0;
                                    v___f_4341_ = lean_alloc_closure(l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__3___boxed as *mut core::ffi::c_void, 2, 1);
                                    lean_closure_set(v___f_4341_, 0, v_vars_4321_);
                                    v___x_4342_ =
                                        l_Lean_RArray_ofFn___redArg(v___x_4322_, v___f_4341_);
                                    lean_inc_ref(v_type_4339_);
                                    v___x_4343_ = l_Lean_RArray_toExpr___redArg(
                                        v_type_4339_,
                                        v___f_4340_,
                                        v___x_4342_,
                                        v_a_4295_,
                                        v_a_4296_,
                                        v_a_4297_,
                                        v_a_4298_,
                                    );
                                    if lean_obj_tag(v___x_4343_) == 0 {
                                        v_a_4344_ = lean_ctor_get(v___x_4343_, 0);
                                        lean_inc(v_a_4344_);
                                        lean_dec_ref_known(v___x_4343_, 1);
                                        v___x_4345_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq___lam__0(v_a_4286_, v_b_4287_, v_a_4319_, v_a_4311_, v_a_4313_, v_a_4344_, v___x_4302_, v_a_4288_, v_a_4289_, v_a_4290_, v_a_4291_, v_a_4292_, v_a_4293_, v_a_4294_, v_a_4295_, v_a_4296_, v_a_4297_, v_a_4298_);
                                        v___y_4308_ = v___x_4345_;
                                        state = 2;
                                        continue;
                                    } else {
                                        lean_dec(v_a_4319_);
                                        lean_dec(v_a_4313_);
                                        lean_dec(v_a_4311_);
                                        lean_dec(v___x_4302_);
                                        lean_dec_ref(v_b_4287_);
                                        lean_dec_ref(v_a_4286_);
                                        v_a_4346_ = lean_ctor_get(v___x_4343_, 0);
                                        v_isSharedCheck_4353_ =
                                            (!lean_is_exclusive(v___x_4343_)) as u8;
                                        if v_isSharedCheck_4353_ == 0 {
                                            v___x_4348_ = v___x_4343_;
                                            v_isShared_4349_ = v_isSharedCheck_4353_;
                                            state = 5;
                                            continue;
                                        } else {
                                            lean_inc(v_a_4346_);
                                            lean_dec(v___x_4343_);
                                            v___x_4348_ = lean_box(0);
                                            v_isShared_4349_ = v_isSharedCheck_4353_;
                                            state = 5;
                                            continue;
                                        }
                                    }
                                }
                            } else {
                                lean_dec(v_a_4313_);
                                lean_dec(v_a_4311_);
                                lean_dec(v___x_4302_);
                                lean_dec_ref(v_b_4287_);
                                lean_dec_ref(v_a_4286_);
                                v_a_4354_ = lean_ctor_get(v___x_4318_, 0);
                                v_isSharedCheck_4361_ = (!lean_is_exclusive(v___x_4318_)) as u8;
                                if v_isSharedCheck_4361_ == 0 {
                                    v___x_4356_ = v___x_4318_;
                                    v_isShared_4357_ = v_isSharedCheck_4361_;
                                    state = 7;
                                    continue;
                                } else {
                                    lean_inc(v_a_4354_);
                                    lean_dec(v___x_4318_);
                                    v___x_4356_ = lean_box(0);
                                    v_isShared_4357_ = v_isSharedCheck_4361_;
                                    state = 7;
                                    continue;
                                }
                            }
                        }
                    } else {
                        lean_dec(v_a_4311_);
                        lean_dec(v___x_4302_);
                        lean_dec_ref(v_b_4287_);
                        lean_dec_ref(v_a_4286_);
                        v_a_4362_ = lean_ctor_get(v___x_4312_, 0);
                        v_isSharedCheck_4369_ = (!lean_is_exclusive(v___x_4312_)) as u8;
                        if v_isSharedCheck_4369_ == 0 {
                            v___x_4364_ = v___x_4312_;
                            v_isShared_4365_ = v_isSharedCheck_4369_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4362_);
                            lean_dec(v___x_4312_);
                            v___x_4364_ = lean_box(0);
                            v_isShared_4365_ = v_isSharedCheck_4369_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    lean_dec(v___x_4302_);
                    lean_dec_ref(v_b_4287_);
                    lean_dec_ref(v_a_4286_);
                    v_a_4370_ = lean_ctor_get(v___x_4310_, 0);
                    v_isSharedCheck_4377_ = (!lean_is_exclusive(v___x_4310_)) as u8;
                    if v_isSharedCheck_4377_ == 0 {
                        v___x_4372_ = v___x_4310_;
                        v_isShared_4373_ = v_isSharedCheck_4377_;
                        state = 11;
                        continue;
                    } else {
                        lean_inc(v_a_4370_);
                        lean_dec(v___x_4310_);
                        v___x_4372_ = lean_box(0);
                        v_isShared_4373_ = v_isSharedCheck_4377_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                v___x_4305_ = lean_st_ref_get(v___x_4302_);
                lean_dec(v___x_4302_);
                lean_dec(v___x_4305_);
                v___x_4306_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_4306_, 0, v_a_4304_);
                return v___x_4306_;
            }
            2 => {
                if lean_obj_tag(v___y_4308_) == 0 {
                    v_a_4309_ = lean_ctor_get(v___y_4308_, 0);
                    lean_inc(v_a_4309_);
                    lean_dec_ref_known(v___y_4308_, 1);
                    v_a_4304_ = v_a_4309_;
                    state = 1;
                    continue;
                } else {
                    lean_dec(v___x_4302_);
                    return v___y_4308_;
                }
            }
            3 => {
                if v_isShared_4334_ == 0 {
                    v___x_4336_ = v___x_4333_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4331_);
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
            7 => {
                if v_isShared_4357_ == 0 {
                    v___x_4359_ = v___x_4356_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4360_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4360_, 0, v_a_4354_);
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
                    v_reuseFailAlloc_4368_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4368_, 0, v_a_4362_);
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
                    v_reuseFailAlloc_4376_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4376_, 0, v_a_4370_);
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
    mut v_a_4378_: *mut LeanObject,
    mut v_b_4379_: *mut LeanObject,
    mut v_a_4380_: *mut LeanObject,
    mut v_a_4381_: *mut LeanObject,
    mut v_a_4382_: *mut LeanObject,
    mut v_a_4383_: *mut LeanObject,
    mut v_a_4384_: *mut LeanObject,
    mut v_a_4385_: *mut LeanObject,
    mut v_a_4386_: *mut LeanObject,
    mut v_a_4387_: *mut LeanObject,
    mut v_a_4388_: *mut LeanObject,
    mut v_a_4389_: *mut LeanObject,
    mut v_a_4390_: *mut LeanObject,
    mut v_a_4391_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_4392_: *mut LeanObject = core::ptr::null_mut();
    v_res_4392_ = l_Lean_Meta_Grind_Arith_Linear_normNatModuleDiseq(
        v_a_4378_, v_b_4379_, v_a_4380_, v_a_4381_, v_a_4382_, v_a_4383_, v_a_4384_, v_a_4385_,
        v_a_4386_, v_a_4387_, v_a_4388_, v_a_4389_, v_a_4390_,
    );
    lean_dec(v_a_4390_);
    lean_dec_ref(v_a_4389_);
    lean_dec(v_a_4388_);
    lean_dec_ref(v_a_4387_);
    lean_dec(v_a_4386_);
    lean_dec_ref(v_a_4385_);
    lean_dec(v_a_4384_);
    lean_dec_ref(v_a_4383_);
    lean_dec(v_a_4382_);
    lean_dec(v_a_4381_);
    lean_dec(v_a_4380_);
    return v_res_4392_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_OfNatModule(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_NatModuleNorm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_meta_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_meta_initialized = true;
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_initialized: bool = false;
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Module_OfNatModule(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Grind_Module_NatModuleNorm(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Diseq(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_ToExpr(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Nat_Order(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Init_Data_Order_Lemmas(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Data_RArray(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_OfNatModule(builtin);
}
