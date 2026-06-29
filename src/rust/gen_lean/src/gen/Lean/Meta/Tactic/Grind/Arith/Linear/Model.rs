// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Model
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.Types Lean.Meta.Tactic.Grind.Arith.Linear.Reify Lean.Meta.Tactic.Grind.Arith.ModelUtil Init.Grind.Module.Envelope
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get, lean_array_get_borrowed, lean_array_get_size,
    lean_array_size, lean_array_uget, lean_array_uget_borrowed, lean_expr_eqv, lean_infer_type,
    lean_mk_array, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_lt, lean_nat_to_int,
    lean_uint64_lor, lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize,
    lean_uint64_xor, lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat,
    lean_usize_shift_left, lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Rat::Basic::{
    l_Rat_add, l_Rat_mul, l_Rat_neg, l_Rat_ofInt, l_Rat_sub, l_instInhabitedRat,
};
use crate::r#gen::Init::Grind::Module::Envelope::{
    initialize_Init_Grind_Module_Envelope, runtime_initialize_Init_Grind_Module_Envelope,
};
use crate::r#gen::Init::System::IOError::lean_io_error_to_string;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hash,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_instantiateMVarsIfMVarApp___redArg,
    l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Reify::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify, l_Lean_Meta_Grind_Arith_Linear_isAddInst,
    l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst, l_Lean_Meta_Grind_Arith_Linear_isNegInst,
    l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst, l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst,
    l_Lean_Meta_Grind_Arith_Linear_isSubInst, l_Lean_Meta_Grind_Arith_Linear_isZeroInst,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types,
    l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default,
    l_Lean_Meta_Grind_Arith_Linear_linearExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::ModelUtil::{
    initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil, l_Lean_Meta_Grind_Arith_assignEqc,
    l_Lean_Meta_Grind_Arith_finalizeModel, l_Lean_Meta_Grind_Arith_traceModel,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg,
    l_Lean_Meta_Grind_ENode_isRoot, l_Lean_Meta_Grind_Goal_getENode,
};
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1: usize = 0;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0: u64 = 0;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2_value: crate::leanh::LeanStringObject<10> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 10, m_capacity: 10, m_length: 9, m_data: [73, 110, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3_value: crate::leanh::LeanStringObject<12> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 12, m_capacity: 12, m_length: 11, m_data: [79, 102, 78, 97, 116, 77, 111, 100, 117, 108, 101, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [116, 111, 81, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__0_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__1_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__2_value) as *mut crate::leanh::LeanObject,7605204649477761179 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_3: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__3_value) as *mut crate::leanh::LeanObject,11314908490917688650 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value_aux_3) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__4_value) as *mut crate::leanh::LeanObject,6592053806809043044 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [90, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [122, 101, 114, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__0_value) as *mut crate::leanh::LeanObject,18263865437487147968 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__1_value) as *mut crate::leanh::LeanObject,2651253468108498348 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [79, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [111, 102, 78, 97, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__3_value) as *mut crate::leanh::LeanObject,17636616155771105671 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__4_value) as *mut crate::leanh::LeanObject,15578568367168711682 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [78, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7_value: crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 4, m_capacity: 4, m_length: 3, m_data: [110, 101, 103, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__6_value) as *mut crate::leanh::LeanObject,9626815015619986526 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__7_value) as *mut crate::leanh::LeanObject,17185717442815859305 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [72, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [104, 83, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__9_value) as *mut crate::leanh::LeanObject,15703084674812832738 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__10_value) as *mut crate::leanh::LeanObject,13609749952674037527 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 77, 117, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__12_value) as *mut crate::leanh::LeanObject,2929883540436775422 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__13_value) as *mut crate::leanh::LeanObject,1611444129324655608 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 83, 117, 98, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__15_value) as *mut crate::leanh::LeanObject,16856108565602861689 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__16_value) as *mut crate::leanh::LeanObject,4187025665268973031 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [72, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [104, 65, 100, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__18_value) as *mut crate::leanh::LeanObject,10393083817453678557 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__19_value) as *mut crate::leanh::LeanObject,10680564408669940870 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_value:
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
    m_data: [103, 114, 105, 110, 100, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value:
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
    m_data: [108, 105, 110, 97, 114, 105, 116, 104, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value:
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
    m_data: [109, 111, 100, 101, 108, 0],
};
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__2_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__3_value)
            as *mut crate::leanh::LeanObject,
        10740975855909177240 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__4_value)
            as *mut crate::leanh::LeanObject,
        4796074624638123820 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(
    mut v_keys_2197_: *mut crate::leanh::LeanObject,
    mut v_vals_2198_: *mut crate::leanh::LeanObject,
    mut v_i_2199_: *mut crate::leanh::LeanObject,
    mut v_k_2200_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2202_: u8 = 0;
    let mut v___x_2203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2205_: u8 = 0;
    let mut v___x_2206_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2201_ = lean_array_get_size(v_keys_2197_);
                v___x_2202_ = lean_nat_dec_lt(v_i_2199_, v___x_2201_);
                if v___x_2202_ == 0 {
                    crate::leanh::lean_dec(v_i_2199_);
                    v___x_2203_ = crate::leanh::lean_box(0);
                    return v___x_2203_;
                } else {
                    v_k_x27_2204_ = lean_array_fget_borrowed(v_keys_2197_, v_i_2199_);
                    v___x_2205_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_2200_,
                            v_k_x27_2204_,
                        );
                    if v___x_2205_ == 0 {
                        v___x_2206_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_2207_ = lean_nat_add(v_i_2199_, v___x_2206_);
                        crate::leanh::lean_dec(v_i_2199_);
                        v_i_2199_ = v___x_2207_;
                        state = 0;
                        continue;
                    } else {
                        v___x_2209_ = lean_array_fget_borrowed(v_vals_2198_, v_i_2199_);
                        crate::leanh::lean_dec(v_i_2199_);
                        crate::leanh::lean_inc(v___x_2209_);
                        v___x_2210_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2210_, 0, v___x_2209_);
                        return v___x_2210_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg___boxed(
    mut v_keys_2211_: *mut crate::leanh::LeanObject,
    mut v_vals_2212_: *mut crate::leanh::LeanObject,
    mut v_i_2213_: *mut crate::leanh::LeanObject,
    mut v_k_2214_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2215_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2211_, v_vals_2212_, v_i_2213_, v_k_2214_);
    crate::leanh::lean_dec_ref(v_k_2214_);
    crate::leanh::lean_dec_ref(v_vals_2212_);
    crate::leanh::lean_dec_ref(v_keys_2211_);
    return v_res_2215_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0()
-> usize {
    let mut v___x_2216_: usize = 0;
    let mut v___x_2217_: usize = 0;
    let mut v___x_2218_: usize = 0;
    v___x_2216_ = 5usize;
    v___x_2217_ = 1usize;
    v___x_2218_ = lean_usize_shift_left(v___x_2217_, v___x_2216_);
    return v___x_2218_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1()
-> usize {
    let mut v___x_2219_: usize = 0;
    let mut v___x_2220_: usize = 0;
    let mut v___x_2221_: usize = 0;
    v___x_2219_ = 1usize;
    v___x_2220_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__0);
    v___x_2221_ = lean_usize_sub(v___x_2220_, v___x_2219_);
    return v___x_2221_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(
    mut v_x_2222_: *mut crate::leanh::LeanObject,
    mut v_x_2223_: usize,
    mut v_x_2224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2227_: usize = 0;
    let mut v___x_2228_: usize = 0;
    let mut v___x_2229_: usize = 0;
    let mut v_j_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2234_: u8 = 0;
    let mut v___x_2235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2238_: usize = 0;
    let mut v___x_2240_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_2241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_2242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2222_) == 0 {
                    v_es_2225_ = crate::leanh::lean_ctor_get(v_x_2222_, 0);
                    v___x_2226_ = crate::leanh::lean_box(2);
                    v___x_2227_ = 5usize;
                    v___x_2228_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___closed__1);
                    v___x_2229_ = lean_usize_land(v_x_2223_, v___x_2228_);
                    v_j_2230_ = lean_usize_to_nat(v___x_2229_);
                    v___x_2231_ = lean_array_get_borrowed(v___x_2226_, v_es_2225_, v_j_2230_);
                    crate::leanh::lean_dec(v_j_2230_);
                    match crate::leanh::lean_obj_tag(v___x_2231_) {
                        0 => {
                            v_key_2232_ = crate::leanh::lean_ctor_get(v___x_2231_, 0);
                            v_val_2233_ = crate::leanh::lean_ctor_get(v___x_2231_, 1);
                            v___x_2234_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_2224_, v_key_2232_);
                            if v___x_2234_ == 0 {
                                v___x_2235_ = crate::leanh::lean_box(0);
                                return v___x_2235_;
                            } else {
                                crate::leanh::lean_inc(v_val_2233_);
                                v___x_2236_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2236_, 0, v_val_2233_);
                                return v___x_2236_;
                            }
                        }
                        1 => {
                            v_node_2237_ = crate::leanh::lean_ctor_get(v___x_2231_, 0);
                            v___x_2238_ = lean_usize_shift_right(v_x_2223_, v___x_2227_);
                            v_x_2222_ = v_node_2237_;
                            v_x_2223_ = v___x_2238_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_2240_ = crate::leanh::lean_box(0);
                            return v___x_2240_;
                        }
                    }
                } else {
                    v_ks_2241_ = crate::leanh::lean_ctor_get(v_x_2222_, 0);
                    v_vs_2242_ = crate::leanh::lean_ctor_get(v_x_2222_, 1);
                    v___x_2243_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_2244_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_ks_2241_, v_vs_2242_, v___x_2243_, v_x_2224_);
                    return v___x_2244_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg___boxed(
    mut v_x_2245_: *mut crate::leanh::LeanObject,
    mut v_x_2246_: *mut crate::leanh::LeanObject,
    mut v_x_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_335__boxed_2248_: usize = 0;
    let mut v_res_2249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_335__boxed_2248_ = crate::leanh::lean_unbox_usize(v_x_2246_);
    crate::leanh::lean_dec(v_x_2246_);
    v_res_2249_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_2245_, v_x_335__boxed_2248_, v_x_2247_);
    crate::leanh::lean_dec_ref(v_x_2247_);
    crate::leanh::lean_dec_ref(v_x_2245_);
    return v_res_2249_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(
    mut v_x_2250_: *mut crate::leanh::LeanObject,
    mut v_x_2251_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2252_: u64 = 0;
    let mut v___x_2253_: usize = 0;
    let mut v___x_2254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2252_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_2251_);
    v___x_2253_ = lean_uint64_to_usize(v___x_2252_);
    v___x_2254_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_2250_, v___x_2253_, v_x_2251_);
    return v___x_2254_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg___boxed(
    mut v_x_2255_: *mut crate::leanh::LeanObject,
    mut v_x_2256_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2257_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_2255_, v_x_2256_);
    crate::leanh::lean_dec_ref(v_x_2256_);
    crate::leanh::lean_dec_ref(v_x_2255_);
    return v_res_2257_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(
    mut v_s_2258_: *mut crate::leanh::LeanObject,
    mut v_e_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_varMap_2260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_2261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v_size_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: u8 = 0;
    let mut v___x_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2275_: u8 = 0;
    let mut v___x_2276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_varMap_2260_ = crate::leanh::lean_ctor_get(v_s_2258_, 31);
                v_assignment_2261_ = crate::leanh::lean_ctor_get(v_s_2258_, 35);
                v___x_2262_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_varMap_2260_, v_e_2259_);
                if crate::leanh::lean_obj_tag(v___x_2262_) == 1 {
                    v_val_2263_ = crate::leanh::lean_ctor_get(v___x_2262_, 0);
                    v_isSharedCheck_2275_ = (!crate::leanh::lean_is_exclusive(v___x_2262_)) as u8;
                    if v_isSharedCheck_2275_ == 0 {
                        v___x_2265_ = v___x_2262_;
                        v_isShared_2266_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2263_);
                        crate::leanh::lean_dec(v___x_2262_);
                        v___x_2265_ = crate::leanh::lean_box(0);
                        v_isShared_2266_ = v_isSharedCheck_2275_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_2262_);
                    v___x_2276_ = crate::leanh::lean_box(0);
                    return v___x_2276_;
                }
            }
            1 => {
                v_size_2267_ = crate::leanh::lean_ctor_get(v_assignment_2261_, 2);
                v___x_2268_ = lean_nat_dec_lt(v_val_2263_, v_size_2267_);
                if v___x_2268_ == 0 {
                    crate::leanh::lean_del_object(v___x_2265_);
                    crate::leanh::lean_dec(v_val_2263_);
                    v___x_2269_ = crate::leanh::lean_box(0);
                    return v___x_2269_;
                } else {
                    v___x_2270_ = l_instInhabitedRat;
                    v___x_2271_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_2270_,
                        v_assignment_2261_,
                        v_val_2263_,
                    );
                    crate::leanh::lean_dec(v_val_2263_);
                    if v_isShared_2266_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2265_, 0, v___x_2271_);
                        v___x_2273_ = v___x_2265_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
                        v___x_2273_ = v_reuseFailAlloc_2274_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2273_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f___boxed(
    mut v_s_2277_: *mut crate::leanh::LeanObject,
    mut v_e_2278_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2279_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(v_s_2277_, v_e_2278_);
    crate::leanh::lean_dec_ref(v_e_2278_);
    crate::leanh::lean_dec_ref(v_s_2277_);
    return v_res_2279_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(
    mut v_00_u03b2_2280_: *mut crate::leanh::LeanObject,
    mut v_x_2281_: *mut crate::leanh::LeanObject,
    mut v_x_2282_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2283_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___redArg(v_x_2281_, v_x_2282_);
    return v___x_2283_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0___boxed(
    mut v_00_u03b2_2284_: *mut crate::leanh::LeanObject,
    mut v_x_2285_: *mut crate::leanh::LeanObject,
    mut v_x_2286_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2287_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0(v_00_u03b2_2284_, v_x_2285_, v_x_2286_);
    crate::leanh::lean_dec_ref(v_x_2286_);
    crate::leanh::lean_dec_ref(v_x_2285_);
    return v_res_2287_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(
    mut v_00_u03b2_2288_: *mut crate::leanh::LeanObject,
    mut v_x_2289_: *mut crate::leanh::LeanObject,
    mut v_x_2290_: usize,
    mut v_x_2291_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2292_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___redArg(v_x_2289_, v_x_2290_, v_x_2291_);
    return v___x_2292_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0___boxed(
    mut v_00_u03b2_2293_: *mut crate::leanh::LeanObject,
    mut v_x_2294_: *mut crate::leanh::LeanObject,
    mut v_x_2295_: *mut crate::leanh::LeanObject,
    mut v_x_2296_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_436__boxed_2297_: usize = 0;
    let mut v_res_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_436__boxed_2297_ = crate::leanh::lean_unbox_usize(v_x_2295_);
    crate::leanh::lean_dec(v_x_2295_);
    v_res_2298_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0(v_00_u03b2_2293_, v_x_2294_, v_x_436__boxed_2297_, v_x_2296_);
    crate::leanh::lean_dec_ref(v_x_2296_);
    crate::leanh::lean_dec_ref(v_x_2294_);
    return v_res_2298_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(
    mut v_00_u03b2_2299_: *mut crate::leanh::LeanObject,
    mut v_keys_2300_: *mut crate::leanh::LeanObject,
    mut v_vals_2301_: *mut crate::leanh::LeanObject,
    mut v_heq_2302_: *mut crate::leanh::LeanObject,
    mut v_i_2303_: *mut crate::leanh::LeanObject,
    mut v_k_2304_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2305_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___redArg(v_keys_2300_, v_vals_2301_, v_i_2303_, v_k_2304_);
    return v___x_2305_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1___boxed(
    mut v_00_u03b2_2306_: *mut crate::leanh::LeanObject,
    mut v_keys_2307_: *mut crate::leanh::LeanObject,
    mut v_vals_2308_: *mut crate::leanh::LeanObject,
    mut v_heq_2309_: *mut crate::leanh::LeanObject,
    mut v_i_2310_: *mut crate::leanh::LeanObject,
    mut v_k_2311_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2312_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Grind_Arith_Linear_getAssignment_x3f_spec__0_spec__0_spec__1(v_00_u03b2_2306_, v_keys_2307_, v_vals_2308_, v_heq_2309_, v_i_2310_, v_k_2311_);
    crate::leanh::lean_dec_ref(v_k_2311_);
    crate::leanh::lean_dec_ref(v_vals_2308_);
    crate::leanh::lean_dec_ref(v_keys_2307_);
    return v_res_2312_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0()
-> u64 {
    let mut v___x_2313_: u8 = 0;
    let mut v___x_2314_: u64 = 0;
    v___x_2313_ = 1;
    v___x_2314_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_2313_);
    return v___x_2314_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(
    mut v_type_2315_: *mut crate::leanh::LeanObject,
    mut v_n_2316_: *mut crate::leanh::LeanObject,
    mut v_a_2317_: *mut crate::leanh::LeanObject,
    mut v_a_2318_: *mut crate::leanh::LeanObject,
    mut v_a_2319_: *mut crate::leanh::LeanObject,
    mut v_a_2320_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_self_2322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_2324_: u8 = 0;
    let mut v_ctxApprox_2325_: u8 = 0;
    let mut v_quasiPatternApprox_2326_: u8 = 0;
    let mut v_constApprox_2327_: u8 = 0;
    let mut v_isDefEqStuckEx_2328_: u8 = 0;
    let mut v_unificationHints_2329_: u8 = 0;
    let mut v_proofIrrelevance_2330_: u8 = 0;
    let mut v_assignSyntheticOpaque_2331_: u8 = 0;
    let mut v_offsetCnstrs_2332_: u8 = 0;
    let mut v_etaStruct_2333_: u8 = 0;
    let mut v_univApprox_2334_: u8 = 0;
    let mut v_iota_2335_: u8 = 0;
    let mut v_beta_2336_: u8 = 0;
    let mut v_proj_2337_: u8 = 0;
    let mut v_zeta_2338_: u8 = 0;
    let mut v_zetaDelta_2339_: u8 = 0;
    let mut v_zetaUnused_2340_: u8 = 0;
    let mut v_zetaHave_2341_: u8 = 0;
    let mut v___x_2343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2344_: u8 = 0;
    let mut v_trackZetaDelta_2345_: u8 = 0;
    let mut v_zetaDeltaSet_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_2349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_2350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_2352_: u8 = 0;
    let mut v_inTypeClassResolution_2353_: u8 = 0;
    let mut v_cacheInferType_2354_: u8 = 0;
    let mut v___x_2355_: u8 = 0;
    let mut v_config_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2358_: u64 = 0;
    let mut v___x_2359_: u64 = 0;
    let mut v___x_2360_: u64 = 0;
    let mut v___x_2361_: u64 = 0;
    let mut v___x_2362_: u64 = 0;
    let mut v_key_2363_: u64 = 0;
    let mut v___x_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2367_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2372_: u8 = 0;
    let mut v___x_2374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2376_: u8 = 0;
    let mut v_reuseFailAlloc_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2378_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_self_2322_ = crate::leanh::lean_ctor_get(v_n_2316_, 0);
                crate::leanh::lean_inc_ref(v_self_2322_);
                crate::leanh::lean_dec_ref(v_n_2316_);
                v___x_2323_ = l_Lean_Meta_Context_config(v_a_2317_);
                v_foApprox_2324_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 0 as u32);
                v_ctxApprox_2325_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 1 as u32);
                v_quasiPatternApprox_2326_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2323_, 2 as u32);
                v_constApprox_2327_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 3 as u32);
                v_isDefEqStuckEx_2328_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 4 as u32);
                v_unificationHints_2329_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 5 as u32);
                v_proofIrrelevance_2330_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 6 as u32);
                v_assignSyntheticOpaque_2331_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_2323_, 7 as u32);
                v_offsetCnstrs_2332_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 8 as u32);
                v_etaStruct_2333_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 10 as u32);
                v_univApprox_2334_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 11 as u32);
                v_iota_2335_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 12 as u32);
                v_beta_2336_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 13 as u32);
                v_proj_2337_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 14 as u32);
                v_zeta_2338_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 15 as u32);
                v_zetaDelta_2339_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 16 as u32);
                v_zetaUnused_2340_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 17 as u32);
                v_zetaHave_2341_ = crate::leanh::lean_ctor_get_uint8(v___x_2323_, 18 as u32);
                v_isSharedCheck_2378_ = (!crate::leanh::lean_is_exclusive(v___x_2323_)) as u8;
                if v_isSharedCheck_2378_ == 0 {
                    v___x_2343_ = v___x_2323_;
                    v_isShared_2344_ = v_isSharedCheck_2378_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_2323_);
                    v___x_2343_ = crate::leanh::lean_box(0);
                    v_isShared_2344_ = v_isSharedCheck_2378_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_2345_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_2346_ = crate::leanh::lean_ctor_get(v_a_2317_, 1);
                v_lctx_2347_ = crate::leanh::lean_ctor_get(v_a_2317_, 2);
                v_localInstances_2348_ = crate::leanh::lean_ctor_get(v_a_2317_, 3);
                v_defEqCtx_x3f_2349_ = crate::leanh::lean_ctor_get(v_a_2317_, 4);
                v_synthPendingDepth_2350_ = crate::leanh::lean_ctor_get(v_a_2317_, 5);
                v_canUnfold_x3f_2351_ = crate::leanh::lean_ctor_get(v_a_2317_, 6);
                v_univApprox_2352_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_2353_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_2354_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_2317_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_2355_ = 1;
                if v_isShared_2344_ == 0 {
                    v_config_2357_ = v___x_2343_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2377_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        0 as u32,
                        v_foApprox_2324_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        1 as u32,
                        v_ctxApprox_2325_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        2 as u32,
                        v_quasiPatternApprox_2326_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        3 as u32,
                        v_constApprox_2327_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        4 as u32,
                        v_isDefEqStuckEx_2328_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        5 as u32,
                        v_unificationHints_2329_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        6 as u32,
                        v_proofIrrelevance_2330_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        7 as u32,
                        v_assignSyntheticOpaque_2331_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        8 as u32,
                        v_offsetCnstrs_2332_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        10 as u32,
                        v_etaStruct_2333_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        11 as u32,
                        v_univApprox_2334_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        12 as u32,
                        v_iota_2335_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        13 as u32,
                        v_beta_2336_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        14 as u32,
                        v_proj_2337_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        15 as u32,
                        v_zeta_2338_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        16 as u32,
                        v_zetaDelta_2339_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        17 as u32,
                        v_zetaUnused_2340_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_2377_,
                        18 as u32,
                        v_zetaHave_2341_,
                    );
                    v_config_2357_ = v_reuseFailAlloc_2377_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_2357_, 9 as u32, v___x_2355_);
                v___x_2358_ = l_Lean_Meta_Context_configKey(v_a_2317_);
                v___x_2359_ = 3u64;
                v___x_2360_ = lean_uint64_shift_right(v___x_2358_, v___x_2359_);
                v___x_2361_ = lean_uint64_shift_left(v___x_2360_, v___x_2359_);
                v___x_2362_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___closed__0);
                v_key_2363_ = lean_uint64_lor(v___x_2361_, v___x_2362_);
                v___x_2364_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_2364_, 0, v_config_2357_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_2364_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_2363_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_2351_);
                crate::leanh::lean_inc(v_synthPendingDepth_2350_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_2349_);
                crate::leanh::lean_inc_ref(v_localInstances_2348_);
                crate::leanh::lean_inc_ref(v_lctx_2347_);
                crate::leanh::lean_inc(v_zetaDeltaSet_2346_);
                v___x_2365_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_2365_, 0, v___x_2364_);
                crate::leanh::lean_ctor_set(v___x_2365_, 1, v_zetaDeltaSet_2346_);
                crate::leanh::lean_ctor_set(v___x_2365_, 2, v_lctx_2347_);
                crate::leanh::lean_ctor_set(v___x_2365_, 3, v_localInstances_2348_);
                crate::leanh::lean_ctor_set(v___x_2365_, 4, v_defEqCtx_x3f_2349_);
                crate::leanh::lean_ctor_set(v___x_2365_, 5, v_synthPendingDepth_2350_);
                crate::leanh::lean_ctor_set(v___x_2365_, 6, v_canUnfold_x3f_2351_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2365_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_2345_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2365_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_2352_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2365_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_2353_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_2365_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_2354_,
                );
                crate::leanh::lean_inc(v_a_2320_);
                crate::leanh::lean_inc_ref(v_a_2319_);
                crate::leanh::lean_inc(v_a_2318_);
                crate::leanh::lean_inc_ref(v___x_2365_);
                v___x_2366_ =
                    lean_infer_type(v_self_2322_, v___x_2365_, v_a_2318_, v_a_2319_, v_a_2320_);
                if crate::leanh::lean_obj_tag(v___x_2366_) == 0 {
                    v_a_2367_ = crate::leanh::lean_ctor_get(v___x_2366_, 0);
                    crate::leanh::lean_inc(v_a_2367_);
                    crate::leanh::lean_dec_ref_known(v___x_2366_, 1);
                    v___x_2368_ = l_Lean_Meta_isExprDefEq(
                        v_a_2367_,
                        v_type_2315_,
                        v___x_2365_,
                        v_a_2318_,
                        v_a_2319_,
                        v_a_2320_,
                    );
                    crate::leanh::lean_dec_ref_known(v___x_2365_, 7);
                    return v___x_2368_;
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_2365_, 7);
                    crate::leanh::lean_dec_ref(v_type_2315_);
                    v_a_2369_ = crate::leanh::lean_ctor_get(v___x_2366_, 0);
                    v_isSharedCheck_2376_ = (!crate::leanh::lean_is_exclusive(v___x_2366_)) as u8;
                    if v_isSharedCheck_2376_ == 0 {
                        v___x_2371_ = v___x_2366_;
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2369_);
                        crate::leanh::lean_dec(v___x_2366_);
                        v___x_2371_ = crate::leanh::lean_box(0);
                        v_isShared_2372_ = v_isSharedCheck_2376_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2372_ == 0 {
                    v___x_2374_ = v___x_2371_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2375_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2375_, 0, v_a_2369_);
                    v___x_2374_ = v_reuseFailAlloc_2375_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2374_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed(
    mut v_type_2379_: *mut crate::leanh::LeanObject,
    mut v_n_2380_: *mut crate::leanh::LeanObject,
    mut v_a_2381_: *mut crate::leanh::LeanObject,
    mut v_a_2382_: *mut crate::leanh::LeanObject,
    mut v_a_2383_: *mut crate::leanh::LeanObject,
    mut v_a_2384_: *mut crate::leanh::LeanObject,
    mut v_a_2385_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2386_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_2379_, v_n_2380_, v_a_2381_, v_a_2382_, v_a_2383_, v_a_2384_);
    crate::leanh::lean_dec(v_a_2384_);
    crate::leanh::lean_dec_ref(v_a_2383_);
    crate::leanh::lean_dec(v_a_2382_);
    crate::leanh::lean_dec_ref(v_a_2381_);
    return v_res_2386_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(
    mut v_e_2398_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2400_: u8 = 0;
    v___x_2399_ = l_Lean_Expr_cleanupAnnotations(v_e_2398_);
    v___x_2400_ = l_Lean_Expr_isApp(v___x_2399_);
    if v___x_2400_ == 0 {
        let mut v___x_2401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_2399_);
        v___x_2401_ = crate::leanh::lean_box(0);
        return v___x_2401_;
    } else {
        let mut v_arg_2402_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_2404_: u8 = 0;
        v_arg_2402_ = crate::leanh::lean_ctor_get(v___x_2399_, 1);
        crate::leanh::lean_inc_ref(v_arg_2402_);
        v___x_2403_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2399_);
        v___x_2404_ = l_Lean_Expr_isApp(v___x_2403_);
        if v___x_2404_ == 0 {
            let mut v___x_2405_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_2403_);
            crate::leanh::lean_dec_ref(v_arg_2402_);
            v___x_2405_ = crate::leanh::lean_box(0);
            return v___x_2405_;
        } else {
            let mut v___x_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_2407_: u8 = 0;
            v___x_2406_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2403_);
            v___x_2407_ = l_Lean_Expr_isApp(v___x_2406_);
            if v___x_2407_ == 0 {
                let mut v___x_2408_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_2406_);
                crate::leanh::lean_dec_ref(v_arg_2402_);
                v___x_2408_ = crate::leanh::lean_box(0);
                return v___x_2408_;
            } else {
                let mut v___x_2409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_2411_: u8 = 0;
                v___x_2409_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2406_);
                v___x_2410_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f___closed__5;
                v___x_2411_ = l_Lean_Expr_isConstOf(v___x_2409_, v___x_2410_);
                crate::leanh::lean_dec_ref(v___x_2409_);
                if v___x_2411_ == 0 {
                    let mut v___x_2412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    crate::leanh::lean_dec_ref(v_arg_2402_);
                    v___x_2412_ = crate::leanh::lean_box(0);
                    return v___x_2412_;
                } else {
                    let mut v___x_2413_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    v___x_2413_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2413_, 0, v_arg_2402_);
                    return v___x_2413_;
                }
            }
        }
    }
}
pub unsafe fn l_Int_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__2(
    mut v_a_2414_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2415_ = l_Rat_ofInt(v_a_2414_);
    return v___x_2415_;
}
pub unsafe fn l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(
    mut v_a_2416_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2417_ = lean_nat_to_int(v_a_2416_);
    v___x_2418_ = l_Rat_ofInt(v___x_2417_);
    return v___x_2418_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(
    mut v_a_2419_: *mut crate::leanh::LeanObject,
    mut v_x_2420_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2422_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2423_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: u8 = 0;
    let mut v___x_2427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2420_) == 0 {
                    v___x_2421_ = crate::leanh::lean_box(0);
                    return v___x_2421_;
                } else {
                    v_key_2422_ = crate::leanh::lean_ctor_get(v_x_2420_, 0);
                    v_value_2423_ = crate::leanh::lean_ctor_get(v_x_2420_, 1);
                    v_tail_2424_ = crate::leanh::lean_ctor_get(v_x_2420_, 2);
                    v___x_2425_ = lean_expr_eqv(v_key_2422_, v_a_2419_);
                    if v___x_2425_ == 0 {
                        v_x_2420_ = v_tail_2424_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2423_);
                        v___x_2427_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2427_, 0, v_value_2423_);
                        return v___x_2427_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg___boxed(
    mut v_a_2428_: *mut crate::leanh::LeanObject,
    mut v_x_2429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2430_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_2428_, v_x_2429_);
    crate::leanh::lean_dec(v_x_2429_);
    crate::leanh::lean_dec_ref(v_a_2428_);
    return v_res_2430_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(
    mut v_m_2431_: *mut crate::leanh::LeanObject,
    mut v_a_2432_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: u64 = 0;
    let mut v___x_2436_: u64 = 0;
    let mut v___x_2437_: u64 = 0;
    let mut v_fold_2438_: u64 = 0;
    let mut v___x_2439_: u64 = 0;
    let mut v___x_2440_: u64 = 0;
    let mut v___x_2441_: u64 = 0;
    let mut v___x_2442_: usize = 0;
    let mut v___x_2443_: usize = 0;
    let mut v___x_2444_: usize = 0;
    let mut v___x_2445_: usize = 0;
    let mut v___x_2446_: usize = 0;
    let mut v___x_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2433_ = crate::leanh::lean_ctor_get(v_m_2431_, 1);
    v___x_2434_ = lean_array_get_size(v_buckets_2433_);
    v___x_2435_ = l_Lean_Expr_hash(v_a_2432_);
    v___x_2436_ = 32u64;
    v___x_2437_ = lean_uint64_shift_right(v___x_2435_, v___x_2436_);
    v_fold_2438_ = lean_uint64_xor(v___x_2435_, v___x_2437_);
    v___x_2439_ = 16u64;
    v___x_2440_ = lean_uint64_shift_right(v_fold_2438_, v___x_2439_);
    v___x_2441_ = lean_uint64_xor(v_fold_2438_, v___x_2440_);
    v___x_2442_ = lean_uint64_to_usize(v___x_2441_);
    v___x_2443_ = lean_usize_of_nat(v___x_2434_);
    v___x_2444_ = 1usize;
    v___x_2445_ = lean_usize_sub(v___x_2443_, v___x_2444_);
    v___x_2446_ = lean_usize_land(v___x_2442_, v___x_2445_);
    v___x_2447_ = lean_array_uget_borrowed(v_buckets_2433_, v___x_2446_);
    v___x_2448_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_2432_, v___x_2447_);
    return v___x_2448_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg___boxed(
    mut v_m_2449_: *mut crate::leanh::LeanObject,
    mut v_a_2450_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2451_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_2449_, v_a_2450_);
    crate::leanh::lean_dec_ref(v_a_2450_);
    crate::leanh::lean_dec_ref(v_m_2449_);
    return v_res_2451_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2487_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2487_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_2488_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v___x_2487_);
    return v___x_2488_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2489_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2490_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2489_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__21);
    v___x_2490_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
    crate::leanh::lean_ctor_set(v___x_2490_, 0, v___x_2489_);
    return v___x_2490_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(
    mut v_s_2491_: *mut crate::leanh::LeanObject,
    mut v_model_2492_: *mut crate::leanh::LeanObject,
    mut v_e_2493_: *mut crate::leanh::LeanObject,
    mut v_a_2494_: *mut crate::leanh::LeanObject,
    mut v_a_2495_: *mut crate::leanh::LeanObject,
    mut v_a_2496_: *mut crate::leanh::LeanObject,
    mut v_a_2497_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2505_: u8 = 0;
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: u8 = 0;
    let mut v_arg_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: u8 = 0;
    let mut v_arg_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2519_: u8 = 0;
    let mut v___x_2520_: u8 = 0;
    let mut v_arg_2521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2524_: u8 = 0;
    let mut v___x_2525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2526_: u8 = 0;
    let mut v___x_2527_: u8 = 0;
    let mut v___x_2528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2529_: u8 = 0;
    let mut v___x_2530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2531_: u8 = 0;
    let mut v___x_2532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2534_: u8 = 0;
    let mut v___x_2535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2536_: u8 = 0;
    let mut v___x_2537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2538_: u8 = 0;
    let mut v___x_2539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2540_: u8 = 0;
    let mut v___x_2541_: u8 = 0;
    let mut v___x_2542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2551_: u8 = 0;
    let mut v_val_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2555_: u8 = 0;
    let mut v___x_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2563_: u8 = 0;
    let mut v_isSharedCheck_2564_: u8 = 0;
    let mut v_unused_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2566_: u8 = 0;
    let mut v___x_2567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2570_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2576_: u8 = 0;
    let mut v_val_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2580_: u8 = 0;
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2588_: u8 = 0;
    let mut v_isSharedCheck_2589_: u8 = 0;
    let mut v_unused_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: u8 = 0;
    let mut v___x_2592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2601_: u8 = 0;
    let mut v_val_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2605_: u8 = 0;
    let mut v___x_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2610_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2613_: u8 = 0;
    let mut v_isSharedCheck_2614_: u8 = 0;
    let mut v_unused_2615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2616_: u8 = 0;
    let mut v___x_2617_: u8 = 0;
    let mut v___x_2618_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2624_: u8 = 0;
    let mut v___x_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2634_: u8 = 0;
    let mut v_val_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2638_: u8 = 0;
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2647_: u8 = 0;
    let mut v_isSharedCheck_2648_: u8 = 0;
    let mut v_unused_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2650_: u8 = 0;
    let mut v_a_2651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2654_: u8 = 0;
    let mut v___x_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2658_: u8 = 0;
    let mut v___x_2659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2663_: u8 = 0;
    let mut v___x_2664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2673_: u8 = 0;
    let mut v_val_2674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2676_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2677_: u8 = 0;
    let mut v___x_2678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2686_: u8 = 0;
    let mut v_isSharedCheck_2687_: u8 = 0;
    let mut v_unused_2688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2689_: u8 = 0;
    let mut v_a_2690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2693_: u8 = 0;
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2697_: u8 = 0;
    let mut v___x_2698_: u8 = 0;
    let mut v___x_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2704_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2705_: u8 = 0;
    let mut v_val_2706_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2717_: u8 = 0;
    let mut v_isSharedCheck_2718_: u8 = 0;
    let mut v_unused_2719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2724_: u8 = 0;
    let mut v___x_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2727_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2732_: u8 = 0;
    let mut v___x_2733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2740_: u8 = 0;
    let mut v_isSharedCheck_2741_: u8 = 0;
    let mut v_a_2742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2745_: u8 = 0;
    let mut v___x_2747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2749_: u8 = 0;
    let mut v___x_2750_: u8 = 0;
    let mut v___x_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2755_: u8 = 0;
    let mut v_a_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2759_: u8 = 0;
    let mut v___x_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2499_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_model_2492_, v_e_2493_);
                if crate::leanh::lean_obj_tag(v___x_2499_) == 1 {
                    crate::leanh::lean_dec_ref(v_e_2493_);
                    v___x_2500_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2500_, 0, v___x_2499_);
                    return v___x_2500_;
                } else {
                    crate::leanh::lean_dec(v___x_2499_);
                    v___x_2501_ =
                        l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(v_e_2493_, v_a_2495_);
                    if crate::leanh::lean_obj_tag(v___x_2501_) == 0 {
                        v_a_2502_ = crate::leanh::lean_ctor_get(v___x_2501_, 0);
                        v_isSharedCheck_2755_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2501_)) as u8;
                        if v_isSharedCheck_2755_ == 0 {
                            v___x_2504_ = v___x_2501_;
                            v_isShared_2505_ = v_isSharedCheck_2755_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2502_);
                            crate::leanh::lean_dec(v___x_2501_);
                            v___x_2504_ = crate::leanh::lean_box(0);
                            v_isShared_2505_ = v_isSharedCheck_2755_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2756_ = crate::leanh::lean_ctor_get(v___x_2501_, 0);
                        v_isSharedCheck_2763_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2501_)) as u8;
                        if v_isSharedCheck_2763_ == 0 {
                            v___x_2758_ = v___x_2501_;
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 43;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2756_);
                            crate::leanh::lean_dec(v___x_2501_);
                            v___x_2758_ = crate::leanh::lean_box(0);
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 43;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_2511_ = l_Lean_Expr_cleanupAnnotations(v_a_2502_);
                v___x_2512_ = l_Lean_Expr_isApp(v___x_2511_);
                if v___x_2512_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_2511_);
                    state = 2;
                    continue;
                } else {
                    v_arg_2513_ = crate::leanh::lean_ctor_get(v___x_2511_, 1);
                    crate::leanh::lean_inc_ref(v_arg_2513_);
                    v___x_2514_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2511_);
                    v___x_2515_ = l_Lean_Expr_isApp(v___x_2514_);
                    if v___x_2515_ == 0 {
                        crate::leanh::lean_dec_ref(v___x_2514_);
                        crate::leanh::lean_dec_ref(v_arg_2513_);
                        state = 2;
                        continue;
                    } else {
                        v_arg_2516_ = crate::leanh::lean_ctor_get(v___x_2514_, 1);
                        crate::leanh::lean_inc_ref(v_arg_2516_);
                        v___x_2517_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2514_);
                        v___x_2518_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__2;
                        v___x_2519_ = l_Lean_Expr_isConstOf(v___x_2517_, v___x_2518_);
                        if v___x_2519_ == 0 {
                            v___x_2520_ = l_Lean_Expr_isApp(v___x_2517_);
                            if v___x_2520_ == 0 {
                                crate::leanh::lean_dec_ref(v___x_2517_);
                                crate::leanh::lean_dec_ref(v_arg_2516_);
                                crate::leanh::lean_dec_ref(v_arg_2513_);
                                state = 2;
                                continue;
                            } else {
                                v_arg_2521_ = crate::leanh::lean_ctor_get(v___x_2517_, 1);
                                crate::leanh::lean_inc_ref(v_arg_2521_);
                                v___x_2522_ = l_Lean_Expr_appFnCleanup___redArg(v___x_2517_);
                                v___x_2523_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__5;
                                v___x_2524_ = l_Lean_Expr_isConstOf(v___x_2522_, v___x_2523_);
                                if v___x_2524_ == 0 {
                                    v___x_2525_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__8;
                                    v___x_2526_ = l_Lean_Expr_isConstOf(v___x_2522_, v___x_2525_);
                                    if v___x_2526_ == 0 {
                                        v___x_2527_ = l_Lean_Expr_isApp(v___x_2522_);
                                        if v___x_2527_ == 0 {
                                            crate::leanh::lean_dec_ref(v___x_2522_);
                                            crate::leanh::lean_dec_ref(v_arg_2521_);
                                            crate::leanh::lean_dec_ref(v_arg_2516_);
                                            crate::leanh::lean_dec_ref(v_arg_2513_);
                                            state = 2;
                                            continue;
                                        } else {
                                            v___x_2528_ =
                                                l_Lean_Expr_appFnCleanup___redArg(v___x_2522_);
                                            v___x_2529_ = l_Lean_Expr_isApp(v___x_2528_);
                                            if v___x_2529_ == 0 {
                                                crate::leanh::lean_dec_ref(v___x_2528_);
                                                crate::leanh::lean_dec_ref(v_arg_2521_);
                                                crate::leanh::lean_dec_ref(v_arg_2516_);
                                                crate::leanh::lean_dec_ref(v_arg_2513_);
                                                state = 2;
                                                continue;
                                            } else {
                                                v___x_2530_ =
                                                    l_Lean_Expr_appFnCleanup___redArg(v___x_2528_);
                                                v___x_2531_ = l_Lean_Expr_isApp(v___x_2530_);
                                                if v___x_2531_ == 0 {
                                                    crate::leanh::lean_dec_ref(v___x_2530_);
                                                    crate::leanh::lean_dec_ref(v_arg_2521_);
                                                    crate::leanh::lean_dec_ref(v_arg_2516_);
                                                    crate::leanh::lean_dec_ref(v_arg_2513_);
                                                    state = 2;
                                                    continue;
                                                } else {
                                                    v___x_2532_ = l_Lean_Expr_appFnCleanup___redArg(
                                                        v___x_2530_,
                                                    );
                                                    v___x_2533_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__11;
                                                    v___x_2534_ = l_Lean_Expr_isConstOf(
                                                        v___x_2532_,
                                                        v___x_2533_,
                                                    );
                                                    if v___x_2534_ == 0 {
                                                        v___x_2535_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__14;
                                                        v___x_2536_ = l_Lean_Expr_isConstOf(
                                                            v___x_2532_,
                                                            v___x_2535_,
                                                        );
                                                        if v___x_2536_ == 0 {
                                                            v___x_2537_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__17;
                                                            v___x_2538_ = l_Lean_Expr_isConstOf(
                                                                v___x_2532_,
                                                                v___x_2537_,
                                                            );
                                                            if v___x_2538_ == 0 {
                                                                v___x_2539_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__20;
                                                                v___x_2540_ = l_Lean_Expr_isConstOf(
                                                                    v___x_2532_,
                                                                    v___x_2539_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2532_,
                                                                );
                                                                if v___x_2540_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2521_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2516_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2513_,
                                                                    );
                                                                    state = 2;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_del_object(
                                                                        v___x_2504_,
                                                                    );
                                                                    v___x_2541_ = l_Lean_Meta_Grind_Arith_Linear_isAddInst(v_s_2491_, v_arg_2521_);
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2521_,
                                                                    );
                                                                    if v___x_2541_ == 0 {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2516_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2513_,
                                                                        );
                                                                        v___x_2542_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v___x_2543_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                        crate::leanh::lean_ctor_set(
                                                                            v___x_2543_,
                                                                            0,
                                                                            v___x_2542_,
                                                                        );
                                                                        return v___x_2543_;
                                                                    } else {
                                                                        v___x_2544_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2516_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
                                                                        if crate::leanh::lean_obj_tag(v___x_2544_) == 0 {
v_a_2545_ = crate::leanh::lean_ctor_get(v___x_2544_, 0);
crate::leanh::lean_inc(v_a_2545_);
if crate::leanh::lean_obj_tag(v_a_2545_) == 0 {
crate::leanh::lean_dec_ref(v_arg_2513_);
return v___x_2544_;
} else {
crate::leanh::lean_dec_ref_known(v___x_2544_, 1);
v_val_2546_ = crate::leanh::lean_ctor_get(v_a_2545_, 0);
crate::leanh::lean_inc(v_val_2546_);
crate::leanh::lean_dec_ref_known(v_a_2545_, 1);
v___x_2547_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2513_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
if crate::leanh::lean_obj_tag(v___x_2547_) == 0 {
v_a_2548_ = crate::leanh::lean_ctor_get(v___x_2547_, 0);
crate::leanh::lean_inc(v_a_2548_);
if crate::leanh::lean_obj_tag(v_a_2548_) == 0 {
crate::leanh::lean_dec(v_val_2546_);
return v___x_2547_;
} else {
v_isSharedCheck_2564_ = (!crate::leanh::lean_is_exclusive(v___x_2547_)) as u8;
if v_isSharedCheck_2564_ == 0 {
v_unused_2565_ = crate::leanh::lean_ctor_get(v___x_2547_, 0);
crate::leanh::lean_dec(v_unused_2565_);
v___x_2550_ = v___x_2547_;
v_isShared_2551_ = v_isSharedCheck_2564_;
state = 4; continue;
} else {
crate::leanh::lean_dec(v___x_2547_);
v___x_2550_ = crate::leanh::lean_box(0);
v_isShared_2551_ = v_isSharedCheck_2564_;
state = 4; continue;
}
}
} else {
crate::leanh::lean_dec(v_val_2546_);
return v___x_2547_;
}
}
} else {
crate::leanh::lean_dec_ref(v_arg_2513_);
return v___x_2544_;
}
                                                                    }
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v___x_2532_,
                                                                );
                                                                crate::leanh::lean_del_object(
                                                                    v___x_2504_,
                                                                );
                                                                v___x_2566_ = l_Lean_Meta_Grind_Arith_Linear_isSubInst(v_s_2491_, v_arg_2521_);
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2521_,
                                                                );
                                                                if v___x_2566_ == 0 {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2516_,
                                                                    );
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2513_,
                                                                    );
                                                                    v___x_2567_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v___x_2568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                                                    crate::leanh::lean_ctor_set(
                                                                        v___x_2568_,
                                                                        0,
                                                                        v___x_2567_,
                                                                    );
                                                                    return v___x_2568_;
                                                                } else {
                                                                    v___x_2569_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2516_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v___x_2569_,
                                                                    ) == 0
                                                                    {
                                                                        v_a_2570_ = crate::leanh::lean_ctor_get(v___x_2569_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2570_,
                                                                        );
                                                                        if crate::leanh::lean_obj_tag(v_a_2570_) == 0 {
crate::leanh::lean_dec_ref(v_arg_2513_);
return v___x_2569_;
} else {
crate::leanh::lean_dec_ref_known(v___x_2569_, 1);
v_val_2571_ = crate::leanh::lean_ctor_get(v_a_2570_, 0);
crate::leanh::lean_inc(v_val_2571_);
crate::leanh::lean_dec_ref_known(v_a_2570_, 1);
v___x_2572_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2513_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
if crate::leanh::lean_obj_tag(v___x_2572_) == 0 {
v_a_2573_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
crate::leanh::lean_inc(v_a_2573_);
if crate::leanh::lean_obj_tag(v_a_2573_) == 0 {
crate::leanh::lean_dec(v_val_2571_);
return v___x_2572_;
} else {
v_isSharedCheck_2589_ = (!crate::leanh::lean_is_exclusive(v___x_2572_)) as u8;
if v_isSharedCheck_2589_ == 0 {
v_unused_2590_ = crate::leanh::lean_ctor_get(v___x_2572_, 0);
crate::leanh::lean_dec(v_unused_2590_);
v___x_2575_ = v___x_2572_;
v_isShared_2576_ = v_isSharedCheck_2589_;
state = 8; continue;
} else {
crate::leanh::lean_dec(v___x_2572_);
v___x_2575_ = crate::leanh::lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2589_;
state = 8; continue;
}
}
} else {
crate::leanh::lean_dec(v_val_2571_);
return v___x_2572_;
}
}
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2513_,
                                                                        );
                                                                        return v___x_2569_;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v___x_2532_);
                                                            crate::leanh::lean_del_object(
                                                                v___x_2504_,
                                                            );
                                                            v___x_2591_ = l_Lean_Meta_Grind_Arith_Linear_isHomoMulInst(v_s_2491_, v_arg_2521_);
                                                            crate::leanh::lean_dec_ref(v_arg_2521_);
                                                            if v___x_2591_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2516_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2513_,
                                                                );
                                                                v___x_2592_ =
                                                                    crate::leanh::lean_box(0);
                                                                v___x_2593_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_2593_,
                                                                    0,
                                                                    v___x_2592_,
                                                                );
                                                                return v___x_2593_;
                                                            } else {
                                                                v___x_2594_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2516_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_2594_,
                                                                ) == 0
                                                                {
                                                                    v_a_2595_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2594_,
                                                                            0,
                                                                        );
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2595_,
                                                                    );
                                                                    if crate::leanh::lean_obj_tag(
                                                                        v_a_2595_,
                                                                    ) == 0
                                                                    {
                                                                        crate::leanh::lean_dec_ref(
                                                                            v_arg_2513_,
                                                                        );
                                                                        return v___x_2594_;
                                                                    } else {
                                                                        crate::leanh::lean_dec_ref_known(v___x_2594_, 1);
                                                                        v_val_2596_ = crate::leanh::lean_ctor_get(v_a_2595_, 0);
                                                                        crate::leanh::lean_inc(
                                                                            v_val_2596_,
                                                                        );
                                                                        crate::leanh::lean_dec_ref_known(v_a_2595_, 1);
                                                                        v___x_2597_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2513_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
                                                                        if crate::leanh::lean_obj_tag(v___x_2597_) == 0 {
v_a_2598_ = crate::leanh::lean_ctor_get(v___x_2597_, 0);
crate::leanh::lean_inc(v_a_2598_);
if crate::leanh::lean_obj_tag(v_a_2598_) == 0 {
crate::leanh::lean_dec(v_val_2596_);
return v___x_2597_;
} else {
v_isSharedCheck_2614_ = (!crate::leanh::lean_is_exclusive(v___x_2597_)) as u8;
if v_isSharedCheck_2614_ == 0 {
v_unused_2615_ = crate::leanh::lean_ctor_get(v___x_2597_, 0);
crate::leanh::lean_dec(v_unused_2615_);
v___x_2600_ = v___x_2597_;
v_isShared_2601_ = v_isSharedCheck_2614_;
state = 12; continue;
} else {
crate::leanh::lean_dec(v___x_2597_);
v___x_2600_ = crate::leanh::lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2614_;
state = 12; continue;
}
}
} else {
crate::leanh::lean_dec(v_val_2596_);
return v___x_2597_;
}
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2513_,
                                                                    );
                                                                    return v___x_2594_;
                                                                }
                                                            }
                                                        }
                                                    } else {
                                                        crate::leanh::lean_dec_ref(v___x_2532_);
                                                        crate::leanh::lean_del_object(v___x_2504_);
                                                        v___x_2616_ = l_Lean_Meta_Grind_Arith_Linear_isSMulIntInst(v_s_2491_, v_arg_2521_);
                                                        if v___x_2616_ == 0 {
                                                            v___x_2617_ = l_Lean_Meta_Grind_Arith_Linear_isSMulNatInst(v_s_2491_, v_arg_2521_);
                                                            crate::leanh::lean_dec_ref(v_arg_2521_);
                                                            if v___x_2617_ == 0 {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2516_,
                                                                );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2513_,
                                                                );
                                                                v___x_2618_ =
                                                                    crate::leanh::lean_box(0);
                                                                v___x_2619_ =
                                                                    crate::leanh::lean_alloc_ctor(
                                                                        0,
                                                                        1,
                                                                        (0) as u32,
                                                                    );
                                                                crate::leanh::lean_ctor_set(
                                                                    v___x_2619_,
                                                                    0,
                                                                    v___x_2618_,
                                                                );
                                                                return v___x_2619_;
                                                            } else {
                                                                v___x_2620_ =
                                                                    l_Lean_Meta_getNatValue_x3f(
                                                                        v_arg_2516_,
                                                                        v_a_2494_,
                                                                        v_a_2495_,
                                                                        v_a_2496_,
                                                                        v_a_2497_,
                                                                    );
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2516_,
                                                                );
                                                                if crate::leanh::lean_obj_tag(
                                                                    v___x_2620_,
                                                                ) == 0
                                                                {
                                                                    v_a_2621_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2620_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_2650_ = (!crate::leanh::lean_is_exclusive(v___x_2620_)) as u8;
                                                                    if v_isSharedCheck_2650_ == 0 {
                                                                        v___x_2623_ = v___x_2620_;
                                                                        v_isShared_2624_ =
                                                                            v_isSharedCheck_2650_;
                                                                        state = 16;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2621_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_2620_,
                                                                        );
                                                                        v___x_2623_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_2624_ =
                                                                            v_isSharedCheck_2650_;
                                                                        state = 16;
                                                                        continue;
                                                                    }
                                                                } else {
                                                                    crate::leanh::lean_dec_ref(
                                                                        v_arg_2513_,
                                                                    );
                                                                    v_a_2651_ =
                                                                        crate::leanh::lean_ctor_get(
                                                                            v___x_2620_,
                                                                            0,
                                                                        );
                                                                    v_isSharedCheck_2658_ = (!crate::leanh::lean_is_exclusive(v___x_2620_)) as u8;
                                                                    if v_isSharedCheck_2658_ == 0 {
                                                                        v___x_2653_ = v___x_2620_;
                                                                        v_isShared_2654_ =
                                                                            v_isSharedCheck_2658_;
                                                                        state = 22;
                                                                        continue;
                                                                    } else {
                                                                        crate::leanh::lean_inc(
                                                                            v_a_2651_,
                                                                        );
                                                                        crate::leanh::lean_dec(
                                                                            v___x_2620_,
                                                                        );
                                                                        v___x_2653_ =
                                                                            crate::leanh::lean_box(
                                                                                0,
                                                                            );
                                                                        v_isShared_2654_ =
                                                                            v_isSharedCheck_2658_;
                                                                        state = 22;
                                                                        continue;
                                                                    }
                                                                }
                                                            }
                                                        } else {
                                                            crate::leanh::lean_dec_ref(v_arg_2521_);
                                                            v___x_2659_ =
                                                                l_Lean_Meta_getIntValue_x3f(
                                                                    v_arg_2516_,
                                                                    v_a_2494_,
                                                                    v_a_2495_,
                                                                    v_a_2496_,
                                                                    v_a_2497_,
                                                                );
                                                            if crate::leanh::lean_obj_tag(
                                                                v___x_2659_,
                                                            ) == 0
                                                            {
                                                                v_a_2660_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_2659_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2689_ = (!crate::leanh::lean_is_exclusive(v___x_2659_)) as u8;
                                                                if v_isSharedCheck_2689_ == 0 {
                                                                    v___x_2662_ = v___x_2659_;
                                                                    v_isShared_2663_ =
                                                                        v_isSharedCheck_2689_;
                                                                    state = 24;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2660_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_2659_,
                                                                    );
                                                                    v___x_2662_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_2663_ =
                                                                        v_isSharedCheck_2689_;
                                                                    state = 24;
                                                                    continue;
                                                                }
                                                            } else {
                                                                crate::leanh::lean_dec_ref(
                                                                    v_arg_2513_,
                                                                );
                                                                v_a_2690_ =
                                                                    crate::leanh::lean_ctor_get(
                                                                        v___x_2659_,
                                                                        0,
                                                                    );
                                                                v_isSharedCheck_2697_ = (!crate::leanh::lean_is_exclusive(v___x_2659_)) as u8;
                                                                if v_isSharedCheck_2697_ == 0 {
                                                                    v___x_2692_ = v___x_2659_;
                                                                    v_isShared_2693_ =
                                                                        v_isSharedCheck_2697_;
                                                                    state = 30;
                                                                    continue;
                                                                } else {
                                                                    crate::leanh::lean_inc(
                                                                        v_a_2690_,
                                                                    );
                                                                    crate::leanh::lean_dec(
                                                                        v___x_2659_,
                                                                    );
                                                                    v___x_2692_ =
                                                                        crate::leanh::lean_box(0);
                                                                    v_isShared_2693_ =
                                                                        v_isSharedCheck_2697_;
                                                                    state = 30;
                                                                    continue;
                                                                }
                                                            }
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    } else {
                                        crate::leanh::lean_dec_ref(v___x_2522_);
                                        crate::leanh::lean_dec_ref(v_arg_2521_);
                                        crate::leanh::lean_del_object(v___x_2504_);
                                        v___x_2698_ = l_Lean_Meta_Grind_Arith_Linear_isNegInst(
                                            v_s_2491_,
                                            v_arg_2516_,
                                        );
                                        crate::leanh::lean_dec_ref(v_arg_2516_);
                                        if v___x_2698_ == 0 {
                                            crate::leanh::lean_dec_ref(v_arg_2513_);
                                            v___x_2699_ = crate::leanh::lean_box(0);
                                            v___x_2700_ =
                                                crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                            crate::leanh::lean_ctor_set(
                                                v___x_2700_,
                                                0,
                                                v___x_2699_,
                                            );
                                            return v___x_2700_;
                                        } else {
                                            v___x_2701_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2513_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
                                            if crate::leanh::lean_obj_tag(v___x_2701_) == 0 {
                                                v_a_2702_ =
                                                    crate::leanh::lean_ctor_get(v___x_2701_, 0);
                                                crate::leanh::lean_inc(v_a_2702_);
                                                if crate::leanh::lean_obj_tag(v_a_2702_) == 0 {
                                                    return v___x_2701_;
                                                } else {
                                                    v_isSharedCheck_2718_ =
                                                        (!crate::leanh::lean_is_exclusive(
                                                            v___x_2701_,
                                                        ))
                                                            as u8;
                                                    if v_isSharedCheck_2718_ == 0 {
                                                        v_unused_2719_ =
                                                            crate::leanh::lean_ctor_get(
                                                                v___x_2701_,
                                                                0,
                                                            );
                                                        crate::leanh::lean_dec(v_unused_2719_);
                                                        v___x_2704_ = v___x_2701_;
                                                        v_isShared_2705_ = v_isSharedCheck_2718_;
                                                        state = 32;
                                                        continue;
                                                    } else {
                                                        crate::leanh::lean_dec(v___x_2701_);
                                                        v___x_2704_ = crate::leanh::lean_box(0);
                                                        v_isShared_2705_ = v_isSharedCheck_2718_;
                                                        state = 32;
                                                        continue;
                                                    }
                                                }
                                            } else {
                                                return v___x_2701_;
                                            }
                                        }
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v___x_2522_);
                                    crate::leanh::lean_dec_ref(v_arg_2521_);
                                    crate::leanh::lean_dec_ref(v_arg_2513_);
                                    crate::leanh::lean_del_object(v___x_2504_);
                                    v___x_2720_ = l_Lean_Meta_getNatValue_x3f(
                                        v_arg_2516_,
                                        v_a_2494_,
                                        v_a_2495_,
                                        v_a_2496_,
                                        v_a_2497_,
                                    );
                                    crate::leanh::lean_dec_ref(v_arg_2516_);
                                    if crate::leanh::lean_obj_tag(v___x_2720_) == 0 {
                                        v_a_2721_ = crate::leanh::lean_ctor_get(v___x_2720_, 0);
                                        v_isSharedCheck_2741_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2720_)) as u8;
                                        if v_isSharedCheck_2741_ == 0 {
                                            v___x_2723_ = v___x_2720_;
                                            v_isShared_2724_ = v_isSharedCheck_2741_;
                                            state = 36;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2721_);
                                            crate::leanh::lean_dec(v___x_2720_);
                                            v___x_2723_ = crate::leanh::lean_box(0);
                                            v_isShared_2724_ = v_isSharedCheck_2741_;
                                            state = 36;
                                            continue;
                                        }
                                    } else {
                                        v_a_2742_ = crate::leanh::lean_ctor_get(v___x_2720_, 0);
                                        v_isSharedCheck_2749_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_2720_)) as u8;
                                        if v_isSharedCheck_2749_ == 0 {
                                            v___x_2744_ = v___x_2720_;
                                            v_isShared_2745_ = v_isSharedCheck_2749_;
                                            state = 41;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_2742_);
                                            crate::leanh::lean_dec(v___x_2720_);
                                            v___x_2744_ = crate::leanh::lean_box(0);
                                            v_isShared_2745_ = v_isSharedCheck_2749_;
                                            state = 41;
                                            continue;
                                        }
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec_ref(v___x_2517_);
                            crate::leanh::lean_dec_ref(v_arg_2516_);
                            crate::leanh::lean_del_object(v___x_2504_);
                            v___x_2750_ =
                                l_Lean_Meta_Grind_Arith_Linear_isZeroInst(v_s_2491_, v_arg_2513_);
                            crate::leanh::lean_dec_ref(v_arg_2513_);
                            if v___x_2750_ == 0 {
                                v___x_2751_ = crate::leanh::lean_box(0);
                                v___x_2752_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2752_, 0, v___x_2751_);
                                return v___x_2752_;
                            } else {
                                v___x_2753_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___closed__22);
                                v___x_2754_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_2754_, 0, v___x_2753_);
                                return v___x_2754_;
                            }
                        }
                    }
                }
            }
            2 => {
                v___x_2507_ = crate::leanh::lean_box(0);
                if v_isShared_2505_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2504_, 0, v___x_2507_);
                    v___x_2509_ = v___x_2504_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2510_, 0, v___x_2507_);
                    v___x_2509_ = v_reuseFailAlloc_2510_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_2509_;
            }
            4 => {
                v_val_2552_ = crate::leanh::lean_ctor_get(v_a_2548_, 0);
                v_isSharedCheck_2563_ = (!crate::leanh::lean_is_exclusive(v_a_2548_)) as u8;
                if v_isSharedCheck_2563_ == 0 {
                    v___x_2554_ = v_a_2548_;
                    v_isShared_2555_ = v_isSharedCheck_2563_;
                    state = 5;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2552_);
                    crate::leanh::lean_dec(v_a_2548_);
                    v___x_2554_ = crate::leanh::lean_box(0);
                    v_isShared_2555_ = v_isSharedCheck_2563_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                v___x_2556_ = l_Rat_add(v_val_2546_, v_val_2552_);
                if v_isShared_2555_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2554_, 0, v___x_2556_);
                    v___x_2558_ = v___x_2554_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2562_, 0, v___x_2556_);
                    v___x_2558_ = v_reuseFailAlloc_2562_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2551_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2550_, 0, v___x_2558_);
                    v___x_2560_ = v___x_2550_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2561_, 0, v___x_2558_);
                    v___x_2560_ = v_reuseFailAlloc_2561_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2560_;
            }
            8 => {
                v_val_2577_ = crate::leanh::lean_ctor_get(v_a_2573_, 0);
                v_isSharedCheck_2588_ = (!crate::leanh::lean_is_exclusive(v_a_2573_)) as u8;
                if v_isSharedCheck_2588_ == 0 {
                    v___x_2579_ = v_a_2573_;
                    v_isShared_2580_ = v_isSharedCheck_2588_;
                    state = 9;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2577_);
                    crate::leanh::lean_dec(v_a_2573_);
                    v___x_2579_ = crate::leanh::lean_box(0);
                    v_isShared_2580_ = v_isSharedCheck_2588_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                v___x_2581_ = l_Rat_sub(v_val_2571_, v_val_2577_);
                if v_isShared_2580_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2579_, 0, v___x_2581_);
                    v___x_2583_ = v___x_2579_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2587_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2587_, 0, v___x_2581_);
                    v___x_2583_ = v_reuseFailAlloc_2587_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                if v_isShared_2576_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2575_, 0, v___x_2583_);
                    v___x_2585_ = v___x_2575_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_2586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
                    v___x_2585_ = v_reuseFailAlloc_2586_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_2585_;
            }
            12 => {
                v_val_2602_ = crate::leanh::lean_ctor_get(v_a_2598_, 0);
                v_isSharedCheck_2613_ = (!crate::leanh::lean_is_exclusive(v_a_2598_)) as u8;
                if v_isSharedCheck_2613_ == 0 {
                    v___x_2604_ = v_a_2598_;
                    v_isShared_2605_ = v_isSharedCheck_2613_;
                    state = 13;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2602_);
                    crate::leanh::lean_dec(v_a_2598_);
                    v___x_2604_ = crate::leanh::lean_box(0);
                    v_isShared_2605_ = v_isSharedCheck_2613_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                v___x_2606_ = l_Rat_mul(v_val_2596_, v_val_2602_);
                crate::leanh::lean_dec(v_val_2596_);
                if v_isShared_2605_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2604_, 0, v___x_2606_);
                    v___x_2608_ = v___x_2604_;
                    state = 14;
                    continue;
                } else {
                    v_reuseFailAlloc_2612_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2606_);
                    v___x_2608_ = v_reuseFailAlloc_2612_;
                    state = 14;
                    continue;
                }
            }
            14 => {
                if v_isShared_2601_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2600_, 0, v___x_2608_);
                    v___x_2610_ = v___x_2600_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_2611_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2611_, 0, v___x_2608_);
                    v___x_2610_ = v_reuseFailAlloc_2611_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_2610_;
            }
            16 => {
                if crate::leanh::lean_obj_tag(v_a_2621_) == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2513_);
                    v___x_2625_ = crate::leanh::lean_box(0);
                    if v_isShared_2624_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2625_);
                        v___x_2627_ = v___x_2623_;
                        state = 17;
                        continue;
                    } else {
                        v_reuseFailAlloc_2628_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2628_, 0, v___x_2625_);
                        v___x_2627_ = v_reuseFailAlloc_2628_;
                        state = 17;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2623_);
                    v_val_2629_ = crate::leanh::lean_ctor_get(v_a_2621_, 0);
                    crate::leanh::lean_inc(v_val_2629_);
                    crate::leanh::lean_dec_ref_known(v_a_2621_, 1);
                    v___x_2630_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2513_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
                    if crate::leanh::lean_obj_tag(v___x_2630_) == 0 {
                        v_a_2631_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
                        crate::leanh::lean_inc(v_a_2631_);
                        if crate::leanh::lean_obj_tag(v_a_2631_) == 0 {
                            crate::leanh::lean_dec(v_val_2629_);
                            return v___x_2630_;
                        } else {
                            v_isSharedCheck_2648_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2630_)) as u8;
                            if v_isSharedCheck_2648_ == 0 {
                                v_unused_2649_ = crate::leanh::lean_ctor_get(v___x_2630_, 0);
                                crate::leanh::lean_dec(v_unused_2649_);
                                v___x_2633_ = v___x_2630_;
                                v_isShared_2634_ = v_isSharedCheck_2648_;
                                state = 18;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2630_);
                                v___x_2633_ = crate::leanh::lean_box(0);
                                v_isShared_2634_ = v_isSharedCheck_2648_;
                                state = 18;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2629_);
                        return v___x_2630_;
                    }
                }
            }
            17 => {
                return v___x_2627_;
            }
            18 => {
                v_val_2635_ = crate::leanh::lean_ctor_get(v_a_2631_, 0);
                v_isSharedCheck_2647_ = (!crate::leanh::lean_is_exclusive(v_a_2631_)) as u8;
                if v_isSharedCheck_2647_ == 0 {
                    v___x_2637_ = v_a_2631_;
                    v_isShared_2638_ = v_isSharedCheck_2647_;
                    state = 19;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2635_);
                    crate::leanh::lean_dec(v_a_2631_);
                    v___x_2637_ = crate::leanh::lean_box(0);
                    v_isShared_2638_ = v_isSharedCheck_2647_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                v___x_2639_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_2629_);
                v___x_2640_ = l_Rat_mul(v___x_2639_, v_val_2635_);
                crate::leanh::lean_dec_ref(v___x_2639_);
                if v_isShared_2638_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2637_, 0, v___x_2640_);
                    v___x_2642_ = v___x_2637_;
                    state = 20;
                    continue;
                } else {
                    v_reuseFailAlloc_2646_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2646_, 0, v___x_2640_);
                    v___x_2642_ = v_reuseFailAlloc_2646_;
                    state = 20;
                    continue;
                }
            }
            20 => {
                if v_isShared_2634_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2633_, 0, v___x_2642_);
                    v___x_2644_ = v___x_2633_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_2645_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
                    v___x_2644_ = v_reuseFailAlloc_2645_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_2644_;
            }
            22 => {
                if v_isShared_2654_ == 0 {
                    v___x_2656_ = v___x_2653_;
                    state = 23;
                    continue;
                } else {
                    v_reuseFailAlloc_2657_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_a_2651_);
                    v___x_2656_ = v_reuseFailAlloc_2657_;
                    state = 23;
                    continue;
                }
            }
            23 => {
                return v___x_2656_;
            }
            24 => {
                if crate::leanh::lean_obj_tag(v_a_2660_) == 0 {
                    crate::leanh::lean_dec_ref(v_arg_2513_);
                    v___x_2664_ = crate::leanh::lean_box(0);
                    if v_isShared_2663_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2662_, 0, v___x_2664_);
                        v___x_2666_ = v___x_2662_;
                        state = 25;
                        continue;
                    } else {
                        v_reuseFailAlloc_2667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2667_, 0, v___x_2664_);
                        v___x_2666_ = v_reuseFailAlloc_2667_;
                        state = 25;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2662_);
                    v_val_2668_ = crate::leanh::lean_ctor_get(v_a_2660_, 0);
                    crate::leanh::lean_inc(v_val_2668_);
                    crate::leanh::lean_dec_ref_known(v_a_2660_, 1);
                    v___x_2669_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2491_, v_model_2492_, v_arg_2513_, v_a_2494_, v_a_2495_, v_a_2496_, v_a_2497_);
                    if crate::leanh::lean_obj_tag(v___x_2669_) == 0 {
                        v_a_2670_ = crate::leanh::lean_ctor_get(v___x_2669_, 0);
                        crate::leanh::lean_inc(v_a_2670_);
                        if crate::leanh::lean_obj_tag(v_a_2670_) == 0 {
                            crate::leanh::lean_dec(v_val_2668_);
                            return v___x_2669_;
                        } else {
                            v_isSharedCheck_2687_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2669_)) as u8;
                            if v_isSharedCheck_2687_ == 0 {
                                v_unused_2688_ = crate::leanh::lean_ctor_get(v___x_2669_, 0);
                                crate::leanh::lean_dec(v_unused_2688_);
                                v___x_2672_ = v___x_2669_;
                                v_isShared_2673_ = v_isSharedCheck_2687_;
                                state = 26;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2669_);
                                v___x_2672_ = crate::leanh::lean_box(0);
                                v_isShared_2673_ = v_isSharedCheck_2687_;
                                state = 26;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v_val_2668_);
                        return v___x_2669_;
                    }
                }
            }
            25 => {
                return v___x_2666_;
            }
            26 => {
                v_val_2674_ = crate::leanh::lean_ctor_get(v_a_2670_, 0);
                v_isSharedCheck_2686_ = (!crate::leanh::lean_is_exclusive(v_a_2670_)) as u8;
                if v_isSharedCheck_2686_ == 0 {
                    v___x_2676_ = v_a_2670_;
                    v_isShared_2677_ = v_isSharedCheck_2686_;
                    state = 27;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2674_);
                    crate::leanh::lean_dec(v_a_2670_);
                    v___x_2676_ = crate::leanh::lean_box(0);
                    v_isShared_2677_ = v_isSharedCheck_2686_;
                    state = 27;
                    continue;
                }
            }
            27 => {
                v___x_2678_ = l_Rat_ofInt(v_val_2668_);
                v___x_2679_ = l_Rat_mul(v___x_2678_, v_val_2674_);
                crate::leanh::lean_dec_ref(v___x_2678_);
                if v_isShared_2677_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2676_, 0, v___x_2679_);
                    v___x_2681_ = v___x_2676_;
                    state = 28;
                    continue;
                } else {
                    v_reuseFailAlloc_2685_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2685_, 0, v___x_2679_);
                    v___x_2681_ = v_reuseFailAlloc_2685_;
                    state = 28;
                    continue;
                }
            }
            28 => {
                if v_isShared_2673_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2672_, 0, v___x_2681_);
                    v___x_2683_ = v___x_2672_;
                    state = 29;
                    continue;
                } else {
                    v_reuseFailAlloc_2684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2684_, 0, v___x_2681_);
                    v___x_2683_ = v_reuseFailAlloc_2684_;
                    state = 29;
                    continue;
                }
            }
            29 => {
                return v___x_2683_;
            }
            30 => {
                if v_isShared_2693_ == 0 {
                    v___x_2695_ = v___x_2692_;
                    state = 31;
                    continue;
                } else {
                    v_reuseFailAlloc_2696_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2690_);
                    v___x_2695_ = v_reuseFailAlloc_2696_;
                    state = 31;
                    continue;
                }
            }
            31 => {
                return v___x_2695_;
            }
            32 => {
                v_val_2706_ = crate::leanh::lean_ctor_get(v_a_2702_, 0);
                v_isSharedCheck_2717_ = (!crate::leanh::lean_is_exclusive(v_a_2702_)) as u8;
                if v_isSharedCheck_2717_ == 0 {
                    v___x_2708_ = v_a_2702_;
                    v_isShared_2709_ = v_isSharedCheck_2717_;
                    state = 33;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_val_2706_);
                    crate::leanh::lean_dec(v_a_2702_);
                    v___x_2708_ = crate::leanh::lean_box(0);
                    v_isShared_2709_ = v_isSharedCheck_2717_;
                    state = 33;
                    continue;
                }
            }
            33 => {
                v___x_2710_ = l_Rat_neg(v_val_2706_);
                if v_isShared_2709_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2708_, 0, v___x_2710_);
                    v___x_2712_ = v___x_2708_;
                    state = 34;
                    continue;
                } else {
                    v_reuseFailAlloc_2716_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2716_, 0, v___x_2710_);
                    v___x_2712_ = v_reuseFailAlloc_2716_;
                    state = 34;
                    continue;
                }
            }
            34 => {
                if v_isShared_2705_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2704_, 0, v___x_2712_);
                    v___x_2714_ = v___x_2704_;
                    state = 35;
                    continue;
                } else {
                    v_reuseFailAlloc_2715_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2715_, 0, v___x_2712_);
                    v___x_2714_ = v_reuseFailAlloc_2715_;
                    state = 35;
                    continue;
                }
            }
            35 => {
                return v___x_2714_;
            }
            36 => {
                if crate::leanh::lean_obj_tag(v_a_2721_) == 0 {
                    v___x_2725_ = crate::leanh::lean_box(0);
                    if v_isShared_2724_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2723_, 0, v___x_2725_);
                        v___x_2727_ = v___x_2723_;
                        state = 37;
                        continue;
                    } else {
                        v_reuseFailAlloc_2728_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
                        v___x_2727_ = v_reuseFailAlloc_2728_;
                        state = 37;
                        continue;
                    }
                } else {
                    v_val_2729_ = crate::leanh::lean_ctor_get(v_a_2721_, 0);
                    v_isSharedCheck_2740_ = (!crate::leanh::lean_is_exclusive(v_a_2721_)) as u8;
                    if v_isSharedCheck_2740_ == 0 {
                        v___x_2731_ = v_a_2721_;
                        v_isShared_2732_ = v_isSharedCheck_2740_;
                        state = 38;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_2729_);
                        crate::leanh::lean_dec(v_a_2721_);
                        v___x_2731_ = crate::leanh::lean_box(0);
                        v_isShared_2732_ = v_isSharedCheck_2740_;
                        state = 38;
                        continue;
                    }
                }
            }
            37 => {
                return v___x_2727_;
            }
            38 => {
                v___x_2733_ = l_Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1(v_val_2729_);
                if v_isShared_2732_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2731_, 0, v___x_2733_);
                    v___x_2735_ = v___x_2731_;
                    state = 39;
                    continue;
                } else {
                    v_reuseFailAlloc_2739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2733_);
                    v___x_2735_ = v_reuseFailAlloc_2739_;
                    state = 39;
                    continue;
                }
            }
            39 => {
                if v_isShared_2724_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2723_, 0, v___x_2735_);
                    v___x_2737_ = v___x_2723_;
                    state = 40;
                    continue;
                } else {
                    v_reuseFailAlloc_2738_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2735_);
                    v___x_2737_ = v_reuseFailAlloc_2738_;
                    state = 40;
                    continue;
                }
            }
            40 => {
                return v___x_2737_;
            }
            41 => {
                if v_isShared_2745_ == 0 {
                    v___x_2747_ = v___x_2744_;
                    state = 42;
                    continue;
                } else {
                    v_reuseFailAlloc_2748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2748_, 0, v_a_2742_);
                    v___x_2747_ = v_reuseFailAlloc_2748_;
                    state = 42;
                    continue;
                }
            }
            42 => {
                return v___x_2747_;
            }
            43 => {
                if v_isShared_2759_ == 0 {
                    v___x_2761_ = v___x_2758_;
                    state = 44;
                    continue;
                } else {
                    v_reuseFailAlloc_2762_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
                    v___x_2761_ = v_reuseFailAlloc_2762_;
                    state = 44;
                    continue;
                }
            }
            44 => {
                return v___x_2761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go___boxed(
    mut v_s_2764_: *mut crate::leanh::LeanObject,
    mut v_model_2765_: *mut crate::leanh::LeanObject,
    mut v_e_2766_: *mut crate::leanh::LeanObject,
    mut v_a_2767_: *mut crate::leanh::LeanObject,
    mut v_a_2768_: *mut crate::leanh::LeanObject,
    mut v_a_2769_: *mut crate::leanh::LeanObject,
    mut v_a_2770_: *mut crate::leanh::LeanObject,
    mut v_a_2771_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2772_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2764_, v_model_2765_, v_e_2766_, v_a_2767_, v_a_2768_, v_a_2769_, v_a_2770_);
    crate::leanh::lean_dec(v_a_2770_);
    crate::leanh::lean_dec_ref(v_a_2769_);
    crate::leanh::lean_dec(v_a_2768_);
    crate::leanh::lean_dec_ref(v_a_2767_);
    crate::leanh::lean_dec_ref(v_model_2765_);
    crate::leanh::lean_dec_ref(v_s_2764_);
    return v_res_2772_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(
    mut v_00_u03b2_2773_: *mut crate::leanh::LeanObject,
    mut v_m_2774_: *mut crate::leanh::LeanObject,
    mut v_a_2775_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2776_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_m_2774_, v_a_2775_);
    return v___x_2776_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___boxed(
    mut v_00_u03b2_2777_: *mut crate::leanh::LeanObject,
    mut v_m_2778_: *mut crate::leanh::LeanObject,
    mut v_a_2779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2780_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0(v_00_u03b2_2777_, v_m_2778_, v_a_2779_);
    crate::leanh::lean_dec_ref(v_a_2779_);
    crate::leanh::lean_dec_ref(v_m_2778_);
    return v_res_2780_;
}
pub unsafe fn l_Nat_cast___at___00Nat_cast___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__1_spec__2(
    mut v_a_2781_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2782_ = lean_nat_to_int(v_a_2781_);
    return v___x_2782_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(
    mut v_00_u03b2_2783_: *mut crate::leanh::LeanObject,
    mut v_a_2784_: *mut crate::leanh::LeanObject,
    mut v_x_2785_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2786_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___redArg(v_a_2784_, v_x_2785_);
    return v___x_2786_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0___boxed(
    mut v_00_u03b2_2787_: *mut crate::leanh::LeanObject,
    mut v_a_2788_: *mut crate::leanh::LeanObject,
    mut v_x_2789_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2790_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0_spec__0(v_00_u03b2_2787_, v_a_2788_, v_x_2789_);
    crate::leanh::lean_dec(v_x_2789_);
    crate::leanh::lean_dec_ref(v_a_2788_);
    return v_res_2790_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(
    mut v_e_2791_: *mut crate::leanh::LeanObject,
    mut v_s_2792_: *mut crate::leanh::LeanObject,
    mut v_model_2793_: *mut crate::leanh::LeanObject,
    mut v_a_2794_: *mut crate::leanh::LeanObject,
    mut v_a_2795_: *mut crate::leanh::LeanObject,
    mut v_a_2796_: *mut crate::leanh::LeanObject,
    mut v_a_2797_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2799_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v_s_2792_, v_model_2793_, v_e_2791_, v_a_2794_, v_a_2795_, v_a_2796_, v_a_2797_);
    return v___x_2799_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f___boxed(
    mut v_e_2800_: *mut crate::leanh::LeanObject,
    mut v_s_2801_: *mut crate::leanh::LeanObject,
    mut v_model_2802_: *mut crate::leanh::LeanObject,
    mut v_a_2803_: *mut crate::leanh::LeanObject,
    mut v_a_2804_: *mut crate::leanh::LeanObject,
    mut v_a_2805_: *mut crate::leanh::LeanObject,
    mut v_a_2806_: *mut crate::leanh::LeanObject,
    mut v_a_2807_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2808_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f(v_e_2800_, v_s_2801_, v_model_2802_, v_a_2803_, v_a_2804_, v_a_2805_, v_a_2806_);
    crate::leanh::lean_dec(v_a_2806_);
    crate::leanh::lean_dec_ref(v_a_2805_);
    crate::leanh::lean_dec(v_a_2804_);
    crate::leanh::lean_dec_ref(v_a_2803_);
    crate::leanh::lean_dec_ref(v_model_2802_);
    crate::leanh::lean_dec_ref(v_s_2801_);
    return v_res_2808_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(
    mut v_a_2809_: *mut crate::leanh::LeanObject,
    mut v_x_2810_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_2811_: u8 = 0;
    let mut v_key_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2810_) == 0 {
                    v___x_2811_ = 0;
                    return v___x_2811_;
                } else {
                    v_key_2812_ = crate::leanh::lean_ctor_get(v_x_2810_, 0);
                    v_tail_2813_ = crate::leanh::lean_ctor_get(v_x_2810_, 2);
                    v___x_2814_ = lean_expr_eqv(v_key_2812_, v_a_2809_);
                    if v___x_2814_ == 0 {
                        v_x_2810_ = v_tail_2813_;
                        state = 0;
                        continue;
                    } else {
                        return v___x_2814_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg___boxed(
    mut v_a_2816_: *mut crate::leanh::LeanObject,
    mut v_x_2817_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2818_: u8 = 0;
    let mut v_r_2819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2818_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_2816_, v_x_2817_);
    crate::leanh::lean_dec(v_x_2817_);
    crate::leanh::lean_dec_ref(v_a_2816_);
    v_r_2819_ = crate::leanh::lean_box((v_res_2818_) as usize);
    return v_r_2819_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(
    mut v_m_2820_: *mut crate::leanh::LeanObject,
    mut v_a_2821_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_buckets_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: u64 = 0;
    let mut v___x_2825_: u64 = 0;
    let mut v___x_2826_: u64 = 0;
    let mut v_fold_2827_: u64 = 0;
    let mut v___x_2828_: u64 = 0;
    let mut v___x_2829_: u64 = 0;
    let mut v___x_2830_: u64 = 0;
    let mut v___x_2831_: usize = 0;
    let mut v___x_2832_: usize = 0;
    let mut v___x_2833_: usize = 0;
    let mut v___x_2834_: usize = 0;
    let mut v___x_2835_: usize = 0;
    let mut v___x_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2837_: u8 = 0;
    v_buckets_2822_ = crate::leanh::lean_ctor_get(v_m_2820_, 1);
    v___x_2823_ = lean_array_get_size(v_buckets_2822_);
    v___x_2824_ = l_Lean_Expr_hash(v_a_2821_);
    v___x_2825_ = 32u64;
    v___x_2826_ = lean_uint64_shift_right(v___x_2824_, v___x_2825_);
    v_fold_2827_ = lean_uint64_xor(v___x_2824_, v___x_2826_);
    v___x_2828_ = 16u64;
    v___x_2829_ = lean_uint64_shift_right(v_fold_2827_, v___x_2828_);
    v___x_2830_ = lean_uint64_xor(v_fold_2827_, v___x_2829_);
    v___x_2831_ = lean_uint64_to_usize(v___x_2830_);
    v___x_2832_ = lean_usize_of_nat(v___x_2823_);
    v___x_2833_ = 1usize;
    v___x_2834_ = lean_usize_sub(v___x_2832_, v___x_2833_);
    v___x_2835_ = lean_usize_land(v___x_2831_, v___x_2834_);
    v___x_2836_ = lean_array_uget_borrowed(v_buckets_2822_, v___x_2835_);
    v___x_2837_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_2821_, v___x_2836_);
    return v___x_2837_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg___boxed(
    mut v_m_2838_: *mut crate::leanh::LeanObject,
    mut v_a_2839_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2840_: u8 = 0;
    let mut v_r_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2840_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_2838_, v_a_2839_);
    crate::leanh::lean_dec_ref(v_a_2839_);
    crate::leanh::lean_dec_ref(v_m_2838_);
    v_r_2841_ = crate::leanh::lean_box((v_res_2840_) as usize);
    return v_r_2841_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(
    mut v___x_2842_: *mut crate::leanh::LeanObject,
    mut v_goal_2843_: *mut crate::leanh::LeanObject,
    mut v_structId_2844_: *mut crate::leanh::LeanObject,
    mut v_as_2845_: *mut crate::leanh::LeanObject,
    mut v_sz_2846_: usize,
    mut v_i_2847_: usize,
    mut v_b_2848_: *mut crate::leanh::LeanObject,
    mut v___y_2849_: *mut crate::leanh::LeanObject,
    mut v___y_2850_: *mut crate::leanh::LeanObject,
    mut v___y_2851_: *mut crate::leanh::LeanObject,
    mut v___y_2852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2854_: u8 = 0;
    let mut v___x_2855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2862_: u8 = 0;
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2868_: usize = 0;
    let mut v___x_2869_: usize = 0;
    let mut v_reuseFailAlloc_2871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2873_: u8 = 0;
    let mut v___x_2874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2881_: u8 = 0;
    let mut v___x_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2885_: u8 = 0;
    let mut v___x_2886_: u8 = 0;
    let mut v___x_2887_: u8 = 0;
    let mut v_isSharedCheck_2888_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2854_ = lean_usize_dec_lt(v_i_2847_, v_sz_2846_);
                if v___x_2854_ == 0 {
                    v___x_2855_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2855_, 0, v_b_2848_);
                    return v___x_2855_;
                } else {
                    v_snd_2856_ = crate::leanh::lean_ctor_get(v_b_2848_, 1);
                    crate::leanh::lean_inc(v_snd_2856_);
                    crate::leanh::lean_dec_ref(v_b_2848_);
                    v_a_2857_ = lean_array_uget(v_as_2845_, v_i_2847_);
                    v_fst_2858_ = crate::leanh::lean_ctor_get(v_a_2857_, 0);
                    v_snd_2859_ = crate::leanh::lean_ctor_get(v_a_2857_, 1);
                    v_isSharedCheck_2888_ = (!crate::leanh::lean_is_exclusive(v_a_2857_)) as u8;
                    if v_isSharedCheck_2888_ == 0 {
                        v___x_2861_ = v_a_2857_;
                        v_isShared_2862_ = v_isSharedCheck_2888_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2859_);
                        crate::leanh::lean_inc(v_fst_2858_);
                        crate::leanh::lean_dec(v_a_2857_);
                        v___x_2861_ = crate::leanh::lean_box(0);
                        v_isShared_2862_ = v_isSharedCheck_2888_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2863_ = crate::leanh::lean_box(0);
                v___x_2886_ = lean_nat_dec_eq(v_structId_2844_, v_snd_2859_);
                crate::leanh::lean_dec(v_snd_2859_);
                if v___x_2886_ == 0 {
                    v___y_2873_ = v___x_2886_;
                    state = 4;
                    continue;
                } else {
                    v___x_2887_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_2856_, v_fst_2858_);
                    if v___x_2887_ == 0 {
                        v___y_2873_ = v___x_2886_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_2858_);
                        v_a_2865_ = v_snd_2856_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2862_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2861_, 1, v_a_2865_);
                    crate::leanh::lean_ctor_set(v___x_2861_, 0, v___x_2863_);
                    v___x_2867_ = v___x_2861_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2871_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 0, v___x_2863_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2871_, 1, v_a_2865_);
                    v___x_2867_ = v_reuseFailAlloc_2871_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2868_ = 1usize;
                v___x_2869_ = lean_usize_add(v_i_2847_, v___x_2868_);
                v_i_2847_ = v___x_2869_;
                v_b_2848_ = v___x_2867_;
                state = 0;
                continue;
            }
            4 => {
                if v___y_2873_ == 0 {
                    crate::leanh::lean_dec(v_fst_2858_);
                    v_a_2865_ = v_snd_2856_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2858_);
                    v___x_2874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_2842_, v_snd_2856_, v_fst_2858_, v___y_2849_, v___y_2850_, v___y_2851_, v___y_2852_);
                    if crate::leanh::lean_obj_tag(v___x_2874_) == 0 {
                        v_a_2875_ = crate::leanh::lean_ctor_get(v___x_2874_, 0);
                        crate::leanh::lean_inc(v_a_2875_);
                        crate::leanh::lean_dec_ref_known(v___x_2874_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2875_) == 1 {
                            v_val_2876_ = crate::leanh::lean_ctor_get(v_a_2875_, 0);
                            crate::leanh::lean_inc(v_val_2876_);
                            crate::leanh::lean_dec_ref_known(v_a_2875_, 1);
                            v___x_2877_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                v_goal_2843_,
                                v_fst_2858_,
                                v_val_2876_,
                                v_snd_2856_,
                            );
                            v_a_2865_ = v___x_2877_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2875_);
                            crate::leanh::lean_dec(v_fst_2858_);
                            v_a_2865_ = v_snd_2856_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2861_);
                        crate::leanh::lean_dec(v_fst_2858_);
                        crate::leanh::lean_dec(v_snd_2856_);
                        v_a_2878_ = crate::leanh::lean_ctor_get(v___x_2874_, 0);
                        v_isSharedCheck_2885_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2874_)) as u8;
                        if v_isSharedCheck_2885_ == 0 {
                            v___x_2880_ = v___x_2874_;
                            v_isShared_2881_ = v_isSharedCheck_2885_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2878_);
                            crate::leanh::lean_dec(v___x_2874_);
                            v___x_2880_ = crate::leanh::lean_box(0);
                            v_isShared_2881_ = v_isSharedCheck_2885_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_2881_ == 0 {
                    v___x_2883_ = v___x_2880_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2884_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_a_2878_);
                    v___x_2883_ = v_reuseFailAlloc_2884_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2883_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5___boxed(
    mut v___x_2889_: *mut crate::leanh::LeanObject,
    mut v_goal_2890_: *mut crate::leanh::LeanObject,
    mut v_structId_2891_: *mut crate::leanh::LeanObject,
    mut v_as_2892_: *mut crate::leanh::LeanObject,
    mut v_sz_2893_: *mut crate::leanh::LeanObject,
    mut v_i_2894_: *mut crate::leanh::LeanObject,
    mut v_b_2895_: *mut crate::leanh::LeanObject,
    mut v___y_2896_: *mut crate::leanh::LeanObject,
    mut v___y_2897_: *mut crate::leanh::LeanObject,
    mut v___y_2898_: *mut crate::leanh::LeanObject,
    mut v___y_2899_: *mut crate::leanh::LeanObject,
    mut v___y_2900_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2901_: usize = 0;
    let mut v_i_boxed_2902_: usize = 0;
    let mut v_res_2903_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2901_ = crate::leanh::lean_unbox_usize(v_sz_2893_);
    crate::leanh::lean_dec(v_sz_2893_);
    v_i_boxed_2902_ = crate::leanh::lean_unbox_usize(v_i_2894_);
    crate::leanh::lean_dec(v_i_2894_);
    v_res_2903_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_2889_, v_goal_2890_, v_structId_2891_, v_as_2892_, v_sz_boxed_2901_, v_i_boxed_2902_, v_b_2895_, v___y_2896_, v___y_2897_, v___y_2898_, v___y_2899_);
    crate::leanh::lean_dec(v___y_2899_);
    crate::leanh::lean_dec_ref(v___y_2898_);
    crate::leanh::lean_dec(v___y_2897_);
    crate::leanh::lean_dec_ref(v___y_2896_);
    crate::leanh::lean_dec_ref(v_as_2892_);
    crate::leanh::lean_dec(v_structId_2891_);
    crate::leanh::lean_dec_ref(v_goal_2890_);
    crate::leanh::lean_dec_ref(v___x_2889_);
    return v_res_2903_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(
    mut v___x_2904_: *mut crate::leanh::LeanObject,
    mut v_goal_2905_: *mut crate::leanh::LeanObject,
    mut v_structId_2906_: *mut crate::leanh::LeanObject,
    mut v_as_2907_: *mut crate::leanh::LeanObject,
    mut v_sz_2908_: usize,
    mut v_i_2909_: usize,
    mut v_b_2910_: *mut crate::leanh::LeanObject,
    mut v___y_2911_: *mut crate::leanh::LeanObject,
    mut v___y_2912_: *mut crate::leanh::LeanObject,
    mut v___y_2913_: *mut crate::leanh::LeanObject,
    mut v___y_2914_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2916_: u8 = 0;
    let mut v___x_2917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2924_: u8 = 0;
    let mut v___x_2925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2927_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: usize = 0;
    let mut v___x_2931_: usize = 0;
    let mut v___x_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_2935_: u8 = 0;
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2943_: u8 = 0;
    let mut v___x_2945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2947_: u8 = 0;
    let mut v___x_2948_: u8 = 0;
    let mut v___x_2949_: u8 = 0;
    let mut v_isSharedCheck_2950_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2916_ = lean_usize_dec_lt(v_i_2909_, v_sz_2908_);
                if v___x_2916_ == 0 {
                    v___x_2917_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2917_, 0, v_b_2910_);
                    return v___x_2917_;
                } else {
                    v_snd_2918_ = crate::leanh::lean_ctor_get(v_b_2910_, 1);
                    crate::leanh::lean_inc(v_snd_2918_);
                    crate::leanh::lean_dec_ref(v_b_2910_);
                    v_a_2919_ = lean_array_uget(v_as_2907_, v_i_2909_);
                    v_fst_2920_ = crate::leanh::lean_ctor_get(v_a_2919_, 0);
                    v_snd_2921_ = crate::leanh::lean_ctor_get(v_a_2919_, 1);
                    v_isSharedCheck_2950_ = (!crate::leanh::lean_is_exclusive(v_a_2919_)) as u8;
                    if v_isSharedCheck_2950_ == 0 {
                        v___x_2923_ = v_a_2919_;
                        v_isShared_2924_ = v_isSharedCheck_2950_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2921_);
                        crate::leanh::lean_inc(v_fst_2920_);
                        crate::leanh::lean_dec(v_a_2919_);
                        v___x_2923_ = crate::leanh::lean_box(0);
                        v_isShared_2924_ = v_isSharedCheck_2950_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2925_ = crate::leanh::lean_box(0);
                v___x_2948_ = lean_nat_dec_eq(v_structId_2906_, v_snd_2921_);
                crate::leanh::lean_dec(v_snd_2921_);
                if v___x_2948_ == 0 {
                    v___y_2935_ = v___x_2948_;
                    state = 4;
                    continue;
                } else {
                    v___x_2949_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_2918_, v_fst_2920_);
                    if v___x_2949_ == 0 {
                        v___y_2935_ = v___x_2948_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_2920_);
                        v_a_2927_ = v_snd_2918_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2924_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2923_, 1, v_a_2927_);
                    crate::leanh::lean_ctor_set(v___x_2923_, 0, v___x_2925_);
                    v___x_2929_ = v___x_2923_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2933_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 0, v___x_2925_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2933_, 1, v_a_2927_);
                    v___x_2929_ = v_reuseFailAlloc_2933_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2930_ = 1usize;
                v___x_2931_ = lean_usize_add(v_i_2909_, v___x_2930_);
                v___x_2932_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4_spec__5(v___x_2904_, v_goal_2905_, v_structId_2906_, v_as_2907_, v_sz_2908_, v___x_2931_, v___x_2929_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
                return v___x_2932_;
            }
            4 => {
                if v___y_2935_ == 0 {
                    crate::leanh::lean_dec(v_fst_2920_);
                    v_a_2927_ = v_snd_2918_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_2920_);
                    v___x_2936_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_2904_, v_snd_2918_, v_fst_2920_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
                    if crate::leanh::lean_obj_tag(v___x_2936_) == 0 {
                        v_a_2937_ = crate::leanh::lean_ctor_get(v___x_2936_, 0);
                        crate::leanh::lean_inc(v_a_2937_);
                        crate::leanh::lean_dec_ref_known(v___x_2936_, 1);
                        if crate::leanh::lean_obj_tag(v_a_2937_) == 1 {
                            v_val_2938_ = crate::leanh::lean_ctor_get(v_a_2937_, 0);
                            crate::leanh::lean_inc(v_val_2938_);
                            crate::leanh::lean_dec_ref_known(v_a_2937_, 1);
                            v___x_2939_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                v_goal_2905_,
                                v_fst_2920_,
                                v_val_2938_,
                                v_snd_2918_,
                            );
                            v_a_2927_ = v___x_2939_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_2937_);
                            crate::leanh::lean_dec(v_fst_2920_);
                            v_a_2927_ = v_snd_2918_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_2923_);
                        crate::leanh::lean_dec(v_fst_2920_);
                        crate::leanh::lean_dec(v_snd_2918_);
                        v_a_2940_ = crate::leanh::lean_ctor_get(v___x_2936_, 0);
                        v_isSharedCheck_2947_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2936_)) as u8;
                        if v_isSharedCheck_2947_ == 0 {
                            v___x_2942_ = v___x_2936_;
                            v_isShared_2943_ = v_isSharedCheck_2947_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2940_);
                            crate::leanh::lean_dec(v___x_2936_);
                            v___x_2942_ = crate::leanh::lean_box(0);
                            v_isShared_2943_ = v_isSharedCheck_2947_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_2943_ == 0 {
                    v___x_2945_ = v___x_2942_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2946_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2946_, 0, v_a_2940_);
                    v___x_2945_ = v_reuseFailAlloc_2946_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2945_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4___boxed(
    mut v___x_2951_: *mut crate::leanh::LeanObject,
    mut v_goal_2952_: *mut crate::leanh::LeanObject,
    mut v_structId_2953_: *mut crate::leanh::LeanObject,
    mut v_as_2954_: *mut crate::leanh::LeanObject,
    mut v_sz_2955_: *mut crate::leanh::LeanObject,
    mut v_i_2956_: *mut crate::leanh::LeanObject,
    mut v_b_2957_: *mut crate::leanh::LeanObject,
    mut v___y_2958_: *mut crate::leanh::LeanObject,
    mut v___y_2959_: *mut crate::leanh::LeanObject,
    mut v___y_2960_: *mut crate::leanh::LeanObject,
    mut v___y_2961_: *mut crate::leanh::LeanObject,
    mut v___y_2962_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2963_: usize = 0;
    let mut v_i_boxed_2964_: usize = 0;
    let mut v_res_2965_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2963_ = crate::leanh::lean_unbox_usize(v_sz_2955_);
    crate::leanh::lean_dec(v_sz_2955_);
    v_i_boxed_2964_ = crate::leanh::lean_unbox_usize(v_i_2956_);
    crate::leanh::lean_dec(v_i_2956_);
    v_res_2965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_2951_, v_goal_2952_, v_structId_2953_, v_as_2954_, v_sz_boxed_2963_, v_i_boxed_2964_, v_b_2957_, v___y_2958_, v___y_2959_, v___y_2960_, v___y_2961_);
    crate::leanh::lean_dec(v___y_2961_);
    crate::leanh::lean_dec_ref(v___y_2960_);
    crate::leanh::lean_dec(v___y_2959_);
    crate::leanh::lean_dec_ref(v___y_2958_);
    crate::leanh::lean_dec_ref(v_as_2954_);
    crate::leanh::lean_dec(v_structId_2953_);
    crate::leanh::lean_dec_ref(v_goal_2952_);
    crate::leanh::lean_dec_ref(v___x_2951_);
    return v_res_2965_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(
    mut v_init_2966_: *mut crate::leanh::LeanObject,
    mut v___x_2967_: *mut crate::leanh::LeanObject,
    mut v_goal_2968_: *mut crate::leanh::LeanObject,
    mut v_structId_2969_: *mut crate::leanh::LeanObject,
    mut v_n_2970_: *mut crate::leanh::LeanObject,
    mut v_b_2971_: *mut crate::leanh::LeanObject,
    mut v___y_2972_: *mut crate::leanh::LeanObject,
    mut v___y_2973_: *mut crate::leanh::LeanObject,
    mut v___y_2974_: *mut crate::leanh::LeanObject,
    mut v___y_2975_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2980_: usize = 0;
    let mut v___x_2981_: usize = 0;
    let mut v___x_2982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2986_: u8 = 0;
    let mut v_fst_2987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2997_: u8 = 0;
    let mut v_a_2998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3001_: u8 = 0;
    let mut v___x_3003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3005_: u8 = 0;
    let mut v_vs_3006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3008_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3009_: usize = 0;
    let mut v___x_3010_: usize = 0;
    let mut v___x_3011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3015_: u8 = 0;
    let mut v_fst_3016_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3020_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3022_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3026_: u8 = 0;
    let mut v_a_3027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3030_: u8 = 0;
    let mut v___x_3032_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3034_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_2970_) == 0 {
                    v_cs_2977_ = crate::leanh::lean_ctor_get(v_n_2970_, 0);
                    v___x_2978_ = crate::leanh::lean_box(0);
                    v___x_2979_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2979_, 0, v___x_2978_);
                    crate::leanh::lean_ctor_set(v___x_2979_, 1, v_b_2971_);
                    v_sz_2980_ = lean_array_size(v_cs_2977_);
                    v___x_2981_ = 0usize;
                    v___x_2982_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_2966_, v___x_2967_, v_goal_2968_, v_structId_2969_, v_cs_2977_, v_sz_2980_, v___x_2981_, v___x_2979_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
                    if crate::leanh::lean_obj_tag(v___x_2982_) == 0 {
                        v_a_2983_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                        v_isSharedCheck_2997_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_2997_ == 0 {
                            v___x_2985_ = v___x_2982_;
                            v_isShared_2986_ = v_isSharedCheck_2997_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2983_);
                            crate::leanh::lean_dec(v___x_2982_);
                            v___x_2985_ = crate::leanh::lean_box(0);
                            v_isShared_2986_ = v_isSharedCheck_2997_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2998_ = crate::leanh::lean_ctor_get(v___x_2982_, 0);
                        v_isSharedCheck_3005_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2982_)) as u8;
                        if v_isSharedCheck_3005_ == 0 {
                            v___x_3000_ = v___x_2982_;
                            v_isShared_3001_ = v_isSharedCheck_3005_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2998_);
                            crate::leanh::lean_dec(v___x_2982_);
                            v___x_3000_ = crate::leanh::lean_box(0);
                            v_isShared_3001_ = v_isSharedCheck_3005_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3006_ = crate::leanh::lean_ctor_get(v_n_2970_, 0);
                    v___x_3007_ = crate::leanh::lean_box(0);
                    v___x_3008_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3008_, 0, v___x_3007_);
                    crate::leanh::lean_ctor_set(v___x_3008_, 1, v_b_2971_);
                    v_sz_3009_ = lean_array_size(v_vs_3006_);
                    v___x_3010_ = 0usize;
                    v___x_3011_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__4(v___x_2967_, v_goal_2968_, v_structId_2969_, v_vs_3006_, v_sz_3009_, v___x_3010_, v___x_3008_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_);
                    if crate::leanh::lean_obj_tag(v___x_3011_) == 0 {
                        v_a_3012_ = crate::leanh::lean_ctor_get(v___x_3011_, 0);
                        v_isSharedCheck_3026_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3011_)) as u8;
                        if v_isSharedCheck_3026_ == 0 {
                            v___x_3014_ = v___x_3011_;
                            v_isShared_3015_ = v_isSharedCheck_3026_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3012_);
                            crate::leanh::lean_dec(v___x_3011_);
                            v___x_3014_ = crate::leanh::lean_box(0);
                            v_isShared_3015_ = v_isSharedCheck_3026_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3027_ = crate::leanh::lean_ctor_get(v___x_3011_, 0);
                        v_isSharedCheck_3034_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3011_)) as u8;
                        if v_isSharedCheck_3034_ == 0 {
                            v___x_3029_ = v___x_3011_;
                            v_isShared_3030_ = v_isSharedCheck_3034_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3027_);
                            crate::leanh::lean_dec(v___x_3011_);
                            v___x_3029_ = crate::leanh::lean_box(0);
                            v_isShared_3030_ = v_isSharedCheck_3034_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2987_ = crate::leanh::lean_ctor_get(v_a_2983_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2987_) == 0 {
                    v_snd_2988_ = crate::leanh::lean_ctor_get(v_a_2983_, 1);
                    crate::leanh::lean_inc(v_snd_2988_);
                    crate::leanh::lean_dec(v_a_2983_);
                    v___x_2989_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2989_, 0, v_snd_2988_);
                    if v_isShared_2986_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2985_, 0, v___x_2989_);
                        v___x_2991_ = v___x_2985_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2992_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2992_, 0, v___x_2989_);
                        v___x_2991_ = v_reuseFailAlloc_2992_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2987_);
                    crate::leanh::lean_dec(v_a_2983_);
                    v_val_2993_ = crate::leanh::lean_ctor_get(v_fst_2987_, 0);
                    crate::leanh::lean_inc(v_val_2993_);
                    crate::leanh::lean_dec_ref_known(v_fst_2987_, 1);
                    if v_isShared_2986_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2985_, 0, v_val_2993_);
                        v___x_2995_ = v___x_2985_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2996_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2996_, 0, v_val_2993_);
                        v___x_2995_ = v_reuseFailAlloc_2996_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2991_;
            }
            3 => {
                return v___x_2995_;
            }
            4 => {
                if v_isShared_3001_ == 0 {
                    v___x_3003_ = v___x_3000_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3004_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3004_, 0, v_a_2998_);
                    v___x_3003_ = v_reuseFailAlloc_3004_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3003_;
            }
            6 => {
                v_fst_3016_ = crate::leanh::lean_ctor_get(v_a_3012_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3016_) == 0 {
                    v_snd_3017_ = crate::leanh::lean_ctor_get(v_a_3012_, 1);
                    crate::leanh::lean_inc(v_snd_3017_);
                    crate::leanh::lean_dec(v_a_3012_);
                    v___x_3018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3018_, 0, v_snd_3017_);
                    if v_isShared_3015_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3014_, 0, v___x_3018_);
                        v___x_3020_ = v___x_3014_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3021_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3021_, 0, v___x_3018_);
                        v___x_3020_ = v_reuseFailAlloc_3021_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3016_);
                    crate::leanh::lean_dec(v_a_3012_);
                    v_val_3022_ = crate::leanh::lean_ctor_get(v_fst_3016_, 0);
                    crate::leanh::lean_inc(v_val_3022_);
                    crate::leanh::lean_dec_ref_known(v_fst_3016_, 1);
                    if v_isShared_3015_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3014_, 0, v_val_3022_);
                        v___x_3024_ = v___x_3014_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3025_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_val_3022_);
                        v___x_3024_ = v_reuseFailAlloc_3025_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3020_;
            }
            8 => {
                return v___x_3024_;
            }
            9 => {
                if v_isShared_3030_ == 0 {
                    v___x_3032_ = v___x_3029_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3033_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
                    v___x_3032_ = v_reuseFailAlloc_3033_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3032_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(
    mut v_init_3035_: *mut crate::leanh::LeanObject,
    mut v___x_3036_: *mut crate::leanh::LeanObject,
    mut v_goal_3037_: *mut crate::leanh::LeanObject,
    mut v_structId_3038_: *mut crate::leanh::LeanObject,
    mut v_as_3039_: *mut crate::leanh::LeanObject,
    mut v_sz_3040_: usize,
    mut v_i_3041_: usize,
    mut v_b_3042_: *mut crate::leanh::LeanObject,
    mut v___y_3043_: *mut crate::leanh::LeanObject,
    mut v___y_3044_: *mut crate::leanh::LeanObject,
    mut v___y_3045_: *mut crate::leanh::LeanObject,
    mut v___y_3046_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3048_: u8 = 0;
    let mut v___x_3049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3053_: u8 = 0;
    let mut v_a_3054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3059_: u8 = 0;
    let mut v___x_3060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3064_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3071_: usize = 0;
    let mut v___x_3072_: usize = 0;
    let mut v_reuseFailAlloc_3074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3075_: u8 = 0;
    let mut v_a_3076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3079_: u8 = 0;
    let mut v___x_3081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3082_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3083_: u8 = 0;
    let mut v_isSharedCheck_3084_: u8 = 0;
    let mut v_unused_3085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3048_ = lean_usize_dec_lt(v_i_3041_, v_sz_3040_);
                if v___x_3048_ == 0 {
                    v___x_3049_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3049_, 0, v_b_3042_);
                    return v___x_3049_;
                } else {
                    v_snd_3050_ = crate::leanh::lean_ctor_get(v_b_3042_, 1);
                    v_isSharedCheck_3084_ = (!crate::leanh::lean_is_exclusive(v_b_3042_)) as u8;
                    if v_isSharedCheck_3084_ == 0 {
                        v_unused_3085_ = crate::leanh::lean_ctor_get(v_b_3042_, 0);
                        crate::leanh::lean_dec(v_unused_3085_);
                        v___x_3052_ = v_b_3042_;
                        v_isShared_3053_ = v_isSharedCheck_3084_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3050_);
                        crate::leanh::lean_dec(v_b_3042_);
                        v___x_3052_ = crate::leanh::lean_box(0);
                        v_isShared_3053_ = v_isSharedCheck_3084_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3054_ = lean_array_uget_borrowed(v_as_3039_, v_i_3041_);
                crate::leanh::lean_inc(v_snd_3050_);
                v___x_3055_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_3035_, v___x_3036_, v_goal_3037_, v_structId_3038_, v_a_3054_, v_snd_3050_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_);
                if crate::leanh::lean_obj_tag(v___x_3055_) == 0 {
                    v_a_3056_ = crate::leanh::lean_ctor_get(v___x_3055_, 0);
                    v_isSharedCheck_3075_ = (!crate::leanh::lean_is_exclusive(v___x_3055_)) as u8;
                    if v_isSharedCheck_3075_ == 0 {
                        v___x_3058_ = v___x_3055_;
                        v_isShared_3059_ = v_isSharedCheck_3075_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3056_);
                        crate::leanh::lean_dec(v___x_3055_);
                        v___x_3058_ = crate::leanh::lean_box(0);
                        v_isShared_3059_ = v_isSharedCheck_3075_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3052_);
                    crate::leanh::lean_dec(v_snd_3050_);
                    v_a_3076_ = crate::leanh::lean_ctor_get(v___x_3055_, 0);
                    v_isSharedCheck_3083_ = (!crate::leanh::lean_is_exclusive(v___x_3055_)) as u8;
                    if v_isSharedCheck_3083_ == 0 {
                        v___x_3078_ = v___x_3055_;
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3076_);
                        crate::leanh::lean_dec(v___x_3055_);
                        v___x_3078_ = crate::leanh::lean_box(0);
                        v_isShared_3079_ = v_isSharedCheck_3083_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3056_) == 0 {
                    v___x_3060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3060_, 0, v_a_3056_);
                    if v_isShared_3053_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3060_);
                        v___x_3062_ = v___x_3052_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3066_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3066_, 0, v___x_3060_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3066_, 1, v_snd_3050_);
                        v___x_3062_ = v_reuseFailAlloc_3066_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3058_);
                    crate::leanh::lean_dec(v_snd_3050_);
                    v_a_3067_ = crate::leanh::lean_ctor_get(v_a_3056_, 0);
                    crate::leanh::lean_inc(v_a_3067_);
                    crate::leanh::lean_dec_ref_known(v_a_3056_, 1);
                    v___x_3068_ = crate::leanh::lean_box(0);
                    if v_isShared_3053_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3052_, 1, v_a_3067_);
                        crate::leanh::lean_ctor_set(v___x_3052_, 0, v___x_3068_);
                        v___x_3070_ = v___x_3052_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3074_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 0, v___x_3068_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3074_, 1, v_a_3067_);
                        v___x_3070_ = v_reuseFailAlloc_3074_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3059_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3058_, 0, v___x_3062_);
                    v___x_3064_ = v___x_3058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3065_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3065_, 0, v___x_3062_);
                    v___x_3064_ = v_reuseFailAlloc_3065_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3064_;
            }
            5 => {
                v___x_3071_ = 1usize;
                v___x_3072_ = lean_usize_add(v_i_3041_, v___x_3071_);
                v_i_3041_ = v___x_3072_;
                v_b_3042_ = v___x_3070_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3079_ == 0 {
                    v___x_3081_ = v___x_3078_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3082_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3076_);
                    v___x_3081_ = v_reuseFailAlloc_3082_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3081_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3___boxed(
    mut v_init_3086_: *mut crate::leanh::LeanObject,
    mut v___x_3087_: *mut crate::leanh::LeanObject,
    mut v_goal_3088_: *mut crate::leanh::LeanObject,
    mut v_structId_3089_: *mut crate::leanh::LeanObject,
    mut v_as_3090_: *mut crate::leanh::LeanObject,
    mut v_sz_3091_: *mut crate::leanh::LeanObject,
    mut v_i_3092_: *mut crate::leanh::LeanObject,
    mut v_b_3093_: *mut crate::leanh::LeanObject,
    mut v___y_3094_: *mut crate::leanh::LeanObject,
    mut v___y_3095_: *mut crate::leanh::LeanObject,
    mut v___y_3096_: *mut crate::leanh::LeanObject,
    mut v___y_3097_: *mut crate::leanh::LeanObject,
    mut v___y_3098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3099_: usize = 0;
    let mut v_i_boxed_3100_: usize = 0;
    let mut v_res_3101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3099_ = crate::leanh::lean_unbox_usize(v_sz_3091_);
    crate::leanh::lean_dec(v_sz_3091_);
    v_i_boxed_3100_ = crate::leanh::lean_unbox_usize(v_i_3092_);
    crate::leanh::lean_dec(v_i_3092_);
    v_res_3101_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2_spec__3(v_init_3086_, v___x_3087_, v_goal_3088_, v_structId_3089_, v_as_3090_, v_sz_boxed_3099_, v_i_boxed_3100_, v_b_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_);
    crate::leanh::lean_dec(v___y_3097_);
    crate::leanh::lean_dec_ref(v___y_3096_);
    crate::leanh::lean_dec(v___y_3095_);
    crate::leanh::lean_dec_ref(v___y_3094_);
    crate::leanh::lean_dec_ref(v_as_3090_);
    crate::leanh::lean_dec(v_structId_3089_);
    crate::leanh::lean_dec_ref(v_goal_3088_);
    crate::leanh::lean_dec_ref(v___x_3087_);
    crate::leanh::lean_dec_ref(v_init_3086_);
    return v_res_3101_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2___boxed(
    mut v_init_3102_: *mut crate::leanh::LeanObject,
    mut v___x_3103_: *mut crate::leanh::LeanObject,
    mut v_goal_3104_: *mut crate::leanh::LeanObject,
    mut v_structId_3105_: *mut crate::leanh::LeanObject,
    mut v_n_3106_: *mut crate::leanh::LeanObject,
    mut v_b_3107_: *mut crate::leanh::LeanObject,
    mut v___y_3108_: *mut crate::leanh::LeanObject,
    mut v___y_3109_: *mut crate::leanh::LeanObject,
    mut v___y_3110_: *mut crate::leanh::LeanObject,
    mut v___y_3111_: *mut crate::leanh::LeanObject,
    mut v___y_3112_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3113_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_3102_, v___x_3103_, v_goal_3104_, v_structId_3105_, v_n_3106_, v_b_3107_, v___y_3108_, v___y_3109_, v___y_3110_, v___y_3111_);
    crate::leanh::lean_dec(v___y_3111_);
    crate::leanh::lean_dec_ref(v___y_3110_);
    crate::leanh::lean_dec(v___y_3109_);
    crate::leanh::lean_dec_ref(v___y_3108_);
    crate::leanh::lean_dec_ref(v_n_3106_);
    crate::leanh::lean_dec(v_structId_3105_);
    crate::leanh::lean_dec_ref(v_goal_3104_);
    crate::leanh::lean_dec_ref(v___x_3103_);
    crate::leanh::lean_dec_ref(v_init_3102_);
    return v_res_3113_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(
    mut v___x_3114_: *mut crate::leanh::LeanObject,
    mut v_goal_3115_: *mut crate::leanh::LeanObject,
    mut v_structId_3116_: *mut crate::leanh::LeanObject,
    mut v_as_3117_: *mut crate::leanh::LeanObject,
    mut v_sz_3118_: usize,
    mut v_i_3119_: usize,
    mut v_b_3120_: *mut crate::leanh::LeanObject,
    mut v___y_3121_: *mut crate::leanh::LeanObject,
    mut v___y_3122_: *mut crate::leanh::LeanObject,
    mut v___y_3123_: *mut crate::leanh::LeanObject,
    mut v___y_3124_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3126_: u8 = 0;
    let mut v___x_3127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3128_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3134_: u8 = 0;
    let mut v___x_3135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3140_: usize = 0;
    let mut v___x_3141_: usize = 0;
    let mut v_reuseFailAlloc_3143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3145_: u8 = 0;
    let mut v___x_3146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3153_: u8 = 0;
    let mut v___x_3155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3157_: u8 = 0;
    let mut v___x_3158_: u8 = 0;
    let mut v___x_3159_: u8 = 0;
    let mut v_isSharedCheck_3160_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3126_ = lean_usize_dec_lt(v_i_3119_, v_sz_3118_);
                if v___x_3126_ == 0 {
                    v___x_3127_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3127_, 0, v_b_3120_);
                    return v___x_3127_;
                } else {
                    v_snd_3128_ = crate::leanh::lean_ctor_get(v_b_3120_, 1);
                    crate::leanh::lean_inc(v_snd_3128_);
                    crate::leanh::lean_dec_ref(v_b_3120_);
                    v_a_3129_ = lean_array_uget(v_as_3117_, v_i_3119_);
                    v_fst_3130_ = crate::leanh::lean_ctor_get(v_a_3129_, 0);
                    v_snd_3131_ = crate::leanh::lean_ctor_get(v_a_3129_, 1);
                    v_isSharedCheck_3160_ = (!crate::leanh::lean_is_exclusive(v_a_3129_)) as u8;
                    if v_isSharedCheck_3160_ == 0 {
                        v___x_3133_ = v_a_3129_;
                        v_isShared_3134_ = v_isSharedCheck_3160_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3131_);
                        crate::leanh::lean_inc(v_fst_3130_);
                        crate::leanh::lean_dec(v_a_3129_);
                        v___x_3133_ = crate::leanh::lean_box(0);
                        v_isShared_3134_ = v_isSharedCheck_3160_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3135_ = crate::leanh::lean_box(0);
                v___x_3158_ = lean_nat_dec_eq(v_structId_3116_, v_snd_3131_);
                crate::leanh::lean_dec(v_snd_3131_);
                if v___x_3158_ == 0 {
                    v___y_3145_ = v___x_3158_;
                    state = 4;
                    continue;
                } else {
                    v___x_3159_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_3128_, v_fst_3130_);
                    if v___x_3159_ == 0 {
                        v___y_3145_ = v___x_3158_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_3130_);
                        v_a_3137_ = v_snd_3128_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3134_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3133_, 1, v_a_3137_);
                    crate::leanh::lean_ctor_set(v___x_3133_, 0, v___x_3135_);
                    v___x_3139_ = v___x_3133_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3143_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 0, v___x_3135_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3143_, 1, v_a_3137_);
                    v___x_3139_ = v_reuseFailAlloc_3143_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3140_ = 1usize;
                v___x_3141_ = lean_usize_add(v_i_3119_, v___x_3140_);
                v_i_3119_ = v___x_3141_;
                v_b_3120_ = v___x_3139_;
                state = 0;
                continue;
            }
            4 => {
                if v___y_3145_ == 0 {
                    crate::leanh::lean_dec(v_fst_3130_);
                    v_a_3137_ = v_snd_3128_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3130_);
                    v___x_3146_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_3114_, v_snd_3128_, v_fst_3130_, v___y_3121_, v___y_3122_, v___y_3123_, v___y_3124_);
                    if crate::leanh::lean_obj_tag(v___x_3146_) == 0 {
                        v_a_3147_ = crate::leanh::lean_ctor_get(v___x_3146_, 0);
                        crate::leanh::lean_inc(v_a_3147_);
                        crate::leanh::lean_dec_ref_known(v___x_3146_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3147_) == 1 {
                            v_val_3148_ = crate::leanh::lean_ctor_get(v_a_3147_, 0);
                            crate::leanh::lean_inc(v_val_3148_);
                            crate::leanh::lean_dec_ref_known(v_a_3147_, 1);
                            v___x_3149_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                v_goal_3115_,
                                v_fst_3130_,
                                v_val_3148_,
                                v_snd_3128_,
                            );
                            v_a_3137_ = v___x_3149_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3147_);
                            crate::leanh::lean_dec(v_fst_3130_);
                            v_a_3137_ = v_snd_3128_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3133_);
                        crate::leanh::lean_dec(v_fst_3130_);
                        crate::leanh::lean_dec(v_snd_3128_);
                        v_a_3150_ = crate::leanh::lean_ctor_get(v___x_3146_, 0);
                        v_isSharedCheck_3157_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3146_)) as u8;
                        if v_isSharedCheck_3157_ == 0 {
                            v___x_3152_ = v___x_3146_;
                            v_isShared_3153_ = v_isSharedCheck_3157_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3150_);
                            crate::leanh::lean_dec(v___x_3146_);
                            v___x_3152_ = crate::leanh::lean_box(0);
                            v_isShared_3153_ = v_isSharedCheck_3157_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_3153_ == 0 {
                    v___x_3155_ = v___x_3152_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
                    v___x_3155_ = v_reuseFailAlloc_3156_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6___boxed(
    mut v___x_3161_: *mut crate::leanh::LeanObject,
    mut v_goal_3162_: *mut crate::leanh::LeanObject,
    mut v_structId_3163_: *mut crate::leanh::LeanObject,
    mut v_as_3164_: *mut crate::leanh::LeanObject,
    mut v_sz_3165_: *mut crate::leanh::LeanObject,
    mut v_i_3166_: *mut crate::leanh::LeanObject,
    mut v_b_3167_: *mut crate::leanh::LeanObject,
    mut v___y_3168_: *mut crate::leanh::LeanObject,
    mut v___y_3169_: *mut crate::leanh::LeanObject,
    mut v___y_3170_: *mut crate::leanh::LeanObject,
    mut v___y_3171_: *mut crate::leanh::LeanObject,
    mut v___y_3172_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3173_: usize = 0;
    let mut v_i_boxed_3174_: usize = 0;
    let mut v_res_3175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3173_ = crate::leanh::lean_unbox_usize(v_sz_3165_);
    crate::leanh::lean_dec(v_sz_3165_);
    v_i_boxed_3174_ = crate::leanh::lean_unbox_usize(v_i_3166_);
    crate::leanh::lean_dec(v_i_3166_);
    v_res_3175_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_3161_, v_goal_3162_, v_structId_3163_, v_as_3164_, v_sz_boxed_3173_, v_i_boxed_3174_, v_b_3167_, v___y_3168_, v___y_3169_, v___y_3170_, v___y_3171_);
    crate::leanh::lean_dec(v___y_3171_);
    crate::leanh::lean_dec_ref(v___y_3170_);
    crate::leanh::lean_dec(v___y_3169_);
    crate::leanh::lean_dec_ref(v___y_3168_);
    crate::leanh::lean_dec_ref(v_as_3164_);
    crate::leanh::lean_dec(v_structId_3163_);
    crate::leanh::lean_dec_ref(v_goal_3162_);
    crate::leanh::lean_dec_ref(v___x_3161_);
    return v_res_3175_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(
    mut v___x_3176_: *mut crate::leanh::LeanObject,
    mut v_goal_3177_: *mut crate::leanh::LeanObject,
    mut v_structId_3178_: *mut crate::leanh::LeanObject,
    mut v_as_3179_: *mut crate::leanh::LeanObject,
    mut v_sz_3180_: usize,
    mut v_i_3181_: usize,
    mut v_b_3182_: *mut crate::leanh::LeanObject,
    mut v___y_3183_: *mut crate::leanh::LeanObject,
    mut v___y_3184_: *mut crate::leanh::LeanObject,
    mut v___y_3185_: *mut crate::leanh::LeanObject,
    mut v___y_3186_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3188_: u8 = 0;
    let mut v___x_3189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_3192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3196_: u8 = 0;
    let mut v___x_3197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3199_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: usize = 0;
    let mut v___x_3203_: usize = 0;
    let mut v___x_3204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3207_: u8 = 0;
    let mut v___x_3208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3215_: u8 = 0;
    let mut v___x_3217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3219_: u8 = 0;
    let mut v___x_3220_: u8 = 0;
    let mut v___x_3221_: u8 = 0;
    let mut v_isSharedCheck_3222_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3188_ = lean_usize_dec_lt(v_i_3181_, v_sz_3180_);
                if v___x_3188_ == 0 {
                    v___x_3189_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3189_, 0, v_b_3182_);
                    return v___x_3189_;
                } else {
                    v_snd_3190_ = crate::leanh::lean_ctor_get(v_b_3182_, 1);
                    crate::leanh::lean_inc(v_snd_3190_);
                    crate::leanh::lean_dec_ref(v_b_3182_);
                    v_a_3191_ = lean_array_uget(v_as_3179_, v_i_3181_);
                    v_fst_3192_ = crate::leanh::lean_ctor_get(v_a_3191_, 0);
                    v_snd_3193_ = crate::leanh::lean_ctor_get(v_a_3191_, 1);
                    v_isSharedCheck_3222_ = (!crate::leanh::lean_is_exclusive(v_a_3191_)) as u8;
                    if v_isSharedCheck_3222_ == 0 {
                        v___x_3195_ = v_a_3191_;
                        v_isShared_3196_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3193_);
                        crate::leanh::lean_inc(v_fst_3192_);
                        crate::leanh::lean_dec(v_a_3191_);
                        v___x_3195_ = crate::leanh::lean_box(0);
                        v_isShared_3196_ = v_isSharedCheck_3222_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_3197_ = crate::leanh::lean_box(0);
                v___x_3220_ = lean_nat_dec_eq(v_structId_3178_, v_snd_3193_);
                crate::leanh::lean_dec(v_snd_3193_);
                if v___x_3220_ == 0 {
                    v___y_3207_ = v___x_3220_;
                    state = 4;
                    continue;
                } else {
                    v___x_3221_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_snd_3190_, v_fst_3192_);
                    if v___x_3221_ == 0 {
                        v___y_3207_ = v___x_3220_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v_fst_3192_);
                        v_a_3199_ = v_snd_3190_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3196_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3195_, 1, v_a_3199_);
                    crate::leanh::lean_ctor_set(v___x_3195_, 0, v___x_3197_);
                    v___x_3201_ = v___x_3195_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3205_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 0, v___x_3197_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3205_, 1, v_a_3199_);
                    v___x_3201_ = v_reuseFailAlloc_3205_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3202_ = 1usize;
                v___x_3203_ = lean_usize_add(v_i_3181_, v___x_3202_);
                v___x_3204_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3_spec__6(v___x_3176_, v_goal_3177_, v_structId_3178_, v_as_3179_, v_sz_3180_, v___x_3203_, v___x_3201_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
                return v___x_3204_;
            }
            4 => {
                if v___y_3207_ == 0 {
                    crate::leanh::lean_dec(v_fst_3192_);
                    v_a_3199_ = v_snd_3190_;
                    state = 2;
                    continue;
                } else {
                    crate::leanh::lean_inc(v_fst_3192_);
                    v___x_3208_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go(v___x_3176_, v_snd_3190_, v_fst_3192_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
                    if crate::leanh::lean_obj_tag(v___x_3208_) == 0 {
                        v_a_3209_ = crate::leanh::lean_ctor_get(v___x_3208_, 0);
                        crate::leanh::lean_inc(v_a_3209_);
                        crate::leanh::lean_dec_ref_known(v___x_3208_, 1);
                        if crate::leanh::lean_obj_tag(v_a_3209_) == 1 {
                            v_val_3210_ = crate::leanh::lean_ctor_get(v_a_3209_, 0);
                            crate::leanh::lean_inc(v_val_3210_);
                            crate::leanh::lean_dec_ref_known(v_a_3209_, 1);
                            v___x_3211_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                v_goal_3177_,
                                v_fst_3192_,
                                v_val_3210_,
                                v_snd_3190_,
                            );
                            v_a_3199_ = v___x_3211_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_dec(v_a_3209_);
                            crate::leanh::lean_dec(v_fst_3192_);
                            v_a_3199_ = v_snd_3190_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_3195_);
                        crate::leanh::lean_dec(v_fst_3192_);
                        crate::leanh::lean_dec(v_snd_3190_);
                        v_a_3212_ = crate::leanh::lean_ctor_get(v___x_3208_, 0);
                        v_isSharedCheck_3219_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3208_)) as u8;
                        if v_isSharedCheck_3219_ == 0 {
                            v___x_3214_ = v___x_3208_;
                            v_isShared_3215_ = v_isSharedCheck_3219_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3212_);
                            crate::leanh::lean_dec(v___x_3208_);
                            v___x_3214_ = crate::leanh::lean_box(0);
                            v_isShared_3215_ = v_isSharedCheck_3219_;
                            state = 5;
                            continue;
                        }
                    }
                }
            }
            5 => {
                if v_isShared_3215_ == 0 {
                    v___x_3217_ = v___x_3214_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_3218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3218_, 0, v_a_3212_);
                    v___x_3217_ = v_reuseFailAlloc_3218_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_3217_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3___boxed(
    mut v___x_3223_: *mut crate::leanh::LeanObject,
    mut v_goal_3224_: *mut crate::leanh::LeanObject,
    mut v_structId_3225_: *mut crate::leanh::LeanObject,
    mut v_as_3226_: *mut crate::leanh::LeanObject,
    mut v_sz_3227_: *mut crate::leanh::LeanObject,
    mut v_i_3228_: *mut crate::leanh::LeanObject,
    mut v_b_3229_: *mut crate::leanh::LeanObject,
    mut v___y_3230_: *mut crate::leanh::LeanObject,
    mut v___y_3231_: *mut crate::leanh::LeanObject,
    mut v___y_3232_: *mut crate::leanh::LeanObject,
    mut v___y_3233_: *mut crate::leanh::LeanObject,
    mut v___y_3234_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3235_: usize = 0;
    let mut v_i_boxed_3236_: usize = 0;
    let mut v_res_3237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3235_ = crate::leanh::lean_unbox_usize(v_sz_3227_);
    crate::leanh::lean_dec(v_sz_3227_);
    v_i_boxed_3236_ = crate::leanh::lean_unbox_usize(v_i_3228_);
    crate::leanh::lean_dec(v_i_3228_);
    v_res_3237_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_3223_, v_goal_3224_, v_structId_3225_, v_as_3226_, v_sz_boxed_3235_, v_i_boxed_3236_, v_b_3229_, v___y_3230_, v___y_3231_, v___y_3232_, v___y_3233_);
    crate::leanh::lean_dec(v___y_3233_);
    crate::leanh::lean_dec_ref(v___y_3232_);
    crate::leanh::lean_dec(v___y_3231_);
    crate::leanh::lean_dec_ref(v___y_3230_);
    crate::leanh::lean_dec_ref(v_as_3226_);
    crate::leanh::lean_dec(v_structId_3225_);
    crate::leanh::lean_dec_ref(v_goal_3224_);
    crate::leanh::lean_dec_ref(v___x_3223_);
    return v_res_3237_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(
    mut v___x_3238_: *mut crate::leanh::LeanObject,
    mut v_goal_3239_: *mut crate::leanh::LeanObject,
    mut v_structId_3240_: *mut crate::leanh::LeanObject,
    mut v_t_3241_: *mut crate::leanh::LeanObject,
    mut v_init_3242_: *mut crate::leanh::LeanObject,
    mut v___y_3243_: *mut crate::leanh::LeanObject,
    mut v___y_3244_: *mut crate::leanh::LeanObject,
    mut v___y_3245_: *mut crate::leanh::LeanObject,
    mut v___y_3246_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3254_: u8 = 0;
    let mut v_a_3255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3257_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3261_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3262_: usize = 0;
    let mut v___x_3263_: usize = 0;
    let mut v___x_3264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3268_: u8 = 0;
    let mut v_fst_3269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3278_: u8 = 0;
    let mut v_a_3279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3282_: u8 = 0;
    let mut v___x_3284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3286_: u8 = 0;
    let mut v_isSharedCheck_3287_: u8 = 0;
    let mut v_a_3288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3291_: u8 = 0;
    let mut v___x_3293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3295_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3248_ = crate::leanh::lean_ctor_get(v_t_3241_, 0);
                v_tail_3249_ = crate::leanh::lean_ctor_get(v_t_3241_, 1);
                crate::leanh::lean_inc_ref(v_init_3242_);
                v___x_3250_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__2(v_init_3242_, v___x_3238_, v_goal_3239_, v_structId_3240_, v_root_3248_, v_init_3242_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
                crate::leanh::lean_dec_ref(v_init_3242_);
                if crate::leanh::lean_obj_tag(v___x_3250_) == 0 {
                    v_a_3251_ = crate::leanh::lean_ctor_get(v___x_3250_, 0);
                    v_isSharedCheck_3287_ = (!crate::leanh::lean_is_exclusive(v___x_3250_)) as u8;
                    if v_isSharedCheck_3287_ == 0 {
                        v___x_3253_ = v___x_3250_;
                        v_isShared_3254_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3251_);
                        crate::leanh::lean_dec(v___x_3250_);
                        v___x_3253_ = crate::leanh::lean_box(0);
                        v_isShared_3254_ = v_isSharedCheck_3287_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3288_ = crate::leanh::lean_ctor_get(v___x_3250_, 0);
                    v_isSharedCheck_3295_ = (!crate::leanh::lean_is_exclusive(v___x_3250_)) as u8;
                    if v_isSharedCheck_3295_ == 0 {
                        v___x_3290_ = v___x_3250_;
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3288_);
                        crate::leanh::lean_dec(v___x_3250_);
                        v___x_3290_ = crate::leanh::lean_box(0);
                        v_isShared_3291_ = v_isSharedCheck_3295_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3251_) == 0 {
                    v_a_3255_ = crate::leanh::lean_ctor_get(v_a_3251_, 0);
                    crate::leanh::lean_inc(v_a_3255_);
                    crate::leanh::lean_dec_ref_known(v_a_3251_, 1);
                    if v_isShared_3254_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3253_, 0, v_a_3255_);
                        v___x_3257_ = v___x_3253_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3258_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3258_, 0, v_a_3255_);
                        v___x_3257_ = v_reuseFailAlloc_3258_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3253_);
                    v_a_3259_ = crate::leanh::lean_ctor_get(v_a_3251_, 0);
                    crate::leanh::lean_inc(v_a_3259_);
                    crate::leanh::lean_dec_ref_known(v_a_3251_, 1);
                    v___x_3260_ = crate::leanh::lean_box(0);
                    v___x_3261_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3261_, 0, v___x_3260_);
                    crate::leanh::lean_ctor_set(v___x_3261_, 1, v_a_3259_);
                    v_sz_3262_ = lean_array_size(v_tail_3249_);
                    v___x_3263_ = 0usize;
                    v___x_3264_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1_spec__3(v___x_3238_, v_goal_3239_, v_structId_3240_, v_tail_3249_, v_sz_3262_, v___x_3263_, v___x_3261_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
                    if crate::leanh::lean_obj_tag(v___x_3264_) == 0 {
                        v_a_3265_ = crate::leanh::lean_ctor_get(v___x_3264_, 0);
                        v_isSharedCheck_3278_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3264_)) as u8;
                        if v_isSharedCheck_3278_ == 0 {
                            v___x_3267_ = v___x_3264_;
                            v_isShared_3268_ = v_isSharedCheck_3278_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3265_);
                            crate::leanh::lean_dec(v___x_3264_);
                            v___x_3267_ = crate::leanh::lean_box(0);
                            v_isShared_3268_ = v_isSharedCheck_3278_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3279_ = crate::leanh::lean_ctor_get(v___x_3264_, 0);
                        v_isSharedCheck_3286_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3264_)) as u8;
                        if v_isSharedCheck_3286_ == 0 {
                            v___x_3281_ = v___x_3264_;
                            v_isShared_3282_ = v_isSharedCheck_3286_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3279_);
                            crate::leanh::lean_dec(v___x_3264_);
                            v___x_3281_ = crate::leanh::lean_box(0);
                            v_isShared_3282_ = v_isSharedCheck_3286_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3257_;
            }
            3 => {
                v_fst_3269_ = crate::leanh::lean_ctor_get(v_a_3265_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3269_) == 0 {
                    v_snd_3270_ = crate::leanh::lean_ctor_get(v_a_3265_, 1);
                    crate::leanh::lean_inc(v_snd_3270_);
                    crate::leanh::lean_dec(v_a_3265_);
                    if v_isShared_3268_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3267_, 0, v_snd_3270_);
                        v___x_3272_ = v___x_3267_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3273_, 0, v_snd_3270_);
                        v___x_3272_ = v_reuseFailAlloc_3273_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3269_);
                    crate::leanh::lean_dec(v_a_3265_);
                    v_val_3274_ = crate::leanh::lean_ctor_get(v_fst_3269_, 0);
                    crate::leanh::lean_inc(v_val_3274_);
                    crate::leanh::lean_dec_ref_known(v_fst_3269_, 1);
                    if v_isShared_3268_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3267_, 0, v_val_3274_);
                        v___x_3276_ = v___x_3267_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3277_, 0, v_val_3274_);
                        v___x_3276_ = v_reuseFailAlloc_3277_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3272_;
            }
            5 => {
                return v___x_3276_;
            }
            6 => {
                if v_isShared_3282_ == 0 {
                    v___x_3284_ = v___x_3281_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3285_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3285_, 0, v_a_3279_);
                    v___x_3284_ = v_reuseFailAlloc_3285_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3284_;
            }
            8 => {
                if v_isShared_3291_ == 0 {
                    v___x_3293_ = v___x_3290_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3294_, 0, v_a_3288_);
                    v___x_3293_ = v_reuseFailAlloc_3294_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3293_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1___boxed(
    mut v___x_3296_: *mut crate::leanh::LeanObject,
    mut v_goal_3297_: *mut crate::leanh::LeanObject,
    mut v_structId_3298_: *mut crate::leanh::LeanObject,
    mut v_t_3299_: *mut crate::leanh::LeanObject,
    mut v_init_3300_: *mut crate::leanh::LeanObject,
    mut v___y_3301_: *mut crate::leanh::LeanObject,
    mut v___y_3302_: *mut crate::leanh::LeanObject,
    mut v___y_3303_: *mut crate::leanh::LeanObject,
    mut v___y_3304_: *mut crate::leanh::LeanObject,
    mut v___y_3305_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3306_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_3296_, v_goal_3297_, v_structId_3298_, v_t_3299_, v_init_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_);
    crate::leanh::lean_dec(v___y_3304_);
    crate::leanh::lean_dec_ref(v___y_3303_);
    crate::leanh::lean_dec(v___y_3302_);
    crate::leanh::lean_dec_ref(v___y_3301_);
    crate::leanh::lean_dec_ref(v_t_3299_);
    crate::leanh::lean_dec(v_structId_3298_);
    crate::leanh::lean_dec_ref(v_goal_3297_);
    crate::leanh::lean_dec_ref(v___x_3296_);
    return v_res_3306_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(
    mut v_goal_3307_: *mut crate::leanh::LeanObject,
    mut v_structId_3308_: *mut crate::leanh::LeanObject,
    mut v_model_3309_: *mut crate::leanh::LeanObject,
    mut v_a_3310_: *mut crate::leanh::LeanObject,
    mut v_a_3311_: *mut crate::leanh::LeanObject,
    mut v_a_3312_: *mut crate::leanh::LeanObject,
    mut v_a_3313_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_3318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprToStructIdEntries_3319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3326_: u8 = 0;
    let mut v_ref_3327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3335_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3315_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                v___x_3316_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_3315_, v_goal_3307_);
                if crate::leanh::lean_obj_tag(v___x_3316_) == 0 {
                    v_a_3317_ = crate::leanh::lean_ctor_get(v___x_3316_, 0);
                    crate::leanh::lean_inc(v_a_3317_);
                    crate::leanh::lean_dec_ref_known(v___x_3316_, 1);
                    v_structs_3318_ = crate::leanh::lean_ctor_get(v_a_3317_, 0);
                    crate::leanh::lean_inc_ref(v_structs_3318_);
                    v_exprToStructIdEntries_3319_ = crate::leanh::lean_ctor_get(v_a_3317_, 3);
                    crate::leanh::lean_inc_ref(v_exprToStructIdEntries_3319_);
                    crate::leanh::lean_dec(v_a_3317_);
                    v___x_3320_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
                    v___x_3321_ = lean_array_get(v___x_3320_, v_structs_3318_, v_structId_3308_);
                    crate::leanh::lean_dec_ref(v_structs_3318_);
                    v___x_3322_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__1(v___x_3321_, v_goal_3307_, v_structId_3308_, v_exprToStructIdEntries_3319_, v_model_3309_, v_a_3310_, v_a_3311_, v_a_3312_, v_a_3313_);
                    crate::leanh::lean_dec_ref(v_exprToStructIdEntries_3319_);
                    crate::leanh::lean_dec(v___x_3321_);
                    return v___x_3322_;
                } else {
                    crate::leanh::lean_dec_ref(v_model_3309_);
                    v_a_3323_ = crate::leanh::lean_ctor_get(v___x_3316_, 0);
                    v_isSharedCheck_3335_ = (!crate::leanh::lean_is_exclusive(v___x_3316_)) as u8;
                    if v_isSharedCheck_3335_ == 0 {
                        v___x_3325_ = v___x_3316_;
                        v_isShared_3326_ = v_isSharedCheck_3335_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3323_);
                        crate::leanh::lean_dec(v___x_3316_);
                        v___x_3325_ = crate::leanh::lean_box(0);
                        v_isShared_3326_ = v_isSharedCheck_3335_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_ref_3327_ = crate::leanh::lean_ctor_get(v_a_3312_, 5);
                v___x_3328_ = lean_io_error_to_string(v_a_3323_);
                v___x_3329_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3329_, 0, v___x_3328_);
                v___x_3330_ = l_Lean_MessageData_ofFormat(v___x_3329_);
                crate::leanh::lean_inc(v_ref_3327_);
                v___x_3331_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_3331_, 0, v_ref_3327_);
                crate::leanh::lean_ctor_set(v___x_3331_, 1, v___x_3330_);
                if v_isShared_3326_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3325_, 0, v___x_3331_);
                    v___x_3333_ = v___x_3325_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3334_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3334_, 0, v___x_3331_);
                    v___x_3333_ = v_reuseFailAlloc_3334_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3333_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms___boxed(
    mut v_goal_3336_: *mut crate::leanh::LeanObject,
    mut v_structId_3337_: *mut crate::leanh::LeanObject,
    mut v_model_3338_: *mut crate::leanh::LeanObject,
    mut v_a_3339_: *mut crate::leanh::LeanObject,
    mut v_a_3340_: *mut crate::leanh::LeanObject,
    mut v_a_3341_: *mut crate::leanh::LeanObject,
    mut v_a_3342_: *mut crate::leanh::LeanObject,
    mut v_a_3343_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3344_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_3336_, v_structId_3337_, v_model_3338_, v_a_3339_, v_a_3340_, v_a_3341_, v_a_3342_);
    crate::leanh::lean_dec(v_a_3342_);
    crate::leanh::lean_dec_ref(v_a_3341_);
    crate::leanh::lean_dec(v_a_3340_);
    crate::leanh::lean_dec_ref(v_a_3339_);
    crate::leanh::lean_dec(v_structId_3337_);
    crate::leanh::lean_dec_ref(v_goal_3336_);
    return v_res_3344_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(
    mut v_00_u03b2_3345_: *mut crate::leanh::LeanObject,
    mut v_m_3346_: *mut crate::leanh::LeanObject,
    mut v_a_3347_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3348_: u8 = 0;
    v___x_3348_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___redArg(v_m_3346_, v_a_3347_);
    return v___x_3348_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0___boxed(
    mut v_00_u03b2_3349_: *mut crate::leanh::LeanObject,
    mut v_m_3350_: *mut crate::leanh::LeanObject,
    mut v_a_3351_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3352_: u8 = 0;
    let mut v_r_3353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3352_ = l_Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0(v_00_u03b2_3349_, v_m_3350_, v_a_3351_);
    crate::leanh::lean_dec_ref(v_a_3351_);
    crate::leanh::lean_dec_ref(v_m_3350_);
    v_r_3353_ = crate::leanh::lean_box((v_res_3352_) as usize);
    return v_r_3353_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(
    mut v_00_u03b2_3354_: *mut crate::leanh::LeanObject,
    mut v_a_3355_: *mut crate::leanh::LeanObject,
    mut v_x_3356_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3357_: u8 = 0;
    v___x_3357_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___redArg(v_a_3355_, v_x_3356_);
    return v___x_3357_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0___boxed(
    mut v_00_u03b2_3358_: *mut crate::leanh::LeanObject,
    mut v_a_3359_: *mut crate::leanh::LeanObject,
    mut v_x_3360_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3361_: u8 = 0;
    let mut v_r_3362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3361_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms_spec__0_spec__0(v_00_u03b2_3358_, v_a_3359_, v_x_3360_);
    crate::leanh::lean_dec(v_x_3360_);
    crate::leanh::lean_dec_ref(v_a_3359_);
    v_r_3362_ = crate::leanh::lean_box((v_res_3361_) as usize);
    return v_r_3362_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(
    mut v_goal_3363_: *mut crate::leanh::LeanObject,
    mut v___x_3364_: *mut crate::leanh::LeanObject,
    mut v_as_3365_: *mut crate::leanh::LeanObject,
    mut v_sz_3366_: usize,
    mut v_i_3367_: usize,
    mut v_b_3368_: *mut crate::leanh::LeanObject,
    mut v___y_3369_: *mut crate::leanh::LeanObject,
    mut v___y_3370_: *mut crate::leanh::LeanObject,
    mut v___y_3371_: *mut crate::leanh::LeanObject,
    mut v___y_3372_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3374_: u8 = 0;
    let mut v___x_3375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3379_: u8 = 0;
    let mut v_a_3380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3388_: usize = 0;
    let mut v___x_3389_: usize = 0;
    let mut v_reuseFailAlloc_3391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3392_: u8 = 0;
    let mut v_type_3393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3396_: u8 = 0;
    let mut v_self_3397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3401_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3404_: u8 = 0;
    let mut v___x_3406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3408_: u8 = 0;
    let mut v_a_3409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3412_: u8 = 0;
    let mut v___x_3414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3416_: u8 = 0;
    let mut v_isSharedCheck_3417_: u8 = 0;
    let mut v_unused_3418_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3374_ = lean_usize_dec_lt(v_i_3367_, v_sz_3366_);
                if v___x_3374_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3364_);
                    v___x_3375_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3375_, 0, v_b_3368_);
                    return v___x_3375_;
                } else {
                    v_snd_3376_ = crate::leanh::lean_ctor_get(v_b_3368_, 1);
                    v_isSharedCheck_3417_ = (!crate::leanh::lean_is_exclusive(v_b_3368_)) as u8;
                    if v_isSharedCheck_3417_ == 0 {
                        v_unused_3418_ = crate::leanh::lean_ctor_get(v_b_3368_, 0);
                        crate::leanh::lean_dec(v_unused_3418_);
                        v___x_3378_ = v_b_3368_;
                        v_isShared_3379_ = v_isSharedCheck_3417_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3376_);
                        crate::leanh::lean_dec(v_b_3368_);
                        v___x_3378_ = crate::leanh::lean_box(0);
                        v_isShared_3379_ = v_isSharedCheck_3417_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3380_ = lean_array_uget_borrowed(v_as_3365_, v_i_3367_);
                crate::leanh::lean_inc(v_a_3380_);
                v___x_3381_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3363_,
                    v_a_3380_,
                    v___y_3369_,
                    v___y_3370_,
                    v___y_3371_,
                    v___y_3372_,
                );
                if crate::leanh::lean_obj_tag(v___x_3381_) == 0 {
                    v_a_3382_ = crate::leanh::lean_ctor_get(v___x_3381_, 0);
                    crate::leanh::lean_inc(v_a_3382_);
                    crate::leanh::lean_dec_ref_known(v___x_3381_, 1);
                    v___x_3383_ = crate::leanh::lean_box(0);
                    v___x_3392_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3382_);
                    if v___x_3392_ == 0 {
                        crate::leanh::lean_dec(v_a_3382_);
                        v_a_3385_ = v_snd_3376_;
                        state = 2;
                        continue;
                    } else {
                        v_type_3393_ = crate::leanh::lean_ctor_get(v___x_3364_, 2);
                        crate::leanh::lean_inc(v_a_3382_);
                        crate::leanh::lean_inc_ref(v_type_3393_);
                        v___x_3394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_3393_, v_a_3382_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
                        if crate::leanh::lean_obj_tag(v___x_3394_) == 0 {
                            v_a_3395_ = crate::leanh::lean_ctor_get(v___x_3394_, 0);
                            crate::leanh::lean_inc(v_a_3395_);
                            crate::leanh::lean_dec_ref_known(v___x_3394_, 1);
                            v___x_3396_ = (crate::leanh::lean_unbox(v_a_3395_) as u8);
                            crate::leanh::lean_dec(v_a_3395_);
                            if v___x_3396_ == 0 {
                                crate::leanh::lean_dec(v_a_3382_);
                                v_a_3385_ = v_snd_3376_;
                                state = 2;
                                continue;
                            } else {
                                v_self_3397_ = crate::leanh::lean_ctor_get(v_a_3382_, 0);
                                crate::leanh::lean_inc_ref(v_self_3397_);
                                crate::leanh::lean_dec(v_a_3382_);
                                v___x_3398_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(
                                    v___x_3364_,
                                    v_self_3397_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3398_) == 1 {
                                    v_val_3399_ = crate::leanh::lean_ctor_get(v___x_3398_, 0);
                                    crate::leanh::lean_inc(v_val_3399_);
                                    crate::leanh::lean_dec_ref_known(v___x_3398_, 1);
                                    v___x_3400_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                        v_goal_3363_,
                                        v_self_3397_,
                                        v_val_3399_,
                                        v_snd_3376_,
                                    );
                                    v_a_3385_ = v___x_3400_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3398_);
                                    crate::leanh::lean_dec_ref(v_self_3397_);
                                    v_a_3385_ = v_snd_3376_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3382_);
                            crate::leanh::lean_del_object(v___x_3378_);
                            crate::leanh::lean_dec(v_snd_3376_);
                            crate::leanh::lean_dec_ref(v___x_3364_);
                            v_a_3401_ = crate::leanh::lean_ctor_get(v___x_3394_, 0);
                            v_isSharedCheck_3408_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3394_)) as u8;
                            if v_isSharedCheck_3408_ == 0 {
                                v___x_3403_ = v___x_3394_;
                                v_isShared_3404_ = v_isSharedCheck_3408_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3401_);
                                crate::leanh::lean_dec(v___x_3394_);
                                v___x_3403_ = crate::leanh::lean_box(0);
                                v_isShared_3404_ = v_isSharedCheck_3408_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3378_);
                    crate::leanh::lean_dec(v_snd_3376_);
                    crate::leanh::lean_dec_ref(v___x_3364_);
                    v_a_3409_ = crate::leanh::lean_ctor_get(v___x_3381_, 0);
                    v_isSharedCheck_3416_ = (!crate::leanh::lean_is_exclusive(v___x_3381_)) as u8;
                    if v_isSharedCheck_3416_ == 0 {
                        v___x_3411_ = v___x_3381_;
                        v_isShared_3412_ = v_isSharedCheck_3416_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3409_);
                        crate::leanh::lean_dec(v___x_3381_);
                        v___x_3411_ = crate::leanh::lean_box(0);
                        v_isShared_3412_ = v_isSharedCheck_3416_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3379_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3378_, 1, v_a_3385_);
                    crate::leanh::lean_ctor_set(v___x_3378_, 0, v___x_3383_);
                    v___x_3387_ = v___x_3378_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3391_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 0, v___x_3383_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3391_, 1, v_a_3385_);
                    v___x_3387_ = v_reuseFailAlloc_3391_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3388_ = 1usize;
                v___x_3389_ = lean_usize_add(v_i_3367_, v___x_3388_);
                v_i_3367_ = v___x_3389_;
                v_b_3368_ = v___x_3387_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3404_ == 0 {
                    v___x_3406_ = v___x_3403_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3407_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3407_, 0, v_a_3401_);
                    v___x_3406_ = v_reuseFailAlloc_3407_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3406_;
            }
            6 => {
                if v_isShared_3412_ == 0 {
                    v___x_3414_ = v___x_3411_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3415_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3415_, 0, v_a_3409_);
                    v___x_3414_ = v_reuseFailAlloc_3415_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3414_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4___boxed(
    mut v_goal_3419_: *mut crate::leanh::LeanObject,
    mut v___x_3420_: *mut crate::leanh::LeanObject,
    mut v_as_3421_: *mut crate::leanh::LeanObject,
    mut v_sz_3422_: *mut crate::leanh::LeanObject,
    mut v_i_3423_: *mut crate::leanh::LeanObject,
    mut v_b_3424_: *mut crate::leanh::LeanObject,
    mut v___y_3425_: *mut crate::leanh::LeanObject,
    mut v___y_3426_: *mut crate::leanh::LeanObject,
    mut v___y_3427_: *mut crate::leanh::LeanObject,
    mut v___y_3428_: *mut crate::leanh::LeanObject,
    mut v___y_3429_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3430_: usize = 0;
    let mut v_i_boxed_3431_: usize = 0;
    let mut v_res_3432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3430_ = crate::leanh::lean_unbox_usize(v_sz_3422_);
    crate::leanh::lean_dec(v_sz_3422_);
    v_i_boxed_3431_ = crate::leanh::lean_unbox_usize(v_i_3423_);
    crate::leanh::lean_dec(v_i_3423_);
    v_res_3432_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_3419_, v___x_3420_, v_as_3421_, v_sz_boxed_3430_, v_i_boxed_3431_, v_b_3424_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
    crate::leanh::lean_dec(v___y_3428_);
    crate::leanh::lean_dec_ref(v___y_3427_);
    crate::leanh::lean_dec(v___y_3426_);
    crate::leanh::lean_dec_ref(v___y_3425_);
    crate::leanh::lean_dec_ref(v_as_3421_);
    crate::leanh::lean_dec_ref(v_goal_3419_);
    return v_res_3432_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(
    mut v_goal_3433_: *mut crate::leanh::LeanObject,
    mut v___x_3434_: *mut crate::leanh::LeanObject,
    mut v_as_3435_: *mut crate::leanh::LeanObject,
    mut v_sz_3436_: usize,
    mut v_i_3437_: usize,
    mut v_b_3438_: *mut crate::leanh::LeanObject,
    mut v___y_3439_: *mut crate::leanh::LeanObject,
    mut v___y_3440_: *mut crate::leanh::LeanObject,
    mut v___y_3441_: *mut crate::leanh::LeanObject,
    mut v___y_3442_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3444_: u8 = 0;
    let mut v___x_3445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3448_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3449_: u8 = 0;
    let mut v_a_3450_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3451_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3458_: usize = 0;
    let mut v___x_3459_: usize = 0;
    let mut v___x_3460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3462_: u8 = 0;
    let mut v_type_3463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3464_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3466_: u8 = 0;
    let mut v_self_3467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3470_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3474_: u8 = 0;
    let mut v___x_3476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3478_: u8 = 0;
    let mut v_a_3479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3481_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3482_: u8 = 0;
    let mut v___x_3484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3485_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3486_: u8 = 0;
    let mut v_isSharedCheck_3487_: u8 = 0;
    let mut v_unused_3488_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3444_ = lean_usize_dec_lt(v_i_3437_, v_sz_3436_);
                if v___x_3444_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3434_);
                    v___x_3445_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3445_, 0, v_b_3438_);
                    return v___x_3445_;
                } else {
                    v_snd_3446_ = crate::leanh::lean_ctor_get(v_b_3438_, 1);
                    v_isSharedCheck_3487_ = (!crate::leanh::lean_is_exclusive(v_b_3438_)) as u8;
                    if v_isSharedCheck_3487_ == 0 {
                        v_unused_3488_ = crate::leanh::lean_ctor_get(v_b_3438_, 0);
                        crate::leanh::lean_dec(v_unused_3488_);
                        v___x_3448_ = v_b_3438_;
                        v_isShared_3449_ = v_isSharedCheck_3487_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3446_);
                        crate::leanh::lean_dec(v_b_3438_);
                        v___x_3448_ = crate::leanh::lean_box(0);
                        v_isShared_3449_ = v_isSharedCheck_3487_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3450_ = lean_array_uget_borrowed(v_as_3435_, v_i_3437_);
                crate::leanh::lean_inc(v_a_3450_);
                v___x_3451_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3433_,
                    v_a_3450_,
                    v___y_3439_,
                    v___y_3440_,
                    v___y_3441_,
                    v___y_3442_,
                );
                if crate::leanh::lean_obj_tag(v___x_3451_) == 0 {
                    v_a_3452_ = crate::leanh::lean_ctor_get(v___x_3451_, 0);
                    crate::leanh::lean_inc(v_a_3452_);
                    crate::leanh::lean_dec_ref_known(v___x_3451_, 1);
                    v___x_3453_ = crate::leanh::lean_box(0);
                    v___x_3462_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3452_);
                    if v___x_3462_ == 0 {
                        crate::leanh::lean_dec(v_a_3452_);
                        v_a_3455_ = v_snd_3446_;
                        state = 2;
                        continue;
                    } else {
                        v_type_3463_ = crate::leanh::lean_ctor_get(v___x_3434_, 2);
                        crate::leanh::lean_inc(v_a_3452_);
                        crate::leanh::lean_inc_ref(v_type_3463_);
                        v___x_3464_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_3463_, v_a_3452_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
                        if crate::leanh::lean_obj_tag(v___x_3464_) == 0 {
                            v_a_3465_ = crate::leanh::lean_ctor_get(v___x_3464_, 0);
                            crate::leanh::lean_inc(v_a_3465_);
                            crate::leanh::lean_dec_ref_known(v___x_3464_, 1);
                            v___x_3466_ = (crate::leanh::lean_unbox(v_a_3465_) as u8);
                            crate::leanh::lean_dec(v_a_3465_);
                            if v___x_3466_ == 0 {
                                crate::leanh::lean_dec(v_a_3452_);
                                v_a_3455_ = v_snd_3446_;
                                state = 2;
                                continue;
                            } else {
                                v_self_3467_ = crate::leanh::lean_ctor_get(v_a_3452_, 0);
                                crate::leanh::lean_inc_ref(v_self_3467_);
                                crate::leanh::lean_dec(v_a_3452_);
                                v___x_3468_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(
                                    v___x_3434_,
                                    v_self_3467_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3468_) == 1 {
                                    v_val_3469_ = crate::leanh::lean_ctor_get(v___x_3468_, 0);
                                    crate::leanh::lean_inc(v_val_3469_);
                                    crate::leanh::lean_dec_ref_known(v___x_3468_, 1);
                                    v___x_3470_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                        v_goal_3433_,
                                        v_self_3467_,
                                        v_val_3469_,
                                        v_snd_3446_,
                                    );
                                    v_a_3455_ = v___x_3470_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3468_);
                                    crate::leanh::lean_dec_ref(v_self_3467_);
                                    v_a_3455_ = v_snd_3446_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3452_);
                            crate::leanh::lean_del_object(v___x_3448_);
                            crate::leanh::lean_dec(v_snd_3446_);
                            crate::leanh::lean_dec_ref(v___x_3434_);
                            v_a_3471_ = crate::leanh::lean_ctor_get(v___x_3464_, 0);
                            v_isSharedCheck_3478_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3464_)) as u8;
                            if v_isSharedCheck_3478_ == 0 {
                                v___x_3473_ = v___x_3464_;
                                v_isShared_3474_ = v_isSharedCheck_3478_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3471_);
                                crate::leanh::lean_dec(v___x_3464_);
                                v___x_3473_ = crate::leanh::lean_box(0);
                                v_isShared_3474_ = v_isSharedCheck_3478_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3448_);
                    crate::leanh::lean_dec(v_snd_3446_);
                    crate::leanh::lean_dec_ref(v___x_3434_);
                    v_a_3479_ = crate::leanh::lean_ctor_get(v___x_3451_, 0);
                    v_isSharedCheck_3486_ = (!crate::leanh::lean_is_exclusive(v___x_3451_)) as u8;
                    if v_isSharedCheck_3486_ == 0 {
                        v___x_3481_ = v___x_3451_;
                        v_isShared_3482_ = v_isSharedCheck_3486_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3479_);
                        crate::leanh::lean_dec(v___x_3451_);
                        v___x_3481_ = crate::leanh::lean_box(0);
                        v_isShared_3482_ = v_isSharedCheck_3486_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3449_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3448_, 1, v_a_3455_);
                    crate::leanh::lean_ctor_set(v___x_3448_, 0, v___x_3453_);
                    v___x_3457_ = v___x_3448_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3461_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3453_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_a_3455_);
                    v___x_3457_ = v_reuseFailAlloc_3461_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3458_ = 1usize;
                v___x_3459_ = lean_usize_add(v_i_3437_, v___x_3458_);
                v___x_3460_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2_spec__4(v_goal_3433_, v___x_3434_, v_as_3435_, v_sz_3436_, v___x_3459_, v___x_3457_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
                return v___x_3460_;
            }
            4 => {
                if v_isShared_3474_ == 0 {
                    v___x_3476_ = v___x_3473_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3477_, 0, v_a_3471_);
                    v___x_3476_ = v_reuseFailAlloc_3477_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3476_;
            }
            6 => {
                if v_isShared_3482_ == 0 {
                    v___x_3484_ = v___x_3481_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3485_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3485_, 0, v_a_3479_);
                    v___x_3484_ = v_reuseFailAlloc_3485_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3484_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2___boxed(
    mut v_goal_3489_: *mut crate::leanh::LeanObject,
    mut v___x_3490_: *mut crate::leanh::LeanObject,
    mut v_as_3491_: *mut crate::leanh::LeanObject,
    mut v_sz_3492_: *mut crate::leanh::LeanObject,
    mut v_i_3493_: *mut crate::leanh::LeanObject,
    mut v_b_3494_: *mut crate::leanh::LeanObject,
    mut v___y_3495_: *mut crate::leanh::LeanObject,
    mut v___y_3496_: *mut crate::leanh::LeanObject,
    mut v___y_3497_: *mut crate::leanh::LeanObject,
    mut v___y_3498_: *mut crate::leanh::LeanObject,
    mut v___y_3499_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3500_: usize = 0;
    let mut v_i_boxed_3501_: usize = 0;
    let mut v_res_3502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3500_ = crate::leanh::lean_unbox_usize(v_sz_3492_);
    crate::leanh::lean_dec(v_sz_3492_);
    v_i_boxed_3501_ = crate::leanh::lean_unbox_usize(v_i_3493_);
    crate::leanh::lean_dec(v_i_3493_);
    v_res_3502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_3489_, v___x_3490_, v_as_3491_, v_sz_boxed_3500_, v_i_boxed_3501_, v_b_3494_, v___y_3495_, v___y_3496_, v___y_3497_, v___y_3498_);
    crate::leanh::lean_dec(v___y_3498_);
    crate::leanh::lean_dec_ref(v___y_3497_);
    crate::leanh::lean_dec(v___y_3496_);
    crate::leanh::lean_dec_ref(v___y_3495_);
    crate::leanh::lean_dec_ref(v_as_3491_);
    crate::leanh::lean_dec_ref(v_goal_3489_);
    return v_res_3502_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(
    mut v_init_3503_: *mut crate::leanh::LeanObject,
    mut v_goal_3504_: *mut crate::leanh::LeanObject,
    mut v___x_3505_: *mut crate::leanh::LeanObject,
    mut v_n_3506_: *mut crate::leanh::LeanObject,
    mut v_b_3507_: *mut crate::leanh::LeanObject,
    mut v___y_3508_: *mut crate::leanh::LeanObject,
    mut v___y_3509_: *mut crate::leanh::LeanObject,
    mut v___y_3510_: *mut crate::leanh::LeanObject,
    mut v___y_3511_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_3513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3516_: usize = 0;
    let mut v___x_3517_: usize = 0;
    let mut v___x_3518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3519_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3522_: u8 = 0;
    let mut v_fst_3523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3533_: u8 = 0;
    let mut v_a_3534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3537_: u8 = 0;
    let mut v___x_3539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3541_: u8 = 0;
    let mut v_vs_3542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3544_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3545_: usize = 0;
    let mut v___x_3546_: usize = 0;
    let mut v___x_3547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3548_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3551_: u8 = 0;
    let mut v_fst_3552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3554_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3562_: u8 = 0;
    let mut v_a_3563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3566_: u8 = 0;
    let mut v___x_3568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3570_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_3506_) == 0 {
                    v_cs_3513_ = crate::leanh::lean_ctor_get(v_n_3506_, 0);
                    v___x_3514_ = crate::leanh::lean_box(0);
                    v___x_3515_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3515_, 0, v___x_3514_);
                    crate::leanh::lean_ctor_set(v___x_3515_, 1, v_b_3507_);
                    v_sz_3516_ = lean_array_size(v_cs_3513_);
                    v___x_3517_ = 0usize;
                    v___x_3518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_3503_, v_goal_3504_, v___x_3505_, v_cs_3513_, v_sz_3516_, v___x_3517_, v___x_3515_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
                    if crate::leanh::lean_obj_tag(v___x_3518_) == 0 {
                        v_a_3519_ = crate::leanh::lean_ctor_get(v___x_3518_, 0);
                        v_isSharedCheck_3533_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3518_)) as u8;
                        if v_isSharedCheck_3533_ == 0 {
                            v___x_3521_ = v___x_3518_;
                            v_isShared_3522_ = v_isSharedCheck_3533_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3519_);
                            crate::leanh::lean_dec(v___x_3518_);
                            v___x_3521_ = crate::leanh::lean_box(0);
                            v_isShared_3522_ = v_isSharedCheck_3533_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_3534_ = crate::leanh::lean_ctor_get(v___x_3518_, 0);
                        v_isSharedCheck_3541_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3518_)) as u8;
                        if v_isSharedCheck_3541_ == 0 {
                            v___x_3536_ = v___x_3518_;
                            v_isShared_3537_ = v_isSharedCheck_3541_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3534_);
                            crate::leanh::lean_dec(v___x_3518_);
                            v___x_3536_ = crate::leanh::lean_box(0);
                            v_isShared_3537_ = v_isSharedCheck_3541_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_3542_ = crate::leanh::lean_ctor_get(v_n_3506_, 0);
                    v___x_3543_ = crate::leanh::lean_box(0);
                    v___x_3544_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3544_, 0, v___x_3543_);
                    crate::leanh::lean_ctor_set(v___x_3544_, 1, v_b_3507_);
                    v_sz_3545_ = lean_array_size(v_vs_3542_);
                    v___x_3546_ = 0usize;
                    v___x_3547_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__2(v_goal_3504_, v___x_3505_, v_vs_3542_, v_sz_3545_, v___x_3546_, v___x_3544_, v___y_3508_, v___y_3509_, v___y_3510_, v___y_3511_);
                    if crate::leanh::lean_obj_tag(v___x_3547_) == 0 {
                        v_a_3548_ = crate::leanh::lean_ctor_get(v___x_3547_, 0);
                        v_isSharedCheck_3562_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3547_)) as u8;
                        if v_isSharedCheck_3562_ == 0 {
                            v___x_3550_ = v___x_3547_;
                            v_isShared_3551_ = v_isSharedCheck_3562_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3548_);
                            crate::leanh::lean_dec(v___x_3547_);
                            v___x_3550_ = crate::leanh::lean_box(0);
                            v_isShared_3551_ = v_isSharedCheck_3562_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_3563_ = crate::leanh::lean_ctor_get(v___x_3547_, 0);
                        v_isSharedCheck_3570_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3547_)) as u8;
                        if v_isSharedCheck_3570_ == 0 {
                            v___x_3565_ = v___x_3547_;
                            v_isShared_3566_ = v_isSharedCheck_3570_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3563_);
                            crate::leanh::lean_dec(v___x_3547_);
                            v___x_3565_ = crate::leanh::lean_box(0);
                            v_isShared_3566_ = v_isSharedCheck_3570_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_3523_ = crate::leanh::lean_ctor_get(v_a_3519_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3523_) == 0 {
                    v_snd_3524_ = crate::leanh::lean_ctor_get(v_a_3519_, 1);
                    crate::leanh::lean_inc(v_snd_3524_);
                    crate::leanh::lean_dec(v_a_3519_);
                    v___x_3525_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3525_, 0, v_snd_3524_);
                    if v_isShared_3522_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3521_, 0, v___x_3525_);
                        v___x_3527_ = v___x_3521_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3528_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3528_, 0, v___x_3525_);
                        v___x_3527_ = v_reuseFailAlloc_3528_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3523_);
                    crate::leanh::lean_dec(v_a_3519_);
                    v_val_3529_ = crate::leanh::lean_ctor_get(v_fst_3523_, 0);
                    crate::leanh::lean_inc(v_val_3529_);
                    crate::leanh::lean_dec_ref_known(v_fst_3523_, 1);
                    if v_isShared_3522_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3521_, 0, v_val_3529_);
                        v___x_3531_ = v___x_3521_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3532_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3532_, 0, v_val_3529_);
                        v___x_3531_ = v_reuseFailAlloc_3532_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_3527_;
            }
            3 => {
                return v___x_3531_;
            }
            4 => {
                if v_isShared_3537_ == 0 {
                    v___x_3539_ = v___x_3536_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3540_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3540_, 0, v_a_3534_);
                    v___x_3539_ = v_reuseFailAlloc_3540_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3539_;
            }
            6 => {
                v_fst_3552_ = crate::leanh::lean_ctor_get(v_a_3548_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3552_) == 0 {
                    v_snd_3553_ = crate::leanh::lean_ctor_get(v_a_3548_, 1);
                    crate::leanh::lean_inc(v_snd_3553_);
                    crate::leanh::lean_dec(v_a_3548_);
                    v___x_3554_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3554_, 0, v_snd_3553_);
                    if v_isShared_3551_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3550_, 0, v___x_3554_);
                        v___x_3556_ = v___x_3550_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_3557_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3557_, 0, v___x_3554_);
                        v___x_3556_ = v_reuseFailAlloc_3557_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3552_);
                    crate::leanh::lean_dec(v_a_3548_);
                    v_val_3558_ = crate::leanh::lean_ctor_get(v_fst_3552_, 0);
                    crate::leanh::lean_inc(v_val_3558_);
                    crate::leanh::lean_dec_ref_known(v_fst_3552_, 1);
                    if v_isShared_3551_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3550_, 0, v_val_3558_);
                        v___x_3560_ = v___x_3550_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_3561_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3561_, 0, v_val_3558_);
                        v___x_3560_ = v_reuseFailAlloc_3561_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_3556_;
            }
            8 => {
                return v___x_3560_;
            }
            9 => {
                if v_isShared_3566_ == 0 {
                    v___x_3568_ = v___x_3565_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_3569_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_a_3563_);
                    v___x_3568_ = v_reuseFailAlloc_3569_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_3568_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(
    mut v_init_3571_: *mut crate::leanh::LeanObject,
    mut v_goal_3572_: *mut crate::leanh::LeanObject,
    mut v___x_3573_: *mut crate::leanh::LeanObject,
    mut v_as_3574_: *mut crate::leanh::LeanObject,
    mut v_sz_3575_: usize,
    mut v_i_3576_: usize,
    mut v_b_3577_: *mut crate::leanh::LeanObject,
    mut v___y_3578_: *mut crate::leanh::LeanObject,
    mut v___y_3579_: *mut crate::leanh::LeanObject,
    mut v___y_3580_: *mut crate::leanh::LeanObject,
    mut v___y_3581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3583_: u8 = 0;
    let mut v___x_3584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3588_: u8 = 0;
    let mut v_a_3589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3594_: u8 = 0;
    let mut v___x_3595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3599_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3603_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3606_: usize = 0;
    let mut v___x_3607_: usize = 0;
    let mut v_reuseFailAlloc_3609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3610_: u8 = 0;
    let mut v_a_3611_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3613_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3614_: u8 = 0;
    let mut v___x_3616_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3617_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3618_: u8 = 0;
    let mut v_isSharedCheck_3619_: u8 = 0;
    let mut v_unused_3620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3583_ = lean_usize_dec_lt(v_i_3576_, v_sz_3575_);
                if v___x_3583_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3573_);
                    v___x_3584_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3584_, 0, v_b_3577_);
                    return v___x_3584_;
                } else {
                    v_snd_3585_ = crate::leanh::lean_ctor_get(v_b_3577_, 1);
                    v_isSharedCheck_3619_ = (!crate::leanh::lean_is_exclusive(v_b_3577_)) as u8;
                    if v_isSharedCheck_3619_ == 0 {
                        v_unused_3620_ = crate::leanh::lean_ctor_get(v_b_3577_, 0);
                        crate::leanh::lean_dec(v_unused_3620_);
                        v___x_3587_ = v_b_3577_;
                        v_isShared_3588_ = v_isSharedCheck_3619_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3585_);
                        crate::leanh::lean_dec(v_b_3577_);
                        v___x_3587_ = crate::leanh::lean_box(0);
                        v_isShared_3588_ = v_isSharedCheck_3619_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3589_ = lean_array_uget_borrowed(v_as_3574_, v_i_3576_);
                crate::leanh::lean_inc(v_snd_3585_);
                crate::leanh::lean_inc_ref(v___x_3573_);
                v___x_3590_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_3571_, v_goal_3572_, v___x_3573_, v_a_3589_, v_snd_3585_, v___y_3578_, v___y_3579_, v___y_3580_, v___y_3581_);
                if crate::leanh::lean_obj_tag(v___x_3590_) == 0 {
                    v_a_3591_ = crate::leanh::lean_ctor_get(v___x_3590_, 0);
                    v_isSharedCheck_3610_ = (!crate::leanh::lean_is_exclusive(v___x_3590_)) as u8;
                    if v_isSharedCheck_3610_ == 0 {
                        v___x_3593_ = v___x_3590_;
                        v_isShared_3594_ = v_isSharedCheck_3610_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3591_);
                        crate::leanh::lean_dec(v___x_3590_);
                        v___x_3593_ = crate::leanh::lean_box(0);
                        v_isShared_3594_ = v_isSharedCheck_3610_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3587_);
                    crate::leanh::lean_dec(v_snd_3585_);
                    crate::leanh::lean_dec_ref(v___x_3573_);
                    v_a_3611_ = crate::leanh::lean_ctor_get(v___x_3590_, 0);
                    v_isSharedCheck_3618_ = (!crate::leanh::lean_is_exclusive(v___x_3590_)) as u8;
                    if v_isSharedCheck_3618_ == 0 {
                        v___x_3613_ = v___x_3590_;
                        v_isShared_3614_ = v_isSharedCheck_3618_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3611_);
                        crate::leanh::lean_dec(v___x_3590_);
                        v___x_3613_ = crate::leanh::lean_box(0);
                        v_isShared_3614_ = v_isSharedCheck_3618_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_3591_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_3573_);
                    v___x_3595_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3595_, 0, v_a_3591_);
                    if v_isShared_3588_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3587_, 0, v___x_3595_);
                        v___x_3597_ = v___x_3587_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_3601_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 0, v___x_3595_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3601_, 1, v_snd_3585_);
                        v___x_3597_ = v_reuseFailAlloc_3601_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3593_);
                    crate::leanh::lean_dec(v_snd_3585_);
                    v_a_3602_ = crate::leanh::lean_ctor_get(v_a_3591_, 0);
                    crate::leanh::lean_inc(v_a_3602_);
                    crate::leanh::lean_dec_ref_known(v_a_3591_, 1);
                    v___x_3603_ = crate::leanh::lean_box(0);
                    if v_isShared_3588_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3587_, 1, v_a_3602_);
                        crate::leanh::lean_ctor_set(v___x_3587_, 0, v___x_3603_);
                        v___x_3605_ = v___x_3587_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3609_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 0, v___x_3603_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3609_, 1, v_a_3602_);
                        v___x_3605_ = v_reuseFailAlloc_3609_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_3594_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3593_, 0, v___x_3597_);
                    v___x_3599_ = v___x_3593_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3600_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3600_, 0, v___x_3597_);
                    v___x_3599_ = v_reuseFailAlloc_3600_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3599_;
            }
            5 => {
                v___x_3606_ = 1usize;
                v___x_3607_ = lean_usize_add(v_i_3576_, v___x_3606_);
                v_i_3576_ = v___x_3607_;
                v_b_3577_ = v___x_3605_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_3614_ == 0 {
                    v___x_3616_ = v___x_3613_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3617_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3617_, 0, v_a_3611_);
                    v___x_3616_ = v_reuseFailAlloc_3617_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3616_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1___boxed(
    mut v_init_3621_: *mut crate::leanh::LeanObject,
    mut v_goal_3622_: *mut crate::leanh::LeanObject,
    mut v___x_3623_: *mut crate::leanh::LeanObject,
    mut v_as_3624_: *mut crate::leanh::LeanObject,
    mut v_sz_3625_: *mut crate::leanh::LeanObject,
    mut v_i_3626_: *mut crate::leanh::LeanObject,
    mut v_b_3627_: *mut crate::leanh::LeanObject,
    mut v___y_3628_: *mut crate::leanh::LeanObject,
    mut v___y_3629_: *mut crate::leanh::LeanObject,
    mut v___y_3630_: *mut crate::leanh::LeanObject,
    mut v___y_3631_: *mut crate::leanh::LeanObject,
    mut v___y_3632_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3633_: usize = 0;
    let mut v_i_boxed_3634_: usize = 0;
    let mut v_res_3635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3633_ = crate::leanh::lean_unbox_usize(v_sz_3625_);
    crate::leanh::lean_dec(v_sz_3625_);
    v_i_boxed_3634_ = crate::leanh::lean_unbox_usize(v_i_3626_);
    crate::leanh::lean_dec(v_i_3626_);
    v_res_3635_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0_spec__1(v_init_3621_, v_goal_3622_, v___x_3623_, v_as_3624_, v_sz_boxed_3633_, v_i_boxed_3634_, v_b_3627_, v___y_3628_, v___y_3629_, v___y_3630_, v___y_3631_);
    crate::leanh::lean_dec(v___y_3631_);
    crate::leanh::lean_dec_ref(v___y_3630_);
    crate::leanh::lean_dec(v___y_3629_);
    crate::leanh::lean_dec_ref(v___y_3628_);
    crate::leanh::lean_dec_ref(v_as_3624_);
    crate::leanh::lean_dec_ref(v_goal_3622_);
    crate::leanh::lean_dec_ref(v_init_3621_);
    return v_res_3635_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0___boxed(
    mut v_init_3636_: *mut crate::leanh::LeanObject,
    mut v_goal_3637_: *mut crate::leanh::LeanObject,
    mut v___x_3638_: *mut crate::leanh::LeanObject,
    mut v_n_3639_: *mut crate::leanh::LeanObject,
    mut v_b_3640_: *mut crate::leanh::LeanObject,
    mut v___y_3641_: *mut crate::leanh::LeanObject,
    mut v___y_3642_: *mut crate::leanh::LeanObject,
    mut v___y_3643_: *mut crate::leanh::LeanObject,
    mut v___y_3644_: *mut crate::leanh::LeanObject,
    mut v___y_3645_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3646_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_3636_, v_goal_3637_, v___x_3638_, v_n_3639_, v_b_3640_, v___y_3641_, v___y_3642_, v___y_3643_, v___y_3644_);
    crate::leanh::lean_dec(v___y_3644_);
    crate::leanh::lean_dec_ref(v___y_3643_);
    crate::leanh::lean_dec(v___y_3642_);
    crate::leanh::lean_dec_ref(v___y_3641_);
    crate::leanh::lean_dec_ref(v_n_3639_);
    crate::leanh::lean_dec_ref(v_goal_3637_);
    crate::leanh::lean_dec_ref(v_init_3636_);
    return v_res_3646_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(
    mut v_goal_3647_: *mut crate::leanh::LeanObject,
    mut v___x_3648_: *mut crate::leanh::LeanObject,
    mut v_as_3649_: *mut crate::leanh::LeanObject,
    mut v_sz_3650_: usize,
    mut v_i_3651_: usize,
    mut v_b_3652_: *mut crate::leanh::LeanObject,
    mut v___y_3653_: *mut crate::leanh::LeanObject,
    mut v___y_3654_: *mut crate::leanh::LeanObject,
    mut v___y_3655_: *mut crate::leanh::LeanObject,
    mut v___y_3656_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3658_: u8 = 0;
    let mut v___x_3659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3663_: u8 = 0;
    let mut v_a_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3671_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3672_: usize = 0;
    let mut v___x_3673_: usize = 0;
    let mut v_reuseFailAlloc_3675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3676_: u8 = 0;
    let mut v_type_3677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3680_: u8 = 0;
    let mut v_self_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3688_: u8 = 0;
    let mut v___x_3690_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3691_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3692_: u8 = 0;
    let mut v_a_3693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3696_: u8 = 0;
    let mut v___x_3698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3700_: u8 = 0;
    let mut v_isSharedCheck_3701_: u8 = 0;
    let mut v_unused_3702_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3658_ = lean_usize_dec_lt(v_i_3651_, v_sz_3650_);
                if v___x_3658_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3648_);
                    v___x_3659_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3659_, 0, v_b_3652_);
                    return v___x_3659_;
                } else {
                    v_snd_3660_ = crate::leanh::lean_ctor_get(v_b_3652_, 1);
                    v_isSharedCheck_3701_ = (!crate::leanh::lean_is_exclusive(v_b_3652_)) as u8;
                    if v_isSharedCheck_3701_ == 0 {
                        v_unused_3702_ = crate::leanh::lean_ctor_get(v_b_3652_, 0);
                        crate::leanh::lean_dec(v_unused_3702_);
                        v___x_3662_ = v_b_3652_;
                        v_isShared_3663_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3660_);
                        crate::leanh::lean_dec(v_b_3652_);
                        v___x_3662_ = crate::leanh::lean_box(0);
                        v_isShared_3663_ = v_isSharedCheck_3701_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3664_ = lean_array_uget_borrowed(v_as_3649_, v_i_3651_);
                crate::leanh::lean_inc(v_a_3664_);
                v___x_3665_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3647_,
                    v_a_3664_,
                    v___y_3653_,
                    v___y_3654_,
                    v___y_3655_,
                    v___y_3656_,
                );
                if crate::leanh::lean_obj_tag(v___x_3665_) == 0 {
                    v_a_3666_ = crate::leanh::lean_ctor_get(v___x_3665_, 0);
                    crate::leanh::lean_inc(v_a_3666_);
                    crate::leanh::lean_dec_ref_known(v___x_3665_, 1);
                    v___x_3667_ = crate::leanh::lean_box(0);
                    v___x_3676_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3666_);
                    if v___x_3676_ == 0 {
                        crate::leanh::lean_dec(v_a_3666_);
                        v_a_3669_ = v_snd_3660_;
                        state = 2;
                        continue;
                    } else {
                        v_type_3677_ = crate::leanh::lean_ctor_get(v___x_3648_, 2);
                        crate::leanh::lean_inc(v_a_3666_);
                        crate::leanh::lean_inc_ref(v_type_3677_);
                        v___x_3678_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_3677_, v_a_3666_, v___y_3653_, v___y_3654_, v___y_3655_, v___y_3656_);
                        if crate::leanh::lean_obj_tag(v___x_3678_) == 0 {
                            v_a_3679_ = crate::leanh::lean_ctor_get(v___x_3678_, 0);
                            crate::leanh::lean_inc(v_a_3679_);
                            crate::leanh::lean_dec_ref_known(v___x_3678_, 1);
                            v___x_3680_ = (crate::leanh::lean_unbox(v_a_3679_) as u8);
                            crate::leanh::lean_dec(v_a_3679_);
                            if v___x_3680_ == 0 {
                                crate::leanh::lean_dec(v_a_3666_);
                                v_a_3669_ = v_snd_3660_;
                                state = 2;
                                continue;
                            } else {
                                v_self_3681_ = crate::leanh::lean_ctor_get(v_a_3666_, 0);
                                crate::leanh::lean_inc_ref(v_self_3681_);
                                crate::leanh::lean_dec(v_a_3666_);
                                v___x_3682_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(
                                    v___x_3648_,
                                    v_self_3681_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3682_) == 1 {
                                    v_val_3683_ = crate::leanh::lean_ctor_get(v___x_3682_, 0);
                                    crate::leanh::lean_inc(v_val_3683_);
                                    crate::leanh::lean_dec_ref_known(v___x_3682_, 1);
                                    v___x_3684_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                        v_goal_3647_,
                                        v_self_3681_,
                                        v_val_3683_,
                                        v_snd_3660_,
                                    );
                                    v_a_3669_ = v___x_3684_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3682_);
                                    crate::leanh::lean_dec_ref(v_self_3681_);
                                    v_a_3669_ = v_snd_3660_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3666_);
                            crate::leanh::lean_del_object(v___x_3662_);
                            crate::leanh::lean_dec(v_snd_3660_);
                            crate::leanh::lean_dec_ref(v___x_3648_);
                            v_a_3685_ = crate::leanh::lean_ctor_get(v___x_3678_, 0);
                            v_isSharedCheck_3692_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3678_)) as u8;
                            if v_isSharedCheck_3692_ == 0 {
                                v___x_3687_ = v___x_3678_;
                                v_isShared_3688_ = v_isSharedCheck_3692_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3685_);
                                crate::leanh::lean_dec(v___x_3678_);
                                v___x_3687_ = crate::leanh::lean_box(0);
                                v_isShared_3688_ = v_isSharedCheck_3692_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3662_);
                    crate::leanh::lean_dec(v_snd_3660_);
                    crate::leanh::lean_dec_ref(v___x_3648_);
                    v_a_3693_ = crate::leanh::lean_ctor_get(v___x_3665_, 0);
                    v_isSharedCheck_3700_ = (!crate::leanh::lean_is_exclusive(v___x_3665_)) as u8;
                    if v_isSharedCheck_3700_ == 0 {
                        v___x_3695_ = v___x_3665_;
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3693_);
                        crate::leanh::lean_dec(v___x_3665_);
                        v___x_3695_ = crate::leanh::lean_box(0);
                        v_isShared_3696_ = v_isSharedCheck_3700_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3663_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3662_, 1, v_a_3669_);
                    crate::leanh::lean_ctor_set(v___x_3662_, 0, v___x_3667_);
                    v___x_3671_ = v___x_3662_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3675_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 0, v___x_3667_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3675_, 1, v_a_3669_);
                    v___x_3671_ = v_reuseFailAlloc_3675_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3672_ = 1usize;
                v___x_3673_ = lean_usize_add(v_i_3651_, v___x_3672_);
                v_i_3651_ = v___x_3673_;
                v_b_3652_ = v___x_3671_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3688_ == 0 {
                    v___x_3690_ = v___x_3687_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3691_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3691_, 0, v_a_3685_);
                    v___x_3690_ = v_reuseFailAlloc_3691_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3690_;
            }
            6 => {
                if v_isShared_3696_ == 0 {
                    v___x_3698_ = v___x_3695_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3699_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3699_, 0, v_a_3693_);
                    v___x_3698_ = v_reuseFailAlloc_3699_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3698_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4___boxed(
    mut v_goal_3703_: *mut crate::leanh::LeanObject,
    mut v___x_3704_: *mut crate::leanh::LeanObject,
    mut v_as_3705_: *mut crate::leanh::LeanObject,
    mut v_sz_3706_: *mut crate::leanh::LeanObject,
    mut v_i_3707_: *mut crate::leanh::LeanObject,
    mut v_b_3708_: *mut crate::leanh::LeanObject,
    mut v___y_3709_: *mut crate::leanh::LeanObject,
    mut v___y_3710_: *mut crate::leanh::LeanObject,
    mut v___y_3711_: *mut crate::leanh::LeanObject,
    mut v___y_3712_: *mut crate::leanh::LeanObject,
    mut v___y_3713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3714_: usize = 0;
    let mut v_i_boxed_3715_: usize = 0;
    let mut v_res_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3714_ = crate::leanh::lean_unbox_usize(v_sz_3706_);
    crate::leanh::lean_dec(v_sz_3706_);
    v_i_boxed_3715_ = crate::leanh::lean_unbox_usize(v_i_3707_);
    crate::leanh::lean_dec(v_i_3707_);
    v_res_3716_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_3703_, v___x_3704_, v_as_3705_, v_sz_boxed_3714_, v_i_boxed_3715_, v_b_3708_, v___y_3709_, v___y_3710_, v___y_3711_, v___y_3712_);
    crate::leanh::lean_dec(v___y_3712_);
    crate::leanh::lean_dec_ref(v___y_3711_);
    crate::leanh::lean_dec(v___y_3710_);
    crate::leanh::lean_dec_ref(v___y_3709_);
    crate::leanh::lean_dec_ref(v_as_3705_);
    crate::leanh::lean_dec_ref(v_goal_3703_);
    return v_res_3716_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(
    mut v_goal_3717_: *mut crate::leanh::LeanObject,
    mut v___x_3718_: *mut crate::leanh::LeanObject,
    mut v_as_3719_: *mut crate::leanh::LeanObject,
    mut v_sz_3720_: usize,
    mut v_i_3721_: usize,
    mut v_b_3722_: *mut crate::leanh::LeanObject,
    mut v___y_3723_: *mut crate::leanh::LeanObject,
    mut v___y_3724_: *mut crate::leanh::LeanObject,
    mut v___y_3725_: *mut crate::leanh::LeanObject,
    mut v___y_3726_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3728_: u8 = 0;
    let mut v___x_3729_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3730_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3733_: u8 = 0;
    let mut v_a_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3742_: usize = 0;
    let mut v___x_3743_: usize = 0;
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3746_: u8 = 0;
    let mut v_type_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3750_: u8 = 0;
    let mut v_self_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3758_: u8 = 0;
    let mut v___x_3760_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3762_: u8 = 0;
    let mut v_a_3763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3766_: u8 = 0;
    let mut v___x_3768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3770_: u8 = 0;
    let mut v_isSharedCheck_3771_: u8 = 0;
    let mut v_unused_3772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3728_ = lean_usize_dec_lt(v_i_3721_, v_sz_3720_);
                if v___x_3728_ == 0 {
                    crate::leanh::lean_dec_ref(v___x_3718_);
                    v___x_3729_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3729_, 0, v_b_3722_);
                    return v___x_3729_;
                } else {
                    v_snd_3730_ = crate::leanh::lean_ctor_get(v_b_3722_, 1);
                    v_isSharedCheck_3771_ = (!crate::leanh::lean_is_exclusive(v_b_3722_)) as u8;
                    if v_isSharedCheck_3771_ == 0 {
                        v_unused_3772_ = crate::leanh::lean_ctor_get(v_b_3722_, 0);
                        crate::leanh::lean_dec(v_unused_3772_);
                        v___x_3732_ = v_b_3722_;
                        v_isShared_3733_ = v_isSharedCheck_3771_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3730_);
                        crate::leanh::lean_dec(v_b_3722_);
                        v___x_3732_ = crate::leanh::lean_box(0);
                        v_isShared_3733_ = v_isSharedCheck_3771_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3734_ = lean_array_uget_borrowed(v_as_3719_, v_i_3721_);
                crate::leanh::lean_inc(v_a_3734_);
                v___x_3735_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3717_,
                    v_a_3734_,
                    v___y_3723_,
                    v___y_3724_,
                    v___y_3725_,
                    v___y_3726_,
                );
                if crate::leanh::lean_obj_tag(v___x_3735_) == 0 {
                    v_a_3736_ = crate::leanh::lean_ctor_get(v___x_3735_, 0);
                    crate::leanh::lean_inc(v_a_3736_);
                    crate::leanh::lean_dec_ref_known(v___x_3735_, 1);
                    v___x_3737_ = crate::leanh::lean_box(0);
                    v___x_3746_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_3736_);
                    if v___x_3746_ == 0 {
                        crate::leanh::lean_dec(v_a_3736_);
                        v_a_3739_ = v_snd_3730_;
                        state = 2;
                        continue;
                    } else {
                        v_type_3747_ = crate::leanh::lean_ctor_get(v___x_3718_, 2);
                        crate::leanh::lean_inc(v_a_3736_);
                        crate::leanh::lean_inc_ref(v_type_3747_);
                        v___x_3748_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType(v_type_3747_, v_a_3736_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
                        if crate::leanh::lean_obj_tag(v___x_3748_) == 0 {
                            v_a_3749_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                            crate::leanh::lean_inc(v_a_3749_);
                            crate::leanh::lean_dec_ref_known(v___x_3748_, 1);
                            v___x_3750_ = (crate::leanh::lean_unbox(v_a_3749_) as u8);
                            crate::leanh::lean_dec(v_a_3749_);
                            if v___x_3750_ == 0 {
                                crate::leanh::lean_dec(v_a_3736_);
                                v_a_3739_ = v_snd_3730_;
                                state = 2;
                                continue;
                            } else {
                                v_self_3751_ = crate::leanh::lean_ctor_get(v_a_3736_, 0);
                                crate::leanh::lean_inc_ref(v_self_3751_);
                                crate::leanh::lean_dec(v_a_3736_);
                                v___x_3752_ = l_Lean_Meta_Grind_Arith_Linear_getAssignment_x3f(
                                    v___x_3718_,
                                    v_self_3751_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_3752_) == 1 {
                                    v_val_3753_ = crate::leanh::lean_ctor_get(v___x_3752_, 0);
                                    crate::leanh::lean_inc(v_val_3753_);
                                    crate::leanh::lean_dec_ref_known(v___x_3752_, 1);
                                    v___x_3754_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                        v_goal_3717_,
                                        v_self_3751_,
                                        v_val_3753_,
                                        v_snd_3730_,
                                    );
                                    v_a_3739_ = v___x_3754_;
                                    state = 2;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_3752_);
                                    crate::leanh::lean_dec_ref(v_self_3751_);
                                    v_a_3739_ = v_snd_3730_;
                                    state = 2;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_3736_);
                            crate::leanh::lean_del_object(v___x_3732_);
                            crate::leanh::lean_dec(v_snd_3730_);
                            crate::leanh::lean_dec_ref(v___x_3718_);
                            v_a_3755_ = crate::leanh::lean_ctor_get(v___x_3748_, 0);
                            v_isSharedCheck_3762_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3748_)) as u8;
                            if v_isSharedCheck_3762_ == 0 {
                                v___x_3757_ = v___x_3748_;
                                v_isShared_3758_ = v_isSharedCheck_3762_;
                                state = 4;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3755_);
                                crate::leanh::lean_dec(v___x_3748_);
                                v___x_3757_ = crate::leanh::lean_box(0);
                                v_isShared_3758_ = v_isSharedCheck_3762_;
                                state = 4;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3732_);
                    crate::leanh::lean_dec(v_snd_3730_);
                    crate::leanh::lean_dec_ref(v___x_3718_);
                    v_a_3763_ = crate::leanh::lean_ctor_get(v___x_3735_, 0);
                    v_isSharedCheck_3770_ = (!crate::leanh::lean_is_exclusive(v___x_3735_)) as u8;
                    if v_isSharedCheck_3770_ == 0 {
                        v___x_3765_ = v___x_3735_;
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3763_);
                        crate::leanh::lean_dec(v___x_3735_);
                        v___x_3765_ = crate::leanh::lean_box(0);
                        v_isShared_3766_ = v_isSharedCheck_3770_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3733_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3732_, 1, v_a_3739_);
                    crate::leanh::lean_ctor_set(v___x_3732_, 0, v___x_3737_);
                    v___x_3741_ = v___x_3732_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3745_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 0, v___x_3737_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3745_, 1, v_a_3739_);
                    v___x_3741_ = v_reuseFailAlloc_3745_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3742_ = 1usize;
                v___x_3743_ = lean_usize_add(v_i_3721_, v___x_3742_);
                v___x_3744_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1_spec__4(v_goal_3717_, v___x_3718_, v_as_3719_, v_sz_3720_, v___x_3743_, v___x_3741_, v___y_3723_, v___y_3724_, v___y_3725_, v___y_3726_);
                return v___x_3744_;
            }
            4 => {
                if v_isShared_3758_ == 0 {
                    v___x_3760_ = v___x_3757_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3761_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3761_, 0, v_a_3755_);
                    v___x_3760_ = v_reuseFailAlloc_3761_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3760_;
            }
            6 => {
                if v_isShared_3766_ == 0 {
                    v___x_3768_ = v___x_3765_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3769_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3769_, 0, v_a_3763_);
                    v___x_3768_ = v_reuseFailAlloc_3769_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3768_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1___boxed(
    mut v_goal_3773_: *mut crate::leanh::LeanObject,
    mut v___x_3774_: *mut crate::leanh::LeanObject,
    mut v_as_3775_: *mut crate::leanh::LeanObject,
    mut v_sz_3776_: *mut crate::leanh::LeanObject,
    mut v_i_3777_: *mut crate::leanh::LeanObject,
    mut v_b_3778_: *mut crate::leanh::LeanObject,
    mut v___y_3779_: *mut crate::leanh::LeanObject,
    mut v___y_3780_: *mut crate::leanh::LeanObject,
    mut v___y_3781_: *mut crate::leanh::LeanObject,
    mut v___y_3782_: *mut crate::leanh::LeanObject,
    mut v___y_3783_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3784_: usize = 0;
    let mut v_i_boxed_3785_: usize = 0;
    let mut v_res_3786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3784_ = crate::leanh::lean_unbox_usize(v_sz_3776_);
    crate::leanh::lean_dec(v_sz_3776_);
    v_i_boxed_3785_ = crate::leanh::lean_unbox_usize(v_i_3777_);
    crate::leanh::lean_dec(v_i_3777_);
    v_res_3786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_3773_, v___x_3774_, v_as_3775_, v_sz_boxed_3784_, v_i_boxed_3785_, v_b_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
    crate::leanh::lean_dec(v___y_3782_);
    crate::leanh::lean_dec_ref(v___y_3781_);
    crate::leanh::lean_dec(v___y_3780_);
    crate::leanh::lean_dec_ref(v___y_3779_);
    crate::leanh::lean_dec_ref(v_as_3775_);
    crate::leanh::lean_dec_ref(v_goal_3773_);
    return v_res_3786_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(
    mut v_goal_3787_: *mut crate::leanh::LeanObject,
    mut v___x_3788_: *mut crate::leanh::LeanObject,
    mut v_t_3789_: *mut crate::leanh::LeanObject,
    mut v_init_3790_: *mut crate::leanh::LeanObject,
    mut v___y_3791_: *mut crate::leanh::LeanObject,
    mut v___y_3792_: *mut crate::leanh::LeanObject,
    mut v___y_3793_: *mut crate::leanh::LeanObject,
    mut v___y_3794_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_3796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_3797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3802_: u8 = 0;
    let mut v_a_3803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_3810_: usize = 0;
    let mut v___x_3811_: usize = 0;
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3816_: u8 = 0;
    let mut v_fst_3817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3826_: u8 = 0;
    let mut v_a_3827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3830_: u8 = 0;
    let mut v___x_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3834_: u8 = 0;
    let mut v_isSharedCheck_3835_: u8 = 0;
    let mut v_a_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3839_: u8 = 0;
    let mut v___x_3841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3843_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3796_ = crate::leanh::lean_ctor_get(v_t_3789_, 0);
                v_tail_3797_ = crate::leanh::lean_ctor_get(v_t_3789_, 1);
                crate::leanh::lean_inc_ref(v___x_3788_);
                crate::leanh::lean_inc_ref(v_init_3790_);
                v___x_3798_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__0(v_init_3790_, v_goal_3787_, v___x_3788_, v_root_3796_, v_init_3790_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
                crate::leanh::lean_dec_ref(v_init_3790_);
                if crate::leanh::lean_obj_tag(v___x_3798_) == 0 {
                    v_a_3799_ = crate::leanh::lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3835_ = (!crate::leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3835_ == 0 {
                        v___x_3801_ = v___x_3798_;
                        v_isShared_3802_ = v_isSharedCheck_3835_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3799_);
                        crate::leanh::lean_dec(v___x_3798_);
                        v___x_3801_ = crate::leanh::lean_box(0);
                        v_isShared_3802_ = v_isSharedCheck_3835_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v___x_3788_);
                    v_a_3836_ = crate::leanh::lean_ctor_get(v___x_3798_, 0);
                    v_isSharedCheck_3843_ = (!crate::leanh::lean_is_exclusive(v___x_3798_)) as u8;
                    if v_isSharedCheck_3843_ == 0 {
                        v___x_3838_ = v___x_3798_;
                        v_isShared_3839_ = v_isSharedCheck_3843_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3836_);
                        crate::leanh::lean_dec(v___x_3798_);
                        v___x_3838_ = crate::leanh::lean_box(0);
                        v_isShared_3839_ = v_isSharedCheck_3843_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_3799_) == 0 {
                    crate::leanh::lean_dec_ref(v___x_3788_);
                    v_a_3803_ = crate::leanh::lean_ctor_get(v_a_3799_, 0);
                    crate::leanh::lean_inc(v_a_3803_);
                    crate::leanh::lean_dec_ref_known(v_a_3799_, 1);
                    if v_isShared_3802_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3801_, 0, v_a_3803_);
                        v___x_3805_ = v___x_3801_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3806_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3806_, 0, v_a_3803_);
                        v___x_3805_ = v_reuseFailAlloc_3806_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3801_);
                    v_a_3807_ = crate::leanh::lean_ctor_get(v_a_3799_, 0);
                    crate::leanh::lean_inc(v_a_3807_);
                    crate::leanh::lean_dec_ref_known(v_a_3799_, 1);
                    v___x_3808_ = crate::leanh::lean_box(0);
                    v___x_3809_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3809_, 0, v___x_3808_);
                    crate::leanh::lean_ctor_set(v___x_3809_, 1, v_a_3807_);
                    v_sz_3810_ = lean_array_size(v_tail_3797_);
                    v___x_3811_ = 0usize;
                    v___x_3812_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0_spec__1(v_goal_3787_, v___x_3788_, v_tail_3797_, v_sz_3810_, v___x_3811_, v___x_3809_, v___y_3791_, v___y_3792_, v___y_3793_, v___y_3794_);
                    if crate::leanh::lean_obj_tag(v___x_3812_) == 0 {
                        v_a_3813_ = crate::leanh::lean_ctor_get(v___x_3812_, 0);
                        v_isSharedCheck_3826_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3812_)) as u8;
                        if v_isSharedCheck_3826_ == 0 {
                            v___x_3815_ = v___x_3812_;
                            v_isShared_3816_ = v_isSharedCheck_3826_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3813_);
                            crate::leanh::lean_dec(v___x_3812_);
                            v___x_3815_ = crate::leanh::lean_box(0);
                            v_isShared_3816_ = v_isSharedCheck_3826_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3827_ = crate::leanh::lean_ctor_get(v___x_3812_, 0);
                        v_isSharedCheck_3834_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3812_)) as u8;
                        if v_isSharedCheck_3834_ == 0 {
                            v___x_3829_ = v___x_3812_;
                            v_isShared_3830_ = v_isSharedCheck_3834_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3827_);
                            crate::leanh::lean_dec(v___x_3812_);
                            v___x_3829_ = crate::leanh::lean_box(0);
                            v_isShared_3830_ = v_isSharedCheck_3834_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3805_;
            }
            3 => {
                v_fst_3817_ = crate::leanh::lean_ctor_get(v_a_3813_, 0);
                if crate::leanh::lean_obj_tag(v_fst_3817_) == 0 {
                    v_snd_3818_ = crate::leanh::lean_ctor_get(v_a_3813_, 1);
                    crate::leanh::lean_inc(v_snd_3818_);
                    crate::leanh::lean_dec(v_a_3813_);
                    if v_isShared_3816_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3815_, 0, v_snd_3818_);
                        v___x_3820_ = v___x_3815_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3821_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3821_, 0, v_snd_3818_);
                        v___x_3820_ = v_reuseFailAlloc_3821_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_3817_);
                    crate::leanh::lean_dec(v_a_3813_);
                    v_val_3822_ = crate::leanh::lean_ctor_get(v_fst_3817_, 0);
                    crate::leanh::lean_inc(v_val_3822_);
                    crate::leanh::lean_dec_ref_known(v_fst_3817_, 1);
                    if v_isShared_3816_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3815_, 0, v_val_3822_);
                        v___x_3824_ = v___x_3815_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3825_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3825_, 0, v_val_3822_);
                        v___x_3824_ = v_reuseFailAlloc_3825_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3820_;
            }
            5 => {
                return v___x_3824_;
            }
            6 => {
                if v_isShared_3830_ == 0 {
                    v___x_3832_ = v___x_3829_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3833_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3833_, 0, v_a_3827_);
                    v___x_3832_ = v_reuseFailAlloc_3833_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3832_;
            }
            8 => {
                if v_isShared_3839_ == 0 {
                    v___x_3841_ = v___x_3838_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3842_, 0, v_a_3836_);
                    v___x_3841_ = v_reuseFailAlloc_3842_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3841_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0___boxed(
    mut v_goal_3844_: *mut crate::leanh::LeanObject,
    mut v___x_3845_: *mut crate::leanh::LeanObject,
    mut v_t_3846_: *mut crate::leanh::LeanObject,
    mut v_init_3847_: *mut crate::leanh::LeanObject,
    mut v___y_3848_: *mut crate::leanh::LeanObject,
    mut v___y_3849_: *mut crate::leanh::LeanObject,
    mut v___y_3850_: *mut crate::leanh::LeanObject,
    mut v___y_3851_: *mut crate::leanh::LeanObject,
    mut v___y_3852_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3853_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(
            v_goal_3844_,
            v___x_3845_,
            v_t_3846_,
            v_init_3847_,
            v___y_3848_,
            v___y_3849_,
            v___y_3850_,
            v___y_3851_,
        );
    crate::leanh::lean_dec(v___y_3851_);
    crate::leanh::lean_dec_ref(v___y_3850_);
    crate::leanh::lean_dec(v___y_3849_);
    crate::leanh::lean_dec_ref(v___y_3848_);
    crate::leanh::lean_dec_ref(v_t_3846_);
    crate::leanh::lean_dec_ref(v_goal_3844_);
    return v_res_3853_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(
    mut v_goal_3854_: *mut crate::leanh::LeanObject,
    mut v_as_3855_: *mut crate::leanh::LeanObject,
    mut v_sz_3856_: usize,
    mut v_i_3857_: usize,
    mut v_b_3858_: *mut crate::leanh::LeanObject,
    mut v___y_3859_: *mut crate::leanh::LeanObject,
    mut v___y_3860_: *mut crate::leanh::LeanObject,
    mut v___y_3861_: *mut crate::leanh::LeanObject,
    mut v___y_3862_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3864_: u8 = 0;
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3869_: u8 = 0;
    let mut v_a_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: usize = 0;
    let mut v___x_3880_: usize = 0;
    let mut v_reuseFailAlloc_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3892_: u8 = 0;
    let mut v___x_3894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3896_: u8 = 0;
    let mut v_isSharedCheck_3897_: u8 = 0;
    let mut v_unused_3898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3864_ = lean_usize_dec_lt(v_i_3857_, v_sz_3856_);
                if v___x_3864_ == 0 {
                    v___x_3865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3865_, 0, v_b_3858_);
                    return v___x_3865_;
                } else {
                    v_snd_3866_ = crate::leanh::lean_ctor_get(v_b_3858_, 1);
                    v_isSharedCheck_3897_ = (!crate::leanh::lean_is_exclusive(v_b_3858_)) as u8;
                    if v_isSharedCheck_3897_ == 0 {
                        v_unused_3898_ = crate::leanh::lean_ctor_get(v_b_3858_, 0);
                        crate::leanh::lean_dec(v_unused_3898_);
                        v___x_3868_ = v_b_3858_;
                        v_isShared_3869_ = v_isSharedCheck_3897_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3866_);
                        crate::leanh::lean_dec(v_b_3858_);
                        v___x_3868_ = crate::leanh::lean_box(0);
                        v_isShared_3869_ = v_isSharedCheck_3897_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3870_ = lean_array_uget_borrowed(v_as_3855_, v_i_3857_);
                crate::leanh::lean_inc(v_a_3870_);
                v___x_3871_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3854_,
                    v_a_3870_,
                    v___y_3859_,
                    v___y_3860_,
                    v___y_3861_,
                    v___y_3862_,
                );
                if crate::leanh::lean_obj_tag(v___x_3871_) == 0 {
                    v_a_3872_ = crate::leanh::lean_ctor_get(v___x_3871_, 0);
                    crate::leanh::lean_inc(v_a_3872_);
                    crate::leanh::lean_dec_ref_known(v___x_3871_, 1);
                    v_self_3873_ = crate::leanh::lean_ctor_get(v_a_3872_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_3873_, 2);
                    crate::leanh::lean_dec(v_a_3872_);
                    v___x_3874_ = crate::leanh::lean_box(0);
                    v___x_3883_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_3873_);
                    if crate::leanh::lean_obj_tag(v___x_3883_) == 1 {
                        v_val_3884_ = crate::leanh::lean_ctor_get(v___x_3883_, 0);
                        crate::leanh::lean_inc(v_val_3884_);
                        crate::leanh::lean_dec_ref_known(v___x_3883_, 1);
                        v___x_3885_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_3866_, v_val_3884_);
                        if crate::leanh::lean_obj_tag(v___x_3885_) == 0 {
                            v___x_3886_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_3866_, v_self_3873_);
                            crate::leanh::lean_dec_ref(v_self_3873_);
                            if crate::leanh::lean_obj_tag(v___x_3886_) == 1 {
                                v_val_3887_ = crate::leanh::lean_ctor_get(v___x_3886_, 0);
                                crate::leanh::lean_inc(v_val_3887_);
                                crate::leanh::lean_dec_ref_known(v___x_3886_, 1);
                                v___x_3888_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3854_,
                                    v_val_3884_,
                                    v_val_3887_,
                                    v_snd_3866_,
                                );
                                v_a_3876_ = v___x_3888_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3886_);
                                crate::leanh::lean_dec(v_val_3884_);
                                v_a_3876_ = v_snd_3866_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3885_, 1);
                            crate::leanh::lean_dec(v_val_3884_);
                            crate::leanh::lean_dec_ref(v_self_3873_);
                            v_a_3876_ = v_snd_3866_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3883_);
                        crate::leanh::lean_dec_ref(v_self_3873_);
                        v_a_3876_ = v_snd_3866_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3868_);
                    crate::leanh::lean_dec(v_snd_3866_);
                    v_a_3889_ = crate::leanh::lean_ctor_get(v___x_3871_, 0);
                    v_isSharedCheck_3896_ = (!crate::leanh::lean_is_exclusive(v___x_3871_)) as u8;
                    if v_isSharedCheck_3896_ == 0 {
                        v___x_3891_ = v___x_3871_;
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3889_);
                        crate::leanh::lean_dec(v___x_3871_);
                        v___x_3891_ = crate::leanh::lean_box(0);
                        v_isShared_3892_ = v_isSharedCheck_3896_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3869_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3868_, 1, v_a_3876_);
                    crate::leanh::lean_ctor_set(v___x_3868_, 0, v___x_3874_);
                    v___x_3878_ = v___x_3868_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3882_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3874_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3882_, 1, v_a_3876_);
                    v___x_3878_ = v_reuseFailAlloc_3882_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3879_ = 1usize;
                v___x_3880_ = lean_usize_add(v_i_3857_, v___x_3879_);
                v_i_3857_ = v___x_3880_;
                v_b_3858_ = v___x_3878_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_3892_ == 0 {
                    v___x_3894_ = v___x_3891_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3895_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3895_, 0, v_a_3889_);
                    v___x_3894_ = v_reuseFailAlloc_3895_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3894_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10___boxed(
    mut v_goal_3899_: *mut crate::leanh::LeanObject,
    mut v_as_3900_: *mut crate::leanh::LeanObject,
    mut v_sz_3901_: *mut crate::leanh::LeanObject,
    mut v_i_3902_: *mut crate::leanh::LeanObject,
    mut v_b_3903_: *mut crate::leanh::LeanObject,
    mut v___y_3904_: *mut crate::leanh::LeanObject,
    mut v___y_3905_: *mut crate::leanh::LeanObject,
    mut v___y_3906_: *mut crate::leanh::LeanObject,
    mut v___y_3907_: *mut crate::leanh::LeanObject,
    mut v___y_3908_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3909_: usize = 0;
    let mut v_i_boxed_3910_: usize = 0;
    let mut v_res_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3909_ = crate::leanh::lean_unbox_usize(v_sz_3901_);
    crate::leanh::lean_dec(v_sz_3901_);
    v_i_boxed_3910_ = crate::leanh::lean_unbox_usize(v_i_3902_);
    crate::leanh::lean_dec(v_i_3902_);
    v_res_3911_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_3899_, v_as_3900_, v_sz_boxed_3909_, v_i_boxed_3910_, v_b_3903_, v___y_3904_, v___y_3905_, v___y_3906_, v___y_3907_);
    crate::leanh::lean_dec(v___y_3907_);
    crate::leanh::lean_dec_ref(v___y_3906_);
    crate::leanh::lean_dec(v___y_3905_);
    crate::leanh::lean_dec_ref(v___y_3904_);
    crate::leanh::lean_dec_ref(v_as_3900_);
    crate::leanh::lean_dec_ref(v_goal_3899_);
    return v_res_3911_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(
    mut v_goal_3912_: *mut crate::leanh::LeanObject,
    mut v_as_3913_: *mut crate::leanh::LeanObject,
    mut v_sz_3914_: usize,
    mut v_i_3915_: usize,
    mut v_b_3916_: *mut crate::leanh::LeanObject,
    mut v___y_3917_: *mut crate::leanh::LeanObject,
    mut v___y_3918_: *mut crate::leanh::LeanObject,
    mut v___y_3919_: *mut crate::leanh::LeanObject,
    mut v___y_3920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3922_: u8 = 0;
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3927_: u8 = 0;
    let mut v_a_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: usize = 0;
    let mut v___x_3938_: usize = 0;
    let mut v___x_3939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3943_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3946_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3947_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3950_: u8 = 0;
    let mut v___x_3952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3953_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3954_: u8 = 0;
    let mut v_isSharedCheck_3955_: u8 = 0;
    let mut v_unused_3956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3922_ = lean_usize_dec_lt(v_i_3915_, v_sz_3914_);
                if v___x_3922_ == 0 {
                    v___x_3923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3923_, 0, v_b_3916_);
                    return v___x_3923_;
                } else {
                    v_snd_3924_ = crate::leanh::lean_ctor_get(v_b_3916_, 1);
                    v_isSharedCheck_3955_ = (!crate::leanh::lean_is_exclusive(v_b_3916_)) as u8;
                    if v_isSharedCheck_3955_ == 0 {
                        v_unused_3956_ = crate::leanh::lean_ctor_get(v_b_3916_, 0);
                        crate::leanh::lean_dec(v_unused_3956_);
                        v___x_3926_ = v_b_3916_;
                        v_isShared_3927_ = v_isSharedCheck_3955_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3924_);
                        crate::leanh::lean_dec(v_b_3916_);
                        v___x_3926_ = crate::leanh::lean_box(0);
                        v_isShared_3927_ = v_isSharedCheck_3955_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3928_ = lean_array_uget_borrowed(v_as_3913_, v_i_3915_);
                crate::leanh::lean_inc(v_a_3928_);
                v___x_3929_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3912_,
                    v_a_3928_,
                    v___y_3917_,
                    v___y_3918_,
                    v___y_3919_,
                    v___y_3920_,
                );
                if crate::leanh::lean_obj_tag(v___x_3929_) == 0 {
                    v_a_3930_ = crate::leanh::lean_ctor_get(v___x_3929_, 0);
                    crate::leanh::lean_inc(v_a_3930_);
                    crate::leanh::lean_dec_ref_known(v___x_3929_, 1);
                    v_self_3931_ = crate::leanh::lean_ctor_get(v_a_3930_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_3931_, 2);
                    crate::leanh::lean_dec(v_a_3930_);
                    v___x_3932_ = crate::leanh::lean_box(0);
                    v___x_3941_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_3931_);
                    if crate::leanh::lean_obj_tag(v___x_3941_) == 1 {
                        v_val_3942_ = crate::leanh::lean_ctor_get(v___x_3941_, 0);
                        crate::leanh::lean_inc(v_val_3942_);
                        crate::leanh::lean_dec_ref_known(v___x_3941_, 1);
                        v___x_3943_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_3924_, v_val_3942_);
                        if crate::leanh::lean_obj_tag(v___x_3943_) == 0 {
                            v___x_3944_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_3924_, v_self_3931_);
                            crate::leanh::lean_dec_ref(v_self_3931_);
                            if crate::leanh::lean_obj_tag(v___x_3944_) == 1 {
                                v_val_3945_ = crate::leanh::lean_ctor_get(v___x_3944_, 0);
                                crate::leanh::lean_inc(v_val_3945_);
                                crate::leanh::lean_dec_ref_known(v___x_3944_, 1);
                                v___x_3946_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3912_,
                                    v_val_3942_,
                                    v_val_3945_,
                                    v_snd_3924_,
                                );
                                v_a_3934_ = v___x_3946_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_3944_);
                                crate::leanh::lean_dec(v_val_3942_);
                                v_a_3934_ = v_snd_3924_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_3943_, 1);
                            crate::leanh::lean_dec(v_val_3942_);
                            crate::leanh::lean_dec_ref(v_self_3931_);
                            v_a_3934_ = v_snd_3924_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3941_);
                        crate::leanh::lean_dec_ref(v_self_3931_);
                        v_a_3934_ = v_snd_3924_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3926_);
                    crate::leanh::lean_dec(v_snd_3924_);
                    v_a_3947_ = crate::leanh::lean_ctor_get(v___x_3929_, 0);
                    v_isSharedCheck_3954_ = (!crate::leanh::lean_is_exclusive(v___x_3929_)) as u8;
                    if v_isSharedCheck_3954_ == 0 {
                        v___x_3949_ = v___x_3929_;
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_3947_);
                        crate::leanh::lean_dec(v___x_3929_);
                        v___x_3949_ = crate::leanh::lean_box(0);
                        v_isShared_3950_ = v_isSharedCheck_3954_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3927_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3926_, 1, v_a_3934_);
                    crate::leanh::lean_ctor_set(v___x_3926_, 0, v___x_3932_);
                    v___x_3936_ = v___x_3926_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 0, v___x_3932_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3940_, 1, v_a_3934_);
                    v___x_3936_ = v_reuseFailAlloc_3940_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3937_ = 1usize;
                v___x_3938_ = lean_usize_add(v_i_3915_, v___x_3937_);
                v___x_3939_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4_spec__10(v_goal_3912_, v_as_3913_, v_sz_3914_, v___x_3938_, v___x_3936_, v___y_3917_, v___y_3918_, v___y_3919_, v___y_3920_);
                return v___x_3939_;
            }
            4 => {
                if v_isShared_3950_ == 0 {
                    v___x_3952_ = v___x_3949_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_3953_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3953_, 0, v_a_3947_);
                    v___x_3952_ = v_reuseFailAlloc_3953_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_3952_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4___boxed(
    mut v_goal_3957_: *mut crate::leanh::LeanObject,
    mut v_as_3958_: *mut crate::leanh::LeanObject,
    mut v_sz_3959_: *mut crate::leanh::LeanObject,
    mut v_i_3960_: *mut crate::leanh::LeanObject,
    mut v_b_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_3967_: usize = 0;
    let mut v_i_boxed_3968_: usize = 0;
    let mut v_res_3969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_3967_ = crate::leanh::lean_unbox_usize(v_sz_3959_);
    crate::leanh::lean_dec(v_sz_3959_);
    v_i_boxed_3968_ = crate::leanh::lean_unbox_usize(v_i_3960_);
    crate::leanh::lean_dec(v_i_3960_);
    v_res_3969_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_3957_, v_as_3958_, v_sz_boxed_3967_, v_i_boxed_3968_, v_b_3961_, v___y_3962_, v___y_3963_, v___y_3964_, v___y_3965_);
    crate::leanh::lean_dec(v___y_3965_);
    crate::leanh::lean_dec_ref(v___y_3964_);
    crate::leanh::lean_dec(v___y_3963_);
    crate::leanh::lean_dec_ref(v___y_3962_);
    crate::leanh::lean_dec_ref(v_as_3958_);
    crate::leanh::lean_dec_ref(v_goal_3957_);
    return v_res_3969_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(
    mut v_goal_3970_: *mut crate::leanh::LeanObject,
    mut v_as_3971_: *mut crate::leanh::LeanObject,
    mut v_sz_3972_: usize,
    mut v_i_3973_: usize,
    mut v_b_3974_: *mut crate::leanh::LeanObject,
    mut v___y_3975_: *mut crate::leanh::LeanObject,
    mut v___y_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3980_: u8 = 0;
    let mut v___x_3981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_3982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3985_: u8 = 0;
    let mut v_a_3986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3987_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3990_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: usize = 0;
    let mut v___x_3996_: usize = 0;
    let mut v_reuseFailAlloc_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4005_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4007_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4008_: u8 = 0;
    let mut v___x_4010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4012_: u8 = 0;
    let mut v_isSharedCheck_4013_: u8 = 0;
    let mut v_unused_4014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3980_ = lean_usize_dec_lt(v_i_3973_, v_sz_3972_);
                if v___x_3980_ == 0 {
                    v___x_3981_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3981_, 0, v_b_3974_);
                    return v___x_3981_;
                } else {
                    v_snd_3982_ = crate::leanh::lean_ctor_get(v_b_3974_, 1);
                    v_isSharedCheck_4013_ = (!crate::leanh::lean_is_exclusive(v_b_3974_)) as u8;
                    if v_isSharedCheck_4013_ == 0 {
                        v_unused_4014_ = crate::leanh::lean_ctor_get(v_b_3974_, 0);
                        crate::leanh::lean_dec(v_unused_4014_);
                        v___x_3984_ = v_b_3974_;
                        v_isShared_3985_ = v_isSharedCheck_4013_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_3982_);
                        crate::leanh::lean_dec(v_b_3974_);
                        v___x_3984_ = crate::leanh::lean_box(0);
                        v_isShared_3985_ = v_isSharedCheck_4013_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_3986_ = lean_array_uget_borrowed(v_as_3971_, v_i_3973_);
                crate::leanh::lean_inc(v_a_3986_);
                v___x_3987_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_3970_,
                    v_a_3986_,
                    v___y_3975_,
                    v___y_3976_,
                    v___y_3977_,
                    v___y_3978_,
                );
                if crate::leanh::lean_obj_tag(v___x_3987_) == 0 {
                    v_a_3988_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    crate::leanh::lean_inc(v_a_3988_);
                    crate::leanh::lean_dec_ref_known(v___x_3987_, 1);
                    v_self_3989_ = crate::leanh::lean_ctor_get(v_a_3988_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_3989_, 2);
                    crate::leanh::lean_dec(v_a_3988_);
                    v___x_3990_ = crate::leanh::lean_box(0);
                    v___x_3999_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_3989_);
                    if crate::leanh::lean_obj_tag(v___x_3999_) == 1 {
                        v_val_4000_ = crate::leanh::lean_ctor_get(v___x_3999_, 0);
                        crate::leanh::lean_inc(v_val_4000_);
                        crate::leanh::lean_dec_ref_known(v___x_3999_, 1);
                        v___x_4001_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_3982_, v_val_4000_);
                        if crate::leanh::lean_obj_tag(v___x_4001_) == 0 {
                            v___x_4002_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_3982_, v_self_3989_);
                            crate::leanh::lean_dec_ref(v_self_3989_);
                            if crate::leanh::lean_obj_tag(v___x_4002_) == 1 {
                                v_val_4003_ = crate::leanh::lean_ctor_get(v___x_4002_, 0);
                                crate::leanh::lean_inc(v_val_4003_);
                                crate::leanh::lean_dec_ref_known(v___x_4002_, 1);
                                v___x_4004_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_3970_,
                                    v_val_4000_,
                                    v_val_4003_,
                                    v_snd_3982_,
                                );
                                v_a_3992_ = v___x_4004_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4002_);
                                crate::leanh::lean_dec(v_val_4000_);
                                v_a_3992_ = v_snd_3982_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4001_, 1);
                            crate::leanh::lean_dec(v_val_4000_);
                            crate::leanh::lean_dec_ref(v_self_3989_);
                            v_a_3992_ = v_snd_3982_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_3999_);
                        crate::leanh::lean_dec_ref(v_self_3989_);
                        v_a_3992_ = v_snd_3982_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_3984_);
                    crate::leanh::lean_dec(v_snd_3982_);
                    v_a_4005_ = crate::leanh::lean_ctor_get(v___x_3987_, 0);
                    v_isSharedCheck_4012_ = (!crate::leanh::lean_is_exclusive(v___x_3987_)) as u8;
                    if v_isSharedCheck_4012_ == 0 {
                        v___x_4007_ = v___x_3987_;
                        v_isShared_4008_ = v_isSharedCheck_4012_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4005_);
                        crate::leanh::lean_dec(v___x_3987_);
                        v___x_4007_ = crate::leanh::lean_box(0);
                        v_isShared_4008_ = v_isSharedCheck_4012_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_3985_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_3984_, 1, v_a_3992_);
                    crate::leanh::lean_ctor_set(v___x_3984_, 0, v___x_3990_);
                    v___x_3994_ = v___x_3984_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3998_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3998_, 0, v___x_3990_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3998_, 1, v_a_3992_);
                    v___x_3994_ = v_reuseFailAlloc_3998_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_3995_ = 1usize;
                v___x_3996_ = lean_usize_add(v_i_3973_, v___x_3995_);
                v_i_3973_ = v___x_3996_;
                v_b_3974_ = v___x_3994_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_4008_ == 0 {
                    v___x_4010_ = v___x_4007_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4011_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4011_, 0, v_a_4005_);
                    v___x_4010_ = v_reuseFailAlloc_4011_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4010_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10___boxed(
    mut v_goal_4015_: *mut crate::leanh::LeanObject,
    mut v_as_4016_: *mut crate::leanh::LeanObject,
    mut v_sz_4017_: *mut crate::leanh::LeanObject,
    mut v_i_4018_: *mut crate::leanh::LeanObject,
    mut v_b_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
    mut v___y_4021_: *mut crate::leanh::LeanObject,
    mut v___y_4022_: *mut crate::leanh::LeanObject,
    mut v___y_4023_: *mut crate::leanh::LeanObject,
    mut v___y_4024_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4025_: usize = 0;
    let mut v_i_boxed_4026_: usize = 0;
    let mut v_res_4027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4025_ = crate::leanh::lean_unbox_usize(v_sz_4017_);
    crate::leanh::lean_dec(v_sz_4017_);
    v_i_boxed_4026_ = crate::leanh::lean_unbox_usize(v_i_4018_);
    crate::leanh::lean_dec(v_i_4018_);
    v_res_4027_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_4015_, v_as_4016_, v_sz_boxed_4025_, v_i_boxed_4026_, v_b_4019_, v___y_4020_, v___y_4021_, v___y_4022_, v___y_4023_);
    crate::leanh::lean_dec(v___y_4023_);
    crate::leanh::lean_dec_ref(v___y_4022_);
    crate::leanh::lean_dec(v___y_4021_);
    crate::leanh::lean_dec_ref(v___y_4020_);
    crate::leanh::lean_dec_ref(v_as_4016_);
    crate::leanh::lean_dec_ref(v_goal_4015_);
    return v_res_4027_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(
    mut v_goal_4028_: *mut crate::leanh::LeanObject,
    mut v_as_4029_: *mut crate::leanh::LeanObject,
    mut v_sz_4030_: usize,
    mut v_i_4031_: usize,
    mut v_b_4032_: *mut crate::leanh::LeanObject,
    mut v___y_4033_: *mut crate::leanh::LeanObject,
    mut v___y_4034_: *mut crate::leanh::LeanObject,
    mut v___y_4035_: *mut crate::leanh::LeanObject,
    mut v___y_4036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4038_: u8 = 0;
    let mut v___x_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4043_: u8 = 0;
    let mut v_a_4044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4053_: usize = 0;
    let mut v___x_4054_: usize = 0;
    let mut v___x_4055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4057_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4066_: u8 = 0;
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4070_: u8 = 0;
    let mut v_isSharedCheck_4071_: u8 = 0;
    let mut v_unused_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4038_ = lean_usize_dec_lt(v_i_4031_, v_sz_4030_);
                if v___x_4038_ == 0 {
                    v___x_4039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4039_, 0, v_b_4032_);
                    return v___x_4039_;
                } else {
                    v_snd_4040_ = crate::leanh::lean_ctor_get(v_b_4032_, 1);
                    v_isSharedCheck_4071_ = (!crate::leanh::lean_is_exclusive(v_b_4032_)) as u8;
                    if v_isSharedCheck_4071_ == 0 {
                        v_unused_4072_ = crate::leanh::lean_ctor_get(v_b_4032_, 0);
                        crate::leanh::lean_dec(v_unused_4072_);
                        v___x_4042_ = v_b_4032_;
                        v_isShared_4043_ = v_isSharedCheck_4071_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4040_);
                        crate::leanh::lean_dec(v_b_4032_);
                        v___x_4042_ = crate::leanh::lean_box(0);
                        v_isShared_4043_ = v_isSharedCheck_4071_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4044_ = lean_array_uget_borrowed(v_as_4029_, v_i_4031_);
                crate::leanh::lean_inc(v_a_4044_);
                v___x_4045_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_4028_,
                    v_a_4044_,
                    v___y_4033_,
                    v___y_4034_,
                    v___y_4035_,
                    v___y_4036_,
                );
                if crate::leanh::lean_obj_tag(v___x_4045_) == 0 {
                    v_a_4046_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                    crate::leanh::lean_inc(v_a_4046_);
                    crate::leanh::lean_dec_ref_known(v___x_4045_, 1);
                    v_self_4047_ = crate::leanh::lean_ctor_get(v_a_4046_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_4047_, 2);
                    crate::leanh::lean_dec(v_a_4046_);
                    v___x_4048_ = crate::leanh::lean_box(0);
                    v___x_4057_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_toQ_x3f(v_self_4047_);
                    if crate::leanh::lean_obj_tag(v___x_4057_) == 1 {
                        v_val_4058_ = crate::leanh::lean_ctor_get(v___x_4057_, 0);
                        crate::leanh::lean_inc(v_val_4058_);
                        crate::leanh::lean_dec_ref_known(v___x_4057_, 1);
                        v___x_4059_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_4040_, v_val_4058_);
                        if crate::leanh::lean_obj_tag(v___x_4059_) == 0 {
                            v___x_4060_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_evalTermAt_x3f_go_spec__0___redArg(v_snd_4040_, v_self_4047_);
                            crate::leanh::lean_dec_ref(v_self_4047_);
                            if crate::leanh::lean_obj_tag(v___x_4060_) == 1 {
                                v_val_4061_ = crate::leanh::lean_ctor_get(v___x_4060_, 0);
                                crate::leanh::lean_inc(v_val_4061_);
                                crate::leanh::lean_dec_ref_known(v___x_4060_, 1);
                                v___x_4062_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_4028_,
                                    v_val_4058_,
                                    v_val_4061_,
                                    v_snd_4040_,
                                );
                                v_a_4050_ = v___x_4062_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_4060_);
                                crate::leanh::lean_dec(v_val_4058_);
                                v_a_4050_ = v_snd_4040_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_4059_, 1);
                            crate::leanh::lean_dec(v_val_4058_);
                            crate::leanh::lean_dec_ref(v_self_4047_);
                            v_a_4050_ = v_snd_4040_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4057_);
                        crate::leanh::lean_dec_ref(v_self_4047_);
                        v_a_4050_ = v_snd_4040_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4042_);
                    crate::leanh::lean_dec(v_snd_4040_);
                    v_a_4063_ = crate::leanh::lean_ctor_get(v___x_4045_, 0);
                    v_isSharedCheck_4070_ = (!crate::leanh::lean_is_exclusive(v___x_4045_)) as u8;
                    if v_isSharedCheck_4070_ == 0 {
                        v___x_4065_ = v___x_4045_;
                        v_isShared_4066_ = v_isSharedCheck_4070_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4063_);
                        crate::leanh::lean_dec(v___x_4045_);
                        v___x_4065_ = crate::leanh::lean_box(0);
                        v_isShared_4066_ = v_isSharedCheck_4070_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4043_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4042_, 1, v_a_4050_);
                    crate::leanh::lean_ctor_set(v___x_4042_, 0, v___x_4048_);
                    v___x_4052_ = v___x_4042_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4056_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 0, v___x_4048_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4056_, 1, v_a_4050_);
                    v___x_4052_ = v_reuseFailAlloc_4056_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4053_ = 1usize;
                v___x_4054_ = lean_usize_add(v_i_4031_, v___x_4053_);
                v___x_4055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8_spec__10(v_goal_4028_, v_as_4029_, v_sz_4030_, v___x_4054_, v___x_4052_, v___y_4033_, v___y_4034_, v___y_4035_, v___y_4036_);
                return v___x_4055_;
            }
            4 => {
                if v_isShared_4066_ == 0 {
                    v___x_4068_ = v___x_4065_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4069_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4069_, 0, v_a_4063_);
                    v___x_4068_ = v_reuseFailAlloc_4069_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4068_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8___boxed(
    mut v_goal_4073_: *mut crate::leanh::LeanObject,
    mut v_as_4074_: *mut crate::leanh::LeanObject,
    mut v_sz_4075_: *mut crate::leanh::LeanObject,
    mut v_i_4076_: *mut crate::leanh::LeanObject,
    mut v_b_4077_: *mut crate::leanh::LeanObject,
    mut v___y_4078_: *mut crate::leanh::LeanObject,
    mut v___y_4079_: *mut crate::leanh::LeanObject,
    mut v___y_4080_: *mut crate::leanh::LeanObject,
    mut v___y_4081_: *mut crate::leanh::LeanObject,
    mut v___y_4082_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4083_: usize = 0;
    let mut v_i_boxed_4084_: usize = 0;
    let mut v_res_4085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4083_ = crate::leanh::lean_unbox_usize(v_sz_4075_);
    crate::leanh::lean_dec(v_sz_4075_);
    v_i_boxed_4084_ = crate::leanh::lean_unbox_usize(v_i_4076_);
    crate::leanh::lean_dec(v_i_4076_);
    v_res_4085_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_4073_, v_as_4074_, v_sz_boxed_4083_, v_i_boxed_4084_, v_b_4077_, v___y_4078_, v___y_4079_, v___y_4080_, v___y_4081_);
    crate::leanh::lean_dec(v___y_4081_);
    crate::leanh::lean_dec_ref(v___y_4080_);
    crate::leanh::lean_dec(v___y_4079_);
    crate::leanh::lean_dec_ref(v___y_4078_);
    crate::leanh::lean_dec_ref(v_as_4074_);
    crate::leanh::lean_dec_ref(v_goal_4073_);
    return v_res_4085_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(
    mut v_init_4086_: *mut crate::leanh::LeanObject,
    mut v_goal_4087_: *mut crate::leanh::LeanObject,
    mut v_n_4088_: *mut crate::leanh::LeanObject,
    mut v_b_4089_: *mut crate::leanh::LeanObject,
    mut v___y_4090_: *mut crate::leanh::LeanObject,
    mut v___y_4091_: *mut crate::leanh::LeanObject,
    mut v___y_4092_: *mut crate::leanh::LeanObject,
    mut v___y_4093_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_4095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4098_: usize = 0;
    let mut v___x_4099_: usize = 0;
    let mut v___x_4100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4104_: u8 = 0;
    let mut v_fst_4105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4115_: u8 = 0;
    let mut v_a_4116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4119_: u8 = 0;
    let mut v___x_4121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4122_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4123_: u8 = 0;
    let mut v_vs_4124_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4127_: usize = 0;
    let mut v___x_4128_: usize = 0;
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v_fst_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4144_: u8 = 0;
    let mut v_a_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4148_: u8 = 0;
    let mut v___x_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4151_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4152_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_4088_) == 0 {
                    v_cs_4095_ = crate::leanh::lean_ctor_get(v_n_4088_, 0);
                    v___x_4096_ = crate::leanh::lean_box(0);
                    v___x_4097_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4097_, 0, v___x_4096_);
                    crate::leanh::lean_ctor_set(v___x_4097_, 1, v_b_4089_);
                    v_sz_4098_ = lean_array_size(v_cs_4095_);
                    v___x_4099_ = 0usize;
                    v___x_4100_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_4086_, v_goal_4087_, v_cs_4095_, v_sz_4098_, v___x_4099_, v___x_4097_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
                    if crate::leanh::lean_obj_tag(v___x_4100_) == 0 {
                        v_a_4101_ = crate::leanh::lean_ctor_get(v___x_4100_, 0);
                        v_isSharedCheck_4115_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4100_)) as u8;
                        if v_isSharedCheck_4115_ == 0 {
                            v___x_4103_ = v___x_4100_;
                            v_isShared_4104_ = v_isSharedCheck_4115_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4101_);
                            crate::leanh::lean_dec(v___x_4100_);
                            v___x_4103_ = crate::leanh::lean_box(0);
                            v_isShared_4104_ = v_isSharedCheck_4115_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4116_ = crate::leanh::lean_ctor_get(v___x_4100_, 0);
                        v_isSharedCheck_4123_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4100_)) as u8;
                        if v_isSharedCheck_4123_ == 0 {
                            v___x_4118_ = v___x_4100_;
                            v_isShared_4119_ = v_isSharedCheck_4123_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4116_);
                            crate::leanh::lean_dec(v___x_4100_);
                            v___x_4118_ = crate::leanh::lean_box(0);
                            v_isShared_4119_ = v_isSharedCheck_4123_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4124_ = crate::leanh::lean_ctor_get(v_n_4088_, 0);
                    v___x_4125_ = crate::leanh::lean_box(0);
                    v___x_4126_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4126_, 0, v___x_4125_);
                    crate::leanh::lean_ctor_set(v___x_4126_, 1, v_b_4089_);
                    v_sz_4127_ = lean_array_size(v_vs_4124_);
                    v___x_4128_ = 0usize;
                    v___x_4129_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__8(v_goal_4087_, v_vs_4124_, v_sz_4127_, v___x_4128_, v___x_4126_, v___y_4090_, v___y_4091_, v___y_4092_, v___y_4093_);
                    if crate::leanh::lean_obj_tag(v___x_4129_) == 0 {
                        v_a_4130_ = crate::leanh::lean_ctor_get(v___x_4129_, 0);
                        v_isSharedCheck_4144_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4129_)) as u8;
                        if v_isSharedCheck_4144_ == 0 {
                            v___x_4132_ = v___x_4129_;
                            v_isShared_4133_ = v_isSharedCheck_4144_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4130_);
                            crate::leanh::lean_dec(v___x_4129_);
                            v___x_4132_ = crate::leanh::lean_box(0);
                            v_isShared_4133_ = v_isSharedCheck_4144_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4145_ = crate::leanh::lean_ctor_get(v___x_4129_, 0);
                        v_isSharedCheck_4152_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4129_)) as u8;
                        if v_isSharedCheck_4152_ == 0 {
                            v___x_4147_ = v___x_4129_;
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4145_);
                            crate::leanh::lean_dec(v___x_4129_);
                            v___x_4147_ = crate::leanh::lean_box(0);
                            v_isShared_4148_ = v_isSharedCheck_4152_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4105_ = crate::leanh::lean_ctor_get(v_a_4101_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4105_) == 0 {
                    v_snd_4106_ = crate::leanh::lean_ctor_get(v_a_4101_, 1);
                    crate::leanh::lean_inc(v_snd_4106_);
                    crate::leanh::lean_dec(v_a_4101_);
                    v___x_4107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4107_, 0, v_snd_4106_);
                    if v_isShared_4104_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4103_, 0, v___x_4107_);
                        v___x_4109_ = v___x_4103_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4110_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4110_, 0, v___x_4107_);
                        v___x_4109_ = v_reuseFailAlloc_4110_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4105_);
                    crate::leanh::lean_dec(v_a_4101_);
                    v_val_4111_ = crate::leanh::lean_ctor_get(v_fst_4105_, 0);
                    crate::leanh::lean_inc(v_val_4111_);
                    crate::leanh::lean_dec_ref_known(v_fst_4105_, 1);
                    if v_isShared_4104_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4103_, 0, v_val_4111_);
                        v___x_4113_ = v___x_4103_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4114_, 0, v_val_4111_);
                        v___x_4113_ = v_reuseFailAlloc_4114_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4109_;
            }
            3 => {
                return v___x_4113_;
            }
            4 => {
                if v_isShared_4119_ == 0 {
                    v___x_4121_ = v___x_4118_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4122_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4122_, 0, v_a_4116_);
                    v___x_4121_ = v_reuseFailAlloc_4122_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4121_;
            }
            6 => {
                v_fst_4134_ = crate::leanh::lean_ctor_get(v_a_4130_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4134_) == 0 {
                    v_snd_4135_ = crate::leanh::lean_ctor_get(v_a_4130_, 1);
                    crate::leanh::lean_inc(v_snd_4135_);
                    crate::leanh::lean_dec(v_a_4130_);
                    v___x_4136_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4136_, 0, v_snd_4135_);
                    if v_isShared_4133_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4132_, 0, v___x_4136_);
                        v___x_4138_ = v___x_4132_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4139_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4139_, 0, v___x_4136_);
                        v___x_4138_ = v_reuseFailAlloc_4139_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4134_);
                    crate::leanh::lean_dec(v_a_4130_);
                    v_val_4140_ = crate::leanh::lean_ctor_get(v_fst_4134_, 0);
                    crate::leanh::lean_inc(v_val_4140_);
                    crate::leanh::lean_dec_ref_known(v_fst_4134_, 1);
                    if v_isShared_4133_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4132_, 0, v_val_4140_);
                        v___x_4142_ = v___x_4132_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4143_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4143_, 0, v_val_4140_);
                        v___x_4142_ = v_reuseFailAlloc_4143_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4138_;
            }
            8 => {
                return v___x_4142_;
            }
            9 => {
                if v_isShared_4148_ == 0 {
                    v___x_4150_ = v___x_4147_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4151_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
                    v___x_4150_ = v_reuseFailAlloc_4151_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4150_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(
    mut v_init_4153_: *mut crate::leanh::LeanObject,
    mut v_goal_4154_: *mut crate::leanh::LeanObject,
    mut v_as_4155_: *mut crate::leanh::LeanObject,
    mut v_sz_4156_: usize,
    mut v_i_4157_: usize,
    mut v_b_4158_: *mut crate::leanh::LeanObject,
    mut v___y_4159_: *mut crate::leanh::LeanObject,
    mut v___y_4160_: *mut crate::leanh::LeanObject,
    mut v___y_4161_: *mut crate::leanh::LeanObject,
    mut v___y_4162_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4164_: u8 = 0;
    let mut v___x_4165_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4169_: u8 = 0;
    let mut v_a_4170_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4175_: u8 = 0;
    let mut v___x_4176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4187_: usize = 0;
    let mut v___x_4188_: usize = 0;
    let mut v_reuseFailAlloc_4190_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4191_: u8 = 0;
    let mut v_a_4192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4195_: u8 = 0;
    let mut v___x_4197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4199_: u8 = 0;
    let mut v_isSharedCheck_4200_: u8 = 0;
    let mut v_unused_4201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4164_ = lean_usize_dec_lt(v_i_4157_, v_sz_4156_);
                if v___x_4164_ == 0 {
                    v___x_4165_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4165_, 0, v_b_4158_);
                    return v___x_4165_;
                } else {
                    v_snd_4166_ = crate::leanh::lean_ctor_get(v_b_4158_, 1);
                    v_isSharedCheck_4200_ = (!crate::leanh::lean_is_exclusive(v_b_4158_)) as u8;
                    if v_isSharedCheck_4200_ == 0 {
                        v_unused_4201_ = crate::leanh::lean_ctor_get(v_b_4158_, 0);
                        crate::leanh::lean_dec(v_unused_4201_);
                        v___x_4168_ = v_b_4158_;
                        v_isShared_4169_ = v_isSharedCheck_4200_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4166_);
                        crate::leanh::lean_dec(v_b_4158_);
                        v___x_4168_ = crate::leanh::lean_box(0);
                        v_isShared_4169_ = v_isSharedCheck_4200_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4170_ = lean_array_uget_borrowed(v_as_4155_, v_i_4157_);
                crate::leanh::lean_inc(v_snd_4166_);
                v___x_4171_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_4153_, v_goal_4154_, v_a_4170_, v_snd_4166_, v___y_4159_, v___y_4160_, v___y_4161_, v___y_4162_);
                if crate::leanh::lean_obj_tag(v___x_4171_) == 0 {
                    v_a_4172_ = crate::leanh::lean_ctor_get(v___x_4171_, 0);
                    v_isSharedCheck_4191_ = (!crate::leanh::lean_is_exclusive(v___x_4171_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4174_ = v___x_4171_;
                        v_isShared_4175_ = v_isSharedCheck_4191_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4172_);
                        crate::leanh::lean_dec(v___x_4171_);
                        v___x_4174_ = crate::leanh::lean_box(0);
                        v_isShared_4175_ = v_isSharedCheck_4191_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4168_);
                    crate::leanh::lean_dec(v_snd_4166_);
                    v_a_4192_ = crate::leanh::lean_ctor_get(v___x_4171_, 0);
                    v_isSharedCheck_4199_ = (!crate::leanh::lean_is_exclusive(v___x_4171_)) as u8;
                    if v_isSharedCheck_4199_ == 0 {
                        v___x_4194_ = v___x_4171_;
                        v_isShared_4195_ = v_isSharedCheck_4199_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4192_);
                        crate::leanh::lean_dec(v___x_4171_);
                        v___x_4194_ = crate::leanh::lean_box(0);
                        v_isShared_4195_ = v_isSharedCheck_4199_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4172_) == 0 {
                    v___x_4176_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4176_, 0, v_a_4172_);
                    if v_isShared_4169_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4168_, 0, v___x_4176_);
                        v___x_4178_ = v___x_4168_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4182_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v___x_4176_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 1, v_snd_4166_);
                        v___x_4178_ = v_reuseFailAlloc_4182_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4174_);
                    crate::leanh::lean_dec(v_snd_4166_);
                    v_a_4183_ = crate::leanh::lean_ctor_get(v_a_4172_, 0);
                    crate::leanh::lean_inc(v_a_4183_);
                    crate::leanh::lean_dec_ref_known(v_a_4172_, 1);
                    v___x_4184_ = crate::leanh::lean_box(0);
                    if v_isShared_4169_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4168_, 1, v_a_4183_);
                        crate::leanh::lean_ctor_set(v___x_4168_, 0, v___x_4184_);
                        v___x_4186_ = v___x_4168_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4190_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4190_, 0, v___x_4184_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4190_, 1, v_a_4183_);
                        v___x_4186_ = v_reuseFailAlloc_4190_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4175_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4174_, 0, v___x_4178_);
                    v___x_4180_ = v___x_4174_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4181_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4181_, 0, v___x_4178_);
                    v___x_4180_ = v_reuseFailAlloc_4181_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4180_;
            }
            5 => {
                v___x_4187_ = 1usize;
                v___x_4188_ = lean_usize_add(v_i_4157_, v___x_4187_);
                v_i_4157_ = v___x_4188_;
                v_b_4158_ = v___x_4186_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4195_ == 0 {
                    v___x_4197_ = v___x_4194_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4198_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4198_, 0, v_a_4192_);
                    v___x_4197_ = v_reuseFailAlloc_4198_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4197_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7___boxed(
    mut v_init_4202_: *mut crate::leanh::LeanObject,
    mut v_goal_4203_: *mut crate::leanh::LeanObject,
    mut v_as_4204_: *mut crate::leanh::LeanObject,
    mut v_sz_4205_: *mut crate::leanh::LeanObject,
    mut v_i_4206_: *mut crate::leanh::LeanObject,
    mut v_b_4207_: *mut crate::leanh::LeanObject,
    mut v___y_4208_: *mut crate::leanh::LeanObject,
    mut v___y_4209_: *mut crate::leanh::LeanObject,
    mut v___y_4210_: *mut crate::leanh::LeanObject,
    mut v___y_4211_: *mut crate::leanh::LeanObject,
    mut v___y_4212_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_4213_: usize = 0;
    let mut v_i_boxed_4214_: usize = 0;
    let mut v_res_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_4213_ = crate::leanh::lean_unbox_usize(v_sz_4205_);
    crate::leanh::lean_dec(v_sz_4205_);
    v_i_boxed_4214_ = crate::leanh::lean_unbox_usize(v_i_4206_);
    crate::leanh::lean_dec(v_i_4206_);
    v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3_spec__7(v_init_4202_, v_goal_4203_, v_as_4204_, v_sz_boxed_4213_, v_i_boxed_4214_, v_b_4207_, v___y_4208_, v___y_4209_, v___y_4210_, v___y_4211_);
    crate::leanh::lean_dec(v___y_4211_);
    crate::leanh::lean_dec_ref(v___y_4210_);
    crate::leanh::lean_dec(v___y_4209_);
    crate::leanh::lean_dec_ref(v___y_4208_);
    crate::leanh::lean_dec_ref(v_as_4204_);
    crate::leanh::lean_dec_ref(v_goal_4203_);
    crate::leanh::lean_dec_ref(v_init_4202_);
    return v_res_4215_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3___boxed(
    mut v_init_4216_: *mut crate::leanh::LeanObject,
    mut v_goal_4217_: *mut crate::leanh::LeanObject,
    mut v_n_4218_: *mut crate::leanh::LeanObject,
    mut v_b_4219_: *mut crate::leanh::LeanObject,
    mut v___y_4220_: *mut crate::leanh::LeanObject,
    mut v___y_4221_: *mut crate::leanh::LeanObject,
    mut v___y_4222_: *mut crate::leanh::LeanObject,
    mut v___y_4223_: *mut crate::leanh::LeanObject,
    mut v___y_4224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4225_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_4216_, v_goal_4217_, v_n_4218_, v_b_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
    crate::leanh::lean_dec(v___y_4223_);
    crate::leanh::lean_dec_ref(v___y_4222_);
    crate::leanh::lean_dec(v___y_4221_);
    crate::leanh::lean_dec_ref(v___y_4220_);
    crate::leanh::lean_dec_ref(v_n_4218_);
    crate::leanh::lean_dec_ref(v_goal_4217_);
    crate::leanh::lean_dec_ref(v_init_4216_);
    return v_res_4225_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(
    mut v_goal_4226_: *mut crate::leanh::LeanObject,
    mut v_t_4227_: *mut crate::leanh::LeanObject,
    mut v_init_4228_: *mut crate::leanh::LeanObject,
    mut v___y_4229_: *mut crate::leanh::LeanObject,
    mut v___y_4230_: *mut crate::leanh::LeanObject,
    mut v___y_4231_: *mut crate::leanh::LeanObject,
    mut v___y_4232_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4240_: u8 = 0;
    let mut v_a_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4246_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4248_: usize = 0;
    let mut v___x_4249_: usize = 0;
    let mut v___x_4250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4253_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4254_: u8 = 0;
    let mut v_fst_4255_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4258_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4264_: u8 = 0;
    let mut v_a_4265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4268_: u8 = 0;
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4271_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4272_: u8 = 0;
    let mut v_isSharedCheck_4273_: u8 = 0;
    let mut v_a_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4277_: u8 = 0;
    let mut v___x_4279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4281_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4234_ = crate::leanh::lean_ctor_get(v_t_4227_, 0);
                v_tail_4235_ = crate::leanh::lean_ctor_get(v_t_4227_, 1);
                crate::leanh::lean_inc_ref(v_init_4228_);
                v___x_4236_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__3(v_init_4228_, v_goal_4226_, v_root_4234_, v_init_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
                crate::leanh::lean_dec_ref(v_init_4228_);
                if crate::leanh::lean_obj_tag(v___x_4236_) == 0 {
                    v_a_4237_ = crate::leanh::lean_ctor_get(v___x_4236_, 0);
                    v_isSharedCheck_4273_ = (!crate::leanh::lean_is_exclusive(v___x_4236_)) as u8;
                    if v_isSharedCheck_4273_ == 0 {
                        v___x_4239_ = v___x_4236_;
                        v_isShared_4240_ = v_isSharedCheck_4273_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4237_);
                        crate::leanh::lean_dec(v___x_4236_);
                        v___x_4239_ = crate::leanh::lean_box(0);
                        v_isShared_4240_ = v_isSharedCheck_4273_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4274_ = crate::leanh::lean_ctor_get(v___x_4236_, 0);
                    v_isSharedCheck_4281_ = (!crate::leanh::lean_is_exclusive(v___x_4236_)) as u8;
                    if v_isSharedCheck_4281_ == 0 {
                        v___x_4276_ = v___x_4236_;
                        v_isShared_4277_ = v_isSharedCheck_4281_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4274_);
                        crate::leanh::lean_dec(v___x_4236_);
                        v___x_4276_ = crate::leanh::lean_box(0);
                        v_isShared_4277_ = v_isSharedCheck_4281_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4237_) == 0 {
                    v_a_4241_ = crate::leanh::lean_ctor_get(v_a_4237_, 0);
                    crate::leanh::lean_inc(v_a_4241_);
                    crate::leanh::lean_dec_ref_known(v_a_4237_, 1);
                    if v_isShared_4240_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4239_, 0, v_a_4241_);
                        v___x_4243_ = v___x_4239_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4244_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4244_, 0, v_a_4241_);
                        v___x_4243_ = v_reuseFailAlloc_4244_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4239_);
                    v_a_4245_ = crate::leanh::lean_ctor_get(v_a_4237_, 0);
                    crate::leanh::lean_inc(v_a_4245_);
                    crate::leanh::lean_dec_ref_known(v_a_4237_, 1);
                    v___x_4246_ = crate::leanh::lean_box(0);
                    v___x_4247_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4247_, 0, v___x_4246_);
                    crate::leanh::lean_ctor_set(v___x_4247_, 1, v_a_4245_);
                    v_sz_4248_ = lean_array_size(v_tail_4235_);
                    v___x_4249_ = 0usize;
                    v___x_4250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1_spec__4(v_goal_4226_, v_tail_4235_, v_sz_4248_, v___x_4249_, v___x_4247_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
                    if crate::leanh::lean_obj_tag(v___x_4250_) == 0 {
                        v_a_4251_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                        v_isSharedCheck_4264_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4250_)) as u8;
                        if v_isSharedCheck_4264_ == 0 {
                            v___x_4253_ = v___x_4250_;
                            v_isShared_4254_ = v_isSharedCheck_4264_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4251_);
                            crate::leanh::lean_dec(v___x_4250_);
                            v___x_4253_ = crate::leanh::lean_box(0);
                            v_isShared_4254_ = v_isSharedCheck_4264_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4265_ = crate::leanh::lean_ctor_get(v___x_4250_, 0);
                        v_isSharedCheck_4272_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4250_)) as u8;
                        if v_isSharedCheck_4272_ == 0 {
                            v___x_4267_ = v___x_4250_;
                            v_isShared_4268_ = v_isSharedCheck_4272_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4265_);
                            crate::leanh::lean_dec(v___x_4250_);
                            v___x_4267_ = crate::leanh::lean_box(0);
                            v_isShared_4268_ = v_isSharedCheck_4272_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4243_;
            }
            3 => {
                v_fst_4255_ = crate::leanh::lean_ctor_get(v_a_4251_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4255_) == 0 {
                    v_snd_4256_ = crate::leanh::lean_ctor_get(v_a_4251_, 1);
                    crate::leanh::lean_inc(v_snd_4256_);
                    crate::leanh::lean_dec(v_a_4251_);
                    if v_isShared_4254_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4253_, 0, v_snd_4256_);
                        v___x_4258_ = v___x_4253_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4259_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_snd_4256_);
                        v___x_4258_ = v_reuseFailAlloc_4259_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4255_);
                    crate::leanh::lean_dec(v_a_4251_);
                    v_val_4260_ = crate::leanh::lean_ctor_get(v_fst_4255_, 0);
                    crate::leanh::lean_inc(v_val_4260_);
                    crate::leanh::lean_dec_ref_known(v_fst_4255_, 1);
                    if v_isShared_4254_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4253_, 0, v_val_4260_);
                        v___x_4262_ = v___x_4253_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4263_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4263_, 0, v_val_4260_);
                        v___x_4262_ = v_reuseFailAlloc_4263_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4258_;
            }
            5 => {
                return v___x_4262_;
            }
            6 => {
                if v_isShared_4268_ == 0 {
                    v___x_4270_ = v___x_4267_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4271_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4271_, 0, v_a_4265_);
                    v___x_4270_ = v_reuseFailAlloc_4271_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4270_;
            }
            8 => {
                if v_isShared_4277_ == 0 {
                    v___x_4279_ = v___x_4276_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4280_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4280_, 0, v_a_4274_);
                    v___x_4279_ = v_reuseFailAlloc_4280_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4279_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1___boxed(
    mut v_goal_4282_: *mut crate::leanh::LeanObject,
    mut v_t_4283_: *mut crate::leanh::LeanObject,
    mut v_init_4284_: *mut crate::leanh::LeanObject,
    mut v___y_4285_: *mut crate::leanh::LeanObject,
    mut v___y_4286_: *mut crate::leanh::LeanObject,
    mut v___y_4287_: *mut crate::leanh::LeanObject,
    mut v___y_4288_: *mut crate::leanh::LeanObject,
    mut v___y_4289_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4290_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(
            v_goal_4282_,
            v_t_4283_,
            v_init_4284_,
            v___y_4285_,
            v___y_4286_,
            v___y_4287_,
            v___y_4288_,
        );
    crate::leanh::lean_dec(v___y_4288_);
    crate::leanh::lean_dec_ref(v___y_4287_);
    crate::leanh::lean_dec(v___y_4286_);
    crate::leanh::lean_dec_ref(v___y_4285_);
    crate::leanh::lean_dec_ref(v_t_4283_);
    crate::leanh::lean_dec_ref(v_goal_4282_);
    return v_res_4290_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4291_ = crate::leanh::lean_box(0);
    v___x_4292_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_4293_ = lean_mk_array(v___x_4292_, v___x_4291_);
    return v___x_4293_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_4294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4295_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_4296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_4294_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__0,
    );
    v___x_4295_ = crate::leanh::lean_unsigned_to_nat(0);
    v_model_4296_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_model_4296_, 0, v___x_4295_);
    crate::leanh::lean_ctor_set(v_model_4296_, 1, v___x_4294_);
    return v_model_4296_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkModel(
    mut v_goal_4304_: *mut crate::leanh::LeanObject,
    mut v_structId_4305_: *mut crate::leanh::LeanObject,
    mut v_a_4306_: *mut crate::leanh::LeanObject,
    mut v_a_4307_: *mut crate::leanh::LeanObject,
    mut v_a_4308_: *mut crate::leanh::LeanObject,
    mut v_a_4309_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_toGoalState_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_4315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4321_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4323_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_type_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4334_: u8 = 0;
    let mut v___x_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4338_: u8 = 0;
    let mut v_unused_4339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4343_: u8 = 0;
    let mut v___x_4345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4347_: u8 = 0;
    let mut v_a_4348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4351_: u8 = 0;
    let mut v___x_4353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4355_: u8 = 0;
    let mut v_a_4356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4359_: u8 = 0;
    let mut v___x_4361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4363_: u8 = 0;
    let mut v_a_4364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4367_: u8 = 0;
    let mut v___x_4369_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4371_: u8 = 0;
    let mut v_a_4372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4375_: u8 = 0;
    let mut v_ref_4376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4378_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4382_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4383_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4384_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4311_ = l_Lean_Meta_Grind_Arith_Linear_linearExt;
                v___x_4312_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_4311_, v_goal_4304_);
                if crate::leanh::lean_obj_tag(v___x_4312_) == 0 {
                    v_a_4313_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    crate::leanh::lean_inc(v_a_4313_);
                    crate::leanh::lean_dec_ref_known(v___x_4312_, 1);
                    v_toGoalState_4314_ = crate::leanh::lean_ctor_get(v_goal_4304_, 0);
                    v_structs_4315_ = crate::leanh::lean_ctor_get(v_a_4313_, 0);
                    crate::leanh::lean_inc_ref(v_structs_4315_);
                    crate::leanh::lean_dec(v_a_4313_);
                    v_exprs_4316_ = crate::leanh::lean_ctor_get(v_toGoalState_4314_, 2);
                    v___x_4317_ = l_Lean_Meta_Grind_Arith_Linear_instInhabitedStruct_default;
                    v_model_4318_ = crate::leanh::lean_obj_once(
                        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1),
                        core::ptr::addr_of_mut!(
                            l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1_once
                        ),
                        _init_l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__1,
                    );
                    v___x_4319_ = lean_array_get(v___x_4317_, v_structs_4315_, v_structId_4305_);
                    crate::leanh::lean_dec_ref(v_structs_4315_);
                    crate::leanh::lean_inc(v___x_4319_);
                    v___x_4320_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__0(v_goal_4304_, v___x_4319_, v_exprs_4316_, v_model_4318_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_);
                    if crate::leanh::lean_obj_tag(v___x_4320_) == 0 {
                        v_a_4321_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                        crate::leanh::lean_inc(v_a_4321_);
                        crate::leanh::lean_dec_ref_known(v___x_4320_, 1);
                        v___x_4322_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_assignTerms(v_goal_4304_, v_structId_4305_, v_a_4321_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_);
                        if crate::leanh::lean_obj_tag(v___x_4322_) == 0 {
                            v_a_4323_ = crate::leanh::lean_ctor_get(v___x_4322_, 0);
                            crate::leanh::lean_inc(v_a_4323_);
                            crate::leanh::lean_dec_ref_known(v___x_4322_, 1);
                            v___x_4324_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Linear_mkModel_spec__1(v_goal_4304_, v_exprs_4316_, v_a_4323_, v_a_4306_, v_a_4307_, v_a_4308_, v_a_4309_);
                            if crate::leanh::lean_obj_tag(v___x_4324_) == 0 {
                                v_a_4325_ = crate::leanh::lean_ctor_get(v___x_4324_, 0);
                                crate::leanh::lean_inc(v_a_4325_);
                                crate::leanh::lean_dec_ref_known(v___x_4324_, 1);
                                v_type_4326_ = crate::leanh::lean_ctor_get(v___x_4319_, 2);
                                crate::leanh::lean_inc_ref(v_type_4326_);
                                crate::leanh::lean_dec(v___x_4319_);
                                v___x_4327_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Model_0__Lean_Meta_Grind_Arith_Linear_hasType___boxed as *mut core::ffi::c_void, 7, 1);
                                crate::leanh::lean_closure_set(v___x_4327_, 0, v_type_4326_);
                                v___x_4328_ = l_Lean_Meta_Grind_Arith_finalizeModel(
                                    v_goal_4304_,
                                    v___x_4327_,
                                    v_a_4325_,
                                    v_a_4306_,
                                    v_a_4307_,
                                    v_a_4308_,
                                    v_a_4309_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_4328_) == 0 {
                                    v_a_4329_ = crate::leanh::lean_ctor_get(v___x_4328_, 0);
                                    crate::leanh::lean_inc(v_a_4329_);
                                    crate::leanh::lean_dec_ref_known(v___x_4328_, 1);
                                    v___x_4330_ =
                                        l_Lean_Meta_Grind_Arith_Linear_mkModel___closed__5;
                                    v___x_4331_ = l_Lean_Meta_Grind_Arith_traceModel(
                                        v___x_4330_,
                                        v_a_4329_,
                                        v_a_4306_,
                                        v_a_4307_,
                                        v_a_4308_,
                                        v_a_4309_,
                                    );
                                    if crate::leanh::lean_obj_tag(v___x_4331_) == 0 {
                                        v_isSharedCheck_4338_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4331_)) as u8;
                                        if v_isSharedCheck_4338_ == 0 {
                                            v_unused_4339_ =
                                                crate::leanh::lean_ctor_get(v___x_4331_, 0);
                                            crate::leanh::lean_dec(v_unused_4339_);
                                            v___x_4333_ = v___x_4331_;
                                            v_isShared_4334_ = v_isSharedCheck_4338_;
                                            state = 1;
                                            continue;
                                        } else {
                                            crate::leanh::lean_dec(v___x_4331_);
                                            v___x_4333_ = crate::leanh::lean_box(0);
                                            v_isShared_4334_ = v_isSharedCheck_4338_;
                                            state = 1;
                                            continue;
                                        }
                                    } else {
                                        crate::leanh::lean_dec(v_a_4329_);
                                        v_a_4340_ = crate::leanh::lean_ctor_get(v___x_4331_, 0);
                                        v_isSharedCheck_4347_ =
                                            (!crate::leanh::lean_is_exclusive(v___x_4331_)) as u8;
                                        if v_isSharedCheck_4347_ == 0 {
                                            v___x_4342_ = v___x_4331_;
                                            v_isShared_4343_ = v_isSharedCheck_4347_;
                                            state = 3;
                                            continue;
                                        } else {
                                            crate::leanh::lean_inc(v_a_4340_);
                                            crate::leanh::lean_dec(v___x_4331_);
                                            v___x_4342_ = crate::leanh::lean_box(0);
                                            v_isShared_4343_ = v_isSharedCheck_4347_;
                                            state = 3;
                                            continue;
                                        }
                                    }
                                } else {
                                    return v___x_4328_;
                                }
                            } else {
                                crate::leanh::lean_dec(v___x_4319_);
                                v_a_4348_ = crate::leanh::lean_ctor_get(v___x_4324_, 0);
                                v_isSharedCheck_4355_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_4324_)) as u8;
                                if v_isSharedCheck_4355_ == 0 {
                                    v___x_4350_ = v___x_4324_;
                                    v_isShared_4351_ = v_isSharedCheck_4355_;
                                    state = 5;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_4348_);
                                    crate::leanh::lean_dec(v___x_4324_);
                                    v___x_4350_ = crate::leanh::lean_box(0);
                                    v_isShared_4351_ = v_isSharedCheck_4355_;
                                    state = 5;
                                    continue;
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v___x_4319_);
                            v_a_4356_ = crate::leanh::lean_ctor_get(v___x_4322_, 0);
                            v_isSharedCheck_4363_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4322_)) as u8;
                            if v_isSharedCheck_4363_ == 0 {
                                v___x_4358_ = v___x_4322_;
                                v_isShared_4359_ = v_isSharedCheck_4363_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4356_);
                                crate::leanh::lean_dec(v___x_4322_);
                                v___x_4358_ = crate::leanh::lean_box(0);
                                v_isShared_4359_ = v_isSharedCheck_4363_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_4319_);
                        v_a_4364_ = crate::leanh::lean_ctor_get(v___x_4320_, 0);
                        v_isSharedCheck_4371_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4320_)) as u8;
                        if v_isSharedCheck_4371_ == 0 {
                            v___x_4366_ = v___x_4320_;
                            v_isShared_4367_ = v_isSharedCheck_4371_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4364_);
                            crate::leanh::lean_dec(v___x_4320_);
                            v___x_4366_ = crate::leanh::lean_box(0);
                            v_isShared_4367_ = v_isSharedCheck_4371_;
                            state = 9;
                            continue;
                        }
                    }
                } else {
                    v_a_4372_ = crate::leanh::lean_ctor_get(v___x_4312_, 0);
                    v_isSharedCheck_4384_ = (!crate::leanh::lean_is_exclusive(v___x_4312_)) as u8;
                    if v_isSharedCheck_4384_ == 0 {
                        v___x_4374_ = v___x_4312_;
                        v_isShared_4375_ = v_isSharedCheck_4384_;
                        state = 11;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4372_);
                        crate::leanh::lean_dec(v___x_4312_);
                        v___x_4374_ = crate::leanh::lean_box(0);
                        v_isShared_4375_ = v_isSharedCheck_4384_;
                        state = 11;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_4334_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4333_, 0, v_a_4329_);
                    v___x_4336_ = v___x_4333_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_4337_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4337_, 0, v_a_4329_);
                    v___x_4336_ = v_reuseFailAlloc_4337_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_4336_;
            }
            3 => {
                if v_isShared_4343_ == 0 {
                    v___x_4345_ = v___x_4342_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4346_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4346_, 0, v_a_4340_);
                    v___x_4345_ = v_reuseFailAlloc_4346_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4345_;
            }
            5 => {
                if v_isShared_4351_ == 0 {
                    v___x_4353_ = v___x_4350_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_4354_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4354_, 0, v_a_4348_);
                    v___x_4353_ = v_reuseFailAlloc_4354_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_4353_;
            }
            7 => {
                if v_isShared_4359_ == 0 {
                    v___x_4361_ = v___x_4358_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4362_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4362_, 0, v_a_4356_);
                    v___x_4361_ = v_reuseFailAlloc_4362_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4361_;
            }
            9 => {
                if v_isShared_4367_ == 0 {
                    v___x_4369_ = v___x_4366_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4370_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4370_, 0, v_a_4364_);
                    v___x_4369_ = v_reuseFailAlloc_4370_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4369_;
            }
            11 => {
                v_ref_4376_ = crate::leanh::lean_ctor_get(v_a_4308_, 5);
                v___x_4377_ = lean_io_error_to_string(v_a_4372_);
                v___x_4378_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4378_, 0, v___x_4377_);
                v___x_4379_ = l_Lean_MessageData_ofFormat(v___x_4378_);
                crate::leanh::lean_inc(v_ref_4376_);
                v___x_4380_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4380_, 0, v_ref_4376_);
                crate::leanh::lean_ctor_set(v___x_4380_, 1, v___x_4379_);
                if v_isShared_4375_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4374_, 0, v___x_4380_);
                    v___x_4382_ = v___x_4374_;
                    state = 12;
                    continue;
                } else {
                    v_reuseFailAlloc_4383_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4383_, 0, v___x_4380_);
                    v___x_4382_ = v_reuseFailAlloc_4383_;
                    state = 12;
                    continue;
                }
            }
            12 => {
                return v___x_4382_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_mkModel___boxed(
    mut v_goal_4385_: *mut crate::leanh::LeanObject,
    mut v_structId_4386_: *mut crate::leanh::LeanObject,
    mut v_a_4387_: *mut crate::leanh::LeanObject,
    mut v_a_4388_: *mut crate::leanh::LeanObject,
    mut v_a_4389_: *mut crate::leanh::LeanObject,
    mut v_a_4390_: *mut crate::leanh::LeanObject,
    mut v_a_4391_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_4392_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_4392_ = l_Lean_Meta_Grind_Arith_Linear_mkModel(
        v_goal_4385_,
        v_structId_4386_,
        v_a_4387_,
        v_a_4388_,
        v_a_4389_,
        v_a_4390_,
    );
    crate::leanh::lean_dec(v_a_4390_);
    crate::leanh::lean_dec_ref(v_a_4389_);
    crate::leanh::lean_dec(v_a_4388_);
    crate::leanh::lean_dec_ref(v_a_4387_);
    crate::leanh::lean_dec(v_structId_4386_);
    crate::leanh::lean_dec_ref(v_goal_4385_);
    return v_res_4392_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Init_Grind_Module_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Reify(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Init_Grind_Module_Envelope(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Model(builtin);
}
