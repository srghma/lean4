// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.Model
// Imports: Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.ModelUtil
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_borrowed, lean_array_get_size, lean_array_size,
    lean_array_uget_borrowed, lean_expr_eqv, lean_infer_type, lean_mk_array, lean_nat_add,
    lean_nat_dec_lt, lean_nat_to_int, lean_panic_fn_borrowed, lean_uint64_lor,
    lean_uint64_shift_left, lean_uint64_shift_right, lean_uint64_to_usize, lean_uint64_xor,
    lean_usize_add, lean_usize_dec_lt, lean_usize_land, lean_usize_of_nat, lean_usize_shift_left,
    lean_usize_shift_right, lean_usize_sub, lean_usize_to_nat,
};
use crate::r#gen::Init::Data::Rat::Basic::{l_Rat_ofInt, l_instInhabitedRat};
use crate::r#gen::Init::System::IO::l_instInhabitedEIO___aux__1___boxed;
use crate::r#gen::Init::System::IOError::{l_instInhabitedError, lean_io_error_to_string};
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::{
    l_Lean_Expr_appFnCleanup___redArg, l_Lean_Expr_cleanupAnnotations, l_Lean_Expr_hash,
    l_Lean_Expr_isApp, l_Lean_Expr_isConstOf, l_Lean_Int_mkType, l_Lean_Nat_mkType,
};
use crate::r#gen::Lean::Message::l_Lean_MessageData_ofFormat;
use crate::r#gen::Lean::Meta::Basic::{
    l_Lean_Meta_Context_config, l_Lean_Meta_Context_configKey,
    l_Lean_Meta_TransparencyMode_toUInt64, l_Lean_Meta_isExprDefEq,
};
use crate::r#gen::Lean::Meta::LitValues::{
    l_Lean_Meta_getIntValue_x3f, l_Lean_Meta_getNatValue_x3f,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::{
    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1,
    l_Lean_Meta_Sym_hashPtrExpr_unsafe__1,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Cutsat::Types::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types, l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::ModelUtil::{
    initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil, l_Lean_Meta_Grind_Arith_assignEqc,
    l_Lean_Meta_Grind_Arith_finalizeModel, l_Lean_Meta_Grind_Arith_traceModel,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::{
    l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg,
    l_Lean_Meta_Grind_ENode_isRoot, l_Lean_Meta_Grind_Goal_getENode,
    l_Lean_Meta_Grind_Goal_getRoot, l_Lean_Meta_Grind_SolverExtension_getTerm___redArg,
};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0: u64 = 0;
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0: usize = 0;
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1: usize = 0;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 77, 111, 100, 101, 108, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1_value: crate::leanh::LeanStringObject<103> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 103, m_capacity: 103, m_length: 102, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 77, 111, 100, 101, 108, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 117, 116, 115, 97, 116, 46, 103, 101, 116, 67, 117, 116, 115, 97, 116, 65, 115, 115, 105, 103, 110, 109, 101, 110, 116, 63, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2_value: crate::leanh::LeanStringObject<55> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 55, m_capacity: 55, m_length: 54, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 110, 111, 100, 101, 46, 115, 101, 108, 102, 32, 110, 111, 100, 101, 46, 114, 111, 111, 116, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [78, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value: crate::leanh::LeanStringObject<8> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 8, m_capacity: 8, m_length: 7, m_data: [110, 97, 116, 67, 97, 115, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__0_value) as *mut crate::leanh::LeanObject,5779414593499529281 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__1_value) as *mut crate::leanh::LeanObject,7063772860359172143 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value: crate::leanh::LeanStringObject<5> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 5, m_capacity: 5, m_length: 4, m_data: [76, 101, 97, 110, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [71, 114, 105, 110, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [84, 111, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value: crate::leanh::LeanStringObject<6> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 6, m_capacity: 6, m_length: 5, m_data: [116, 111, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value) as *mut crate::leanh::LeanObject;
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_0: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__3_value) as *mut crate::leanh::LeanObject,11948124481539785030 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_1: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_0) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__4_value) as *mut crate::leanh::LeanObject,13563742693681136756 as *mut crate::leanh::LeanObject] };
static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_2: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__5_value) as *mut crate::leanh::LeanObject,16822059798527729847 as *mut crate::leanh::LeanObject] };
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value_aux_2) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__6_value) as *mut crate::leanh::LeanObject,2495166364501146107 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value: crate::leanh::LeanStringObject<15> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 15, m_capacity: 15, m_length: 14, m_data: [105, 110, 115, 116, 78, 97, 116, 67, 97, 115, 116, 73, 110, 116, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9_value: crate::leanh::LeanCtorObject<3> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 8) as u16, other: 2, tag: 1 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__8_value) as *mut crate::leanh::LeanObject,14240220390202531956 as *mut crate::leanh::LeanObject] };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9_value) as *mut crate::leanh::LeanObject;
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once: crate::leanh::LeanOnceCell =
    crate::leanh::LeanOnceCell {
        state: core::sync::atomic::AtomicI32::new(0),
        lock: core::sync::atomic::AtomicI32::new(0),
    };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1: *mut crate::leanh::LeanObject =
    core::ptr::null_mut();
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2_value: crate::leanh::LeanClosureObject<0> = crate::leanh::LeanClosureObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*const core::ffi::c_void>() + 4 + core::mem::size_of::<*mut crate::leanh::LeanObject>()*0) as u16, other: 0, tag: 245 }, m_fun: l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed as *const core::ffi::c_void, m_arity: 6, m_num_fixed: 0, m_objs: [] };
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value:
    crate::leanh::LeanStringObject<4> = crate::leanh::LeanStringObject {
    m_header: crate::leanh::LeanObject {
        rc: 0,
        cs_size: (0) as u16,
        other: 0,
        tag: 249,
    },
    m_size: 4,
    m_capacity: 4,
    m_length: 3,
    m_data: [108, 105, 97, 0],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value)
        as *mut crate::leanh::LeanObject;
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value:
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
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value)
        as *mut crate::leanh::LeanObject;
static l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_0:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__3_value)
            as *mut crate::leanh::LeanObject,
        15947788021050471391 as *mut crate::leanh::LeanObject,
    ],
};
static l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_1:
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_0)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__4_value)
            as *mut crate::leanh::LeanObject,
        11074150007773075224 as *mut crate::leanh::LeanObject,
    ],
};
pub static l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value: crate::leanh::LeanCtorObject<
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
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value_aux_1)
            as *mut crate::leanh::LeanObject,
        core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__5_value)
            as *mut crate::leanh::LeanObject,
        10981442452371052972 as *mut crate::leanh::LeanObject,
    ],
};
static mut l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6: *mut crate::leanh::LeanObject =
    core::ptr::addr_of!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6_value)
        as *mut crate::leanh::LeanObject;
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0()
-> u64 {
    let mut v___x_1475_: u8 = 0;
    let mut v___x_1476_: u64 = 0;
    v___x_1475_ = 1;
    v___x_1476_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_1475_);
    return v___x_1476_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(
    mut v_n_1477_: *mut crate::leanh::LeanObject,
    mut v_a_1478_: *mut crate::leanh::LeanObject,
    mut v_a_1479_: *mut crate::leanh::LeanObject,
    mut v_a_1480_: *mut crate::leanh::LeanObject,
    mut v_a_1481_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_self_1483_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1484_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_foApprox_1485_: u8 = 0;
    let mut v_ctxApprox_1486_: u8 = 0;
    let mut v_quasiPatternApprox_1487_: u8 = 0;
    let mut v_constApprox_1488_: u8 = 0;
    let mut v_isDefEqStuckEx_1489_: u8 = 0;
    let mut v_unificationHints_1490_: u8 = 0;
    let mut v_proofIrrelevance_1491_: u8 = 0;
    let mut v_assignSyntheticOpaque_1492_: u8 = 0;
    let mut v_offsetCnstrs_1493_: u8 = 0;
    let mut v_etaStruct_1494_: u8 = 0;
    let mut v_univApprox_1495_: u8 = 0;
    let mut v_iota_1496_: u8 = 0;
    let mut v_beta_1497_: u8 = 0;
    let mut v_proj_1498_: u8 = 0;
    let mut v_zeta_1499_: u8 = 0;
    let mut v_zetaDelta_1500_: u8 = 0;
    let mut v_zetaUnused_1501_: u8 = 0;
    let mut v_zetaHave_1502_: u8 = 0;
    let mut v___x_1504_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1505_: u8 = 0;
    let mut v_trackZetaDelta_1506_: u8 = 0;
    let mut v_zetaDeltaSet_1507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lctx_1508_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_localInstances_1509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_defEqCtx_x3f_1510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_synthPendingDepth_1511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_canUnfold_x3f_1512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_univApprox_1513_: u8 = 0;
    let mut v_inTypeClassResolution_1514_: u8 = 0;
    let mut v_cacheInferType_1515_: u8 = 0;
    let mut v___x_1516_: u8 = 0;
    let mut v_config_1518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1519_: u64 = 0;
    let mut v___x_1520_: u64 = 0;
    let mut v___x_1521_: u64 = 0;
    let mut v___x_1522_: u64 = 0;
    let mut v___x_1523_: u64 = 0;
    let mut v_key_1524_: u64 = 0;
    let mut v___x_1525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1532_: u8 = 0;
    let mut v___x_1533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1538_: u8 = 0;
    let mut v___x_1540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1542_: u8 = 0;
    let mut v_reuseFailAlloc_1543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1544_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_self_1483_ = crate::leanh::lean_ctor_get(v_n_1477_, 0);
                crate::leanh::lean_inc_ref(v_self_1483_);
                crate::leanh::lean_dec_ref(v_n_1477_);
                v___x_1484_ = l_Lean_Meta_Context_config(v_a_1478_);
                v_foApprox_1485_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 0 as u32);
                v_ctxApprox_1486_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 1 as u32);
                v_quasiPatternApprox_1487_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1484_, 2 as u32);
                v_constApprox_1488_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 3 as u32);
                v_isDefEqStuckEx_1489_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 4 as u32);
                v_unificationHints_1490_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 5 as u32);
                v_proofIrrelevance_1491_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 6 as u32);
                v_assignSyntheticOpaque_1492_ =
                    crate::leanh::lean_ctor_get_uint8(v___x_1484_, 7 as u32);
                v_offsetCnstrs_1493_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 8 as u32);
                v_etaStruct_1494_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 10 as u32);
                v_univApprox_1495_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 11 as u32);
                v_iota_1496_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 12 as u32);
                v_beta_1497_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 13 as u32);
                v_proj_1498_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 14 as u32);
                v_zeta_1499_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 15 as u32);
                v_zetaDelta_1500_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 16 as u32);
                v_zetaUnused_1501_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 17 as u32);
                v_zetaHave_1502_ = crate::leanh::lean_ctor_get_uint8(v___x_1484_, 18 as u32);
                v_isSharedCheck_1544_ = (!crate::leanh::lean_is_exclusive(v___x_1484_)) as u8;
                if v_isSharedCheck_1544_ == 0 {
                    v___x_1504_ = v___x_1484_;
                    v_isShared_1505_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                } else {
                    crate::leanh::lean_dec(v___x_1484_);
                    v___x_1504_ = crate::leanh::lean_box(0);
                    v_isShared_1505_ = v_isSharedCheck_1544_;
                    state = 1;
                    continue;
                }
            }
            1 => {
                v_trackZetaDelta_1506_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                );
                v_zetaDeltaSet_1507_ = crate::leanh::lean_ctor_get(v_a_1478_, 1);
                v_lctx_1508_ = crate::leanh::lean_ctor_get(v_a_1478_, 2);
                v_localInstances_1509_ = crate::leanh::lean_ctor_get(v_a_1478_, 3);
                v_defEqCtx_x3f_1510_ = crate::leanh::lean_ctor_get(v_a_1478_, 4);
                v_synthPendingDepth_1511_ = crate::leanh::lean_ctor_get(v_a_1478_, 5);
                v_canUnfold_x3f_1512_ = crate::leanh::lean_ctor_get(v_a_1478_, 6);
                v_univApprox_1513_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                );
                v_inTypeClassResolution_1514_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                );
                v_cacheInferType_1515_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_1478_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                );
                v___x_1516_ = 1;
                if v_isShared_1505_ == 0 {
                    v_config_1518_ = v___x_1504_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_1543_ = crate::leanh::lean_alloc_ctor(0, 0, (19) as u32);
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        0 as u32,
                        v_foApprox_1485_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        1 as u32,
                        v_ctxApprox_1486_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        2 as u32,
                        v_quasiPatternApprox_1487_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        3 as u32,
                        v_constApprox_1488_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        4 as u32,
                        v_isDefEqStuckEx_1489_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        5 as u32,
                        v_unificationHints_1490_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        6 as u32,
                        v_proofIrrelevance_1491_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        7 as u32,
                        v_assignSyntheticOpaque_1492_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        8 as u32,
                        v_offsetCnstrs_1493_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        10 as u32,
                        v_etaStruct_1494_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        11 as u32,
                        v_univApprox_1495_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        12 as u32,
                        v_iota_1496_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        13 as u32,
                        v_beta_1497_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        14 as u32,
                        v_proj_1498_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        15 as u32,
                        v_zeta_1499_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        16 as u32,
                        v_zetaDelta_1500_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        17 as u32,
                        v_zetaUnused_1501_,
                    );
                    crate::leanh::lean_ctor_set_uint8(
                        v_reuseFailAlloc_1543_,
                        18 as u32,
                        v_zetaHave_1502_,
                    );
                    v_config_1518_ = v_reuseFailAlloc_1543_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                crate::leanh::lean_ctor_set_uint8(v_config_1518_, 9 as u32, v___x_1516_);
                v___x_1519_ = l_Lean_Meta_Context_configKey(v_a_1478_);
                v___x_1520_ = 3u64;
                v___x_1521_ = lean_uint64_shift_right(v___x_1519_, v___x_1520_);
                v___x_1522_ = lean_uint64_shift_left(v___x_1521_, v___x_1520_);
                v___x_1523_ = crate::leanh::lean_uint64_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___closed__0);
                v_key_1524_ = lean_uint64_lor(v___x_1522_, v___x_1523_);
                v___x_1525_ = crate::leanh::lean_alloc_ctor(0, 1, (8) as u32);
                crate::leanh::lean_ctor_set(v___x_1525_, 0, v_config_1518_);
                crate::leanh::lean_ctor_set_uint64(
                    v___x_1525_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 1) as u32,
                    v_key_1524_,
                );
                crate::leanh::lean_inc(v_canUnfold_x3f_1512_);
                crate::leanh::lean_inc(v_synthPendingDepth_1511_);
                crate::leanh::lean_inc(v_defEqCtx_x3f_1510_);
                crate::leanh::lean_inc_ref(v_localInstances_1509_);
                crate::leanh::lean_inc_ref(v_lctx_1508_);
                crate::leanh::lean_inc(v_zetaDeltaSet_1507_);
                v___x_1526_ = crate::leanh::lean_alloc_ctor(0, 7, (4) as u32);
                crate::leanh::lean_ctor_set(v___x_1526_, 0, v___x_1525_);
                crate::leanh::lean_ctor_set(v___x_1526_, 1, v_zetaDeltaSet_1507_);
                crate::leanh::lean_ctor_set(v___x_1526_, 2, v_lctx_1508_);
                crate::leanh::lean_ctor_set(v___x_1526_, 3, v_localInstances_1509_);
                crate::leanh::lean_ctor_set(v___x_1526_, 4, v_defEqCtx_x3f_1510_);
                crate::leanh::lean_ctor_set(v___x_1526_, 5, v_synthPendingDepth_1511_);
                crate::leanh::lean_ctor_set(v___x_1526_, 6, v_canUnfold_x3f_1512_);
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7) as u32,
                    v_trackZetaDelta_1506_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 1) as u32,
                    v_univApprox_1513_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 2) as u32,
                    v_inTypeClassResolution_1514_,
                );
                crate::leanh::lean_ctor_set_uint8(
                    v___x_1526_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 7 + 3) as u32,
                    v_cacheInferType_1515_,
                );
                crate::leanh::lean_inc(v_a_1481_);
                crate::leanh::lean_inc_ref(v_a_1480_);
                crate::leanh::lean_inc(v_a_1479_);
                crate::leanh::lean_inc_ref(v___x_1526_);
                v___x_1527_ =
                    lean_infer_type(v_self_1483_, v___x_1526_, v_a_1479_, v_a_1480_, v_a_1481_);
                if crate::leanh::lean_obj_tag(v___x_1527_) == 0 {
                    v_a_1528_ = crate::leanh::lean_ctor_get(v___x_1527_, 0);
                    crate::leanh::lean_inc_n(v_a_1528_, 2);
                    crate::leanh::lean_dec_ref_known(v___x_1527_, 1);
                    v___x_1529_ = l_Lean_Int_mkType;
                    v___x_1530_ = l_Lean_Meta_isExprDefEq(
                        v_a_1528_,
                        v___x_1529_,
                        v___x_1526_,
                        v_a_1479_,
                        v_a_1480_,
                        v_a_1481_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1530_) == 0 {
                        v_a_1531_ = crate::leanh::lean_ctor_get(v___x_1530_, 0);
                        crate::leanh::lean_inc(v_a_1531_);
                        v___x_1532_ = (crate::leanh::lean_unbox(v_a_1531_) as u8);
                        crate::leanh::lean_dec(v_a_1531_);
                        if v___x_1532_ == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_1530_, 1);
                            v___x_1533_ = l_Lean_Nat_mkType;
                            v___x_1534_ = l_Lean_Meta_isExprDefEq(
                                v_a_1528_,
                                v___x_1533_,
                                v___x_1526_,
                                v_a_1479_,
                                v_a_1480_,
                                v_a_1481_,
                            );
                            crate::leanh::lean_dec_ref_known(v___x_1526_, 7);
                            return v___x_1534_;
                        } else {
                            crate::leanh::lean_dec(v_a_1528_);
                            crate::leanh::lean_dec_ref_known(v___x_1526_, 7);
                            return v___x_1530_;
                        }
                    } else {
                        crate::leanh::lean_dec(v_a_1528_);
                        crate::leanh::lean_dec_ref_known(v___x_1526_, 7);
                        return v___x_1530_;
                    }
                } else {
                    crate::leanh::lean_dec_ref_known(v___x_1526_, 7);
                    v_a_1535_ = crate::leanh::lean_ctor_get(v___x_1527_, 0);
                    v_isSharedCheck_1542_ = (!crate::leanh::lean_is_exclusive(v___x_1527_)) as u8;
                    if v_isSharedCheck_1542_ == 0 {
                        v___x_1537_ = v___x_1527_;
                        v_isShared_1538_ = v_isSharedCheck_1542_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1535_);
                        crate::leanh::lean_dec(v___x_1527_);
                        v___x_1537_ = crate::leanh::lean_box(0);
                        v_isShared_1538_ = v_isSharedCheck_1542_;
                        state = 3;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_1538_ == 0 {
                    v___x_1540_ = v___x_1537_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_1541_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1541_, 0, v_a_1535_);
                    v___x_1540_ = v_reuseFailAlloc_1541_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_1540_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode___boxed(
    mut v_n_1545_: *mut crate::leanh::LeanObject,
    mut v_a_1546_: *mut crate::leanh::LeanObject,
    mut v_a_1547_: *mut crate::leanh::LeanObject,
    mut v_a_1548_: *mut crate::leanh::LeanObject,
    mut v_a_1549_: *mut crate::leanh::LeanObject,
    mut v_a_1550_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1551_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_n_1545_, v_a_1546_, v_a_1547_, v_a_1548_, v_a_1549_);
    crate::leanh::lean_dec(v_a_1549_);
    crate::leanh::lean_dec_ref(v_a_1548_);
    crate::leanh::lean_dec(v_a_1547_);
    crate::leanh::lean_dec_ref(v_a_1546_);
    return v_res_1551_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1552_ = l_instInhabitedError;
    v___x_1553_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedEIO___aux__1___boxed as *mut core::ffi::c_void,
        4,
        3,
    );
    crate::leanh::lean_closure_set(v___x_1553_, 0, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1553_, 1, crate::leanh::lean_box(0));
    crate::leanh::lean_closure_set(v___x_1553_, 2, v___x_1552_);
    return v___x_1553_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(
    mut v_msg_1554_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_481__overap_1557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1556_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___closed__0);
    v___x_481__overap_1557_ = lean_panic_fn_borrowed(v___x_1556_, v_msg_1554_);
    v___x_1558_ = crate::leanh::lean_apply_1(v___x_481__overap_1557_, crate::leanh::lean_box(0));
    return v___x_1558_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0___boxed(
    mut v_msg_1559_: *mut crate::leanh::LeanObject,
    mut v___y_1560_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1561_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v_msg_1559_);
    return v_res_1561_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(
    mut v_keys_1562_: *mut crate::leanh::LeanObject,
    mut v_vals_1563_: *mut crate::leanh::LeanObject,
    mut v_i_1564_: *mut crate::leanh::LeanObject,
    mut v_k_1565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1567_: u8 = 0;
    let mut v___x_1568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_x27_1569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1570_: u8 = 0;
    let mut v___x_1571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1566_ = lean_array_get_size(v_keys_1562_);
                v___x_1567_ = lean_nat_dec_lt(v_i_1564_, v___x_1566_);
                if v___x_1567_ == 0 {
                    crate::leanh::lean_dec(v_i_1564_);
                    v___x_1568_ = crate::leanh::lean_box(0);
                    return v___x_1568_;
                } else {
                    v_k_x27_1569_ = lean_array_fget_borrowed(v_keys_1562_, v_i_1564_);
                    v___x_1570_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_k_1565_,
                            v_k_x27_1569_,
                        );
                    if v___x_1570_ == 0 {
                        v___x_1571_ = crate::leanh::lean_unsigned_to_nat(1);
                        v___x_1572_ = lean_nat_add(v_i_1564_, v___x_1571_);
                        crate::leanh::lean_dec(v_i_1564_);
                        v_i_1564_ = v___x_1572_;
                        state = 0;
                        continue;
                    } else {
                        v___x_1574_ = lean_array_fget_borrowed(v_vals_1563_, v_i_1564_);
                        crate::leanh::lean_dec(v_i_1564_);
                        crate::leanh::lean_inc(v___x_1574_);
                        v___x_1575_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1575_, 0, v___x_1574_);
                        return v___x_1575_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_keys_1576_: *mut crate::leanh::LeanObject,
    mut v_vals_1577_: *mut crate::leanh::LeanObject,
    mut v_i_1578_: *mut crate::leanh::LeanObject,
    mut v_k_1579_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1580_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_1576_, v_vals_1577_, v_i_1578_, v_k_1579_);
    crate::leanh::lean_dec_ref(v_k_1579_);
    crate::leanh::lean_dec_ref(v_vals_1577_);
    crate::leanh::lean_dec_ref(v_keys_1576_);
    return v_res_1580_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0()
-> usize {
    let mut v___x_1581_: usize = 0;
    let mut v___x_1582_: usize = 0;
    let mut v___x_1583_: usize = 0;
    v___x_1581_ = 5usize;
    v___x_1582_ = 1usize;
    v___x_1583_ = lean_usize_shift_left(v___x_1582_, v___x_1581_);
    return v___x_1583_;
}
pub unsafe fn _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1()
-> usize {
    let mut v___x_1584_: usize = 0;
    let mut v___x_1585_: usize = 0;
    let mut v___x_1586_: usize = 0;
    v___x_1584_ = 1usize;
    v___x_1585_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__0);
    v___x_1586_ = lean_usize_sub(v___x_1585_, v___x_1584_);
    return v___x_1586_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(
    mut v_x_1587_: *mut crate::leanh::LeanObject,
    mut v_x_1588_: usize,
    mut v_x_1589_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_1590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1592_: usize = 0;
    let mut v___x_1593_: usize = 0;
    let mut v___x_1594_: usize = 0;
    let mut v_j_1595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1596_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_1597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1599_: u8 = 0;
    let mut v___x_1600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_1602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1603_: usize = 0;
    let mut v___x_1605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_ks_1606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_1607_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1608_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1609_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_1587_) == 0 {
                    v_es_1590_ = crate::leanh::lean_ctor_get(v_x_1587_, 0);
                    v___x_1591_ = crate::leanh::lean_box(2);
                    v___x_1592_ = 5usize;
                    v___x_1593_ = crate::leanh::lean_usize_once(core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1), core::ptr::addr_of_mut!(l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1_once), _init_l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___closed__1);
                    v___x_1594_ = lean_usize_land(v_x_1588_, v___x_1593_);
                    v_j_1595_ = lean_usize_to_nat(v___x_1594_);
                    v___x_1596_ = lean_array_get_borrowed(v___x_1591_, v_es_1590_, v_j_1595_);
                    crate::leanh::lean_dec(v_j_1595_);
                    match crate::leanh::lean_obj_tag(v___x_1596_) {
                        0 => {
                            v_key_1597_ = crate::leanh::lean_ctor_get(v___x_1596_, 0);
                            v_val_1598_ = crate::leanh::lean_ctor_get(v___x_1596_, 1);
                            v___x_1599_ = l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(v_x_1589_, v_key_1597_);
                            if v___x_1599_ == 0 {
                                v___x_1600_ = crate::leanh::lean_box(0);
                                return v___x_1600_;
                            } else {
                                crate::leanh::lean_inc(v_val_1598_);
                                v___x_1601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v___x_1601_, 0, v_val_1598_);
                                return v___x_1601_;
                            }
                        }
                        1 => {
                            v_node_1602_ = crate::leanh::lean_ctor_get(v___x_1596_, 0);
                            v___x_1603_ = lean_usize_shift_right(v_x_1588_, v___x_1592_);
                            v_x_1587_ = v_node_1602_;
                            v_x_1588_ = v___x_1603_;
                            state = 0;
                            continue;
                        }
                        _ => {
                            v___x_1605_ = crate::leanh::lean_box(0);
                            return v___x_1605_;
                        }
                    }
                } else {
                    v_ks_1606_ = crate::leanh::lean_ctor_get(v_x_1587_, 0);
                    v_vs_1607_ = crate::leanh::lean_ctor_get(v_x_1587_, 1);
                    v___x_1608_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_1609_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_ks_1606_, v_vs_1607_, v___x_1608_, v_x_1589_);
                    return v___x_1609_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg___boxed(
    mut v_x_1610_: *mut crate::leanh::LeanObject,
    mut v_x_1611_: *mut crate::leanh::LeanObject,
    mut v_x_1612_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_655__boxed_1613_: usize = 0;
    let mut v_res_1614_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_655__boxed_1613_ = crate::leanh::lean_unbox_usize(v_x_1611_);
    crate::leanh::lean_dec(v_x_1611_);
    v_res_1614_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_1610_, v_x_655__boxed_1613_, v_x_1612_);
    crate::leanh::lean_dec_ref(v_x_1612_);
    crate::leanh::lean_dec_ref(v_x_1610_);
    return v_res_1614_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(
    mut v_x_1615_: *mut crate::leanh::LeanObject,
    mut v_x_1616_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1617_: u64 = 0;
    let mut v___x_1618_: usize = 0;
    let mut v___x_1619_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1617_ = l_Lean_Meta_Sym_hashPtrExpr_unsafe__1(v_x_1616_);
    v___x_1618_ = lean_uint64_to_usize(v___x_1617_);
    v___x_1619_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_1615_, v___x_1618_, v_x_1616_);
    return v___x_1619_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg___boxed(
    mut v_x_1620_: *mut crate::leanh::LeanObject,
    mut v_x_1621_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1622_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1622_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_1620_, v_x_1621_);
    crate::leanh::lean_dec_ref(v_x_1621_);
    crate::leanh::lean_dec_ref(v_x_1620_);
    return v_res_1622_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_1626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1626_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__2;
    v___x_1627_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_1628_ = crate::leanh::lean_unsigned_to_nat(21);
    v___x_1629_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__1;
    v___x_1630_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__0;
    v___x_1631_ = l_mkPanicMessageWithDecl(
        v___x_1630_,
        v___x_1629_,
        v___x_1628_,
        v___x_1627_,
        v___x_1626_,
    );
    return v___x_1631_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(
    mut v_goal_1632_: *mut crate::leanh::LeanObject,
    mut v_node_1633_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_self_1635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_root_1636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1637_: u8 = 0;
    let mut v___x_1638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1647_: u8 = 0;
    let mut v_varMap_1648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_assignment_1649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1650_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1654_: u8 = 0;
    let mut v_size_1655_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1656_: u8 = 0;
    let mut v___x_1657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1659_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1662_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1669_: u8 = 0;
    let mut v___x_1670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1674_: u8 = 0;
    let mut v_a_1675_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1678_: u8 = 0;
    let mut v___x_1680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1682_: u8 = 0;
    let mut v___x_1683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_self_1635_ = crate::leanh::lean_ctor_get(v_node_1633_, 0);
                v_root_1636_ = crate::leanh::lean_ctor_get(v_node_1633_, 2);
                v___x_1637_ =
                    l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                        v_self_1635_,
                        v_root_1636_,
                    );
                if v___x_1637_ == 0 {
                    v___x_1638_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___closed__3);
                    v___x_1639_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__0(v___x_1638_);
                    return v___x_1639_;
                } else {
                    v___x_1640_ = l_Lean_Meta_Grind_Arith_Cutsat_cutsatExt;
                    v___x_1641_ = l_Lean_Meta_Grind_SolverExtension_getTerm___redArg(
                        v___x_1640_,
                        v_node_1633_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1641_) == 1 {
                        v_val_1642_ = crate::leanh::lean_ctor_get(v___x_1641_, 0);
                        crate::leanh::lean_inc(v_val_1642_);
                        crate::leanh::lean_dec_ref_known(v___x_1641_, 1);
                        v___x_1643_ = l___private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_SolverExtension_getStateCoreImpl___redArg(v___x_1640_, v_goal_1632_);
                        if crate::leanh::lean_obj_tag(v___x_1643_) == 0 {
                            v_a_1644_ = crate::leanh::lean_ctor_get(v___x_1643_, 0);
                            v_isSharedCheck_1674_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1643_)) as u8;
                            if v_isSharedCheck_1674_ == 0 {
                                v___x_1646_ = v___x_1643_;
                                v_isShared_1647_ = v_isSharedCheck_1674_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1644_);
                                crate::leanh::lean_dec(v___x_1643_);
                                v___x_1646_ = crate::leanh::lean_box(0);
                                v_isShared_1647_ = v_isSharedCheck_1674_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_val_1642_);
                            v_a_1675_ = crate::leanh::lean_ctor_get(v___x_1643_, 0);
                            v_isSharedCheck_1682_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1643_)) as u8;
                            if v_isSharedCheck_1682_ == 0 {
                                v___x_1677_ = v___x_1643_;
                                v_isShared_1678_ = v_isSharedCheck_1682_;
                                state = 7;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1675_);
                                crate::leanh::lean_dec(v___x_1643_);
                                v___x_1677_ = crate::leanh::lean_box(0);
                                v_isShared_1678_ = v_isSharedCheck_1682_;
                                state = 7;
                                continue;
                            }
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_1641_);
                        v___x_1683_ = crate::leanh::lean_box(0);
                        v___x_1684_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1684_, 0, v___x_1683_);
                        return v___x_1684_;
                    }
                }
            }
            1 => {
                v_varMap_1648_ = crate::leanh::lean_ctor_get(v_a_1644_, 1);
                crate::leanh::lean_inc_ref(v_varMap_1648_);
                v_assignment_1649_ = crate::leanh::lean_ctor_get(v_a_1644_, 13);
                crate::leanh::lean_inc_ref(v_assignment_1649_);
                crate::leanh::lean_dec(v_a_1644_);
                v___x_1650_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_varMap_1648_, v_val_1642_);
                crate::leanh::lean_dec(v_val_1642_);
                crate::leanh::lean_dec_ref(v_varMap_1648_);
                if crate::leanh::lean_obj_tag(v___x_1650_) == 1 {
                    v_val_1651_ = crate::leanh::lean_ctor_get(v___x_1650_, 0);
                    v_isSharedCheck_1669_ = (!crate::leanh::lean_is_exclusive(v___x_1650_)) as u8;
                    if v_isSharedCheck_1669_ == 0 {
                        v___x_1653_ = v___x_1650_;
                        v_isShared_1654_ = v_isSharedCheck_1669_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1651_);
                        crate::leanh::lean_dec(v___x_1650_);
                        v___x_1653_ = crate::leanh::lean_box(0);
                        v_isShared_1654_ = v_isSharedCheck_1669_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v___x_1650_);
                    crate::leanh::lean_dec_ref(v_assignment_1649_);
                    v___x_1670_ = crate::leanh::lean_box(0);
                    if v_isShared_1647_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1670_);
                        v___x_1672_ = v___x_1646_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_1673_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1673_, 0, v___x_1670_);
                        v___x_1672_ = v_reuseFailAlloc_1673_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                v_size_1655_ = crate::leanh::lean_ctor_get(v_assignment_1649_, 2);
                v___x_1656_ = lean_nat_dec_lt(v_val_1651_, v_size_1655_);
                if v___x_1656_ == 0 {
                    crate::leanh::lean_del_object(v___x_1653_);
                    crate::leanh::lean_dec(v_val_1651_);
                    crate::leanh::lean_dec_ref(v_assignment_1649_);
                    v___x_1657_ = crate::leanh::lean_box(0);
                    if v_isShared_1647_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1657_);
                        v___x_1659_ = v___x_1646_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_1660_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1660_, 0, v___x_1657_);
                        v___x_1659_ = v_reuseFailAlloc_1660_;
                        state = 3;
                        continue;
                    }
                } else {
                    v___x_1661_ = l_instInhabitedRat;
                    v___x_1662_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1661_,
                        v_assignment_1649_,
                        v_val_1651_,
                    );
                    crate::leanh::lean_dec(v_val_1651_);
                    crate::leanh::lean_dec_ref(v_assignment_1649_);
                    if v_isShared_1654_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1653_, 0, v___x_1662_);
                        v___x_1664_ = v___x_1653_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_1668_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1668_, 0, v___x_1662_);
                        v___x_1664_ = v_reuseFailAlloc_1668_;
                        state = 4;
                        continue;
                    }
                }
            }
            3 => {
                return v___x_1659_;
            }
            4 => {
                if v_isShared_1647_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1646_, 0, v___x_1664_);
                    v___x_1666_ = v___x_1646_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1667_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1667_, 0, v___x_1664_);
                    v___x_1666_ = v_reuseFailAlloc_1667_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1666_;
            }
            6 => {
                return v___x_1672_;
            }
            7 => {
                if v_isShared_1678_ == 0 {
                    v___x_1680_ = v___x_1677_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_1681_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1681_, 0, v_a_1675_);
                    v___x_1680_ = v_reuseFailAlloc_1681_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_1680_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f___boxed(
    mut v_goal_1685_: *mut crate::leanh::LeanObject,
    mut v_node_1686_: *mut crate::leanh::LeanObject,
    mut v_a_1687_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1688_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_1685_, v_node_1686_);
    crate::leanh::lean_dec_ref(v_node_1686_);
    crate::leanh::lean_dec_ref(v_goal_1685_);
    return v_res_1688_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(
    mut v_00_u03b2_1689_: *mut crate::leanh::LeanObject,
    mut v_x_1690_: *mut crate::leanh::LeanObject,
    mut v_x_1691_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1692_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___redArg(v_x_1690_, v_x_1691_);
    return v___x_1692_;
}
pub unsafe fn l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1___boxed(
    mut v_00_u03b2_1693_: *mut crate::leanh::LeanObject,
    mut v_x_1694_: *mut crate::leanh::LeanObject,
    mut v_x_1695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1696_ = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1(v_00_u03b2_1693_, v_x_1694_, v_x_1695_);
    crate::leanh::lean_dec_ref(v_x_1695_);
    crate::leanh::lean_dec_ref(v_x_1694_);
    return v_res_1696_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(
    mut v_00_u03b2_1697_: *mut crate::leanh::LeanObject,
    mut v_x_1698_: *mut crate::leanh::LeanObject,
    mut v_x_1699_: usize,
    mut v_x_1700_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1701_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___redArg(v_x_1698_, v_x_1699_, v_x_1700_);
    return v___x_1701_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1___boxed(
    mut v_00_u03b2_1702_: *mut crate::leanh::LeanObject,
    mut v_x_1703_: *mut crate::leanh::LeanObject,
    mut v_x_1704_: *mut crate::leanh::LeanObject,
    mut v_x_1705_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_848__boxed_1706_: usize = 0;
    let mut v_res_1707_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_x_848__boxed_1706_ = crate::leanh::lean_unbox_usize(v_x_1704_);
    crate::leanh::lean_dec(v_x_1704_);
    v_res_1707_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1(v_00_u03b2_1702_, v_x_1703_, v_x_848__boxed_1706_, v_x_1705_);
    crate::leanh::lean_dec_ref(v_x_1705_);
    crate::leanh::lean_dec_ref(v_x_1703_);
    return v_res_1707_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(
    mut v_00_u03b2_1708_: *mut crate::leanh::LeanObject,
    mut v_keys_1709_: *mut crate::leanh::LeanObject,
    mut v_vals_1710_: *mut crate::leanh::LeanObject,
    mut v_heq_1711_: *mut crate::leanh::LeanObject,
    mut v_i_1712_: *mut crate::leanh::LeanObject,
    mut v_k_1713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1714_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___redArg(v_keys_1709_, v_vals_1710_, v_i_1712_, v_k_1713_);
    return v___x_1714_;
}
pub unsafe fn l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2___boxed(
    mut v_00_u03b2_1715_: *mut crate::leanh::LeanObject,
    mut v_keys_1716_: *mut crate::leanh::LeanObject,
    mut v_vals_1717_: *mut crate::leanh::LeanObject,
    mut v_heq_1718_: *mut crate::leanh::LeanObject,
    mut v_i_1719_: *mut crate::leanh::LeanObject,
    mut v_k_1720_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1721_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f_spec__1_spec__1_spec__2(v_00_u03b2_1715_, v_keys_1716_, v_vals_1717_, v_heq_1718_, v_i_1719_, v_k_1720_);
    crate::leanh::lean_dec_ref(v_k_1720_);
    crate::leanh::lean_dec_ref(v_vals_1717_);
    crate::leanh::lean_dec_ref(v_keys_1716_);
    return v_res_1721_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(
    mut v_e_1739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1741_: u8 = 0;
    v___x_1740_ = l_Lean_Expr_cleanupAnnotations(v_e_1739_);
    v___x_1741_ = l_Lean_Expr_isApp(v___x_1740_);
    if v___x_1741_ == 0 {
        let mut v___x_1742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref(v___x_1740_);
        v___x_1742_ = crate::leanh::lean_box(0);
        return v___x_1742_;
    } else {
        let mut v_arg_1743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_1745_: u8 = 0;
        v_arg_1743_ = crate::leanh::lean_ctor_get(v___x_1740_, 1);
        crate::leanh::lean_inc_ref(v_arg_1743_);
        v___x_1744_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1740_);
        v___x_1745_ = l_Lean_Expr_isApp(v___x_1744_);
        if v___x_1745_ == 0 {
            let mut v___x_1746_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref(v___x_1744_);
            crate::leanh::lean_dec_ref(v_arg_1743_);
            v___x_1746_ = crate::leanh::lean_box(0);
            return v___x_1746_;
        } else {
            let mut v_arg_1747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            let mut v___x_1749_: u8 = 0;
            v_arg_1747_ = crate::leanh::lean_ctor_get(v___x_1744_, 1);
            crate::leanh::lean_inc_ref(v_arg_1747_);
            v___x_1748_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1744_);
            v___x_1749_ = l_Lean_Expr_isApp(v___x_1748_);
            if v___x_1749_ == 0 {
                let mut v___x_1750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref(v___x_1748_);
                crate::leanh::lean_dec_ref(v_arg_1747_);
                crate::leanh::lean_dec_ref(v_arg_1743_);
                v___x_1750_ = crate::leanh::lean_box(0);
                return v___x_1750_;
            } else {
                let mut v___x_1751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                let mut v___x_1753_: u8 = 0;
                v___x_1751_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1748_);
                v___x_1752_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__2;
                v___x_1753_ = l_Lean_Expr_isConstOf(v___x_1751_, v___x_1752_);
                if v___x_1753_ == 0 {
                    let mut v___x_1754_: u8 = 0;
                    crate::leanh::lean_dec_ref(v_arg_1747_);
                    v___x_1754_ = l_Lean_Expr_isApp(v___x_1751_);
                    if v___x_1754_ == 0 {
                        let mut v___x_1755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref(v___x_1751_);
                        crate::leanh::lean_dec_ref(v_arg_1743_);
                        v___x_1755_ = crate::leanh::lean_box(0);
                        return v___x_1755_;
                    } else {
                        let mut v___x_1756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        let mut v___x_1758_: u8 = 0;
                        v___x_1756_ = l_Lean_Expr_appFnCleanup___redArg(v___x_1751_);
                        v___x_1757_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__7;
                        v___x_1758_ = l_Lean_Expr_isConstOf(v___x_1756_, v___x_1757_);
                        crate::leanh::lean_dec_ref(v___x_1756_);
                        if v___x_1758_ == 0 {
                            let mut v___x_1759_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            crate::leanh::lean_dec_ref(v_arg_1743_);
                            v___x_1759_ = crate::leanh::lean_box(0);
                            return v___x_1759_;
                        } else {
                            let mut v___x_1760_: *mut crate::leanh::LeanObject =
                                core::ptr::null_mut();
                            v___x_1760_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                            crate::leanh::lean_ctor_set(v___x_1760_, 0, v_arg_1743_);
                            return v___x_1760_;
                        }
                    }
                } else {
                    let mut v___x_1761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1762_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                    let mut v___x_1763_: u8 = 0;
                    crate::leanh::lean_dec_ref(v___x_1751_);
                    v___x_1761_ = l_Lean_Expr_cleanupAnnotations(v_arg_1747_);
                    v___x_1762_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f___closed__9;
                    v___x_1763_ = l_Lean_Expr_isConstOf(v___x_1761_, v___x_1762_);
                    crate::leanh::lean_dec_ref(v___x_1761_);
                    if v___x_1763_ == 0 {
                        let mut v___x_1764_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        crate::leanh::lean_dec_ref(v_arg_1743_);
                        v___x_1764_ = crate::leanh::lean_box(0);
                        return v___x_1764_;
                    } else {
                        let mut v___x_1765_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                        v___x_1765_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_1765_, 0, v_arg_1743_);
                        return v___x_1765_;
                    }
                }
            }
        }
    }
}
pub unsafe fn l_Int_cast___at___00Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f_spec__0(
    mut v_a_1766_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_1767_ = l_Rat_ofInt(v_a_1766_);
    return v___x_1767_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
    mut v_goal_1768_: *mut crate::leanh::LeanObject,
    mut v_e_1769_: *mut crate::leanh::LeanObject,
    mut v_a_1770_: *mut crate::leanh::LeanObject,
    mut v_a_1771_: *mut crate::leanh::LeanObject,
    mut v_a_1772_: *mut crate::leanh::LeanObject,
    mut v_a_1773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1783_: u8 = 0;
    let mut v___x_1785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_1787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1792_: u8 = 0;
    let mut v_val_1793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1796_: u8 = 0;
    let mut v___x_1797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1803_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1804_: u8 = 0;
    let mut v___x_1805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1809_: u8 = 0;
    let mut v_val_1810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1813_: u8 = 0;
    let mut v___x_1814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1819_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1822_: u8 = 0;
    let mut v___x_1823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1827_: u8 = 0;
    let mut v_a_1828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1831_: u8 = 0;
    let mut v___x_1833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1835_: u8 = 0;
    let mut v_isSharedCheck_1836_: u8 = 0;
    let mut v_a_1837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1840_: u8 = 0;
    let mut v___x_1842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1844_: u8 = 0;
    let mut v_isSharedCheck_1845_: u8 = 0;
    let mut v_a_1846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1849_: u8 = 0;
    let mut v_ref_1850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1858_: u8 = 0;
    let mut v_a_1859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1862_: u8 = 0;
    let mut v___x_1864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1866_: u8 = 0;
    let mut v_a_1867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1870_: u8 = 0;
    let mut v___x_1872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1874_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1775_ = l_Lean_Meta_Grind_Goal_getRoot(
                    v_goal_1768_,
                    v_e_1769_,
                    v_a_1770_,
                    v_a_1771_,
                    v_a_1772_,
                    v_a_1773_,
                );
                if crate::leanh::lean_obj_tag(v___x_1775_) == 0 {
                    v_a_1776_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                    crate::leanh::lean_inc(v_a_1776_);
                    crate::leanh::lean_dec_ref_known(v___x_1775_, 1);
                    v___x_1777_ = l_Lean_Meta_Grind_Goal_getENode(
                        v_goal_1768_,
                        v_a_1776_,
                        v_a_1770_,
                        v_a_1771_,
                        v_a_1772_,
                        v_a_1773_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1777_) == 0 {
                        v_a_1778_ = crate::leanh::lean_ctor_get(v___x_1777_, 0);
                        crate::leanh::lean_inc(v_a_1778_);
                        crate::leanh::lean_dec_ref_known(v___x_1777_, 1);
                        v___x_1779_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_getCutsatAssignment_x3f(v_goal_1768_, v_a_1778_);
                        if crate::leanh::lean_obj_tag(v___x_1779_) == 0 {
                            v_a_1780_ = crate::leanh::lean_ctor_get(v___x_1779_, 0);
                            v_isSharedCheck_1845_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1779_)) as u8;
                            if v_isSharedCheck_1845_ == 0 {
                                v___x_1782_ = v___x_1779_;
                                v_isShared_1783_ = v_isSharedCheck_1845_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1780_);
                                crate::leanh::lean_dec(v___x_1779_);
                                v___x_1782_ = crate::leanh::lean_box(0);
                                v_isShared_1783_ = v_isSharedCheck_1845_;
                                state = 1;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1778_);
                            v_a_1846_ = crate::leanh::lean_ctor_get(v___x_1779_, 0);
                            v_isSharedCheck_1858_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1779_)) as u8;
                            if v_isSharedCheck_1858_ == 0 {
                                v___x_1848_ = v___x_1779_;
                                v_isShared_1849_ = v_isSharedCheck_1858_;
                                state = 16;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1846_);
                                crate::leanh::lean_dec(v___x_1779_);
                                v___x_1848_ = crate::leanh::lean_box(0);
                                v_isShared_1849_ = v_isSharedCheck_1858_;
                                state = 16;
                                continue;
                            }
                        }
                    } else {
                        v_a_1859_ = crate::leanh::lean_ctor_get(v___x_1777_, 0);
                        v_isSharedCheck_1866_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1777_)) as u8;
                        if v_isSharedCheck_1866_ == 0 {
                            v___x_1861_ = v___x_1777_;
                            v_isShared_1862_ = v_isSharedCheck_1866_;
                            state = 18;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1859_);
                            crate::leanh::lean_dec(v___x_1777_);
                            v___x_1861_ = crate::leanh::lean_box(0);
                            v_isShared_1862_ = v_isSharedCheck_1866_;
                            state = 18;
                            continue;
                        }
                    }
                } else {
                    v_a_1867_ = crate::leanh::lean_ctor_get(v___x_1775_, 0);
                    v_isSharedCheck_1874_ = (!crate::leanh::lean_is_exclusive(v___x_1775_)) as u8;
                    if v_isSharedCheck_1874_ == 0 {
                        v___x_1869_ = v___x_1775_;
                        v_isShared_1870_ = v_isSharedCheck_1874_;
                        state = 20;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1867_);
                        crate::leanh::lean_dec(v___x_1775_);
                        v___x_1869_ = crate::leanh::lean_box(0);
                        v_isShared_1870_ = v_isSharedCheck_1874_;
                        state = 20;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_1780_) == 1 {
                    crate::leanh::lean_dec(v_a_1778_);
                    if v_isShared_1783_ == 0 {
                        v___x_1785_ = v___x_1782_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1786_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1786_, 0, v_a_1780_);
                        v___x_1785_ = v_reuseFailAlloc_1786_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1782_);
                    crate::leanh::lean_dec(v_a_1780_);
                    v_self_1787_ = crate::leanh::lean_ctor_get(v_a_1778_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_1787_, 2);
                    crate::leanh::lean_dec(v_a_1778_);
                    v___x_1788_ = l_Lean_Meta_getIntValue_x3f(
                        v_self_1787_,
                        v_a_1770_,
                        v_a_1771_,
                        v_a_1772_,
                        v_a_1773_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_1788_) == 0 {
                        v_a_1789_ = crate::leanh::lean_ctor_get(v___x_1788_, 0);
                        v_isSharedCheck_1836_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1788_)) as u8;
                        if v_isSharedCheck_1836_ == 0 {
                            v___x_1791_ = v___x_1788_;
                            v_isShared_1792_ = v_isSharedCheck_1836_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1789_);
                            crate::leanh::lean_dec(v___x_1788_);
                            v___x_1791_ = crate::leanh::lean_box(0);
                            v_isShared_1792_ = v_isSharedCheck_1836_;
                            state = 3;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_self_1787_);
                        v_a_1837_ = crate::leanh::lean_ctor_get(v___x_1788_, 0);
                        v_isSharedCheck_1844_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1788_)) as u8;
                        if v_isSharedCheck_1844_ == 0 {
                            v___x_1839_ = v___x_1788_;
                            v_isShared_1840_ = v_isSharedCheck_1844_;
                            state = 14;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1837_);
                            crate::leanh::lean_dec(v___x_1788_);
                            v___x_1839_ = crate::leanh::lean_box(0);
                            v_isShared_1840_ = v_isSharedCheck_1844_;
                            state = 14;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_1785_;
            }
            3 => {
                if crate::leanh::lean_obj_tag(v_a_1789_) == 1 {
                    crate::leanh::lean_dec_ref(v_self_1787_);
                    v_val_1793_ = crate::leanh::lean_ctor_get(v_a_1789_, 0);
                    v_isSharedCheck_1804_ = (!crate::leanh::lean_is_exclusive(v_a_1789_)) as u8;
                    if v_isSharedCheck_1804_ == 0 {
                        v___x_1795_ = v_a_1789_;
                        v_isShared_1796_ = v_isSharedCheck_1804_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1793_);
                        crate::leanh::lean_dec(v_a_1789_);
                        v___x_1795_ = crate::leanh::lean_box(0);
                        v_isShared_1796_ = v_isSharedCheck_1804_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1791_);
                    crate::leanh::lean_dec(v_a_1789_);
                    v___x_1805_ = l_Lean_Meta_getNatValue_x3f(
                        v_self_1787_,
                        v_a_1770_,
                        v_a_1771_,
                        v_a_1772_,
                        v_a_1773_,
                    );
                    crate::leanh::lean_dec_ref(v_self_1787_);
                    if crate::leanh::lean_obj_tag(v___x_1805_) == 0 {
                        v_a_1806_ = crate::leanh::lean_ctor_get(v___x_1805_, 0);
                        v_isSharedCheck_1827_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1805_)) as u8;
                        if v_isSharedCheck_1827_ == 0 {
                            v___x_1808_ = v___x_1805_;
                            v_isShared_1809_ = v_isSharedCheck_1827_;
                            state = 7;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1806_);
                            crate::leanh::lean_dec(v___x_1805_);
                            v___x_1808_ = crate::leanh::lean_box(0);
                            v_isShared_1809_ = v_isSharedCheck_1827_;
                            state = 7;
                            continue;
                        }
                    } else {
                        v_a_1828_ = crate::leanh::lean_ctor_get(v___x_1805_, 0);
                        v_isSharedCheck_1835_ =
                            (!crate::leanh::lean_is_exclusive(v___x_1805_)) as u8;
                        if v_isSharedCheck_1835_ == 0 {
                            v___x_1830_ = v___x_1805_;
                            v_isShared_1831_ = v_isSharedCheck_1835_;
                            state = 12;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_1828_);
                            crate::leanh::lean_dec(v___x_1805_);
                            v___x_1830_ = crate::leanh::lean_box(0);
                            v_isShared_1831_ = v_isSharedCheck_1835_;
                            state = 12;
                            continue;
                        }
                    }
                }
            }
            4 => {
                v___x_1797_ = l_Rat_ofInt(v_val_1793_);
                if v_isShared_1796_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1795_, 0, v___x_1797_);
                    v___x_1799_ = v___x_1795_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1803_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1803_, 0, v___x_1797_);
                    v___x_1799_ = v_reuseFailAlloc_1803_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                if v_isShared_1792_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1791_, 0, v___x_1799_);
                    v___x_1801_ = v___x_1791_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_1802_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1802_, 0, v___x_1799_);
                    v___x_1801_ = v_reuseFailAlloc_1802_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_1801_;
            }
            7 => {
                if crate::leanh::lean_obj_tag(v_a_1806_) == 1 {
                    v_val_1810_ = crate::leanh::lean_ctor_get(v_a_1806_, 0);
                    v_isSharedCheck_1822_ = (!crate::leanh::lean_is_exclusive(v_a_1806_)) as u8;
                    if v_isSharedCheck_1822_ == 0 {
                        v___x_1812_ = v_a_1806_;
                        v_isShared_1813_ = v_isSharedCheck_1822_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_val_1810_);
                        crate::leanh::lean_dec(v_a_1806_);
                        v___x_1812_ = crate::leanh::lean_box(0);
                        v_isShared_1813_ = v_isSharedCheck_1822_;
                        state = 8;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec(v_a_1806_);
                    v___x_1823_ = crate::leanh::lean_box(0);
                    if v_isShared_1809_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_1808_, 0, v___x_1823_);
                        v___x_1825_ = v___x_1808_;
                        state = 11;
                        continue;
                    } else {
                        v_reuseFailAlloc_1826_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_1826_, 0, v___x_1823_);
                        v___x_1825_ = v_reuseFailAlloc_1826_;
                        state = 11;
                        continue;
                    }
                }
            }
            8 => {
                v___x_1814_ = lean_nat_to_int(v_val_1810_);
                v___x_1815_ = l_Rat_ofInt(v___x_1814_);
                if v_isShared_1813_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1812_, 0, v___x_1815_);
                    v___x_1817_ = v___x_1812_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1821_, 0, v___x_1815_);
                    v___x_1817_ = v_reuseFailAlloc_1821_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                if v_isShared_1809_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1808_, 0, v___x_1817_);
                    v___x_1819_ = v___x_1808_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_1820_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1820_, 0, v___x_1817_);
                    v___x_1819_ = v_reuseFailAlloc_1820_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_1819_;
            }
            11 => {
                return v___x_1825_;
            }
            12 => {
                if v_isShared_1831_ == 0 {
                    v___x_1833_ = v___x_1830_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_1834_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1834_, 0, v_a_1828_);
                    v___x_1833_ = v_reuseFailAlloc_1834_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_1833_;
            }
            14 => {
                if v_isShared_1840_ == 0 {
                    v___x_1842_ = v___x_1839_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_1843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1843_, 0, v_a_1837_);
                    v___x_1842_ = v_reuseFailAlloc_1843_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_1842_;
            }
            16 => {
                v_ref_1850_ = crate::leanh::lean_ctor_get(v_a_1772_, 5);
                v___x_1851_ = lean_io_error_to_string(v_a_1846_);
                v___x_1852_ = crate::leanh::lean_alloc_ctor(3, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1852_, 0, v___x_1851_);
                v___x_1853_ = l_Lean_MessageData_ofFormat(v___x_1852_);
                crate::leanh::lean_inc(v_ref_1850_);
                v___x_1854_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_1854_, 0, v_ref_1850_);
                crate::leanh::lean_ctor_set(v___x_1854_, 1, v___x_1853_);
                if v_isShared_1849_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1848_, 0, v___x_1854_);
                    v___x_1856_ = v___x_1848_;
                    state = 17;
                    continue;
                } else {
                    v_reuseFailAlloc_1857_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1854_);
                    v___x_1856_ = v_reuseFailAlloc_1857_;
                    state = 17;
                    continue;
                }
            }
            17 => {
                return v___x_1856_;
            }
            18 => {
                if v_isShared_1862_ == 0 {
                    v___x_1864_ = v___x_1861_;
                    state = 19;
                    continue;
                } else {
                    v_reuseFailAlloc_1865_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1865_, 0, v_a_1859_);
                    v___x_1864_ = v_reuseFailAlloc_1865_;
                    state = 19;
                    continue;
                }
            }
            19 => {
                return v___x_1864_;
            }
            20 => {
                if v_isShared_1870_ == 0 {
                    v___x_1872_ = v___x_1869_;
                    state = 21;
                    continue;
                } else {
                    v_reuseFailAlloc_1873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1873_, 0, v_a_1867_);
                    v___x_1872_ = v_reuseFailAlloc_1873_;
                    state = 21;
                    continue;
                }
            }
            21 => {
                return v___x_1872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f___boxed(
    mut v_goal_1875_: *mut crate::leanh::LeanObject,
    mut v_e_1876_: *mut crate::leanh::LeanObject,
    mut v_a_1877_: *mut crate::leanh::LeanObject,
    mut v_a_1878_: *mut crate::leanh::LeanObject,
    mut v_a_1879_: *mut crate::leanh::LeanObject,
    mut v_a_1880_: *mut crate::leanh::LeanObject,
    mut v_a_1881_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_1882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_1882_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
        v_goal_1875_,
        v_e_1876_,
        v_a_1877_,
        v_a_1878_,
        v_a_1879_,
        v_a_1880_,
    );
    crate::leanh::lean_dec(v_a_1880_);
    crate::leanh::lean_dec_ref(v_a_1879_);
    crate::leanh::lean_dec(v_a_1878_);
    crate::leanh::lean_dec_ref(v_a_1877_);
    crate::leanh::lean_dec_ref(v_goal_1875_);
    return v_res_1882_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(
    mut v_goal_1883_: *mut crate::leanh::LeanObject,
    mut v_as_1884_: *mut crate::leanh::LeanObject,
    mut v_sz_1885_: usize,
    mut v_i_1886_: usize,
    mut v_b_1887_: *mut crate::leanh::LeanObject,
    mut v___y_1888_: *mut crate::leanh::LeanObject,
    mut v___y_1889_: *mut crate::leanh::LeanObject,
    mut v___y_1890_: *mut crate::leanh::LeanObject,
    mut v___y_1891_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1893_: u8 = 0;
    let mut v___x_1894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1897_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1898_: u8 = 0;
    let mut v_a_1899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1900_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: usize = 0;
    let mut v___x_1908_: usize = 0;
    let mut v_reuseFailAlloc_1910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1911_: u8 = 0;
    let mut v___x_1912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1914_: u8 = 0;
    let mut v_self_1915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1917_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1923_: u8 = 0;
    let mut v___x_1925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1927_: u8 = 0;
    let mut v_a_1928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1931_: u8 = 0;
    let mut v___x_1933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1935_: u8 = 0;
    let mut v_a_1936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1939_: u8 = 0;
    let mut v___x_1941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1943_: u8 = 0;
    let mut v_isSharedCheck_1944_: u8 = 0;
    let mut v_unused_1945_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1893_ = lean_usize_dec_lt(v_i_1886_, v_sz_1885_);
                if v___x_1893_ == 0 {
                    v___x_1894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1894_, 0, v_b_1887_);
                    return v___x_1894_;
                } else {
                    v_snd_1895_ = crate::leanh::lean_ctor_get(v_b_1887_, 1);
                    v_isSharedCheck_1944_ = (!crate::leanh::lean_is_exclusive(v_b_1887_)) as u8;
                    if v_isSharedCheck_1944_ == 0 {
                        v_unused_1945_ = crate::leanh::lean_ctor_get(v_b_1887_, 0);
                        crate::leanh::lean_dec(v_unused_1945_);
                        v___x_1897_ = v_b_1887_;
                        v_isShared_1898_ = v_isSharedCheck_1944_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1895_);
                        crate::leanh::lean_dec(v_b_1887_);
                        v___x_1897_ = crate::leanh::lean_box(0);
                        v_isShared_1898_ = v_isSharedCheck_1944_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1899_ = lean_array_uget_borrowed(v_as_1884_, v_i_1886_);
                crate::leanh::lean_inc(v_a_1899_);
                v___x_1900_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_1883_,
                    v_a_1899_,
                    v___y_1888_,
                    v___y_1889_,
                    v___y_1890_,
                    v___y_1891_,
                );
                if crate::leanh::lean_obj_tag(v___x_1900_) == 0 {
                    v_a_1901_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                    crate::leanh::lean_inc(v_a_1901_);
                    crate::leanh::lean_dec_ref_known(v___x_1900_, 1);
                    v___x_1902_ = crate::leanh::lean_box(0);
                    v___x_1911_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1901_);
                    if v___x_1911_ == 0 {
                        crate::leanh::lean_dec(v_a_1901_);
                        v_a_1904_ = v_snd_1895_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1901_);
                        v___x_1912_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_1901_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_);
                        if crate::leanh::lean_obj_tag(v___x_1912_) == 0 {
                            v_a_1913_ = crate::leanh::lean_ctor_get(v___x_1912_, 0);
                            crate::leanh::lean_inc(v_a_1913_);
                            crate::leanh::lean_dec_ref_known(v___x_1912_, 1);
                            v___x_1914_ = (crate::leanh::lean_unbox(v_a_1913_) as u8);
                            crate::leanh::lean_dec(v_a_1913_);
                            if v___x_1914_ == 0 {
                                crate::leanh::lean_dec(v_a_1901_);
                                v_a_1904_ = v_snd_1895_;
                                state = 2;
                                continue;
                            } else {
                                v_self_1915_ = crate::leanh::lean_ctor_get(v_a_1901_, 0);
                                crate::leanh::lean_inc_ref_n(v_self_1915_, 2);
                                crate::leanh::lean_dec(v_a_1901_);
                                v___x_1916_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                                    v_goal_1883_,
                                    v_self_1915_,
                                    v___y_1888_,
                                    v___y_1889_,
                                    v___y_1890_,
                                    v___y_1891_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1916_) == 0 {
                                    v_a_1917_ = crate::leanh::lean_ctor_get(v___x_1916_, 0);
                                    crate::leanh::lean_inc(v_a_1917_);
                                    crate::leanh::lean_dec_ref_known(v___x_1916_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_1917_) == 1 {
                                        v_val_1918_ = crate::leanh::lean_ctor_get(v_a_1917_, 0);
                                        crate::leanh::lean_inc(v_val_1918_);
                                        crate::leanh::lean_dec_ref_known(v_a_1917_, 1);
                                        v___x_1919_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                            v_goal_1883_,
                                            v_self_1915_,
                                            v_val_1918_,
                                            v_snd_1895_,
                                        );
                                        v_a_1904_ = v___x_1919_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_1917_);
                                        crate::leanh::lean_dec_ref(v_self_1915_);
                                        v_a_1904_ = v_snd_1895_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_self_1915_);
                                    crate::leanh::lean_del_object(v___x_1897_);
                                    crate::leanh::lean_dec(v_snd_1895_);
                                    v_a_1920_ = crate::leanh::lean_ctor_get(v___x_1916_, 0);
                                    v_isSharedCheck_1927_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1916_)) as u8;
                                    if v_isSharedCheck_1927_ == 0 {
                                        v___x_1922_ = v___x_1916_;
                                        v_isShared_1923_ = v_isSharedCheck_1927_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1920_);
                                        crate::leanh::lean_dec(v___x_1916_);
                                        v___x_1922_ = crate::leanh::lean_box(0);
                                        v_isShared_1923_ = v_isSharedCheck_1927_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1901_);
                            crate::leanh::lean_del_object(v___x_1897_);
                            crate::leanh::lean_dec(v_snd_1895_);
                            v_a_1928_ = crate::leanh::lean_ctor_get(v___x_1912_, 0);
                            v_isSharedCheck_1935_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1912_)) as u8;
                            if v_isSharedCheck_1935_ == 0 {
                                v___x_1930_ = v___x_1912_;
                                v_isShared_1931_ = v_isSharedCheck_1935_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_1928_);
                                crate::leanh::lean_dec(v___x_1912_);
                                v___x_1930_ = crate::leanh::lean_box(0);
                                v_isShared_1931_ = v_isSharedCheck_1935_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1897_);
                    crate::leanh::lean_dec(v_snd_1895_);
                    v_a_1936_ = crate::leanh::lean_ctor_get(v___x_1900_, 0);
                    v_isSharedCheck_1943_ = (!crate::leanh::lean_is_exclusive(v___x_1900_)) as u8;
                    if v_isSharedCheck_1943_ == 0 {
                        v___x_1938_ = v___x_1900_;
                        v_isShared_1939_ = v_isSharedCheck_1943_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1936_);
                        crate::leanh::lean_dec(v___x_1900_);
                        v___x_1938_ = crate::leanh::lean_box(0);
                        v_isShared_1939_ = v_isSharedCheck_1943_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1898_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1897_, 1, v_a_1904_);
                    crate::leanh::lean_ctor_set(v___x_1897_, 0, v___x_1902_);
                    v___x_1906_ = v___x_1897_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1910_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 0, v___x_1902_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1910_, 1, v_a_1904_);
                    v___x_1906_ = v_reuseFailAlloc_1910_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1907_ = 1usize;
                v___x_1908_ = lean_usize_add(v_i_1886_, v___x_1907_);
                v_i_1886_ = v___x_1908_;
                v_b_1887_ = v___x_1906_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_1923_ == 0 {
                    v___x_1925_ = v___x_1922_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_1926_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1926_, 0, v_a_1920_);
                    v___x_1925_ = v_reuseFailAlloc_1926_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_1925_;
            }
            6 => {
                if v_isShared_1931_ == 0 {
                    v___x_1933_ = v___x_1930_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_1934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1934_, 0, v_a_1928_);
                    v___x_1933_ = v_reuseFailAlloc_1934_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_1933_;
            }
            8 => {
                if v_isShared_1939_ == 0 {
                    v___x_1941_ = v___x_1938_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_1942_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1942_, 0, v_a_1936_);
                    v___x_1941_ = v_reuseFailAlloc_1942_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_1941_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6___boxed(
    mut v_goal_1946_: *mut crate::leanh::LeanObject,
    mut v_as_1947_: *mut crate::leanh::LeanObject,
    mut v_sz_1948_: *mut crate::leanh::LeanObject,
    mut v_i_1949_: *mut crate::leanh::LeanObject,
    mut v_b_1950_: *mut crate::leanh::LeanObject,
    mut v___y_1951_: *mut crate::leanh::LeanObject,
    mut v___y_1952_: *mut crate::leanh::LeanObject,
    mut v___y_1953_: *mut crate::leanh::LeanObject,
    mut v___y_1954_: *mut crate::leanh::LeanObject,
    mut v___y_1955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_1956_: usize = 0;
    let mut v_i_boxed_1957_: usize = 0;
    let mut v_res_1958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_1956_ = crate::leanh::lean_unbox_usize(v_sz_1948_);
    crate::leanh::lean_dec(v_sz_1948_);
    v_i_boxed_1957_ = crate::leanh::lean_unbox_usize(v_i_1949_);
    crate::leanh::lean_dec(v_i_1949_);
    v_res_1958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_1946_, v_as_1947_, v_sz_boxed_1956_, v_i_boxed_1957_, v_b_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
    crate::leanh::lean_dec(v___y_1954_);
    crate::leanh::lean_dec_ref(v___y_1953_);
    crate::leanh::lean_dec(v___y_1952_);
    crate::leanh::lean_dec_ref(v___y_1951_);
    crate::leanh::lean_dec_ref(v_as_1947_);
    crate::leanh::lean_dec_ref(v_goal_1946_);
    return v_res_1958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(
    mut v_goal_1959_: *mut crate::leanh::LeanObject,
    mut v_as_1960_: *mut crate::leanh::LeanObject,
    mut v_sz_1961_: usize,
    mut v_i_1962_: usize,
    mut v_b_1963_: *mut crate::leanh::LeanObject,
    mut v___y_1964_: *mut crate::leanh::LeanObject,
    mut v___y_1965_: *mut crate::leanh::LeanObject,
    mut v___y_1966_: *mut crate::leanh::LeanObject,
    mut v___y_1967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_1969_: u8 = 0;
    let mut v___x_1970_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_1971_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1974_: u8 = 0;
    let mut v_a_1975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1978_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1980_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1983_: usize = 0;
    let mut v___x_1984_: usize = 0;
    let mut v___x_1985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1987_: u8 = 0;
    let mut v___x_1988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1990_: u8 = 0;
    let mut v_self_1991_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_1994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_1996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_1998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_1999_: u8 = 0;
    let mut v___x_2001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2003_: u8 = 0;
    let mut v_a_2004_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2006_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2007_: u8 = 0;
    let mut v___x_2009_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2010_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2011_: u8 = 0;
    let mut v_a_2012_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v___x_2017_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2019_: u8 = 0;
    let mut v_isSharedCheck_2020_: u8 = 0;
    let mut v_unused_2021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1969_ = lean_usize_dec_lt(v_i_1962_, v_sz_1961_);
                if v___x_1969_ == 0 {
                    v___x_1970_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_1970_, 0, v_b_1963_);
                    return v___x_1970_;
                } else {
                    v_snd_1971_ = crate::leanh::lean_ctor_get(v_b_1963_, 1);
                    v_isSharedCheck_2020_ = (!crate::leanh::lean_is_exclusive(v_b_1963_)) as u8;
                    if v_isSharedCheck_2020_ == 0 {
                        v_unused_2021_ = crate::leanh::lean_ctor_get(v_b_1963_, 0);
                        crate::leanh::lean_dec(v_unused_2021_);
                        v___x_1973_ = v_b_1963_;
                        v_isShared_1974_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_1971_);
                        crate::leanh::lean_dec(v_b_1963_);
                        v___x_1973_ = crate::leanh::lean_box(0);
                        v_isShared_1974_ = v_isSharedCheck_2020_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_1975_ = lean_array_uget_borrowed(v_as_1960_, v_i_1962_);
                crate::leanh::lean_inc(v_a_1975_);
                v___x_1976_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_1959_,
                    v_a_1975_,
                    v___y_1964_,
                    v___y_1965_,
                    v___y_1966_,
                    v___y_1967_,
                );
                if crate::leanh::lean_obj_tag(v___x_1976_) == 0 {
                    v_a_1977_ = crate::leanh::lean_ctor_get(v___x_1976_, 0);
                    crate::leanh::lean_inc(v_a_1977_);
                    crate::leanh::lean_dec_ref_known(v___x_1976_, 1);
                    v___x_1978_ = crate::leanh::lean_box(0);
                    v___x_1987_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_1977_);
                    if v___x_1987_ == 0 {
                        crate::leanh::lean_dec(v_a_1977_);
                        v_a_1980_ = v_snd_1971_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_1977_);
                        v___x_1988_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_1977_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
                        if crate::leanh::lean_obj_tag(v___x_1988_) == 0 {
                            v_a_1989_ = crate::leanh::lean_ctor_get(v___x_1988_, 0);
                            crate::leanh::lean_inc(v_a_1989_);
                            crate::leanh::lean_dec_ref_known(v___x_1988_, 1);
                            v___x_1990_ = (crate::leanh::lean_unbox(v_a_1989_) as u8);
                            crate::leanh::lean_dec(v_a_1989_);
                            if v___x_1990_ == 0 {
                                crate::leanh::lean_dec(v_a_1977_);
                                v_a_1980_ = v_snd_1971_;
                                state = 2;
                                continue;
                            } else {
                                v_self_1991_ = crate::leanh::lean_ctor_get(v_a_1977_, 0);
                                crate::leanh::lean_inc_ref_n(v_self_1991_, 2);
                                crate::leanh::lean_dec(v_a_1977_);
                                v___x_1992_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                                    v_goal_1959_,
                                    v_self_1991_,
                                    v___y_1964_,
                                    v___y_1965_,
                                    v___y_1966_,
                                    v___y_1967_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_1992_) == 0 {
                                    v_a_1993_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                                    crate::leanh::lean_inc(v_a_1993_);
                                    crate::leanh::lean_dec_ref_known(v___x_1992_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_1993_) == 1 {
                                        v_val_1994_ = crate::leanh::lean_ctor_get(v_a_1993_, 0);
                                        crate::leanh::lean_inc(v_val_1994_);
                                        crate::leanh::lean_dec_ref_known(v_a_1993_, 1);
                                        v___x_1995_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                            v_goal_1959_,
                                            v_self_1991_,
                                            v_val_1994_,
                                            v_snd_1971_,
                                        );
                                        v_a_1980_ = v___x_1995_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_1993_);
                                        crate::leanh::lean_dec_ref(v_self_1991_);
                                        v_a_1980_ = v_snd_1971_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_self_1991_);
                                    crate::leanh::lean_del_object(v___x_1973_);
                                    crate::leanh::lean_dec(v_snd_1971_);
                                    v_a_1996_ = crate::leanh::lean_ctor_get(v___x_1992_, 0);
                                    v_isSharedCheck_2003_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_1992_)) as u8;
                                    if v_isSharedCheck_2003_ == 0 {
                                        v___x_1998_ = v___x_1992_;
                                        v_isShared_1999_ = v_isSharedCheck_2003_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_1996_);
                                        crate::leanh::lean_dec(v___x_1992_);
                                        v___x_1998_ = crate::leanh::lean_box(0);
                                        v_isShared_1999_ = v_isSharedCheck_2003_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_1977_);
                            crate::leanh::lean_del_object(v___x_1973_);
                            crate::leanh::lean_dec(v_snd_1971_);
                            v_a_2004_ = crate::leanh::lean_ctor_get(v___x_1988_, 0);
                            v_isSharedCheck_2011_ =
                                (!crate::leanh::lean_is_exclusive(v___x_1988_)) as u8;
                            if v_isSharedCheck_2011_ == 0 {
                                v___x_2006_ = v___x_1988_;
                                v_isShared_2007_ = v_isSharedCheck_2011_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2004_);
                                crate::leanh::lean_dec(v___x_1988_);
                                v___x_2006_ = crate::leanh::lean_box(0);
                                v_isShared_2007_ = v_isSharedCheck_2011_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_1973_);
                    crate::leanh::lean_dec(v_snd_1971_);
                    v_a_2012_ = crate::leanh::lean_ctor_get(v___x_1976_, 0);
                    v_isSharedCheck_2019_ = (!crate::leanh::lean_is_exclusive(v___x_1976_)) as u8;
                    if v_isSharedCheck_2019_ == 0 {
                        v___x_2014_ = v___x_1976_;
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2012_);
                        crate::leanh::lean_dec(v___x_1976_);
                        v___x_2014_ = crate::leanh::lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2019_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_1974_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_1973_, 1, v_a_1980_);
                    crate::leanh::lean_ctor_set(v___x_1973_, 0, v___x_1978_);
                    v___x_1982_ = v___x_1973_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1986_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 0, v___x_1978_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_1986_, 1, v_a_1980_);
                    v___x_1982_ = v_reuseFailAlloc_1986_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_1983_ = 1usize;
                v___x_1984_ = lean_usize_add(v_i_1962_, v___x_1983_);
                v___x_1985_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4_spec__6(v_goal_1959_, v_as_1960_, v_sz_1961_, v___x_1984_, v___x_1982_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_);
                return v___x_1985_;
            }
            4 => {
                if v_isShared_1999_ == 0 {
                    v___x_2001_ = v___x_1998_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2002_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2002_, 0, v_a_1996_);
                    v___x_2001_ = v_reuseFailAlloc_2002_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2001_;
            }
            6 => {
                if v_isShared_2007_ == 0 {
                    v___x_2009_ = v___x_2006_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2010_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2010_, 0, v_a_2004_);
                    v___x_2009_ = v_reuseFailAlloc_2010_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2009_;
            }
            8 => {
                if v_isShared_2015_ == 0 {
                    v___x_2017_ = v___x_2014_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2018_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2018_, 0, v_a_2012_);
                    v___x_2017_ = v_reuseFailAlloc_2018_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2017_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4___boxed(
    mut v_goal_2022_: *mut crate::leanh::LeanObject,
    mut v_as_2023_: *mut crate::leanh::LeanObject,
    mut v_sz_2024_: *mut crate::leanh::LeanObject,
    mut v_i_2025_: *mut crate::leanh::LeanObject,
    mut v_b_2026_: *mut crate::leanh::LeanObject,
    mut v___y_2027_: *mut crate::leanh::LeanObject,
    mut v___y_2028_: *mut crate::leanh::LeanObject,
    mut v___y_2029_: *mut crate::leanh::LeanObject,
    mut v___y_2030_: *mut crate::leanh::LeanObject,
    mut v___y_2031_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2032_: usize = 0;
    let mut v_i_boxed_2033_: usize = 0;
    let mut v_res_2034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2032_ = crate::leanh::lean_unbox_usize(v_sz_2024_);
    crate::leanh::lean_dec(v_sz_2024_);
    v_i_boxed_2033_ = crate::leanh::lean_unbox_usize(v_i_2025_);
    crate::leanh::lean_dec(v_i_2025_);
    v_res_2034_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_2022_, v_as_2023_, v_sz_boxed_2032_, v_i_boxed_2033_, v_b_2026_, v___y_2027_, v___y_2028_, v___y_2029_, v___y_2030_);
    crate::leanh::lean_dec(v___y_2030_);
    crate::leanh::lean_dec_ref(v___y_2029_);
    crate::leanh::lean_dec(v___y_2028_);
    crate::leanh::lean_dec_ref(v___y_2027_);
    crate::leanh::lean_dec_ref(v_as_2023_);
    crate::leanh::lean_dec_ref(v_goal_2022_);
    return v_res_2034_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(
    mut v_init_2035_: *mut crate::leanh::LeanObject,
    mut v_goal_2036_: *mut crate::leanh::LeanObject,
    mut v_n_2037_: *mut crate::leanh::LeanObject,
    mut v_b_2038_: *mut crate::leanh::LeanObject,
    mut v___y_2039_: *mut crate::leanh::LeanObject,
    mut v___y_2040_: *mut crate::leanh::LeanObject,
    mut v___y_2041_: *mut crate::leanh::LeanObject,
    mut v___y_2042_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2047_: usize = 0;
    let mut v___x_2048_: usize = 0;
    let mut v___x_2049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2053_: u8 = 0;
    let mut v_fst_2054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2063_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2064_: u8 = 0;
    let mut v_a_2065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2067_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2068_: u8 = 0;
    let mut v___x_2070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2071_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2072_: u8 = 0;
    let mut v_vs_2073_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2074_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2076_: usize = 0;
    let mut v___x_2077_: usize = 0;
    let mut v___x_2078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2079_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2082_: u8 = 0;
    let mut v_fst_2083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2093_: u8 = 0;
    let mut v_a_2094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2097_: u8 = 0;
    let mut v___x_2099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2101_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_2037_) == 0 {
                    v_cs_2044_ = crate::leanh::lean_ctor_get(v_n_2037_, 0);
                    v___x_2045_ = crate::leanh::lean_box(0);
                    v___x_2046_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2046_, 0, v___x_2045_);
                    crate::leanh::lean_ctor_set(v___x_2046_, 1, v_b_2038_);
                    v_sz_2047_ = lean_array_size(v_cs_2044_);
                    v___x_2048_ = 0usize;
                    v___x_2049_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_2035_, v_goal_2036_, v_cs_2044_, v_sz_2047_, v___x_2048_, v___x_2046_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                    if crate::leanh::lean_obj_tag(v___x_2049_) == 0 {
                        v_a_2050_ = crate::leanh::lean_ctor_get(v___x_2049_, 0);
                        v_isSharedCheck_2064_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2049_)) as u8;
                        if v_isSharedCheck_2064_ == 0 {
                            v___x_2052_ = v___x_2049_;
                            v_isShared_2053_ = v_isSharedCheck_2064_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2050_);
                            crate::leanh::lean_dec(v___x_2049_);
                            v___x_2052_ = crate::leanh::lean_box(0);
                            v_isShared_2053_ = v_isSharedCheck_2064_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2065_ = crate::leanh::lean_ctor_get(v___x_2049_, 0);
                        v_isSharedCheck_2072_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2049_)) as u8;
                        if v_isSharedCheck_2072_ == 0 {
                            v___x_2067_ = v___x_2049_;
                            v_isShared_2068_ = v_isSharedCheck_2072_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2065_);
                            crate::leanh::lean_dec(v___x_2049_);
                            v___x_2067_ = crate::leanh::lean_box(0);
                            v_isShared_2068_ = v_isSharedCheck_2072_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2073_ = crate::leanh::lean_ctor_get(v_n_2037_, 0);
                    v___x_2074_ = crate::leanh::lean_box(0);
                    v___x_2075_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2075_, 0, v___x_2074_);
                    crate::leanh::lean_ctor_set(v___x_2075_, 1, v_b_2038_);
                    v_sz_2076_ = lean_array_size(v_vs_2073_);
                    v___x_2077_ = 0usize;
                    v___x_2078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__4(v_goal_2036_, v_vs_2073_, v_sz_2076_, v___x_2077_, v___x_2075_, v___y_2039_, v___y_2040_, v___y_2041_, v___y_2042_);
                    if crate::leanh::lean_obj_tag(v___x_2078_) == 0 {
                        v_a_2079_ = crate::leanh::lean_ctor_get(v___x_2078_, 0);
                        v_isSharedCheck_2093_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2078_)) as u8;
                        if v_isSharedCheck_2093_ == 0 {
                            v___x_2081_ = v___x_2078_;
                            v_isShared_2082_ = v_isSharedCheck_2093_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2079_);
                            crate::leanh::lean_dec(v___x_2078_);
                            v___x_2081_ = crate::leanh::lean_box(0);
                            v_isShared_2082_ = v_isSharedCheck_2093_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2094_ = crate::leanh::lean_ctor_get(v___x_2078_, 0);
                        v_isSharedCheck_2101_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2078_)) as u8;
                        if v_isSharedCheck_2101_ == 0 {
                            v___x_2096_ = v___x_2078_;
                            v_isShared_2097_ = v_isSharedCheck_2101_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2094_);
                            crate::leanh::lean_dec(v___x_2078_);
                            v___x_2096_ = crate::leanh::lean_box(0);
                            v_isShared_2097_ = v_isSharedCheck_2101_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2054_ = crate::leanh::lean_ctor_get(v_a_2050_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2054_) == 0 {
                    v_snd_2055_ = crate::leanh::lean_ctor_get(v_a_2050_, 1);
                    crate::leanh::lean_inc(v_snd_2055_);
                    crate::leanh::lean_dec(v_a_2050_);
                    v___x_2056_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2056_, 0, v_snd_2055_);
                    if v_isShared_2053_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2052_, 0, v___x_2056_);
                        v___x_2058_ = v___x_2052_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2059_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2059_, 0, v___x_2056_);
                        v___x_2058_ = v_reuseFailAlloc_2059_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2054_);
                    crate::leanh::lean_dec(v_a_2050_);
                    v_val_2060_ = crate::leanh::lean_ctor_get(v_fst_2054_, 0);
                    crate::leanh::lean_inc(v_val_2060_);
                    crate::leanh::lean_dec_ref_known(v_fst_2054_, 1);
                    if v_isShared_2053_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2052_, 0, v_val_2060_);
                        v___x_2062_ = v___x_2052_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2063_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2063_, 0, v_val_2060_);
                        v___x_2062_ = v_reuseFailAlloc_2063_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2058_;
            }
            3 => {
                return v___x_2062_;
            }
            4 => {
                if v_isShared_2068_ == 0 {
                    v___x_2070_ = v___x_2067_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2071_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_a_2065_);
                    v___x_2070_ = v_reuseFailAlloc_2071_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2070_;
            }
            6 => {
                v_fst_2083_ = crate::leanh::lean_ctor_get(v_a_2079_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2083_) == 0 {
                    v_snd_2084_ = crate::leanh::lean_ctor_get(v_a_2079_, 1);
                    crate::leanh::lean_inc(v_snd_2084_);
                    crate::leanh::lean_dec(v_a_2079_);
                    v___x_2085_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2085_, 0, v_snd_2084_);
                    if v_isShared_2082_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2081_, 0, v___x_2085_);
                        v___x_2087_ = v___x_2081_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2088_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2088_, 0, v___x_2085_);
                        v___x_2087_ = v_reuseFailAlloc_2088_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2083_);
                    crate::leanh::lean_dec(v_a_2079_);
                    v_val_2089_ = crate::leanh::lean_ctor_get(v_fst_2083_, 0);
                    crate::leanh::lean_inc(v_val_2089_);
                    crate::leanh::lean_dec_ref_known(v_fst_2083_, 1);
                    if v_isShared_2082_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2081_, 0, v_val_2089_);
                        v___x_2091_ = v___x_2081_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2092_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2092_, 0, v_val_2089_);
                        v___x_2091_ = v_reuseFailAlloc_2092_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2087_;
            }
            8 => {
                return v___x_2091_;
            }
            9 => {
                if v_isShared_2097_ == 0 {
                    v___x_2099_ = v___x_2096_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2100_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2100_, 0, v_a_2094_);
                    v___x_2099_ = v_reuseFailAlloc_2100_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2099_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(
    mut v_init_2102_: *mut crate::leanh::LeanObject,
    mut v_goal_2103_: *mut crate::leanh::LeanObject,
    mut v_as_2104_: *mut crate::leanh::LeanObject,
    mut v_sz_2105_: usize,
    mut v_i_2106_: usize,
    mut v_b_2107_: *mut crate::leanh::LeanObject,
    mut v___y_2108_: *mut crate::leanh::LeanObject,
    mut v___y_2109_: *mut crate::leanh::LeanObject,
    mut v___y_2110_: *mut crate::leanh::LeanObject,
    mut v___y_2111_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2113_: u8 = 0;
    let mut v___x_2114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2118_: u8 = 0;
    let mut v_a_2119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2124_: u8 = 0;
    let mut v___x_2125_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2133_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2136_: usize = 0;
    let mut v___x_2137_: usize = 0;
    let mut v_reuseFailAlloc_2139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2140_: u8 = 0;
    let mut v_a_2141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v___x_2146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2148_: u8 = 0;
    let mut v_isSharedCheck_2149_: u8 = 0;
    let mut v_unused_2150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2113_ = lean_usize_dec_lt(v_i_2106_, v_sz_2105_);
                if v___x_2113_ == 0 {
                    v___x_2114_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2114_, 0, v_b_2107_);
                    return v___x_2114_;
                } else {
                    v_snd_2115_ = crate::leanh::lean_ctor_get(v_b_2107_, 1);
                    v_isSharedCheck_2149_ = (!crate::leanh::lean_is_exclusive(v_b_2107_)) as u8;
                    if v_isSharedCheck_2149_ == 0 {
                        v_unused_2150_ = crate::leanh::lean_ctor_get(v_b_2107_, 0);
                        crate::leanh::lean_dec(v_unused_2150_);
                        v___x_2117_ = v_b_2107_;
                        v_isShared_2118_ = v_isSharedCheck_2149_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2115_);
                        crate::leanh::lean_dec(v_b_2107_);
                        v___x_2117_ = crate::leanh::lean_box(0);
                        v_isShared_2118_ = v_isSharedCheck_2149_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2119_ = lean_array_uget_borrowed(v_as_2104_, v_i_2106_);
                crate::leanh::lean_inc(v_snd_2115_);
                v___x_2120_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_2102_, v_goal_2103_, v_a_2119_, v_snd_2115_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
                if crate::leanh::lean_obj_tag(v___x_2120_) == 0 {
                    v_a_2121_ = crate::leanh::lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2140_ = (!crate::leanh::lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2140_ == 0 {
                        v___x_2123_ = v___x_2120_;
                        v_isShared_2124_ = v_isSharedCheck_2140_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2121_);
                        crate::leanh::lean_dec(v___x_2120_);
                        v___x_2123_ = crate::leanh::lean_box(0);
                        v_isShared_2124_ = v_isSharedCheck_2140_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2117_);
                    crate::leanh::lean_dec(v_snd_2115_);
                    v_a_2141_ = crate::leanh::lean_ctor_get(v___x_2120_, 0);
                    v_isSharedCheck_2148_ = (!crate::leanh::lean_is_exclusive(v___x_2120_)) as u8;
                    if v_isSharedCheck_2148_ == 0 {
                        v___x_2143_ = v___x_2120_;
                        v_isShared_2144_ = v_isSharedCheck_2148_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2141_);
                        crate::leanh::lean_dec(v___x_2120_);
                        v___x_2143_ = crate::leanh::lean_box(0);
                        v_isShared_2144_ = v_isSharedCheck_2148_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2121_) == 0 {
                    v___x_2125_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2125_, 0, v_a_2121_);
                    if v_isShared_2118_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2117_, 0, v___x_2125_);
                        v___x_2127_ = v___x_2117_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 0, v___x_2125_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2131_, 1, v_snd_2115_);
                        v___x_2127_ = v_reuseFailAlloc_2131_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2123_);
                    crate::leanh::lean_dec(v_snd_2115_);
                    v_a_2132_ = crate::leanh::lean_ctor_get(v_a_2121_, 0);
                    crate::leanh::lean_inc(v_a_2132_);
                    crate::leanh::lean_dec_ref_known(v_a_2121_, 1);
                    v___x_2133_ = crate::leanh::lean_box(0);
                    if v_isShared_2118_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2117_, 1, v_a_2132_);
                        crate::leanh::lean_ctor_set(v___x_2117_, 0, v___x_2133_);
                        v___x_2135_ = v___x_2117_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2139_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 0, v___x_2133_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2139_, 1, v_a_2132_);
                        v___x_2135_ = v_reuseFailAlloc_2139_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2124_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2123_, 0, v___x_2127_);
                    v___x_2129_ = v___x_2123_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2130_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2130_, 0, v___x_2127_);
                    v___x_2129_ = v_reuseFailAlloc_2130_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2129_;
            }
            5 => {
                v___x_2136_ = 1usize;
                v___x_2137_ = lean_usize_add(v_i_2106_, v___x_2136_);
                v_i_2106_ = v___x_2137_;
                v_b_2107_ = v___x_2135_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2144_ == 0 {
                    v___x_2146_ = v___x_2143_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2147_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2147_, 0, v_a_2141_);
                    v___x_2146_ = v_reuseFailAlloc_2147_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2146_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3___boxed(
    mut v_init_2151_: *mut crate::leanh::LeanObject,
    mut v_goal_2152_: *mut crate::leanh::LeanObject,
    mut v_as_2153_: *mut crate::leanh::LeanObject,
    mut v_sz_2154_: *mut crate::leanh::LeanObject,
    mut v_i_2155_: *mut crate::leanh::LeanObject,
    mut v_b_2156_: *mut crate::leanh::LeanObject,
    mut v___y_2157_: *mut crate::leanh::LeanObject,
    mut v___y_2158_: *mut crate::leanh::LeanObject,
    mut v___y_2159_: *mut crate::leanh::LeanObject,
    mut v___y_2160_: *mut crate::leanh::LeanObject,
    mut v___y_2161_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2162_: usize = 0;
    let mut v_i_boxed_2163_: usize = 0;
    let mut v_res_2164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2162_ = crate::leanh::lean_unbox_usize(v_sz_2154_);
    crate::leanh::lean_dec(v_sz_2154_);
    v_i_boxed_2163_ = crate::leanh::lean_unbox_usize(v_i_2155_);
    crate::leanh::lean_dec(v_i_2155_);
    v_res_2164_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2_spec__3(v_init_2151_, v_goal_2152_, v_as_2153_, v_sz_boxed_2162_, v_i_boxed_2163_, v_b_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
    crate::leanh::lean_dec(v___y_2160_);
    crate::leanh::lean_dec_ref(v___y_2159_);
    crate::leanh::lean_dec(v___y_2158_);
    crate::leanh::lean_dec_ref(v___y_2157_);
    crate::leanh::lean_dec_ref(v_as_2153_);
    crate::leanh::lean_dec_ref(v_goal_2152_);
    crate::leanh::lean_dec_ref(v_init_2151_);
    return v_res_2164_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2___boxed(
    mut v_init_2165_: *mut crate::leanh::LeanObject,
    mut v_goal_2166_: *mut crate::leanh::LeanObject,
    mut v_n_2167_: *mut crate::leanh::LeanObject,
    mut v_b_2168_: *mut crate::leanh::LeanObject,
    mut v___y_2169_: *mut crate::leanh::LeanObject,
    mut v___y_2170_: *mut crate::leanh::LeanObject,
    mut v___y_2171_: *mut crate::leanh::LeanObject,
    mut v___y_2172_: *mut crate::leanh::LeanObject,
    mut v___y_2173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2174_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_2165_, v_goal_2166_, v_n_2167_, v_b_2168_, v___y_2169_, v___y_2170_, v___y_2171_, v___y_2172_);
    crate::leanh::lean_dec(v___y_2172_);
    crate::leanh::lean_dec_ref(v___y_2171_);
    crate::leanh::lean_dec(v___y_2170_);
    crate::leanh::lean_dec_ref(v___y_2169_);
    crate::leanh::lean_dec_ref(v_n_2167_);
    crate::leanh::lean_dec_ref(v_goal_2166_);
    crate::leanh::lean_dec_ref(v_init_2165_);
    return v_res_2174_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(
    mut v_goal_2175_: *mut crate::leanh::LeanObject,
    mut v_as_2176_: *mut crate::leanh::LeanObject,
    mut v_sz_2177_: usize,
    mut v_i_2178_: usize,
    mut v_b_2179_: *mut crate::leanh::LeanObject,
    mut v___y_2180_: *mut crate::leanh::LeanObject,
    mut v___y_2181_: *mut crate::leanh::LeanObject,
    mut v___y_2182_: *mut crate::leanh::LeanObject,
    mut v___y_2183_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2185_: u8 = 0;
    let mut v___x_2186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2190_: u8 = 0;
    let mut v_a_2191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2196_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2198_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2199_: usize = 0;
    let mut v___x_2200_: usize = 0;
    let mut v_reuseFailAlloc_2202_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2203_: u8 = 0;
    let mut v___x_2204_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2206_: u8 = 0;
    let mut v_self_2207_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2210_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2214_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2215_: u8 = 0;
    let mut v___x_2217_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2218_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2219_: u8 = 0;
    let mut v_a_2220_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2222_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2223_: u8 = 0;
    let mut v___x_2225_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2227_: u8 = 0;
    let mut v_a_2228_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2230_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2231_: u8 = 0;
    let mut v___x_2233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2235_: u8 = 0;
    let mut v_isSharedCheck_2236_: u8 = 0;
    let mut v_unused_2237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2185_ = lean_usize_dec_lt(v_i_2178_, v_sz_2177_);
                if v___x_2185_ == 0 {
                    v___x_2186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2186_, 0, v_b_2179_);
                    return v___x_2186_;
                } else {
                    v_snd_2187_ = crate::leanh::lean_ctor_get(v_b_2179_, 1);
                    v_isSharedCheck_2236_ = (!crate::leanh::lean_is_exclusive(v_b_2179_)) as u8;
                    if v_isSharedCheck_2236_ == 0 {
                        v_unused_2237_ = crate::leanh::lean_ctor_get(v_b_2179_, 0);
                        crate::leanh::lean_dec(v_unused_2237_);
                        v___x_2189_ = v_b_2179_;
                        v_isShared_2190_ = v_isSharedCheck_2236_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2187_);
                        crate::leanh::lean_dec(v_b_2179_);
                        v___x_2189_ = crate::leanh::lean_box(0);
                        v_isShared_2190_ = v_isSharedCheck_2236_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2191_ = lean_array_uget_borrowed(v_as_2176_, v_i_2178_);
                crate::leanh::lean_inc(v_a_2191_);
                v___x_2192_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2175_,
                    v_a_2191_,
                    v___y_2180_,
                    v___y_2181_,
                    v___y_2182_,
                    v___y_2183_,
                );
                if crate::leanh::lean_obj_tag(v___x_2192_) == 0 {
                    v_a_2193_ = crate::leanh::lean_ctor_get(v___x_2192_, 0);
                    crate::leanh::lean_inc(v_a_2193_);
                    crate::leanh::lean_dec_ref_known(v___x_2192_, 1);
                    v___x_2194_ = crate::leanh::lean_box(0);
                    v___x_2203_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2193_);
                    if v___x_2203_ == 0 {
                        crate::leanh::lean_dec(v_a_2193_);
                        v_a_2196_ = v_snd_2187_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2193_);
                        v___x_2204_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_2193_, v___y_2180_, v___y_2181_, v___y_2182_, v___y_2183_);
                        if crate::leanh::lean_obj_tag(v___x_2204_) == 0 {
                            v_a_2205_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
                            crate::leanh::lean_inc(v_a_2205_);
                            crate::leanh::lean_dec_ref_known(v___x_2204_, 1);
                            v___x_2206_ = (crate::leanh::lean_unbox(v_a_2205_) as u8);
                            crate::leanh::lean_dec(v_a_2205_);
                            if v___x_2206_ == 0 {
                                crate::leanh::lean_dec(v_a_2193_);
                                v_a_2196_ = v_snd_2187_;
                                state = 2;
                                continue;
                            } else {
                                v_self_2207_ = crate::leanh::lean_ctor_get(v_a_2193_, 0);
                                crate::leanh::lean_inc_ref_n(v_self_2207_, 2);
                                crate::leanh::lean_dec(v_a_2193_);
                                v___x_2208_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                                    v_goal_2175_,
                                    v_self_2207_,
                                    v___y_2180_,
                                    v___y_2181_,
                                    v___y_2182_,
                                    v___y_2183_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2208_) == 0 {
                                    v_a_2209_ = crate::leanh::lean_ctor_get(v___x_2208_, 0);
                                    crate::leanh::lean_inc(v_a_2209_);
                                    crate::leanh::lean_dec_ref_known(v___x_2208_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_2209_) == 1 {
                                        v_val_2210_ = crate::leanh::lean_ctor_get(v_a_2209_, 0);
                                        crate::leanh::lean_inc(v_val_2210_);
                                        crate::leanh::lean_dec_ref_known(v_a_2209_, 1);
                                        v___x_2211_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                            v_goal_2175_,
                                            v_self_2207_,
                                            v_val_2210_,
                                            v_snd_2187_,
                                        );
                                        v_a_2196_ = v___x_2211_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_2209_);
                                        crate::leanh::lean_dec_ref(v_self_2207_);
                                        v_a_2196_ = v_snd_2187_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_self_2207_);
                                    crate::leanh::lean_del_object(v___x_2189_);
                                    crate::leanh::lean_dec(v_snd_2187_);
                                    v_a_2212_ = crate::leanh::lean_ctor_get(v___x_2208_, 0);
                                    v_isSharedCheck_2219_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2208_)) as u8;
                                    if v_isSharedCheck_2219_ == 0 {
                                        v___x_2214_ = v___x_2208_;
                                        v_isShared_2215_ = v_isSharedCheck_2219_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2212_);
                                        crate::leanh::lean_dec(v___x_2208_);
                                        v___x_2214_ = crate::leanh::lean_box(0);
                                        v_isShared_2215_ = v_isSharedCheck_2219_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2193_);
                            crate::leanh::lean_del_object(v___x_2189_);
                            crate::leanh::lean_dec(v_snd_2187_);
                            v_a_2220_ = crate::leanh::lean_ctor_get(v___x_2204_, 0);
                            v_isSharedCheck_2227_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2204_)) as u8;
                            if v_isSharedCheck_2227_ == 0 {
                                v___x_2222_ = v___x_2204_;
                                v_isShared_2223_ = v_isSharedCheck_2227_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2220_);
                                crate::leanh::lean_dec(v___x_2204_);
                                v___x_2222_ = crate::leanh::lean_box(0);
                                v_isShared_2223_ = v_isSharedCheck_2227_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2189_);
                    crate::leanh::lean_dec(v_snd_2187_);
                    v_a_2228_ = crate::leanh::lean_ctor_get(v___x_2192_, 0);
                    v_isSharedCheck_2235_ = (!crate::leanh::lean_is_exclusive(v___x_2192_)) as u8;
                    if v_isSharedCheck_2235_ == 0 {
                        v___x_2230_ = v___x_2192_;
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2228_);
                        crate::leanh::lean_dec(v___x_2192_);
                        v___x_2230_ = crate::leanh::lean_box(0);
                        v_isShared_2231_ = v_isSharedCheck_2235_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2190_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2189_, 1, v_a_2196_);
                    crate::leanh::lean_ctor_set(v___x_2189_, 0, v___x_2194_);
                    v___x_2198_ = v___x_2189_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2202_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2194_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_a_2196_);
                    v___x_2198_ = v_reuseFailAlloc_2202_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2199_ = 1usize;
                v___x_2200_ = lean_usize_add(v_i_2178_, v___x_2199_);
                v_i_2178_ = v___x_2200_;
                v_b_2179_ = v___x_2198_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2215_ == 0 {
                    v___x_2217_ = v___x_2214_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2218_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2218_, 0, v_a_2212_);
                    v___x_2217_ = v_reuseFailAlloc_2218_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2217_;
            }
            6 => {
                if v_isShared_2223_ == 0 {
                    v___x_2225_ = v___x_2222_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2226_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2226_, 0, v_a_2220_);
                    v___x_2225_ = v_reuseFailAlloc_2226_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2225_;
            }
            8 => {
                if v_isShared_2231_ == 0 {
                    v___x_2233_ = v___x_2230_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2234_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2234_, 0, v_a_2228_);
                    v___x_2233_ = v_reuseFailAlloc_2234_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2233_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6___boxed(
    mut v_goal_2238_: *mut crate::leanh::LeanObject,
    mut v_as_2239_: *mut crate::leanh::LeanObject,
    mut v_sz_2240_: *mut crate::leanh::LeanObject,
    mut v_i_2241_: *mut crate::leanh::LeanObject,
    mut v_b_2242_: *mut crate::leanh::LeanObject,
    mut v___y_2243_: *mut crate::leanh::LeanObject,
    mut v___y_2244_: *mut crate::leanh::LeanObject,
    mut v___y_2245_: *mut crate::leanh::LeanObject,
    mut v___y_2246_: *mut crate::leanh::LeanObject,
    mut v___y_2247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2248_: usize = 0;
    let mut v_i_boxed_2249_: usize = 0;
    let mut v_res_2250_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2248_ = crate::leanh::lean_unbox_usize(v_sz_2240_);
    crate::leanh::lean_dec(v_sz_2240_);
    v_i_boxed_2249_ = crate::leanh::lean_unbox_usize(v_i_2241_);
    crate::leanh::lean_dec(v_i_2241_);
    v_res_2250_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_2238_, v_as_2239_, v_sz_boxed_2248_, v_i_boxed_2249_, v_b_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_);
    crate::leanh::lean_dec(v___y_2246_);
    crate::leanh::lean_dec_ref(v___y_2245_);
    crate::leanh::lean_dec(v___y_2244_);
    crate::leanh::lean_dec_ref(v___y_2243_);
    crate::leanh::lean_dec_ref(v_as_2239_);
    crate::leanh::lean_dec_ref(v_goal_2238_);
    return v_res_2250_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(
    mut v_goal_2251_: *mut crate::leanh::LeanObject,
    mut v_as_2252_: *mut crate::leanh::LeanObject,
    mut v_sz_2253_: usize,
    mut v_i_2254_: usize,
    mut v_b_2255_: *mut crate::leanh::LeanObject,
    mut v___y_2256_: *mut crate::leanh::LeanObject,
    mut v___y_2257_: *mut crate::leanh::LeanObject,
    mut v___y_2258_: *mut crate::leanh::LeanObject,
    mut v___y_2259_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2261_: u8 = 0;
    let mut v___x_2262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2266_: u8 = 0;
    let mut v_a_2267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2269_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2275_: usize = 0;
    let mut v___x_2276_: usize = 0;
    let mut v___x_2277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2279_: u8 = 0;
    let mut v___x_2280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2282_: u8 = 0;
    let mut v_self_2283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2291_: u8 = 0;
    let mut v___x_2293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2295_: u8 = 0;
    let mut v_a_2296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2298_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2299_: u8 = 0;
    let mut v___x_2301_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2302_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2303_: u8 = 0;
    let mut v_a_2304_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2306_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2307_: u8 = 0;
    let mut v___x_2309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2310_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2311_: u8 = 0;
    let mut v_isSharedCheck_2312_: u8 = 0;
    let mut v_unused_2313_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2261_ = lean_usize_dec_lt(v_i_2254_, v_sz_2253_);
                if v___x_2261_ == 0 {
                    v___x_2262_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2262_, 0, v_b_2255_);
                    return v___x_2262_;
                } else {
                    v_snd_2263_ = crate::leanh::lean_ctor_get(v_b_2255_, 1);
                    v_isSharedCheck_2312_ = (!crate::leanh::lean_is_exclusive(v_b_2255_)) as u8;
                    if v_isSharedCheck_2312_ == 0 {
                        v_unused_2313_ = crate::leanh::lean_ctor_get(v_b_2255_, 0);
                        crate::leanh::lean_dec(v_unused_2313_);
                        v___x_2265_ = v_b_2255_;
                        v_isShared_2266_ = v_isSharedCheck_2312_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2263_);
                        crate::leanh::lean_dec(v_b_2255_);
                        v___x_2265_ = crate::leanh::lean_box(0);
                        v_isShared_2266_ = v_isSharedCheck_2312_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2267_ = lean_array_uget_borrowed(v_as_2252_, v_i_2254_);
                crate::leanh::lean_inc(v_a_2267_);
                v___x_2268_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2251_,
                    v_a_2267_,
                    v___y_2256_,
                    v___y_2257_,
                    v___y_2258_,
                    v___y_2259_,
                );
                if crate::leanh::lean_obj_tag(v___x_2268_) == 0 {
                    v_a_2269_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
                    crate::leanh::lean_inc(v_a_2269_);
                    crate::leanh::lean_dec_ref_known(v___x_2268_, 1);
                    v___x_2270_ = crate::leanh::lean_box(0);
                    v___x_2279_ = l_Lean_Meta_Grind_ENode_isRoot(v_a_2269_);
                    if v___x_2279_ == 0 {
                        crate::leanh::lean_dec(v_a_2269_);
                        v_a_2272_ = v_snd_2263_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2269_);
                        v___x_2280_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_isIntNatENode(v_a_2269_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
                        if crate::leanh::lean_obj_tag(v___x_2280_) == 0 {
                            v_a_2281_ = crate::leanh::lean_ctor_get(v___x_2280_, 0);
                            crate::leanh::lean_inc(v_a_2281_);
                            crate::leanh::lean_dec_ref_known(v___x_2280_, 1);
                            v___x_2282_ = (crate::leanh::lean_unbox(v_a_2281_) as u8);
                            crate::leanh::lean_dec(v_a_2281_);
                            if v___x_2282_ == 0 {
                                crate::leanh::lean_dec(v_a_2269_);
                                v_a_2272_ = v_snd_2263_;
                                state = 2;
                                continue;
                            } else {
                                v_self_2283_ = crate::leanh::lean_ctor_get(v_a_2269_, 0);
                                crate::leanh::lean_inc_ref_n(v_self_2283_, 2);
                                crate::leanh::lean_dec(v_a_2269_);
                                v___x_2284_ = l_Lean_Meta_Grind_Arith_Cutsat_getAssignment_x3f(
                                    v_goal_2251_,
                                    v_self_2283_,
                                    v___y_2256_,
                                    v___y_2257_,
                                    v___y_2258_,
                                    v___y_2259_,
                                );
                                if crate::leanh::lean_obj_tag(v___x_2284_) == 0 {
                                    v_a_2285_ = crate::leanh::lean_ctor_get(v___x_2284_, 0);
                                    crate::leanh::lean_inc(v_a_2285_);
                                    crate::leanh::lean_dec_ref_known(v___x_2284_, 1);
                                    if crate::leanh::lean_obj_tag(v_a_2285_) == 1 {
                                        v_val_2286_ = crate::leanh::lean_ctor_get(v_a_2285_, 0);
                                        crate::leanh::lean_inc(v_val_2286_);
                                        crate::leanh::lean_dec_ref_known(v_a_2285_, 1);
                                        v___x_2287_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                            v_goal_2251_,
                                            v_self_2283_,
                                            v_val_2286_,
                                            v_snd_2263_,
                                        );
                                        v_a_2272_ = v___x_2287_;
                                        state = 2;
                                        continue;
                                    } else {
                                        crate::leanh::lean_dec(v_a_2285_);
                                        crate::leanh::lean_dec_ref(v_self_2283_);
                                        v_a_2272_ = v_snd_2263_;
                                        state = 2;
                                        continue;
                                    }
                                } else {
                                    crate::leanh::lean_dec_ref(v_self_2283_);
                                    crate::leanh::lean_del_object(v___x_2265_);
                                    crate::leanh::lean_dec(v_snd_2263_);
                                    v_a_2288_ = crate::leanh::lean_ctor_get(v___x_2284_, 0);
                                    v_isSharedCheck_2295_ =
                                        (!crate::leanh::lean_is_exclusive(v___x_2284_)) as u8;
                                    if v_isSharedCheck_2295_ == 0 {
                                        v___x_2290_ = v___x_2284_;
                                        v_isShared_2291_ = v_isSharedCheck_2295_;
                                        state = 4;
                                        continue;
                                    } else {
                                        crate::leanh::lean_inc(v_a_2288_);
                                        crate::leanh::lean_dec(v___x_2284_);
                                        v___x_2290_ = crate::leanh::lean_box(0);
                                        v_isShared_2291_ = v_isSharedCheck_2295_;
                                        state = 4;
                                        continue;
                                    }
                                }
                            }
                        } else {
                            crate::leanh::lean_dec(v_a_2269_);
                            crate::leanh::lean_del_object(v___x_2265_);
                            crate::leanh::lean_dec(v_snd_2263_);
                            v_a_2296_ = crate::leanh::lean_ctor_get(v___x_2280_, 0);
                            v_isSharedCheck_2303_ =
                                (!crate::leanh::lean_is_exclusive(v___x_2280_)) as u8;
                            if v_isSharedCheck_2303_ == 0 {
                                v___x_2298_ = v___x_2280_;
                                v_isShared_2299_ = v_isSharedCheck_2303_;
                                state = 6;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_2296_);
                                crate::leanh::lean_dec(v___x_2280_);
                                v___x_2298_ = crate::leanh::lean_box(0);
                                v_isShared_2299_ = v_isSharedCheck_2303_;
                                state = 6;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2265_);
                    crate::leanh::lean_dec(v_snd_2263_);
                    v_a_2304_ = crate::leanh::lean_ctor_get(v___x_2268_, 0);
                    v_isSharedCheck_2311_ = (!crate::leanh::lean_is_exclusive(v___x_2268_)) as u8;
                    if v_isSharedCheck_2311_ == 0 {
                        v___x_2306_ = v___x_2268_;
                        v_isShared_2307_ = v_isSharedCheck_2311_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2304_);
                        crate::leanh::lean_dec(v___x_2268_);
                        v___x_2306_ = crate::leanh::lean_box(0);
                        v_isShared_2307_ = v_isSharedCheck_2311_;
                        state = 8;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2266_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2265_, 1, v_a_2272_);
                    crate::leanh::lean_ctor_set(v___x_2265_, 0, v___x_2270_);
                    v___x_2274_ = v___x_2265_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2278_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 0, v___x_2270_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2278_, 1, v_a_2272_);
                    v___x_2274_ = v_reuseFailAlloc_2278_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2275_ = 1usize;
                v___x_2276_ = lean_usize_add(v_i_2254_, v___x_2275_);
                v___x_2277_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3_spec__6(v_goal_2251_, v_as_2252_, v_sz_2253_, v___x_2276_, v___x_2274_, v___y_2256_, v___y_2257_, v___y_2258_, v___y_2259_);
                return v___x_2277_;
            }
            4 => {
                if v_isShared_2291_ == 0 {
                    v___x_2293_ = v___x_2290_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2294_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
                    v___x_2293_ = v_reuseFailAlloc_2294_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2293_;
            }
            6 => {
                if v_isShared_2299_ == 0 {
                    v___x_2301_ = v___x_2298_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2302_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
                    v___x_2301_ = v_reuseFailAlloc_2302_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2301_;
            }
            8 => {
                if v_isShared_2307_ == 0 {
                    v___x_2309_ = v___x_2306_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2310_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2310_, 0, v_a_2304_);
                    v___x_2309_ = v_reuseFailAlloc_2310_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2309_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3___boxed(
    mut v_goal_2314_: *mut crate::leanh::LeanObject,
    mut v_as_2315_: *mut crate::leanh::LeanObject,
    mut v_sz_2316_: *mut crate::leanh::LeanObject,
    mut v_i_2317_: *mut crate::leanh::LeanObject,
    mut v_b_2318_: *mut crate::leanh::LeanObject,
    mut v___y_2319_: *mut crate::leanh::LeanObject,
    mut v___y_2320_: *mut crate::leanh::LeanObject,
    mut v___y_2321_: *mut crate::leanh::LeanObject,
    mut v___y_2322_: *mut crate::leanh::LeanObject,
    mut v___y_2323_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2324_: usize = 0;
    let mut v_i_boxed_2325_: usize = 0;
    let mut v_res_2326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2324_ = crate::leanh::lean_unbox_usize(v_sz_2316_);
    crate::leanh::lean_dec(v_sz_2316_);
    v_i_boxed_2325_ = crate::leanh::lean_unbox_usize(v_i_2317_);
    crate::leanh::lean_dec(v_i_2317_);
    v_res_2326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_2314_, v_as_2315_, v_sz_boxed_2324_, v_i_boxed_2325_, v_b_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_);
    crate::leanh::lean_dec(v___y_2322_);
    crate::leanh::lean_dec_ref(v___y_2321_);
    crate::leanh::lean_dec(v___y_2320_);
    crate::leanh::lean_dec_ref(v___y_2319_);
    crate::leanh::lean_dec_ref(v_as_2315_);
    crate::leanh::lean_dec_ref(v_goal_2314_);
    return v_res_2326_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(
    mut v_goal_2327_: *mut crate::leanh::LeanObject,
    mut v_t_2328_: *mut crate::leanh::LeanObject,
    mut v_init_2329_: *mut crate::leanh::LeanObject,
    mut v___y_2330_: *mut crate::leanh::LeanObject,
    mut v___y_2331_: *mut crate::leanh::LeanObject,
    mut v___y_2332_: *mut crate::leanh::LeanObject,
    mut v___y_2333_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2341_: u8 = 0;
    let mut v_a_2342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2349_: usize = 0;
    let mut v___x_2350_: usize = 0;
    let mut v___x_2351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2352_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2355_: u8 = 0;
    let mut v_fst_2356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2357_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2359_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2361_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2364_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2365_: u8 = 0;
    let mut v_a_2366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2369_: u8 = 0;
    let mut v___x_2371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2373_: u8 = 0;
    let mut v_isSharedCheck_2374_: u8 = 0;
    let mut v_a_2375_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2377_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2378_: u8 = 0;
    let mut v___x_2380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2381_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2382_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2335_ = crate::leanh::lean_ctor_get(v_t_2328_, 0);
                v_tail_2336_ = crate::leanh::lean_ctor_get(v_t_2328_, 1);
                crate::leanh::lean_inc_ref(v_init_2329_);
                v___x_2337_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__2(v_init_2329_, v_goal_2327_, v_root_2335_, v_init_2329_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
                crate::leanh::lean_dec_ref(v_init_2329_);
                if crate::leanh::lean_obj_tag(v___x_2337_) == 0 {
                    v_a_2338_ = crate::leanh::lean_ctor_get(v___x_2337_, 0);
                    v_isSharedCheck_2374_ = (!crate::leanh::lean_is_exclusive(v___x_2337_)) as u8;
                    if v_isSharedCheck_2374_ == 0 {
                        v___x_2340_ = v___x_2337_;
                        v_isShared_2341_ = v_isSharedCheck_2374_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2338_);
                        crate::leanh::lean_dec(v___x_2337_);
                        v___x_2340_ = crate::leanh::lean_box(0);
                        v_isShared_2341_ = v_isSharedCheck_2374_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2375_ = crate::leanh::lean_ctor_get(v___x_2337_, 0);
                    v_isSharedCheck_2382_ = (!crate::leanh::lean_is_exclusive(v___x_2337_)) as u8;
                    if v_isSharedCheck_2382_ == 0 {
                        v___x_2377_ = v___x_2337_;
                        v_isShared_2378_ = v_isSharedCheck_2382_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2375_);
                        crate::leanh::lean_dec(v___x_2337_);
                        v___x_2377_ = crate::leanh::lean_box(0);
                        v_isShared_2378_ = v_isSharedCheck_2382_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2338_) == 0 {
                    v_a_2342_ = crate::leanh::lean_ctor_get(v_a_2338_, 0);
                    crate::leanh::lean_inc(v_a_2342_);
                    crate::leanh::lean_dec_ref_known(v_a_2338_, 1);
                    if v_isShared_2341_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2340_, 0, v_a_2342_);
                        v___x_2344_ = v___x_2340_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2345_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2345_, 0, v_a_2342_);
                        v___x_2344_ = v_reuseFailAlloc_2345_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2340_);
                    v_a_2346_ = crate::leanh::lean_ctor_get(v_a_2338_, 0);
                    crate::leanh::lean_inc(v_a_2346_);
                    crate::leanh::lean_dec_ref_known(v_a_2338_, 1);
                    v___x_2347_ = crate::leanh::lean_box(0);
                    v___x_2348_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2348_, 0, v___x_2347_);
                    crate::leanh::lean_ctor_set(v___x_2348_, 1, v_a_2346_);
                    v_sz_2349_ = lean_array_size(v_tail_2336_);
                    v___x_2350_ = 0usize;
                    v___x_2351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1_spec__3(v_goal_2327_, v_tail_2336_, v_sz_2349_, v___x_2350_, v___x_2348_, v___y_2330_, v___y_2331_, v___y_2332_, v___y_2333_);
                    if crate::leanh::lean_obj_tag(v___x_2351_) == 0 {
                        v_a_2352_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                        v_isSharedCheck_2365_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                        if v_isSharedCheck_2365_ == 0 {
                            v___x_2354_ = v___x_2351_;
                            v_isShared_2355_ = v_isSharedCheck_2365_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2352_);
                            crate::leanh::lean_dec(v___x_2351_);
                            v___x_2354_ = crate::leanh::lean_box(0);
                            v_isShared_2355_ = v_isSharedCheck_2365_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2366_ = crate::leanh::lean_ctor_get(v___x_2351_, 0);
                        v_isSharedCheck_2373_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2351_)) as u8;
                        if v_isSharedCheck_2373_ == 0 {
                            v___x_2368_ = v___x_2351_;
                            v_isShared_2369_ = v_isSharedCheck_2373_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2366_);
                            crate::leanh::lean_dec(v___x_2351_);
                            v___x_2368_ = crate::leanh::lean_box(0);
                            v_isShared_2369_ = v_isSharedCheck_2373_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2344_;
            }
            3 => {
                v_fst_2356_ = crate::leanh::lean_ctor_get(v_a_2352_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2356_) == 0 {
                    v_snd_2357_ = crate::leanh::lean_ctor_get(v_a_2352_, 1);
                    crate::leanh::lean_inc(v_snd_2357_);
                    crate::leanh::lean_dec(v_a_2352_);
                    if v_isShared_2355_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2354_, 0, v_snd_2357_);
                        v___x_2359_ = v___x_2354_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2360_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_snd_2357_);
                        v___x_2359_ = v_reuseFailAlloc_2360_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2356_);
                    crate::leanh::lean_dec(v_a_2352_);
                    v_val_2361_ = crate::leanh::lean_ctor_get(v_fst_2356_, 0);
                    crate::leanh::lean_inc(v_val_2361_);
                    crate::leanh::lean_dec_ref_known(v_fst_2356_, 1);
                    if v_isShared_2355_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2354_, 0, v_val_2361_);
                        v___x_2363_ = v___x_2354_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2364_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_val_2361_);
                        v___x_2363_ = v_reuseFailAlloc_2364_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2359_;
            }
            5 => {
                return v___x_2363_;
            }
            6 => {
                if v_isShared_2369_ == 0 {
                    v___x_2371_ = v___x_2368_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2372_, 0, v_a_2366_);
                    v___x_2371_ = v_reuseFailAlloc_2372_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2371_;
            }
            8 => {
                if v_isShared_2378_ == 0 {
                    v___x_2380_ = v___x_2377_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2381_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
                    v___x_2380_ = v_reuseFailAlloc_2381_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2380_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1___boxed(
    mut v_goal_2383_: *mut crate::leanh::LeanObject,
    mut v_t_2384_: *mut crate::leanh::LeanObject,
    mut v_init_2385_: *mut crate::leanh::LeanObject,
    mut v___y_2386_: *mut crate::leanh::LeanObject,
    mut v___y_2387_: *mut crate::leanh::LeanObject,
    mut v___y_2388_: *mut crate::leanh::LeanObject,
    mut v___y_2389_: *mut crate::leanh::LeanObject,
    mut v___y_2390_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2391_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2391_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(
            v_goal_2383_,
            v_t_2384_,
            v_init_2385_,
            v___y_2386_,
            v___y_2387_,
            v___y_2388_,
            v___y_2389_,
        );
    crate::leanh::lean_dec(v___y_2389_);
    crate::leanh::lean_dec_ref(v___y_2388_);
    crate::leanh::lean_dec(v___y_2387_);
    crate::leanh::lean_dec_ref(v___y_2386_);
    crate::leanh::lean_dec_ref(v_t_2384_);
    crate::leanh::lean_dec_ref(v_goal_2383_);
    return v_res_2391_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(
    mut v_a_2392_: *mut crate::leanh::LeanObject,
    mut v_x_2393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_2395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_value_2396_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2397_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2398_: u8 = 0;
    let mut v___x_2400_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_2393_) == 0 {
                    v___x_2394_ = crate::leanh::lean_box(0);
                    return v___x_2394_;
                } else {
                    v_key_2395_ = crate::leanh::lean_ctor_get(v_x_2393_, 0);
                    v_value_2396_ = crate::leanh::lean_ctor_get(v_x_2393_, 1);
                    v_tail_2397_ = crate::leanh::lean_ctor_get(v_x_2393_, 2);
                    v___x_2398_ = lean_expr_eqv(v_key_2395_, v_a_2392_);
                    if v___x_2398_ == 0 {
                        v_x_2393_ = v_tail_2397_;
                        state = 0;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_value_2396_);
                        v___x_2400_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_2400_, 0, v_value_2396_);
                        return v___x_2400_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg___boxed(
    mut v_a_2401_: *mut crate::leanh::LeanObject,
    mut v_x_2402_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2403_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2403_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_2401_, v_x_2402_);
    crate::leanh::lean_dec(v_x_2402_);
    crate::leanh::lean_dec_ref(v_a_2401_);
    return v_res_2403_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(
    mut v_m_2404_: *mut crate::leanh::LeanObject,
    mut v_a_2405_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_buckets_2406_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2407_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2408_: u64 = 0;
    let mut v___x_2409_: u64 = 0;
    let mut v___x_2410_: u64 = 0;
    let mut v_fold_2411_: u64 = 0;
    let mut v___x_2412_: u64 = 0;
    let mut v___x_2413_: u64 = 0;
    let mut v___x_2414_: u64 = 0;
    let mut v___x_2415_: usize = 0;
    let mut v___x_2416_: usize = 0;
    let mut v___x_2417_: usize = 0;
    let mut v___x_2418_: usize = 0;
    let mut v___x_2419_: usize = 0;
    let mut v___x_2420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_buckets_2406_ = crate::leanh::lean_ctor_get(v_m_2404_, 1);
    v___x_2407_ = lean_array_get_size(v_buckets_2406_);
    v___x_2408_ = l_Lean_Expr_hash(v_a_2405_);
    v___x_2409_ = 32u64;
    v___x_2410_ = lean_uint64_shift_right(v___x_2408_, v___x_2409_);
    v_fold_2411_ = lean_uint64_xor(v___x_2408_, v___x_2410_);
    v___x_2412_ = 16u64;
    v___x_2413_ = lean_uint64_shift_right(v_fold_2411_, v___x_2412_);
    v___x_2414_ = lean_uint64_xor(v_fold_2411_, v___x_2413_);
    v___x_2415_ = lean_uint64_to_usize(v___x_2414_);
    v___x_2416_ = lean_usize_of_nat(v___x_2407_);
    v___x_2417_ = 1usize;
    v___x_2418_ = lean_usize_sub(v___x_2416_, v___x_2417_);
    v___x_2419_ = lean_usize_land(v___x_2415_, v___x_2418_);
    v___x_2420_ = lean_array_uget_borrowed(v_buckets_2406_, v___x_2419_);
    v___x_2421_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_2405_, v___x_2420_);
    return v___x_2421_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg___boxed(
    mut v_m_2422_: *mut crate::leanh::LeanObject,
    mut v_a_2423_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2424_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2424_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_2422_, v_a_2423_);
    crate::leanh::lean_dec_ref(v_a_2423_);
    crate::leanh::lean_dec_ref(v_m_2422_);
    return v_res_2424_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(
    mut v_goal_2425_: *mut crate::leanh::LeanObject,
    mut v_as_2426_: *mut crate::leanh::LeanObject,
    mut v_sz_2427_: usize,
    mut v_i_2428_: usize,
    mut v_b_2429_: *mut crate::leanh::LeanObject,
    mut v___y_2430_: *mut crate::leanh::LeanObject,
    mut v___y_2431_: *mut crate::leanh::LeanObject,
    mut v___y_2432_: *mut crate::leanh::LeanObject,
    mut v___y_2433_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2435_: u8 = 0;
    let mut v___x_2436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2440_: u8 = 0;
    let mut v_a_2441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_2444_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2450_: usize = 0;
    let mut v___x_2451_: usize = 0;
    let mut v_reuseFailAlloc_2453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2454_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2456_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2463_: u8 = 0;
    let mut v___x_2465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2467_: u8 = 0;
    let mut v_isSharedCheck_2468_: u8 = 0;
    let mut v_unused_2469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2435_ = lean_usize_dec_lt(v_i_2428_, v_sz_2427_);
                if v___x_2435_ == 0 {
                    v___x_2436_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2436_, 0, v_b_2429_);
                    return v___x_2436_;
                } else {
                    v_snd_2437_ = crate::leanh::lean_ctor_get(v_b_2429_, 1);
                    v_isSharedCheck_2468_ = (!crate::leanh::lean_is_exclusive(v_b_2429_)) as u8;
                    if v_isSharedCheck_2468_ == 0 {
                        v_unused_2469_ = crate::leanh::lean_ctor_get(v_b_2429_, 0);
                        crate::leanh::lean_dec(v_unused_2469_);
                        v___x_2439_ = v_b_2429_;
                        v_isShared_2440_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2437_);
                        crate::leanh::lean_dec(v_b_2429_);
                        v___x_2439_ = crate::leanh::lean_box(0);
                        v_isShared_2440_ = v_isSharedCheck_2468_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2441_ = lean_array_uget_borrowed(v_as_2426_, v_i_2428_);
                crate::leanh::lean_inc(v_a_2441_);
                v___x_2442_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2425_,
                    v_a_2441_,
                    v___y_2430_,
                    v___y_2431_,
                    v___y_2432_,
                    v___y_2433_,
                );
                if crate::leanh::lean_obj_tag(v___x_2442_) == 0 {
                    v_a_2443_ = crate::leanh::lean_ctor_get(v___x_2442_, 0);
                    crate::leanh::lean_inc(v_a_2443_);
                    crate::leanh::lean_dec_ref_known(v___x_2442_, 1);
                    v_self_2444_ = crate::leanh::lean_ctor_get(v_a_2443_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_2444_, 2);
                    crate::leanh::lean_dec(v_a_2443_);
                    v___x_2445_ = crate::leanh::lean_box(0);
                    v___x_2454_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_2444_);
                    if crate::leanh::lean_obj_tag(v___x_2454_) == 1 {
                        v_val_2455_ = crate::leanh::lean_ctor_get(v___x_2454_, 0);
                        crate::leanh::lean_inc(v_val_2455_);
                        crate::leanh::lean_dec_ref_known(v___x_2454_, 1);
                        v___x_2456_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2437_, v_val_2455_);
                        if crate::leanh::lean_obj_tag(v___x_2456_) == 0 {
                            v___x_2457_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2437_, v_self_2444_);
                            crate::leanh::lean_dec_ref(v_self_2444_);
                            if crate::leanh::lean_obj_tag(v___x_2457_) == 1 {
                                v_val_2458_ = crate::leanh::lean_ctor_get(v___x_2457_, 0);
                                crate::leanh::lean_inc(v_val_2458_);
                                crate::leanh::lean_dec_ref_known(v___x_2457_, 1);
                                v___x_2459_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_2425_,
                                    v_val_2455_,
                                    v_val_2458_,
                                    v_snd_2437_,
                                );
                                v_a_2447_ = v___x_2459_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2457_);
                                crate::leanh::lean_dec(v_val_2455_);
                                v_a_2447_ = v_snd_2437_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2456_, 1);
                            crate::leanh::lean_dec(v_val_2455_);
                            crate::leanh::lean_dec_ref(v_self_2444_);
                            v_a_2447_ = v_snd_2437_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2454_);
                        crate::leanh::lean_dec_ref(v_self_2444_);
                        v_a_2447_ = v_snd_2437_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2439_);
                    crate::leanh::lean_dec(v_snd_2437_);
                    v_a_2460_ = crate::leanh::lean_ctor_get(v___x_2442_, 0);
                    v_isSharedCheck_2467_ = (!crate::leanh::lean_is_exclusive(v___x_2442_)) as u8;
                    if v_isSharedCheck_2467_ == 0 {
                        v___x_2462_ = v___x_2442_;
                        v_isShared_2463_ = v_isSharedCheck_2467_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2460_);
                        crate::leanh::lean_dec(v___x_2442_);
                        v___x_2462_ = crate::leanh::lean_box(0);
                        v_isShared_2463_ = v_isSharedCheck_2467_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2440_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2439_, 1, v_a_2447_);
                    crate::leanh::lean_ctor_set(v___x_2439_, 0, v___x_2445_);
                    v___x_2449_ = v___x_2439_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2453_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2445_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2453_, 1, v_a_2447_);
                    v___x_2449_ = v_reuseFailAlloc_2453_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2450_ = 1usize;
                v___x_2451_ = lean_usize_add(v_i_2428_, v___x_2450_);
                v_i_2428_ = v___x_2451_;
                v_b_2429_ = v___x_2449_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2463_ == 0 {
                    v___x_2465_ = v___x_2462_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2466_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2466_, 0, v_a_2460_);
                    v___x_2465_ = v_reuseFailAlloc_2466_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2465_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12___boxed(
    mut v_goal_2470_: *mut crate::leanh::LeanObject,
    mut v_as_2471_: *mut crate::leanh::LeanObject,
    mut v_sz_2472_: *mut crate::leanh::LeanObject,
    mut v_i_2473_: *mut crate::leanh::LeanObject,
    mut v_b_2474_: *mut crate::leanh::LeanObject,
    mut v___y_2475_: *mut crate::leanh::LeanObject,
    mut v___y_2476_: *mut crate::leanh::LeanObject,
    mut v___y_2477_: *mut crate::leanh::LeanObject,
    mut v___y_2478_: *mut crate::leanh::LeanObject,
    mut v___y_2479_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2480_: usize = 0;
    let mut v_i_boxed_2481_: usize = 0;
    let mut v_res_2482_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2480_ = crate::leanh::lean_unbox_usize(v_sz_2472_);
    crate::leanh::lean_dec(v_sz_2472_);
    v_i_boxed_2481_ = crate::leanh::lean_unbox_usize(v_i_2473_);
    crate::leanh::lean_dec(v_i_2473_);
    v_res_2482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(v_goal_2470_, v_as_2471_, v_sz_boxed_2480_, v_i_boxed_2481_, v_b_2474_, v___y_2475_, v___y_2476_, v___y_2477_, v___y_2478_);
    crate::leanh::lean_dec(v___y_2478_);
    crate::leanh::lean_dec_ref(v___y_2477_);
    crate::leanh::lean_dec(v___y_2476_);
    crate::leanh::lean_dec_ref(v___y_2475_);
    crate::leanh::lean_dec_ref(v_as_2471_);
    crate::leanh::lean_dec_ref(v_goal_2470_);
    return v_res_2482_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(
    mut v_goal_2483_: *mut crate::leanh::LeanObject,
    mut v_as_2484_: *mut crate::leanh::LeanObject,
    mut v_sz_2485_: usize,
    mut v_i_2486_: usize,
    mut v_b_2487_: *mut crate::leanh::LeanObject,
    mut v___y_2488_: *mut crate::leanh::LeanObject,
    mut v___y_2489_: *mut crate::leanh::LeanObject,
    mut v___y_2490_: *mut crate::leanh::LeanObject,
    mut v___y_2491_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2493_: u8 = 0;
    let mut v___x_2494_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2498_: u8 = 0;
    let mut v_a_2499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2500_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_2502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2508_: usize = 0;
    let mut v___x_2509_: usize = 0;
    let mut v___x_2510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2511_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2515_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2521_: u8 = 0;
    let mut v___x_2523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2524_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2525_: u8 = 0;
    let mut v_isSharedCheck_2526_: u8 = 0;
    let mut v_unused_2527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2493_ = lean_usize_dec_lt(v_i_2486_, v_sz_2485_);
                if v___x_2493_ == 0 {
                    v___x_2494_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2494_, 0, v_b_2487_);
                    return v___x_2494_;
                } else {
                    v_snd_2495_ = crate::leanh::lean_ctor_get(v_b_2487_, 1);
                    v_isSharedCheck_2526_ = (!crate::leanh::lean_is_exclusive(v_b_2487_)) as u8;
                    if v_isSharedCheck_2526_ == 0 {
                        v_unused_2527_ = crate::leanh::lean_ctor_get(v_b_2487_, 0);
                        crate::leanh::lean_dec(v_unused_2527_);
                        v___x_2497_ = v_b_2487_;
                        v_isShared_2498_ = v_isSharedCheck_2526_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2495_);
                        crate::leanh::lean_dec(v_b_2487_);
                        v___x_2497_ = crate::leanh::lean_box(0);
                        v_isShared_2498_ = v_isSharedCheck_2526_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2499_ = lean_array_uget_borrowed(v_as_2484_, v_i_2486_);
                crate::leanh::lean_inc(v_a_2499_);
                v___x_2500_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2483_,
                    v_a_2499_,
                    v___y_2488_,
                    v___y_2489_,
                    v___y_2490_,
                    v___y_2491_,
                );
                if crate::leanh::lean_obj_tag(v___x_2500_) == 0 {
                    v_a_2501_ = crate::leanh::lean_ctor_get(v___x_2500_, 0);
                    crate::leanh::lean_inc(v_a_2501_);
                    crate::leanh::lean_dec_ref_known(v___x_2500_, 1);
                    v_self_2502_ = crate::leanh::lean_ctor_get(v_a_2501_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_2502_, 2);
                    crate::leanh::lean_dec(v_a_2501_);
                    v___x_2503_ = crate::leanh::lean_box(0);
                    v___x_2512_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_2502_);
                    if crate::leanh::lean_obj_tag(v___x_2512_) == 1 {
                        v_val_2513_ = crate::leanh::lean_ctor_get(v___x_2512_, 0);
                        crate::leanh::lean_inc(v_val_2513_);
                        crate::leanh::lean_dec_ref_known(v___x_2512_, 1);
                        v___x_2514_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2495_, v_val_2513_);
                        if crate::leanh::lean_obj_tag(v___x_2514_) == 0 {
                            v___x_2515_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2495_, v_self_2502_);
                            crate::leanh::lean_dec_ref(v_self_2502_);
                            if crate::leanh::lean_obj_tag(v___x_2515_) == 1 {
                                v_val_2516_ = crate::leanh::lean_ctor_get(v___x_2515_, 0);
                                crate::leanh::lean_inc(v_val_2516_);
                                crate::leanh::lean_dec_ref_known(v___x_2515_, 1);
                                v___x_2517_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_2483_,
                                    v_val_2513_,
                                    v_val_2516_,
                                    v_snd_2495_,
                                );
                                v_a_2505_ = v___x_2517_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2515_);
                                crate::leanh::lean_dec(v_val_2513_);
                                v_a_2505_ = v_snd_2495_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2514_, 1);
                            crate::leanh::lean_dec(v_val_2513_);
                            crate::leanh::lean_dec_ref(v_self_2502_);
                            v_a_2505_ = v_snd_2495_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2512_);
                        crate::leanh::lean_dec_ref(v_self_2502_);
                        v_a_2505_ = v_snd_2495_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2497_);
                    crate::leanh::lean_dec(v_snd_2495_);
                    v_a_2518_ = crate::leanh::lean_ctor_get(v___x_2500_, 0);
                    v_isSharedCheck_2525_ = (!crate::leanh::lean_is_exclusive(v___x_2500_)) as u8;
                    if v_isSharedCheck_2525_ == 0 {
                        v___x_2520_ = v___x_2500_;
                        v_isShared_2521_ = v_isSharedCheck_2525_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2518_);
                        crate::leanh::lean_dec(v___x_2500_);
                        v___x_2520_ = crate::leanh::lean_box(0);
                        v_isShared_2521_ = v_isSharedCheck_2525_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2498_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2497_, 1, v_a_2505_);
                    crate::leanh::lean_ctor_set(v___x_2497_, 0, v___x_2503_);
                    v___x_2507_ = v___x_2497_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2511_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 0, v___x_2503_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2511_, 1, v_a_2505_);
                    v___x_2507_ = v_reuseFailAlloc_2511_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2508_ = 1usize;
                v___x_2509_ = lean_usize_add(v_i_2486_, v___x_2508_);
                v___x_2510_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10_spec__12(v_goal_2483_, v_as_2484_, v_sz_2485_, v___x_2509_, v___x_2507_, v___y_2488_, v___y_2489_, v___y_2490_, v___y_2491_);
                return v___x_2510_;
            }
            4 => {
                if v_isShared_2521_ == 0 {
                    v___x_2523_ = v___x_2520_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2524_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_a_2518_);
                    v___x_2523_ = v_reuseFailAlloc_2524_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2523_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10___boxed(
    mut v_goal_2528_: *mut crate::leanh::LeanObject,
    mut v_as_2529_: *mut crate::leanh::LeanObject,
    mut v_sz_2530_: *mut crate::leanh::LeanObject,
    mut v_i_2531_: *mut crate::leanh::LeanObject,
    mut v_b_2532_: *mut crate::leanh::LeanObject,
    mut v___y_2533_: *mut crate::leanh::LeanObject,
    mut v___y_2534_: *mut crate::leanh::LeanObject,
    mut v___y_2535_: *mut crate::leanh::LeanObject,
    mut v___y_2536_: *mut crate::leanh::LeanObject,
    mut v___y_2537_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2538_: usize = 0;
    let mut v_i_boxed_2539_: usize = 0;
    let mut v_res_2540_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2538_ = crate::leanh::lean_unbox_usize(v_sz_2530_);
    crate::leanh::lean_dec(v_sz_2530_);
    v_i_boxed_2539_ = crate::leanh::lean_unbox_usize(v_i_2531_);
    crate::leanh::lean_dec(v_i_2531_);
    v_res_2540_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(v_goal_2528_, v_as_2529_, v_sz_boxed_2538_, v_i_boxed_2539_, v_b_2532_, v___y_2533_, v___y_2534_, v___y_2535_, v___y_2536_);
    crate::leanh::lean_dec(v___y_2536_);
    crate::leanh::lean_dec_ref(v___y_2535_);
    crate::leanh::lean_dec(v___y_2534_);
    crate::leanh::lean_dec_ref(v___y_2533_);
    crate::leanh::lean_dec_ref(v_as_2529_);
    crate::leanh::lean_dec_ref(v_goal_2528_);
    return v_res_2540_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(
    mut v_init_2541_: *mut crate::leanh::LeanObject,
    mut v_goal_2542_: *mut crate::leanh::LeanObject,
    mut v_n_2543_: *mut crate::leanh::LeanObject,
    mut v_b_2544_: *mut crate::leanh::LeanObject,
    mut v___y_2545_: *mut crate::leanh::LeanObject,
    mut v___y_2546_: *mut crate::leanh::LeanObject,
    mut v___y_2547_: *mut crate::leanh::LeanObject,
    mut v___y_2548_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_2550_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2551_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2553_: usize = 0;
    let mut v___x_2554_: usize = 0;
    let mut v___x_2555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2558_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2559_: u8 = 0;
    let mut v_fst_2560_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2562_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2564_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v_a_2571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut v_vs_2579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2580_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2582_: usize = 0;
    let mut v___x_2583_: usize = 0;
    let mut v___x_2584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2588_: u8 = 0;
    let mut v_fst_2589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2594_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2598_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2599_: u8 = 0;
    let mut v_a_2600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2602_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2603_: u8 = 0;
    let mut v___x_2605_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2606_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2607_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_2543_) == 0 {
                    v_cs_2550_ = crate::leanh::lean_ctor_get(v_n_2543_, 0);
                    v___x_2551_ = crate::leanh::lean_box(0);
                    v___x_2552_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2552_, 0, v___x_2551_);
                    crate::leanh::lean_ctor_set(v___x_2552_, 1, v_b_2544_);
                    v_sz_2553_ = lean_array_size(v_cs_2550_);
                    v___x_2554_ = 0usize;
                    v___x_2555_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(v_init_2541_, v_goal_2542_, v_cs_2550_, v_sz_2553_, v___x_2554_, v___x_2552_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
                    if crate::leanh::lean_obj_tag(v___x_2555_) == 0 {
                        v_a_2556_ = crate::leanh::lean_ctor_get(v___x_2555_, 0);
                        v_isSharedCheck_2570_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2555_)) as u8;
                        if v_isSharedCheck_2570_ == 0 {
                            v___x_2558_ = v___x_2555_;
                            v_isShared_2559_ = v_isSharedCheck_2570_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2556_);
                            crate::leanh::lean_dec(v___x_2555_);
                            v___x_2558_ = crate::leanh::lean_box(0);
                            v_isShared_2559_ = v_isSharedCheck_2570_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2571_ = crate::leanh::lean_ctor_get(v___x_2555_, 0);
                        v_isSharedCheck_2578_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2555_)) as u8;
                        if v_isSharedCheck_2578_ == 0 {
                            v___x_2573_ = v___x_2555_;
                            v_isShared_2574_ = v_isSharedCheck_2578_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2571_);
                            crate::leanh::lean_dec(v___x_2555_);
                            v___x_2573_ = crate::leanh::lean_box(0);
                            v_isShared_2574_ = v_isSharedCheck_2578_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2579_ = crate::leanh::lean_ctor_get(v_n_2543_, 0);
                    v___x_2580_ = crate::leanh::lean_box(0);
                    v___x_2581_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2581_, 0, v___x_2580_);
                    crate::leanh::lean_ctor_set(v___x_2581_, 1, v_b_2544_);
                    v_sz_2582_ = lean_array_size(v_vs_2579_);
                    v___x_2583_ = 0usize;
                    v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__10(v_goal_2542_, v_vs_2579_, v_sz_2582_, v___x_2583_, v___x_2581_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
                    if crate::leanh::lean_obj_tag(v___x_2584_) == 0 {
                        v_a_2585_ = crate::leanh::lean_ctor_get(v___x_2584_, 0);
                        v_isSharedCheck_2599_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2584_)) as u8;
                        if v_isSharedCheck_2599_ == 0 {
                            v___x_2587_ = v___x_2584_;
                            v_isShared_2588_ = v_isSharedCheck_2599_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2585_);
                            crate::leanh::lean_dec(v___x_2584_);
                            v___x_2587_ = crate::leanh::lean_box(0);
                            v_isShared_2588_ = v_isSharedCheck_2599_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2600_ = crate::leanh::lean_ctor_get(v___x_2584_, 0);
                        v_isSharedCheck_2607_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2584_)) as u8;
                        if v_isSharedCheck_2607_ == 0 {
                            v___x_2602_ = v___x_2584_;
                            v_isShared_2603_ = v_isSharedCheck_2607_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2600_);
                            crate::leanh::lean_dec(v___x_2584_);
                            v___x_2602_ = crate::leanh::lean_box(0);
                            v_isShared_2603_ = v_isSharedCheck_2607_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2560_ = crate::leanh::lean_ctor_get(v_a_2556_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2560_) == 0 {
                    v_snd_2561_ = crate::leanh::lean_ctor_get(v_a_2556_, 1);
                    crate::leanh::lean_inc(v_snd_2561_);
                    crate::leanh::lean_dec(v_a_2556_);
                    v___x_2562_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2562_, 0, v_snd_2561_);
                    if v_isShared_2559_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2558_, 0, v___x_2562_);
                        v___x_2564_ = v___x_2558_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2565_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2565_, 0, v___x_2562_);
                        v___x_2564_ = v_reuseFailAlloc_2565_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2560_);
                    crate::leanh::lean_dec(v_a_2556_);
                    v_val_2566_ = crate::leanh::lean_ctor_get(v_fst_2560_, 0);
                    crate::leanh::lean_inc(v_val_2566_);
                    crate::leanh::lean_dec_ref_known(v_fst_2560_, 1);
                    if v_isShared_2559_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2558_, 0, v_val_2566_);
                        v___x_2568_ = v___x_2558_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2569_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_val_2566_);
                        v___x_2568_ = v_reuseFailAlloc_2569_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2564_;
            }
            3 => {
                return v___x_2568_;
            }
            4 => {
                if v_isShared_2574_ == 0 {
                    v___x_2576_ = v___x_2573_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
                    v___x_2576_ = v_reuseFailAlloc_2577_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2576_;
            }
            6 => {
                v_fst_2589_ = crate::leanh::lean_ctor_get(v_a_2585_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2589_) == 0 {
                    v_snd_2590_ = crate::leanh::lean_ctor_get(v_a_2585_, 1);
                    crate::leanh::lean_inc(v_snd_2590_);
                    crate::leanh::lean_dec(v_a_2585_);
                    v___x_2591_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2591_, 0, v_snd_2590_);
                    if v_isShared_2588_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2587_, 0, v___x_2591_);
                        v___x_2593_ = v___x_2587_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2594_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2594_, 0, v___x_2591_);
                        v___x_2593_ = v_reuseFailAlloc_2594_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2589_);
                    crate::leanh::lean_dec(v_a_2585_);
                    v_val_2595_ = crate::leanh::lean_ctor_get(v_fst_2589_, 0);
                    crate::leanh::lean_inc(v_val_2595_);
                    crate::leanh::lean_dec_ref_known(v_fst_2589_, 1);
                    if v_isShared_2588_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2587_, 0, v_val_2595_);
                        v___x_2597_ = v___x_2587_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2598_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_val_2595_);
                        v___x_2597_ = v_reuseFailAlloc_2598_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2593_;
            }
            8 => {
                return v___x_2597_;
            }
            9 => {
                if v_isShared_2603_ == 0 {
                    v___x_2605_ = v___x_2602_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2606_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2606_, 0, v_a_2600_);
                    v___x_2605_ = v_reuseFailAlloc_2606_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2605_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(
    mut v_init_2608_: *mut crate::leanh::LeanObject,
    mut v_goal_2609_: *mut crate::leanh::LeanObject,
    mut v_as_2610_: *mut crate::leanh::LeanObject,
    mut v_sz_2611_: usize,
    mut v_i_2612_: usize,
    mut v_b_2613_: *mut crate::leanh::LeanObject,
    mut v___y_2614_: *mut crate::leanh::LeanObject,
    mut v___y_2615_: *mut crate::leanh::LeanObject,
    mut v___y_2616_: *mut crate::leanh::LeanObject,
    mut v___y_2617_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2619_: u8 = 0;
    let mut v___x_2620_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2621_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2623_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2624_: u8 = 0;
    let mut v_a_2625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2629_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2630_: u8 = 0;
    let mut v___x_2631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2642_: usize = 0;
    let mut v___x_2643_: usize = 0;
    let mut v_reuseFailAlloc_2645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2646_: u8 = 0;
    let mut v_a_2647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2650_: u8 = 0;
    let mut v___x_2652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2654_: u8 = 0;
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v_unused_2656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2619_ = lean_usize_dec_lt(v_i_2612_, v_sz_2611_);
                if v___x_2619_ == 0 {
                    v___x_2620_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2620_, 0, v_b_2613_);
                    return v___x_2620_;
                } else {
                    v_snd_2621_ = crate::leanh::lean_ctor_get(v_b_2613_, 1);
                    v_isSharedCheck_2655_ = (!crate::leanh::lean_is_exclusive(v_b_2613_)) as u8;
                    if v_isSharedCheck_2655_ == 0 {
                        v_unused_2656_ = crate::leanh::lean_ctor_get(v_b_2613_, 0);
                        crate::leanh::lean_dec(v_unused_2656_);
                        v___x_2623_ = v_b_2613_;
                        v_isShared_2624_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2621_);
                        crate::leanh::lean_dec(v_b_2613_);
                        v___x_2623_ = crate::leanh::lean_box(0);
                        v_isShared_2624_ = v_isSharedCheck_2655_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2625_ = lean_array_uget_borrowed(v_as_2610_, v_i_2612_);
                crate::leanh::lean_inc(v_snd_2621_);
                v___x_2626_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_init_2608_, v_goal_2609_, v_a_2625_, v_snd_2621_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_);
                if crate::leanh::lean_obj_tag(v___x_2626_) == 0 {
                    v_a_2627_ = crate::leanh::lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2646_ = (!crate::leanh::lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2646_ == 0 {
                        v___x_2629_ = v___x_2626_;
                        v_isShared_2630_ = v_isSharedCheck_2646_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2627_);
                        crate::leanh::lean_dec(v___x_2626_);
                        v___x_2629_ = crate::leanh::lean_box(0);
                        v_isShared_2630_ = v_isSharedCheck_2646_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2623_);
                    crate::leanh::lean_dec(v_snd_2621_);
                    v_a_2647_ = crate::leanh::lean_ctor_get(v___x_2626_, 0);
                    v_isSharedCheck_2654_ = (!crate::leanh::lean_is_exclusive(v___x_2626_)) as u8;
                    if v_isSharedCheck_2654_ == 0 {
                        v___x_2649_ = v___x_2626_;
                        v_isShared_2650_ = v_isSharedCheck_2654_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2647_);
                        crate::leanh::lean_dec(v___x_2626_);
                        v___x_2649_ = crate::leanh::lean_box(0);
                        v_isShared_2650_ = v_isSharedCheck_2654_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_2627_) == 0 {
                    v___x_2631_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2631_, 0, v_a_2627_);
                    if v_isShared_2624_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2631_);
                        v___x_2633_ = v___x_2623_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2637_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2637_, 0, v___x_2631_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_snd_2621_);
                        v___x_2633_ = v_reuseFailAlloc_2637_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2629_);
                    crate::leanh::lean_dec(v_snd_2621_);
                    v_a_2638_ = crate::leanh::lean_ctor_get(v_a_2627_, 0);
                    crate::leanh::lean_inc(v_a_2638_);
                    crate::leanh::lean_dec_ref_known(v_a_2627_, 1);
                    v___x_2639_ = crate::leanh::lean_box(0);
                    if v_isShared_2624_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2623_, 1, v_a_2638_);
                        crate::leanh::lean_ctor_set(v___x_2623_, 0, v___x_2639_);
                        v___x_2641_ = v___x_2623_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2645_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2639_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_a_2638_);
                        v___x_2641_ = v_reuseFailAlloc_2645_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2630_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2629_, 0, v___x_2633_);
                    v___x_2635_ = v___x_2629_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2636_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2636_, 0, v___x_2633_);
                    v___x_2635_ = v_reuseFailAlloc_2636_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2635_;
            }
            5 => {
                v___x_2642_ = 1usize;
                v___x_2643_ = lean_usize_add(v_i_2612_, v___x_2642_);
                v_i_2612_ = v___x_2643_;
                v_b_2613_ = v___x_2641_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2650_ == 0 {
                    v___x_2652_ = v___x_2649_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2653_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2653_, 0, v_a_2647_);
                    v___x_2652_ = v_reuseFailAlloc_2653_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2652_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9___boxed(
    mut v_init_2657_: *mut crate::leanh::LeanObject,
    mut v_goal_2658_: *mut crate::leanh::LeanObject,
    mut v_as_2659_: *mut crate::leanh::LeanObject,
    mut v_sz_2660_: *mut crate::leanh::LeanObject,
    mut v_i_2661_: *mut crate::leanh::LeanObject,
    mut v_b_2662_: *mut crate::leanh::LeanObject,
    mut v___y_2663_: *mut crate::leanh::LeanObject,
    mut v___y_2664_: *mut crate::leanh::LeanObject,
    mut v___y_2665_: *mut crate::leanh::LeanObject,
    mut v___y_2666_: *mut crate::leanh::LeanObject,
    mut v___y_2667_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2668_: usize = 0;
    let mut v_i_boxed_2669_: usize = 0;
    let mut v_res_2670_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2668_ = crate::leanh::lean_unbox_usize(v_sz_2660_);
    crate::leanh::lean_dec(v_sz_2660_);
    v_i_boxed_2669_ = crate::leanh::lean_unbox_usize(v_i_2661_);
    crate::leanh::lean_dec(v_i_2661_);
    v_res_2670_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5_spec__9(v_init_2657_, v_goal_2658_, v_as_2659_, v_sz_boxed_2668_, v_i_boxed_2669_, v_b_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_);
    crate::leanh::lean_dec(v___y_2666_);
    crate::leanh::lean_dec_ref(v___y_2665_);
    crate::leanh::lean_dec(v___y_2664_);
    crate::leanh::lean_dec_ref(v___y_2663_);
    crate::leanh::lean_dec_ref(v_as_2659_);
    crate::leanh::lean_dec_ref(v_goal_2658_);
    crate::leanh::lean_dec_ref(v_init_2657_);
    return v_res_2670_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5___boxed(
    mut v_init_2671_: *mut crate::leanh::LeanObject,
    mut v_goal_2672_: *mut crate::leanh::LeanObject,
    mut v_n_2673_: *mut crate::leanh::LeanObject,
    mut v_b_2674_: *mut crate::leanh::LeanObject,
    mut v___y_2675_: *mut crate::leanh::LeanObject,
    mut v___y_2676_: *mut crate::leanh::LeanObject,
    mut v___y_2677_: *mut crate::leanh::LeanObject,
    mut v___y_2678_: *mut crate::leanh::LeanObject,
    mut v___y_2679_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2680_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_init_2671_, v_goal_2672_, v_n_2673_, v_b_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
    crate::leanh::lean_dec(v___y_2678_);
    crate::leanh::lean_dec_ref(v___y_2677_);
    crate::leanh::lean_dec(v___y_2676_);
    crate::leanh::lean_dec_ref(v___y_2675_);
    crate::leanh::lean_dec_ref(v_n_2673_);
    crate::leanh::lean_dec_ref(v_goal_2672_);
    crate::leanh::lean_dec_ref(v_init_2671_);
    return v_res_2680_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(
    mut v_goal_2681_: *mut crate::leanh::LeanObject,
    mut v_as_2682_: *mut crate::leanh::LeanObject,
    mut v_sz_2683_: usize,
    mut v_i_2684_: usize,
    mut v_b_2685_: *mut crate::leanh::LeanObject,
    mut v___y_2686_: *mut crate::leanh::LeanObject,
    mut v___y_2687_: *mut crate::leanh::LeanObject,
    mut v___y_2688_: *mut crate::leanh::LeanObject,
    mut v___y_2689_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2691_: u8 = 0;
    let mut v___x_2692_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2693_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2695_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2696_: u8 = 0;
    let mut v_a_2697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2698_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_2700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2703_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2705_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2706_: usize = 0;
    let mut v___x_2707_: usize = 0;
    let mut v_reuseFailAlloc_2709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2711_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2712_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2713_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2719_: u8 = 0;
    let mut v___x_2721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2723_: u8 = 0;
    let mut v_isSharedCheck_2724_: u8 = 0;
    let mut v_unused_2725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2691_ = lean_usize_dec_lt(v_i_2684_, v_sz_2683_);
                if v___x_2691_ == 0 {
                    v___x_2692_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2692_, 0, v_b_2685_);
                    return v___x_2692_;
                } else {
                    v_snd_2693_ = crate::leanh::lean_ctor_get(v_b_2685_, 1);
                    v_isSharedCheck_2724_ = (!crate::leanh::lean_is_exclusive(v_b_2685_)) as u8;
                    if v_isSharedCheck_2724_ == 0 {
                        v_unused_2725_ = crate::leanh::lean_ctor_get(v_b_2685_, 0);
                        crate::leanh::lean_dec(v_unused_2725_);
                        v___x_2695_ = v_b_2685_;
                        v_isShared_2696_ = v_isSharedCheck_2724_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2693_);
                        crate::leanh::lean_dec(v_b_2685_);
                        v___x_2695_ = crate::leanh::lean_box(0);
                        v_isShared_2696_ = v_isSharedCheck_2724_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2697_ = lean_array_uget_borrowed(v_as_2682_, v_i_2684_);
                crate::leanh::lean_inc(v_a_2697_);
                v___x_2698_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2681_,
                    v_a_2697_,
                    v___y_2686_,
                    v___y_2687_,
                    v___y_2688_,
                    v___y_2689_,
                );
                if crate::leanh::lean_obj_tag(v___x_2698_) == 0 {
                    v_a_2699_ = crate::leanh::lean_ctor_get(v___x_2698_, 0);
                    crate::leanh::lean_inc(v_a_2699_);
                    crate::leanh::lean_dec_ref_known(v___x_2698_, 1);
                    v_self_2700_ = crate::leanh::lean_ctor_get(v_a_2699_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_2700_, 2);
                    crate::leanh::lean_dec(v_a_2699_);
                    v___x_2701_ = crate::leanh::lean_box(0);
                    v___x_2710_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_2700_);
                    if crate::leanh::lean_obj_tag(v___x_2710_) == 1 {
                        v_val_2711_ = crate::leanh::lean_ctor_get(v___x_2710_, 0);
                        crate::leanh::lean_inc(v_val_2711_);
                        crate::leanh::lean_dec_ref_known(v___x_2710_, 1);
                        v___x_2712_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2693_, v_val_2711_);
                        if crate::leanh::lean_obj_tag(v___x_2712_) == 0 {
                            v___x_2713_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2693_, v_self_2700_);
                            crate::leanh::lean_dec_ref(v_self_2700_);
                            if crate::leanh::lean_obj_tag(v___x_2713_) == 1 {
                                v_val_2714_ = crate::leanh::lean_ctor_get(v___x_2713_, 0);
                                crate::leanh::lean_inc(v_val_2714_);
                                crate::leanh::lean_dec_ref_known(v___x_2713_, 1);
                                v___x_2715_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_2681_,
                                    v_val_2711_,
                                    v_val_2714_,
                                    v_snd_2693_,
                                );
                                v_a_2703_ = v___x_2715_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2713_);
                                crate::leanh::lean_dec(v_val_2711_);
                                v_a_2703_ = v_snd_2693_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2712_, 1);
                            crate::leanh::lean_dec(v_val_2711_);
                            crate::leanh::lean_dec_ref(v_self_2700_);
                            v_a_2703_ = v_snd_2693_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2710_);
                        crate::leanh::lean_dec_ref(v_self_2700_);
                        v_a_2703_ = v_snd_2693_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2695_);
                    crate::leanh::lean_dec(v_snd_2693_);
                    v_a_2716_ = crate::leanh::lean_ctor_get(v___x_2698_, 0);
                    v_isSharedCheck_2723_ = (!crate::leanh::lean_is_exclusive(v___x_2698_)) as u8;
                    if v_isSharedCheck_2723_ == 0 {
                        v___x_2718_ = v___x_2698_;
                        v_isShared_2719_ = v_isSharedCheck_2723_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2716_);
                        crate::leanh::lean_dec(v___x_2698_);
                        v___x_2718_ = crate::leanh::lean_box(0);
                        v_isShared_2719_ = v_isSharedCheck_2723_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2696_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2695_, 1, v_a_2703_);
                    crate::leanh::lean_ctor_set(v___x_2695_, 0, v___x_2701_);
                    v___x_2705_ = v___x_2695_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2709_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2709_, 0, v___x_2701_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2709_, 1, v_a_2703_);
                    v___x_2705_ = v_reuseFailAlloc_2709_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2706_ = 1usize;
                v___x_2707_ = lean_usize_add(v_i_2684_, v___x_2706_);
                v_i_2684_ = v___x_2707_;
                v_b_2685_ = v___x_2705_;
                state = 0;
                continue;
            }
            4 => {
                if v_isShared_2719_ == 0 {
                    v___x_2721_ = v___x_2718_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2722_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
                    v___x_2721_ = v_reuseFailAlloc_2722_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2721_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12___boxed(
    mut v_goal_2726_: *mut crate::leanh::LeanObject,
    mut v_as_2727_: *mut crate::leanh::LeanObject,
    mut v_sz_2728_: *mut crate::leanh::LeanObject,
    mut v_i_2729_: *mut crate::leanh::LeanObject,
    mut v_b_2730_: *mut crate::leanh::LeanObject,
    mut v___y_2731_: *mut crate::leanh::LeanObject,
    mut v___y_2732_: *mut crate::leanh::LeanObject,
    mut v___y_2733_: *mut crate::leanh::LeanObject,
    mut v___y_2734_: *mut crate::leanh::LeanObject,
    mut v___y_2735_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2736_: usize = 0;
    let mut v_i_boxed_2737_: usize = 0;
    let mut v_res_2738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2736_ = crate::leanh::lean_unbox_usize(v_sz_2728_);
    crate::leanh::lean_dec(v_sz_2728_);
    v_i_boxed_2737_ = crate::leanh::lean_unbox_usize(v_i_2729_);
    crate::leanh::lean_dec(v_i_2729_);
    v_res_2738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(v_goal_2726_, v_as_2727_, v_sz_boxed_2736_, v_i_boxed_2737_, v_b_2730_, v___y_2731_, v___y_2732_, v___y_2733_, v___y_2734_);
    crate::leanh::lean_dec(v___y_2734_);
    crate::leanh::lean_dec_ref(v___y_2733_);
    crate::leanh::lean_dec(v___y_2732_);
    crate::leanh::lean_dec_ref(v___y_2731_);
    crate::leanh::lean_dec_ref(v_as_2727_);
    crate::leanh::lean_dec_ref(v_goal_2726_);
    return v_res_2738_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(
    mut v_goal_2739_: *mut crate::leanh::LeanObject,
    mut v_as_2740_: *mut crate::leanh::LeanObject,
    mut v_sz_2741_: usize,
    mut v_i_2742_: usize,
    mut v_b_2743_: *mut crate::leanh::LeanObject,
    mut v___y_2744_: *mut crate::leanh::LeanObject,
    mut v___y_2745_: *mut crate::leanh::LeanObject,
    mut v___y_2746_: *mut crate::leanh::LeanObject,
    mut v___y_2747_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2749_: u8 = 0;
    let mut v___x_2750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2754_: u8 = 0;
    let mut v_a_2755_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2756_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_self_2758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2759_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2761_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2764_: usize = 0;
    let mut v___x_2765_: usize = 0;
    let mut v___x_2766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2767_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2768_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2773_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2777_: u8 = 0;
    let mut v___x_2779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2781_: u8 = 0;
    let mut v_isSharedCheck_2782_: u8 = 0;
    let mut v_unused_2783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2749_ = lean_usize_dec_lt(v_i_2742_, v_sz_2741_);
                if v___x_2749_ == 0 {
                    v___x_2750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2750_, 0, v_b_2743_);
                    return v___x_2750_;
                } else {
                    v_snd_2751_ = crate::leanh::lean_ctor_get(v_b_2743_, 1);
                    v_isSharedCheck_2782_ = (!crate::leanh::lean_is_exclusive(v_b_2743_)) as u8;
                    if v_isSharedCheck_2782_ == 0 {
                        v_unused_2783_ = crate::leanh::lean_ctor_get(v_b_2743_, 0);
                        crate::leanh::lean_dec(v_unused_2783_);
                        v___x_2753_ = v_b_2743_;
                        v_isShared_2754_ = v_isSharedCheck_2782_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_2751_);
                        crate::leanh::lean_dec(v_b_2743_);
                        v___x_2753_ = crate::leanh::lean_box(0);
                        v_isShared_2754_ = v_isSharedCheck_2782_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2755_ = lean_array_uget_borrowed(v_as_2740_, v_i_2742_);
                crate::leanh::lean_inc(v_a_2755_);
                v___x_2756_ = l_Lean_Meta_Grind_Goal_getENode(
                    v_goal_2739_,
                    v_a_2755_,
                    v___y_2744_,
                    v___y_2745_,
                    v___y_2746_,
                    v___y_2747_,
                );
                if crate::leanh::lean_obj_tag(v___x_2756_) == 0 {
                    v_a_2757_ = crate::leanh::lean_ctor_get(v___x_2756_, 0);
                    crate::leanh::lean_inc(v_a_2757_);
                    crate::leanh::lean_dec_ref_known(v___x_2756_, 1);
                    v_self_2758_ = crate::leanh::lean_ctor_get(v_a_2757_, 0);
                    crate::leanh::lean_inc_ref_n(v_self_2758_, 2);
                    crate::leanh::lean_dec(v_a_2757_);
                    v___x_2759_ = crate::leanh::lean_box(0);
                    v___x_2768_ = l___private_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model_0__Lean_Meta_Grind_Arith_Cutsat_natCastToInt_x3f(v_self_2758_);
                    if crate::leanh::lean_obj_tag(v___x_2768_) == 1 {
                        v_val_2769_ = crate::leanh::lean_ctor_get(v___x_2768_, 0);
                        crate::leanh::lean_inc(v_val_2769_);
                        crate::leanh::lean_dec_ref_known(v___x_2768_, 1);
                        v___x_2770_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2751_, v_val_2769_);
                        if crate::leanh::lean_obj_tag(v___x_2770_) == 0 {
                            v___x_2771_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_snd_2751_, v_self_2758_);
                            crate::leanh::lean_dec_ref(v_self_2758_);
                            if crate::leanh::lean_obj_tag(v___x_2771_) == 1 {
                                v_val_2772_ = crate::leanh::lean_ctor_get(v___x_2771_, 0);
                                crate::leanh::lean_inc(v_val_2772_);
                                crate::leanh::lean_dec_ref_known(v___x_2771_, 1);
                                v___x_2773_ = l_Lean_Meta_Grind_Arith_assignEqc(
                                    v_goal_2739_,
                                    v_val_2769_,
                                    v_val_2772_,
                                    v_snd_2751_,
                                );
                                v_a_2761_ = v___x_2773_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_2771_);
                                crate::leanh::lean_dec(v_val_2769_);
                                v_a_2761_ = v_snd_2751_;
                                state = 2;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_2770_, 1);
                            crate::leanh::lean_dec(v_val_2769_);
                            crate::leanh::lean_dec_ref(v_self_2758_);
                            v_a_2761_ = v_snd_2751_;
                            state = 2;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v___x_2768_);
                        crate::leanh::lean_dec_ref(v_self_2758_);
                        v_a_2761_ = v_snd_2751_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2753_);
                    crate::leanh::lean_dec(v_snd_2751_);
                    v_a_2774_ = crate::leanh::lean_ctor_get(v___x_2756_, 0);
                    v_isSharedCheck_2781_ = (!crate::leanh::lean_is_exclusive(v___x_2756_)) as u8;
                    if v_isSharedCheck_2781_ == 0 {
                        v___x_2776_ = v___x_2756_;
                        v_isShared_2777_ = v_isSharedCheck_2781_;
                        state = 4;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2774_);
                        crate::leanh::lean_dec(v___x_2756_);
                        v___x_2776_ = crate::leanh::lean_box(0);
                        v_isShared_2777_ = v_isSharedCheck_2781_;
                        state = 4;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2754_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2753_, 1, v_a_2761_);
                    crate::leanh::lean_ctor_set(v___x_2753_, 0, v___x_2759_);
                    v___x_2763_ = v___x_2753_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2767_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 0, v___x_2759_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2767_, 1, v_a_2761_);
                    v___x_2763_ = v_reuseFailAlloc_2767_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_2764_ = 1usize;
                v___x_2765_ = lean_usize_add(v_i_2742_, v___x_2764_);
                v___x_2766_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6_spec__12(v_goal_2739_, v_as_2740_, v_sz_2741_, v___x_2765_, v___x_2763_, v___y_2744_, v___y_2745_, v___y_2746_, v___y_2747_);
                return v___x_2766_;
            }
            4 => {
                if v_isShared_2777_ == 0 {
                    v___x_2779_ = v___x_2776_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2780_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2780_, 0, v_a_2774_);
                    v___x_2779_ = v_reuseFailAlloc_2780_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2779_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6___boxed(
    mut v_goal_2784_: *mut crate::leanh::LeanObject,
    mut v_as_2785_: *mut crate::leanh::LeanObject,
    mut v_sz_2786_: *mut crate::leanh::LeanObject,
    mut v_i_2787_: *mut crate::leanh::LeanObject,
    mut v_b_2788_: *mut crate::leanh::LeanObject,
    mut v___y_2789_: *mut crate::leanh::LeanObject,
    mut v___y_2790_: *mut crate::leanh::LeanObject,
    mut v___y_2791_: *mut crate::leanh::LeanObject,
    mut v___y_2792_: *mut crate::leanh::LeanObject,
    mut v___y_2793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_2794_: usize = 0;
    let mut v_i_boxed_2795_: usize = 0;
    let mut v_res_2796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_2794_ = crate::leanh::lean_unbox_usize(v_sz_2786_);
    crate::leanh::lean_dec(v_sz_2786_);
    v_i_boxed_2795_ = crate::leanh::lean_unbox_usize(v_i_2787_);
    crate::leanh::lean_dec(v_i_2787_);
    v_res_2796_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(v_goal_2784_, v_as_2785_, v_sz_boxed_2794_, v_i_boxed_2795_, v_b_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_);
    crate::leanh::lean_dec(v___y_2792_);
    crate::leanh::lean_dec_ref(v___y_2791_);
    crate::leanh::lean_dec(v___y_2790_);
    crate::leanh::lean_dec_ref(v___y_2789_);
    crate::leanh::lean_dec_ref(v_as_2785_);
    crate::leanh::lean_dec_ref(v_goal_2784_);
    return v_res_2796_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(
    mut v_goal_2797_: *mut crate::leanh::LeanObject,
    mut v_t_2798_: *mut crate::leanh::LeanObject,
    mut v_init_2799_: *mut crate::leanh::LeanObject,
    mut v___y_2800_: *mut crate::leanh::LeanObject,
    mut v___y_2801_: *mut crate::leanh::LeanObject,
    mut v___y_2802_: *mut crate::leanh::LeanObject,
    mut v___y_2803_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_2805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_2806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2811_: u8 = 0;
    let mut v_a_2812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2816_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2818_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_2819_: usize = 0;
    let mut v___x_2820_: usize = 0;
    let mut v___x_2821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2822_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2824_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2825_: u8 = 0;
    let mut v_fst_2826_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_2827_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_2831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2833_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2834_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2835_: u8 = 0;
    let mut v_a_2836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2838_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2839_: u8 = 0;
    let mut v___x_2841_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2843_: u8 = 0;
    let mut v_isSharedCheck_2844_: u8 = 0;
    let mut v_a_2845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2848_: u8 = 0;
    let mut v___x_2850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2852_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_2805_ = crate::leanh::lean_ctor_get(v_t_2798_, 0);
                v_tail_2806_ = crate::leanh::lean_ctor_get(v_t_2798_, 1);
                crate::leanh::lean_inc_ref(v_init_2799_);
                v___x_2807_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__5(v_init_2799_, v_goal_2797_, v_root_2805_, v_init_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
                crate::leanh::lean_dec_ref(v_init_2799_);
                if crate::leanh::lean_obj_tag(v___x_2807_) == 0 {
                    v_a_2808_ = crate::leanh::lean_ctor_get(v___x_2807_, 0);
                    v_isSharedCheck_2844_ = (!crate::leanh::lean_is_exclusive(v___x_2807_)) as u8;
                    if v_isSharedCheck_2844_ == 0 {
                        v___x_2810_ = v___x_2807_;
                        v_isShared_2811_ = v_isSharedCheck_2844_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2808_);
                        crate::leanh::lean_dec(v___x_2807_);
                        v___x_2810_ = crate::leanh::lean_box(0);
                        v_isShared_2811_ = v_isSharedCheck_2844_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2845_ = crate::leanh::lean_ctor_get(v___x_2807_, 0);
                    v_isSharedCheck_2852_ = (!crate::leanh::lean_is_exclusive(v___x_2807_)) as u8;
                    if v_isSharedCheck_2852_ == 0 {
                        v___x_2847_ = v___x_2807_;
                        v_isShared_2848_ = v_isSharedCheck_2852_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2845_);
                        crate::leanh::lean_dec(v___x_2807_);
                        v___x_2847_ = crate::leanh::lean_box(0);
                        v_isShared_2848_ = v_isSharedCheck_2852_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_2808_) == 0 {
                    v_a_2812_ = crate::leanh::lean_ctor_get(v_a_2808_, 0);
                    crate::leanh::lean_inc(v_a_2812_);
                    crate::leanh::lean_dec_ref_known(v_a_2808_, 1);
                    if v_isShared_2811_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2810_, 0, v_a_2812_);
                        v___x_2814_ = v___x_2810_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2815_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2812_);
                        v___x_2814_ = v_reuseFailAlloc_2815_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_2810_);
                    v_a_2816_ = crate::leanh::lean_ctor_get(v_a_2808_, 0);
                    crate::leanh::lean_inc(v_a_2816_);
                    crate::leanh::lean_dec_ref_known(v_a_2808_, 1);
                    v___x_2817_ = crate::leanh::lean_box(0);
                    v___x_2818_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_2818_, 0, v___x_2817_);
                    crate::leanh::lean_ctor_set(v___x_2818_, 1, v_a_2816_);
                    v_sz_2819_ = lean_array_size(v_tail_2806_);
                    v___x_2820_ = 0usize;
                    v___x_2821_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2_spec__6(v_goal_2797_, v_tail_2806_, v_sz_2819_, v___x_2820_, v___x_2818_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
                    if crate::leanh::lean_obj_tag(v___x_2821_) == 0 {
                        v_a_2822_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                        v_isSharedCheck_2835_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2821_)) as u8;
                        if v_isSharedCheck_2835_ == 0 {
                            v___x_2824_ = v___x_2821_;
                            v_isShared_2825_ = v_isSharedCheck_2835_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2822_);
                            crate::leanh::lean_dec(v___x_2821_);
                            v___x_2824_ = crate::leanh::lean_box(0);
                            v_isShared_2825_ = v_isSharedCheck_2835_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_2836_ = crate::leanh::lean_ctor_get(v___x_2821_, 0);
                        v_isSharedCheck_2843_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2821_)) as u8;
                        if v_isSharedCheck_2843_ == 0 {
                            v___x_2838_ = v___x_2821_;
                            v_isShared_2839_ = v_isSharedCheck_2843_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2836_);
                            crate::leanh::lean_dec(v___x_2821_);
                            v___x_2838_ = crate::leanh::lean_box(0);
                            v_isShared_2839_ = v_isSharedCheck_2843_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_2814_;
            }
            3 => {
                v_fst_2826_ = crate::leanh::lean_ctor_get(v_a_2822_, 0);
                if crate::leanh::lean_obj_tag(v_fst_2826_) == 0 {
                    v_snd_2827_ = crate::leanh::lean_ctor_get(v_a_2822_, 1);
                    crate::leanh::lean_inc(v_snd_2827_);
                    crate::leanh::lean_dec(v_a_2822_);
                    if v_isShared_2825_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2824_, 0, v_snd_2827_);
                        v___x_2829_ = v___x_2824_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_2830_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2830_, 0, v_snd_2827_);
                        v___x_2829_ = v_reuseFailAlloc_2830_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_2826_);
                    crate::leanh::lean_dec(v_a_2822_);
                    v_val_2831_ = crate::leanh::lean_ctor_get(v_fst_2826_, 0);
                    crate::leanh::lean_inc(v_val_2831_);
                    crate::leanh::lean_dec_ref_known(v_fst_2826_, 1);
                    if v_isShared_2825_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_2824_, 0, v_val_2831_);
                        v___x_2833_ = v___x_2824_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2834_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_2834_, 0, v_val_2831_);
                        v___x_2833_ = v_reuseFailAlloc_2834_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_2829_;
            }
            5 => {
                return v___x_2833_;
            }
            6 => {
                if v_isShared_2839_ == 0 {
                    v___x_2841_ = v___x_2838_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2842_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2842_, 0, v_a_2836_);
                    v___x_2841_ = v_reuseFailAlloc_2842_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2841_;
            }
            8 => {
                if v_isShared_2848_ == 0 {
                    v___x_2850_ = v___x_2847_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2851_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_a_2845_);
                    v___x_2850_ = v_reuseFailAlloc_2851_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2850_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2___boxed(
    mut v_goal_2853_: *mut crate::leanh::LeanObject,
    mut v_t_2854_: *mut crate::leanh::LeanObject,
    mut v_init_2855_: *mut crate::leanh::LeanObject,
    mut v___y_2856_: *mut crate::leanh::LeanObject,
    mut v___y_2857_: *mut crate::leanh::LeanObject,
    mut v___y_2858_: *mut crate::leanh::LeanObject,
    mut v___y_2859_: *mut crate::leanh::LeanObject,
    mut v___y_2860_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2861_ =
        l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(
            v_goal_2853_,
            v_t_2854_,
            v_init_2855_,
            v___y_2856_,
            v___y_2857_,
            v___y_2858_,
            v___y_2859_,
        );
    crate::leanh::lean_dec(v___y_2859_);
    crate::leanh::lean_dec_ref(v___y_2858_);
    crate::leanh::lean_dec(v___y_2857_);
    crate::leanh::lean_dec_ref(v___y_2856_);
    crate::leanh::lean_dec_ref(v_t_2854_);
    crate::leanh::lean_dec_ref(v_goal_2853_);
    return v_res_2861_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2862_ = crate::leanh::lean_box(0);
    v___x_2863_ = crate::leanh::lean_unsigned_to_nat(16);
    v___x_2864_ = lean_mk_array(v___x_2863_, v___x_2862_);
    return v___x_2864_;
}
pub unsafe fn _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_2865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_2867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2865_ = crate::leanh::lean_obj_once(
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0),
        core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0_once),
        _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__0,
    );
    v___x_2866_ = crate::leanh::lean_unsigned_to_nat(0);
    v_model_2867_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
    crate::leanh::lean_ctor_set(v_model_2867_, 0, v___x_2866_);
    crate::leanh::lean_ctor_set(v_model_2867_, 1, v___x_2865_);
    return v_model_2867_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkModel(
    mut v_goal_2876_: *mut crate::leanh::LeanObject,
    mut v_a_2877_: *mut crate::leanh::LeanObject,
    mut v_a_2878_: *mut crate::leanh::LeanObject,
    mut v_a_2879_: *mut crate::leanh::LeanObject,
    mut v_a_2880_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_toGoalState_2882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_exprs_2883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_model_2884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2896_: u8 = 0;
    let mut v___x_2898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_unused_2901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_2902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2904_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2905_: u8 = 0;
    let mut v___x_2907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2909_: u8 = 0;
    let mut v_a_2910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2913_: u8 = 0;
    let mut v___x_2915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2917_: u8 = 0;
    let mut v_a_2918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_2921_: u8 = 0;
    let mut v___x_2923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2925_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_toGoalState_2882_ = crate::leanh::lean_ctor_get(v_goal_2876_, 0);
                v_exprs_2883_ = crate::leanh::lean_ctor_get(v_toGoalState_2882_, 2);
                v_model_2884_ = crate::leanh::lean_obj_once(
                    core::ptr::addr_of_mut!(l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1),
                    core::ptr::addr_of_mut!(
                        l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1_once
                    ),
                    _init_l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__1,
                );
                v___x_2885_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__1(v_goal_2876_, v_exprs_2883_, v_model_2884_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
                if crate::leanh::lean_obj_tag(v___x_2885_) == 0 {
                    v_a_2886_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                    crate::leanh::lean_inc(v_a_2886_);
                    crate::leanh::lean_dec_ref_known(v___x_2885_, 1);
                    v___x_2887_ = l_Lean_PersistentArray_forIn___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__2(v_goal_2876_, v_exprs_2883_, v_a_2886_, v_a_2877_, v_a_2878_, v_a_2879_, v_a_2880_);
                    if crate::leanh::lean_obj_tag(v___x_2887_) == 0 {
                        v_a_2888_ = crate::leanh::lean_ctor_get(v___x_2887_, 0);
                        crate::leanh::lean_inc(v_a_2888_);
                        crate::leanh::lean_dec_ref_known(v___x_2887_, 1);
                        v___x_2889_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__2;
                        v___x_2890_ = l_Lean_Meta_Grind_Arith_finalizeModel(
                            v_goal_2876_,
                            v___x_2889_,
                            v_a_2888_,
                            v_a_2877_,
                            v_a_2878_,
                            v_a_2879_,
                            v_a_2880_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_2890_) == 0 {
                            v_a_2891_ = crate::leanh::lean_ctor_get(v___x_2890_, 0);
                            crate::leanh::lean_inc(v_a_2891_);
                            crate::leanh::lean_dec_ref_known(v___x_2890_, 1);
                            v___x_2892_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel___closed__6;
                            v___x_2893_ = l_Lean_Meta_Grind_Arith_traceModel(
                                v___x_2892_,
                                v_a_2891_,
                                v_a_2877_,
                                v_a_2878_,
                                v_a_2879_,
                                v_a_2880_,
                            );
                            if crate::leanh::lean_obj_tag(v___x_2893_) == 0 {
                                v_isSharedCheck_2900_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2893_)) as u8;
                                if v_isSharedCheck_2900_ == 0 {
                                    v_unused_2901_ = crate::leanh::lean_ctor_get(v___x_2893_, 0);
                                    crate::leanh::lean_dec(v_unused_2901_);
                                    v___x_2895_ = v___x_2893_;
                                    v_isShared_2896_ = v_isSharedCheck_2900_;
                                    state = 1;
                                    continue;
                                } else {
                                    crate::leanh::lean_dec(v___x_2893_);
                                    v___x_2895_ = crate::leanh::lean_box(0);
                                    v_isShared_2896_ = v_isSharedCheck_2900_;
                                    state = 1;
                                    continue;
                                }
                            } else {
                                crate::leanh::lean_dec(v_a_2891_);
                                v_a_2902_ = crate::leanh::lean_ctor_get(v___x_2893_, 0);
                                v_isSharedCheck_2909_ =
                                    (!crate::leanh::lean_is_exclusive(v___x_2893_)) as u8;
                                if v_isSharedCheck_2909_ == 0 {
                                    v___x_2904_ = v___x_2893_;
                                    v_isShared_2905_ = v_isSharedCheck_2909_;
                                    state = 3;
                                    continue;
                                } else {
                                    crate::leanh::lean_inc(v_a_2902_);
                                    crate::leanh::lean_dec(v___x_2893_);
                                    v___x_2904_ = crate::leanh::lean_box(0);
                                    v_isShared_2905_ = v_isSharedCheck_2909_;
                                    state = 3;
                                    continue;
                                }
                            }
                        } else {
                            return v___x_2890_;
                        }
                    } else {
                        v_a_2910_ = crate::leanh::lean_ctor_get(v___x_2887_, 0);
                        v_isSharedCheck_2917_ =
                            (!crate::leanh::lean_is_exclusive(v___x_2887_)) as u8;
                        if v_isSharedCheck_2917_ == 0 {
                            v___x_2912_ = v___x_2887_;
                            v_isShared_2913_ = v_isSharedCheck_2917_;
                            state = 5;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_2910_);
                            crate::leanh::lean_dec(v___x_2887_);
                            v___x_2912_ = crate::leanh::lean_box(0);
                            v_isShared_2913_ = v_isSharedCheck_2917_;
                            state = 5;
                            continue;
                        }
                    }
                } else {
                    v_a_2918_ = crate::leanh::lean_ctor_get(v___x_2885_, 0);
                    v_isSharedCheck_2925_ = (!crate::leanh::lean_is_exclusive(v___x_2885_)) as u8;
                    if v_isSharedCheck_2925_ == 0 {
                        v___x_2920_ = v___x_2885_;
                        v_isShared_2921_ = v_isSharedCheck_2925_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_2918_);
                        crate::leanh::lean_dec(v___x_2885_);
                        v___x_2920_ = crate::leanh::lean_box(0);
                        v_isShared_2921_ = v_isSharedCheck_2925_;
                        state = 7;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2896_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_2895_, 0, v_a_2891_);
                    v___x_2898_ = v___x_2895_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2899_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_a_2891_);
                    v___x_2898_ = v_reuseFailAlloc_2899_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2898_;
            }
            3 => {
                if v_isShared_2905_ == 0 {
                    v___x_2907_ = v___x_2904_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2908_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2902_);
                    v___x_2907_ = v_reuseFailAlloc_2908_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2907_;
            }
            5 => {
                if v_isShared_2913_ == 0 {
                    v___x_2915_ = v___x_2912_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2916_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2916_, 0, v_a_2910_);
                    v___x_2915_ = v_reuseFailAlloc_2916_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2915_;
            }
            7 => {
                if v_isShared_2921_ == 0 {
                    v___x_2923_ = v___x_2920_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_2924_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_a_2918_);
                    v___x_2923_ = v_reuseFailAlloc_2924_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_2923_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Cutsat_mkModel___boxed(
    mut v_goal_2926_: *mut crate::leanh::LeanObject,
    mut v_a_2927_: *mut crate::leanh::LeanObject,
    mut v_a_2928_: *mut crate::leanh::LeanObject,
    mut v_a_2929_: *mut crate::leanh::LeanObject,
    mut v_a_2930_: *mut crate::leanh::LeanObject,
    mut v_a_2931_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2932_ = l_Lean_Meta_Grind_Arith_Cutsat_mkModel(
        v_goal_2926_,
        v_a_2927_,
        v_a_2928_,
        v_a_2929_,
        v_a_2930_,
    );
    crate::leanh::lean_dec(v_a_2930_);
    crate::leanh::lean_dec_ref(v_a_2929_);
    crate::leanh::lean_dec(v_a_2928_);
    crate::leanh::lean_dec_ref(v_a_2927_);
    crate::leanh::lean_dec_ref(v_goal_2926_);
    return v_res_2932_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(
    mut v_00_u03b2_2933_: *mut crate::leanh::LeanObject,
    mut v_m_2934_: *mut crate::leanh::LeanObject,
    mut v_a_2935_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2936_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___redArg(v_m_2934_, v_a_2935_);
    return v___x_2936_;
}
pub unsafe fn l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0___boxed(
    mut v_00_u03b2_2937_: *mut crate::leanh::LeanObject,
    mut v_m_2938_: *mut crate::leanh::LeanObject,
    mut v_a_2939_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2940_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0(v_00_u03b2_2937_, v_m_2938_, v_a_2939_);
    crate::leanh::lean_dec_ref(v_a_2939_);
    crate::leanh::lean_dec_ref(v_m_2938_);
    return v_res_2940_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(
    mut v_00_u03b2_2941_: *mut crate::leanh::LeanObject,
    mut v_a_2942_: *mut crate::leanh::LeanObject,
    mut v_x_2943_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_2944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_2944_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___redArg(v_a_2942_, v_x_2943_);
    return v___x_2944_;
}
pub unsafe fn l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0___boxed(
    mut v_00_u03b2_2945_: *mut crate::leanh::LeanObject,
    mut v_a_2946_: *mut crate::leanh::LeanObject,
    mut v_x_2947_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_2948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_2948_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Grind_Arith_Cutsat_mkModel_spec__0_spec__0(v_00_u03b2_2945_, v_a_2946_, v_x_2947_);
    crate::leanh::lean_dec(v_x_2947_);
    crate::leanh::lean_dec_ref(v_a_2946_);
    return v_res_2948_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(
    builtin: u8,
) -> *mut crate::leanh::LeanObject {
    let mut res: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_ModelUtil(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Model(builtin);
}
