// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Inv
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.RingM Lean.Meta.Sym.Arith.Poly
use crate::r#gen::Init::Grind::Ring::CommSolver::l_Lean_Grind_CommRing_Poly_isSorted;
use crate::r#gen::Init::Prelude::l_instInhabitedForall___redArg___lam__0___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Meta::Sym::Arith::Poly::{
    initialize_Lean_Meta_Sym_Arith_Poly, l_Lean_Grind_CommRing_Poly_checkCoeffs,
    l_Lean_Grind_CommRing_Poly_checkNoUnitMon, runtime_initialize_Lean_Meta_Sym_Arith_Poly,
};
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::RingM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
    l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::CommRing::Types::{
    l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p,
    l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_instInhabitedGoalM;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::UInt::BasicAux::{
    lean_usize_add, lean_usize_dec_lt, lean_usize_of_nat,
};
use crate::lean_imports_rs::Init::Prelude::{
    lean_array_fget_borrowed, lean_array_get_size, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_panic_fn_borrowed, lean_usize_dec_eq,
};
use crate::leanh::{
    LeanArrayObject, LeanClosureObject, LeanCtorObject, LeanExternalClass, LeanExternalObject,
    LeanObject, LeanOnceCell, LeanPromiseObject, LeanRefObject, LeanScalarArray, LeanStringObject,
    LeanTaskObject, LeanThunkObject, lean_alloc_closure, lean_alloc_ctor, lean_apply_12,
    lean_apply_14, lean_apply_15, lean_box, lean_closure_set, lean_ctor_get, lean_ctor_get_uint8,
    lean_ctor_set, lean_ctor_set_tag, lean_ctor_set_uint8, lean_dec, lean_dec_ref,
    lean_dec_ref_known, lean_del_object, lean_inc, lean_inc_ref, lean_inc_ref_n,
    lean_io_result_is_error, lean_io_result_mk_ok, lean_is_exclusive, lean_obj_once, lean_obj_tag,
    lean_unbox_usize, lean_unsigned_to_nat,
};
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1_value: LeanStringObject<94> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 99, 104, 101, 99, 107, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 120, 112, 114, 32, 101, 120, 112, 114, 39, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110, 117, 109, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0_value: LeanStringObject<94> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 99, 104, 101, 99, 107, 80, 111, 108, 121, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1_value: LeanStringObject<43> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 43, m_capacity: 43, m_length: 42, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 40, 112, 32, 109, 97, 116, 99, 104, 101, 115, 32, 46, 110, 117, 109, 32, 95, 41, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 99, 104, 101, 99, 107, 67, 111, 101, 102, 102, 115, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7_value: LeanStringObject<41> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 41, m_capacity: 41, m_length: 40, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 99, 104, 101, 99, 107, 78, 111, 85, 110, 105, 116, 77, 111, 110, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0_value: LeanStringObject<47> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 47, m_capacity: 47, m_length: 46, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 99, 104, 101, 99, 107, 73, 110, 118, 97, 114, 105, 97, 110, 116, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1_value: LeanStringObject<126> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 67, 111, 109, 109, 82, 105, 110, 103, 46, 73, 110, 118, 46, 51, 49, 49, 57, 50, 50, 53, 55, 54, 52, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 48, 46, 48, 32, 41, 32, 61, 61, 32, 114, 105, 110, 103, 73, 100, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_1699_: *mut LeanObject = core::ptr::null_mut();
    v___x_1699_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_1699_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(
    mut v_msg_1700_: *mut LeanObject,
    mut v___y_1701_: *mut LeanObject,
    mut v___y_1702_: *mut LeanObject,
    mut v___y_1703_: *mut LeanObject,
    mut v___y_1704_: *mut LeanObject,
    mut v___y_1705_: *mut LeanObject,
    mut v___y_1706_: *mut LeanObject,
    mut v___y_1707_: *mut LeanObject,
    mut v___y_1708_: *mut LeanObject,
    mut v___y_1709_: *mut LeanObject,
    mut v___y_1710_: *mut LeanObject,
    mut v___y_1711_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1713_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6983__overap_1715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1716_: *mut LeanObject = core::ptr::null_mut();
    v___x_1713_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___closed__0);
    v___f_1714_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1714_, 0, v___x_1713_);
    v___x_6983__overap_1715_ = lean_panic_fn_borrowed(v___f_1714_, v_msg_1700_);
    lean_dec_ref(v___f_1714_);
    lean_inc(v___y_1711_);
    lean_inc_ref(v___y_1710_);
    lean_inc(v___y_1709_);
    lean_inc_ref(v___y_1708_);
    lean_inc(v___y_1707_);
    lean_inc_ref(v___y_1706_);
    lean_inc(v___y_1705_);
    lean_inc_ref(v___y_1704_);
    lean_inc(v___y_1703_);
    lean_inc(v___y_1702_);
    lean_inc_ref(v___y_1701_);
    v___x_1716_ = lean_apply_12(
        v___x_6983__overap_1715_,
        v___y_1701_,
        v___y_1702_,
        v___y_1703_,
        v___y_1704_,
        v___y_1705_,
        v___y_1706_,
        v___y_1707_,
        v___y_1708_,
        v___y_1709_,
        v___y_1710_,
        v___y_1711_,
        lean_box(0),
    );
    return v___x_1716_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0___boxed(
    mut v_msg_1717_: *mut LeanObject,
    mut v___y_1718_: *mut LeanObject,
    mut v___y_1719_: *mut LeanObject,
    mut v___y_1720_: *mut LeanObject,
    mut v___y_1721_: *mut LeanObject,
    mut v___y_1722_: *mut LeanObject,
    mut v___y_1723_: *mut LeanObject,
    mut v___y_1724_: *mut LeanObject,
    mut v___y_1725_: *mut LeanObject,
    mut v___y_1726_: *mut LeanObject,
    mut v___y_1727_: *mut LeanObject,
    mut v___y_1728_: *mut LeanObject,
    mut v___y_1729_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1730_: *mut LeanObject = core::ptr::null_mut();
    v_res_1730_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v_msg_1717_, v___y_1718_, v___y_1719_, v___y_1720_, v___y_1721_, v___y_1722_, v___y_1723_, v___y_1724_, v___y_1725_, v___y_1726_, v___y_1727_, v___y_1728_);
    lean_dec(v___y_1728_);
    lean_dec_ref(v___y_1727_);
    lean_dec(v___y_1726_);
    lean_dec_ref(v___y_1725_);
    lean_dec(v___y_1724_);
    lean_dec_ref(v___y_1723_);
    lean_dec(v___y_1722_);
    lean_dec_ref(v___y_1721_);
    lean_dec(v___y_1720_);
    lean_dec(v___y_1719_);
    lean_dec_ref(v___y_1718_);
    return v_res_1730_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_1731_: *mut LeanObject = core::ptr::null_mut();
    v___x_1731_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_1731_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(
    mut v_msg_1732_: *mut LeanObject,
    mut v___y_1733_: *mut LeanObject,
    mut v___y_1734_: *mut LeanObject,
    mut v___y_1735_: *mut LeanObject,
    mut v___y_1736_: *mut LeanObject,
    mut v___y_1737_: *mut LeanObject,
    mut v___y_1738_: *mut LeanObject,
    mut v___y_1739_: *mut LeanObject,
    mut v___y_1740_: *mut LeanObject,
    mut v___y_1741_: *mut LeanObject,
    mut v___y_1742_: *mut LeanObject,
    mut v___y_1743_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1745_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_1746_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7001__overap_1747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1748_: *mut LeanObject = core::ptr::null_mut();
    v___x_1745_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___closed__0);
    v___f_1746_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_1746_, 0, v___x_1745_);
    v___x_7001__overap_1747_ = lean_panic_fn_borrowed(v___f_1746_, v_msg_1732_);
    lean_dec_ref(v___f_1746_);
    lean_inc(v___y_1743_);
    lean_inc_ref(v___y_1742_);
    lean_inc(v___y_1741_);
    lean_inc_ref(v___y_1740_);
    lean_inc(v___y_1739_);
    lean_inc_ref(v___y_1738_);
    lean_inc(v___y_1737_);
    lean_inc_ref(v___y_1736_);
    lean_inc(v___y_1735_);
    lean_inc(v___y_1734_);
    lean_inc_ref(v___y_1733_);
    v___x_1748_ = lean_apply_12(
        v___x_7001__overap_1747_,
        v___y_1733_,
        v___y_1734_,
        v___y_1735_,
        v___y_1736_,
        v___y_1737_,
        v___y_1738_,
        v___y_1739_,
        v___y_1740_,
        v___y_1741_,
        v___y_1742_,
        v___y_1743_,
        lean_box(0),
    );
    return v___x_1748_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1___boxed(
    mut v_msg_1749_: *mut LeanObject,
    mut v___y_1750_: *mut LeanObject,
    mut v___y_1751_: *mut LeanObject,
    mut v___y_1752_: *mut LeanObject,
    mut v___y_1753_: *mut LeanObject,
    mut v___y_1754_: *mut LeanObject,
    mut v___y_1755_: *mut LeanObject,
    mut v___y_1756_: *mut LeanObject,
    mut v___y_1757_: *mut LeanObject,
    mut v___y_1758_: *mut LeanObject,
    mut v___y_1759_: *mut LeanObject,
    mut v___y_1760_: *mut LeanObject,
    mut v___y_1761_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1762_: *mut LeanObject = core::ptr::null_mut();
    v_res_1762_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(v_msg_1749_, v___y_1750_, v___y_1751_, v___y_1752_, v___y_1753_, v___y_1754_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_, v___y_1759_, v___y_1760_);
    lean_dec(v___y_1760_);
    lean_dec_ref(v___y_1759_);
    lean_dec(v___y_1758_);
    lean_dec_ref(v___y_1757_);
    lean_dec(v___y_1756_);
    lean_dec_ref(v___y_1755_);
    lean_dec(v___y_1754_);
    lean_dec_ref(v___y_1753_);
    lean_dec(v___y_1752_);
    lean_dec(v___y_1751_);
    lean_dec_ref(v___y_1750_);
    return v_res_1762_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_1766_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1767_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1768_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1769_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1771_: *mut LeanObject = core::ptr::null_mut();
    v___x_1766_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__2;
    v___x_1767_ = lean_unsigned_to_nat(6);
    v___x_1768_ = lean_unsigned_to_nat(21);
    v___x_1769_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1;
    v___x_1770_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_1771_ = l_mkPanicMessageWithDecl(
        v___x_1770_,
        v___x_1769_,
        v___x_1768_,
        v___x_1767_,
        v___x_1766_,
    );
    return v___x_1771_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5()
-> *mut LeanObject {
    let mut v___x_1773_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1774_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1775_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1778_: *mut LeanObject = core::ptr::null_mut();
    v___x_1773_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__4;
    v___x_1774_ = lean_unsigned_to_nat(6);
    v___x_1775_ = lean_unsigned_to_nat(19);
    v___x_1776_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1;
    v___x_1777_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_1778_ = l_mkPanicMessageWithDecl(
        v___x_1777_,
        v___x_1776_,
        v___x_1775_,
        v___x_1774_,
        v___x_1773_,
    );
    return v___x_1778_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(
    mut v_vars_1779_: *mut LeanObject,
    mut v_x_1780_: *mut LeanObject,
    mut v_____s_1781_: *mut LeanObject,
    mut v___y_1782_: *mut LeanObject,
    mut v___y_1783_: *mut LeanObject,
    mut v___y_1784_: *mut LeanObject,
    mut v___y_1785_: *mut LeanObject,
    mut v___y_1786_: *mut LeanObject,
    mut v___y_1787_: *mut LeanObject,
    mut v___y_1788_: *mut LeanObject,
    mut v___y_1789_: *mut LeanObject,
    mut v___y_1790_: *mut LeanObject,
    mut v___y_1791_: *mut LeanObject,
    mut v___y_1792_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1796_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1797_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_1799_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_1800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_1801_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1802_: u8 = 0;
    let mut v___x_1803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1807_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1808_: u8 = 0;
    let mut v___x_1810_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1812_: u8 = 0;
    let mut v___x_1813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1815_: u8 = 0;
    let mut v___x_1816_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1817_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_1799_ = lean_ctor_get(v_x_1780_, 0);
                v_snd_1800_ = lean_ctor_get(v_x_1780_, 1);
                v_size_1801_ = lean_ctor_get(v_vars_1779_, 2);
                v___x_1802_ = lean_nat_dec_lt(v_snd_1800_, v_size_1801_);
                if v___x_1802_ == 0 {
                    v___x_1803_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__3);
                    v___x_1804_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_1803_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
                    if lean_obj_tag(v___x_1804_) == 0 {
                        lean_dec_ref_known(v___x_1804_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
                        v_isSharedCheck_1812_ = (!lean_is_exclusive(v___x_1804_)) as u8;
                        if v_isSharedCheck_1812_ == 0 {
                            v___x_1807_ = v___x_1804_;
                            v_isShared_1808_ = v_isSharedCheck_1812_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_1805_);
                            lean_dec(v___x_1804_);
                            v___x_1807_ = lean_box(0);
                            v_isShared_1808_ = v_isSharedCheck_1812_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_1813_ = l_Lean_instInhabitedExpr;
                    v___x_1814_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_1813_,
                        v_vars_1779_,
                        v_snd_1800_,
                    );
                    v___x_1815_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_1799_,
                            v___x_1814_,
                        );
                    lean_dec(v___x_1814_);
                    if v___x_1815_ == 0 {
                        v___x_1816_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__5);
                        v___x_1817_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__1(v___x_1816_, v___y_1782_, v___y_1783_, v___y_1784_, v___y_1785_, v___y_1786_, v___y_1787_, v___y_1788_, v___y_1789_, v___y_1790_, v___y_1791_, v___y_1792_);
                        return v___x_1817_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_1795_ = lean_unsigned_to_nat(1);
                v___x_1796_ = lean_nat_add(v_____s_1781_, v___x_1795_);
                v___x_1797_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_1797_, 0, v___x_1796_);
                v___x_1798_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1798_, 0, v___x_1797_);
                return v___x_1798_;
            }
            2 => {
                if v_isShared_1808_ == 0 {
                    v___x_1810_ = v___x_1807_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_1811_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_1811_, 0, v_a_1805_);
                    v___x_1810_ = v_reuseFailAlloc_1811_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_1810_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed(
    mut v_vars_1818_: *mut LeanObject,
    mut v_x_1819_: *mut LeanObject,
    mut v_____s_1820_: *mut LeanObject,
    mut v___y_1821_: *mut LeanObject,
    mut v___y_1822_: *mut LeanObject,
    mut v___y_1823_: *mut LeanObject,
    mut v___y_1824_: *mut LeanObject,
    mut v___y_1825_: *mut LeanObject,
    mut v___y_1826_: *mut LeanObject,
    mut v___y_1827_: *mut LeanObject,
    mut v___y_1828_: *mut LeanObject,
    mut v___y_1829_: *mut LeanObject,
    mut v___y_1830_: *mut LeanObject,
    mut v___y_1831_: *mut LeanObject,
    mut v___y_1832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1833_: *mut LeanObject = core::ptr::null_mut();
    v_res_1833_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0(v_vars_1818_, v_x_1819_, v_____s_1820_, v___y_1821_, v___y_1822_, v___y_1823_, v___y_1824_, v___y_1825_, v___y_1826_, v___y_1827_, v___y_1828_, v___y_1829_, v___y_1830_, v___y_1831_);
    lean_dec(v___y_1831_);
    lean_dec_ref(v___y_1830_);
    lean_dec(v___y_1829_);
    lean_dec_ref(v___y_1828_);
    lean_dec(v___y_1827_);
    lean_dec_ref(v___y_1826_);
    lean_dec(v___y_1825_);
    lean_dec_ref(v___y_1824_);
    lean_dec(v___y_1823_);
    lean_dec(v___y_1822_);
    lean_dec_ref(v___y_1821_);
    lean_dec(v_____s_1820_);
    lean_dec_ref(v_x_1819_);
    lean_dec_ref(v_vars_1818_);
    return v_res_1833_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(
    mut v_f_1834_: *mut LeanObject,
    mut v_keys_1835_: *mut LeanObject,
    mut v_vals_1836_: *mut LeanObject,
    mut v_i_1837_: *mut LeanObject,
    mut v_acc_1838_: *mut LeanObject,
    mut v___y_1839_: *mut LeanObject,
    mut v___y_1840_: *mut LeanObject,
    mut v___y_1841_: *mut LeanObject,
    mut v___y_1842_: *mut LeanObject,
    mut v___y_1843_: *mut LeanObject,
    mut v___y_1844_: *mut LeanObject,
    mut v___y_1845_: *mut LeanObject,
    mut v___y_1846_: *mut LeanObject,
    mut v___y_1847_: *mut LeanObject,
    mut v___y_1848_: *mut LeanObject,
    mut v___y_1849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_1851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1852_: u8 = 0;
    let mut v___x_1853_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_1855_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_1856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1857_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1858_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1861_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1851_ = lean_array_get_size(v_keys_1835_);
                v___x_1852_ = lean_nat_dec_lt(v_i_1837_, v___x_1851_);
                if v___x_1852_ == 0 {
                    lean_dec(v_i_1837_);
                    lean_dec_ref(v_f_1834_);
                    v___x_1853_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1853_, 0, v_acc_1838_);
                    v___x_1854_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1854_, 0, v___x_1853_);
                    return v___x_1854_;
                } else {
                    v_k_1855_ = lean_array_fget_borrowed(v_keys_1835_, v_i_1837_);
                    v_v_1856_ = lean_array_fget_borrowed(v_vals_1836_, v_i_1837_);
                    lean_inc_ref(v_f_1834_);
                    lean_inc(v___y_1849_);
                    lean_inc_ref(v___y_1848_);
                    lean_inc(v___y_1847_);
                    lean_inc_ref(v___y_1846_);
                    lean_inc(v___y_1845_);
                    lean_inc_ref(v___y_1844_);
                    lean_inc(v___y_1843_);
                    lean_inc_ref(v___y_1842_);
                    lean_inc(v___y_1841_);
                    lean_inc(v___y_1840_);
                    lean_inc_ref(v___y_1839_);
                    lean_inc(v_v_1856_);
                    lean_inc(v_k_1855_);
                    v___x_1857_ = lean_apply_15(
                        v_f_1834_,
                        v_acc_1838_,
                        v_k_1855_,
                        v_v_1856_,
                        v___y_1839_,
                        v___y_1840_,
                        v___y_1841_,
                        v___y_1842_,
                        v___y_1843_,
                        v___y_1844_,
                        v___y_1845_,
                        v___y_1846_,
                        v___y_1847_,
                        v___y_1848_,
                        v___y_1849_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_1857_) == 0 {
                        v_a_1858_ = lean_ctor_get(v___x_1857_, 0);
                        lean_inc(v_a_1858_);
                        if lean_obj_tag(v_a_1858_) == 0 {
                            lean_dec_ref_known(v_a_1858_, 1);
                            lean_dec(v_i_1837_);
                            lean_dec_ref(v_f_1834_);
                            return v___x_1857_;
                        } else {
                            lean_dec_ref_known(v___x_1857_, 1);
                            v_a_1859_ = lean_ctor_get(v_a_1858_, 0);
                            lean_inc(v_a_1859_);
                            lean_dec_ref_known(v_a_1858_, 1);
                            v___x_1860_ = lean_unsigned_to_nat(1);
                            v___x_1861_ = lean_nat_add(v_i_1837_, v___x_1860_);
                            lean_dec(v_i_1837_);
                            v_i_1837_ = v___x_1861_;
                            v_acc_1838_ = v_a_1859_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_1837_);
                        lean_dec_ref(v_f_1834_);
                        return v___x_1857_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_1863_: *mut LeanObject = *_args.add(0);
    let mut v_keys_1864_: *mut LeanObject = *_args.add(1);
    let mut v_vals_1865_: *mut LeanObject = *_args.add(2);
    let mut v_i_1866_: *mut LeanObject = *_args.add(3);
    let mut v_acc_1867_: *mut LeanObject = *_args.add(4);
    let mut v___y_1868_: *mut LeanObject = *_args.add(5);
    let mut v___y_1869_: *mut LeanObject = *_args.add(6);
    let mut v___y_1870_: *mut LeanObject = *_args.add(7);
    let mut v___y_1871_: *mut LeanObject = *_args.add(8);
    let mut v___y_1872_: *mut LeanObject = *_args.add(9);
    let mut v___y_1873_: *mut LeanObject = *_args.add(10);
    let mut v___y_1874_: *mut LeanObject = *_args.add(11);
    let mut v___y_1875_: *mut LeanObject = *_args.add(12);
    let mut v___y_1876_: *mut LeanObject = *_args.add(13);
    let mut v___y_1877_: *mut LeanObject = *_args.add(14);
    let mut v___y_1878_: *mut LeanObject = *_args.add(15);
    let mut v___y_1879_: *mut LeanObject = *_args.add(16);
    let mut v_res_1880_: *mut LeanObject = core::ptr::null_mut();
    v_res_1880_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_1863_, v_keys_1864_, v_vals_1865_, v_i_1866_, v_acc_1867_, v___y_1868_, v___y_1869_, v___y_1870_, v___y_1871_, v___y_1872_, v___y_1873_, v___y_1874_, v___y_1875_, v___y_1876_, v___y_1877_, v___y_1878_);
    lean_dec(v___y_1878_);
    lean_dec_ref(v___y_1877_);
    lean_dec(v___y_1876_);
    lean_dec_ref(v___y_1875_);
    lean_dec(v___y_1874_);
    lean_dec_ref(v___y_1873_);
    lean_dec(v___y_1872_);
    lean_dec_ref(v___y_1871_);
    lean_dec(v___y_1870_);
    lean_dec(v___y_1869_);
    lean_dec_ref(v___y_1868_);
    lean_dec_ref(v_vals_1865_);
    lean_dec_ref(v_keys_1864_);
    return v_res_1880_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(
    mut v_f_1881_: *mut LeanObject,
    mut v_x_1882_: *mut LeanObject,
    mut v_x_1883_: *mut LeanObject,
    mut v___y_1884_: *mut LeanObject,
    mut v___y_1885_: *mut LeanObject,
    mut v___y_1886_: *mut LeanObject,
    mut v___y_1887_: *mut LeanObject,
    mut v___y_1888_: *mut LeanObject,
    mut v___y_1889_: *mut LeanObject,
    mut v___y_1890_: *mut LeanObject,
    mut v___y_1891_: *mut LeanObject,
    mut v___y_1892_: *mut LeanObject,
    mut v___y_1893_: *mut LeanObject,
    mut v___y_1894_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_1896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_1899_: u8 = 0;
    let mut v___x_1900_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1902_: u8 = 0;
    let mut v___x_1904_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1905_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1907_: u8 = 0;
    let mut v___x_1909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1910_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_1911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1912_: usize = 0;
    let mut v___x_1913_: usize = 0;
    let mut v___x_1914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1915_: usize = 0;
    let mut v___x_1916_: usize = 0;
    let mut v___x_1917_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_1918_: u8 = 0;
    let mut v_ks_1919_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_1920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1922_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_1882_) == 0 {
                    v_es_1896_ = lean_ctor_get(v_x_1882_, 0);
                    v_isSharedCheck_1918_ = (!lean_is_exclusive(v_x_1882_)) as u8;
                    if v_isSharedCheck_1918_ == 0 {
                        v___x_1898_ = v_x_1882_;
                        v_isShared_1899_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_1896_);
                        lean_dec(v_x_1882_);
                        v___x_1898_ = lean_box(0);
                        v_isShared_1899_ = v_isSharedCheck_1918_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_1919_ = lean_ctor_get(v_x_1882_, 0);
                    lean_inc_ref(v_ks_1919_);
                    v_vs_1920_ = lean_ctor_get(v_x_1882_, 1);
                    lean_inc_ref(v_vs_1920_);
                    lean_dec_ref_known(v_x_1882_, 2);
                    v___x_1921_ = lean_unsigned_to_nat(0);
                    v___x_1922_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_1881_, v_ks_1919_, v_vs_1920_, v___x_1921_, v_x_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
                    lean_dec_ref(v_vs_1920_);
                    lean_dec_ref(v_ks_1919_);
                    return v___x_1922_;
                }
            }
            1 => {
                v___x_1900_ = lean_unsigned_to_nat(0);
                v___x_1901_ = lean_array_get_size(v_es_1896_);
                v___x_1902_ = lean_nat_dec_lt(v___x_1900_, v___x_1901_);
                if v___x_1902_ == 0 {
                    lean_dec_ref(v_es_1896_);
                    lean_dec_ref(v_f_1881_);
                    if v_isShared_1899_ == 0 {
                        lean_ctor_set_tag(v___x_1898_, 1);
                        lean_ctor_set(v___x_1898_, 0, v_x_1883_);
                        v___x_1904_ = v___x_1898_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_1906_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_1906_, 0, v_x_1883_);
                        v___x_1904_ = v_reuseFailAlloc_1906_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_1907_ = lean_nat_dec_le(v___x_1901_, v___x_1901_);
                    if v___x_1907_ == 0 {
                        if v___x_1902_ == 0 {
                            lean_dec_ref(v_es_1896_);
                            lean_dec_ref(v_f_1881_);
                            if v_isShared_1899_ == 0 {
                                lean_ctor_set_tag(v___x_1898_, 1);
                                lean_ctor_set(v___x_1898_, 0, v_x_1883_);
                                v___x_1909_ = v___x_1898_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_1911_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_1911_, 0, v_x_1883_);
                                v___x_1909_ = v_reuseFailAlloc_1911_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_1898_);
                            v___x_1912_ = 0usize;
                            v___x_1913_ = lean_usize_of_nat(v___x_1901_);
                            v___x_1914_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_1881_, v_es_1896_, v___x_1912_, v___x_1913_, v_x_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
                            lean_dec_ref(v_es_1896_);
                            return v___x_1914_;
                        }
                    } else {
                        lean_del_object(v___x_1898_);
                        v___x_1915_ = 0usize;
                        v___x_1916_ = lean_usize_of_nat(v___x_1901_);
                        v___x_1917_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_1881_, v_es_1896_, v___x_1915_, v___x_1916_, v_x_1883_, v___y_1884_, v___y_1885_, v___y_1886_, v___y_1887_, v___y_1888_, v___y_1889_, v___y_1890_, v___y_1891_, v___y_1892_, v___y_1893_, v___y_1894_);
                        lean_dec_ref(v_es_1896_);
                        return v___x_1917_;
                    }
                }
            }
            2 => {
                v___x_1905_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1905_, 0, v___x_1904_);
                return v___x_1905_;
            }
            3 => {
                v___x_1910_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_1910_, 0, v___x_1909_);
                return v___x_1910_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(
    mut v_f_1923_: *mut LeanObject,
    mut v_as_1924_: *mut LeanObject,
    mut v_i_1925_: usize,
    mut v_stop_1926_: usize,
    mut v_b_1927_: *mut LeanObject,
    mut v___y_1928_: *mut LeanObject,
    mut v___y_1929_: *mut LeanObject,
    mut v___y_1930_: *mut LeanObject,
    mut v___y_1931_: *mut LeanObject,
    mut v___y_1932_: *mut LeanObject,
    mut v___y_1933_: *mut LeanObject,
    mut v___y_1934_: *mut LeanObject,
    mut v___y_1935_: *mut LeanObject,
    mut v___y_1936_: *mut LeanObject,
    mut v___y_1937_: *mut LeanObject,
    mut v___y_1938_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_1941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1942_: usize = 0;
    let mut v___x_1943_: usize = 0;
    let mut v___y_1946_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1947_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_1948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1949_: u8 = 0;
    let mut v___x_1950_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_1951_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_1952_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1953_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_1954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1955_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1956_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_1957_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_1949_ = lean_usize_dec_eq(v_i_1925_, v_stop_1926_);
                if v___x_1949_ == 0 {
                    v___x_1950_ = lean_array_uget_borrowed(v_as_1924_, v_i_1925_);
                    match lean_obj_tag(v___x_1950_) {
                        0 => {
                            v_key_1951_ = lean_ctor_get(v___x_1950_, 0);
                            v_val_1952_ = lean_ctor_get(v___x_1950_, 1);
                            lean_inc_ref(v_f_1923_);
                            lean_inc(v___y_1938_);
                            lean_inc_ref(v___y_1937_);
                            lean_inc(v___y_1936_);
                            lean_inc_ref(v___y_1935_);
                            lean_inc(v___y_1934_);
                            lean_inc_ref(v___y_1933_);
                            lean_inc(v___y_1932_);
                            lean_inc_ref(v___y_1931_);
                            lean_inc(v___y_1930_);
                            lean_inc(v___y_1929_);
                            lean_inc_ref(v___y_1928_);
                            lean_inc(v_val_1952_);
                            lean_inc(v_key_1951_);
                            v___x_1953_ = lean_apply_15(
                                v_f_1923_,
                                v_b_1927_,
                                v_key_1951_,
                                v_val_1952_,
                                v___y_1928_,
                                v___y_1929_,
                                v___y_1930_,
                                v___y_1931_,
                                v___y_1932_,
                                v___y_1933_,
                                v___y_1934_,
                                v___y_1935_,
                                v___y_1936_,
                                v___y_1937_,
                                v___y_1938_,
                                lean_box(0),
                            );
                            v___y_1946_ = v___x_1953_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_1954_ = lean_ctor_get(v___x_1950_, 0);
                            lean_inc(v_node_1954_);
                            lean_inc_ref(v_f_1923_);
                            v___x_1955_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_1923_, v_node_1954_, v_b_1927_, v___y_1928_, v___y_1929_, v___y_1930_, v___y_1931_, v___y_1932_, v___y_1933_, v___y_1934_, v___y_1935_, v___y_1936_, v___y_1937_, v___y_1938_);
                            v___y_1946_ = v___x_1955_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_1941_ = v_b_1927_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_1923_);
                    v___x_1956_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_1956_, 0, v_b_1927_);
                    v___x_1957_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_1957_, 0, v___x_1956_);
                    return v___x_1957_;
                }
            }
            1 => {
                v___x_1942_ = 1usize;
                v___x_1943_ = lean_usize_add(v_i_1925_, v___x_1942_);
                v_i_1925_ = v___x_1943_;
                v_b_1927_ = v_a_1941_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_1946_) == 0 {
                    v_a_1947_ = lean_ctor_get(v___y_1946_, 0);
                    if lean_obj_tag(v_a_1947_) == 0 {
                        lean_dec_ref(v_f_1923_);
                        return v___y_1946_;
                    } else {
                        lean_inc_ref(v_a_1947_);
                        lean_dec_ref_known(v___y_1946_, 1);
                        v_a_1948_ = lean_ctor_get(v_a_1947_, 0);
                        lean_inc(v_a_1948_);
                        lean_dec_ref_known(v_a_1947_, 1);
                        v_a_1941_ = v_a_1948_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_1923_);
                    return v___y_1946_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_1958_: *mut LeanObject = *_args.add(0);
    let mut v_as_1959_: *mut LeanObject = *_args.add(1);
    let mut v_i_1960_: *mut LeanObject = *_args.add(2);
    let mut v_stop_1961_: *mut LeanObject = *_args.add(3);
    let mut v_b_1962_: *mut LeanObject = *_args.add(4);
    let mut v___y_1963_: *mut LeanObject = *_args.add(5);
    let mut v___y_1964_: *mut LeanObject = *_args.add(6);
    let mut v___y_1965_: *mut LeanObject = *_args.add(7);
    let mut v___y_1966_: *mut LeanObject = *_args.add(8);
    let mut v___y_1967_: *mut LeanObject = *_args.add(9);
    let mut v___y_1968_: *mut LeanObject = *_args.add(10);
    let mut v___y_1969_: *mut LeanObject = *_args.add(11);
    let mut v___y_1970_: *mut LeanObject = *_args.add(12);
    let mut v___y_1971_: *mut LeanObject = *_args.add(13);
    let mut v___y_1972_: *mut LeanObject = *_args.add(14);
    let mut v___y_1973_: *mut LeanObject = *_args.add(15);
    let mut v___y_1974_: *mut LeanObject = *_args.add(16);
    let mut v_i_boxed_1975_: usize = 0;
    let mut v_stop_boxed_1976_: usize = 0;
    let mut v_res_1977_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_1975_ = lean_unbox_usize(v_i_1960_);
    lean_dec(v_i_1960_);
    v_stop_boxed_1976_ = lean_unbox_usize(v_stop_1961_);
    lean_dec(v_stop_1961_);
    v_res_1977_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_1958_, v_as_1959_, v_i_boxed_1975_, v_stop_boxed_1976_, v_b_1962_, v___y_1963_, v___y_1964_, v___y_1965_, v___y_1966_, v___y_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
    lean_dec(v___y_1973_);
    lean_dec_ref(v___y_1972_);
    lean_dec(v___y_1971_);
    lean_dec_ref(v___y_1970_);
    lean_dec(v___y_1969_);
    lean_dec_ref(v___y_1968_);
    lean_dec(v___y_1967_);
    lean_dec_ref(v___y_1966_);
    lean_dec(v___y_1965_);
    lean_dec(v___y_1964_);
    lean_dec_ref(v___y_1963_);
    lean_dec_ref(v_as_1959_);
    return v_res_1977_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg___boxed(
    mut v_f_1978_: *mut LeanObject,
    mut v_x_1979_: *mut LeanObject,
    mut v_x_1980_: *mut LeanObject,
    mut v___y_1981_: *mut LeanObject,
    mut v___y_1982_: *mut LeanObject,
    mut v___y_1983_: *mut LeanObject,
    mut v___y_1984_: *mut LeanObject,
    mut v___y_1985_: *mut LeanObject,
    mut v___y_1986_: *mut LeanObject,
    mut v___y_1987_: *mut LeanObject,
    mut v___y_1988_: *mut LeanObject,
    mut v___y_1989_: *mut LeanObject,
    mut v___y_1990_: *mut LeanObject,
    mut v___y_1991_: *mut LeanObject,
    mut v___y_1992_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_1993_: *mut LeanObject = core::ptr::null_mut();
    v_res_1993_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_1978_, v_x_1979_, v_x_1980_, v___y_1981_, v___y_1982_, v___y_1983_, v___y_1984_, v___y_1985_, v___y_1986_, v___y_1987_, v___y_1988_, v___y_1989_, v___y_1990_, v___y_1991_);
    lean_dec(v___y_1991_);
    lean_dec_ref(v___y_1990_);
    lean_dec(v___y_1989_);
    lean_dec_ref(v___y_1988_);
    lean_dec(v___y_1987_);
    lean_dec_ref(v___y_1986_);
    lean_dec(v___y_1985_);
    lean_dec_ref(v___y_1984_);
    lean_dec(v___y_1983_);
    lean_dec(v___y_1982_);
    lean_dec_ref(v___y_1981_);
    return v_res_1993_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(
    mut v_f_1994_: *mut LeanObject,
    mut v_s_1995_: *mut LeanObject,
    mut v_a_1996_: *mut LeanObject,
    mut v_b_1997_: *mut LeanObject,
    mut v___y_1998_: *mut LeanObject,
    mut v___y_1999_: *mut LeanObject,
    mut v___y_2000_: *mut LeanObject,
    mut v___y_2001_: *mut LeanObject,
    mut v___y_2002_: *mut LeanObject,
    mut v___y_2003_: *mut LeanObject,
    mut v___y_2004_: *mut LeanObject,
    mut v___y_2005_: *mut LeanObject,
    mut v___y_2006_: *mut LeanObject,
    mut v___y_2007_: *mut LeanObject,
    mut v___y_2008_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2010_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2011_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2012_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2014_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2015_: u8 = 0;
    let mut v_a_2016_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2019_: u8 = 0;
    let mut v___x_2021_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2024_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2025_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2026_: u8 = 0;
    let mut v_a_2027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2029_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2030_: u8 = 0;
    let mut v___x_2032_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2036_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2037_: u8 = 0;
    let mut v_isSharedCheck_2038_: u8 = 0;
    let mut v_a_2039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2042_: u8 = 0;
    let mut v___x_2044_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2046_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2010_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_2010_, 0, v_a_1996_);
                lean_ctor_set(v___x_2010_, 1, v_b_1997_);
                lean_inc(v___y_2008_);
                lean_inc_ref(v___y_2007_);
                lean_inc(v___y_2006_);
                lean_inc_ref(v___y_2005_);
                lean_inc(v___y_2004_);
                lean_inc_ref(v___y_2003_);
                lean_inc(v___y_2002_);
                lean_inc_ref(v___y_2001_);
                lean_inc(v___y_2000_);
                lean_inc(v___y_1999_);
                lean_inc_ref(v___y_1998_);
                v___x_2011_ = lean_apply_14(
                    v_f_1994_,
                    v___x_2010_,
                    v_s_1995_,
                    v___y_1998_,
                    v___y_1999_,
                    v___y_2000_,
                    v___y_2001_,
                    v___y_2002_,
                    v___y_2003_,
                    v___y_2004_,
                    v___y_2005_,
                    v___y_2006_,
                    v___y_2007_,
                    v___y_2008_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_2011_) == 0 {
                    v_a_2012_ = lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2038_ = (!lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2038_ == 0 {
                        v___x_2014_ = v___x_2011_;
                        v_isShared_2015_ = v_isSharedCheck_2038_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2012_);
                        lean_dec(v___x_2011_);
                        v___x_2014_ = lean_box(0);
                        v_isShared_2015_ = v_isSharedCheck_2038_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2039_ = lean_ctor_get(v___x_2011_, 0);
                    v_isSharedCheck_2046_ = (!lean_is_exclusive(v___x_2011_)) as u8;
                    if v_isSharedCheck_2046_ == 0 {
                        v___x_2041_ = v___x_2011_;
                        v_isShared_2042_ = v_isSharedCheck_2046_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_2039_);
                        lean_dec(v___x_2011_);
                        v___x_2041_ = lean_box(0);
                        v_isShared_2042_ = v_isSharedCheck_2046_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_2012_) == 0 {
                    v_a_2016_ = lean_ctor_get(v_a_2012_, 0);
                    v_isSharedCheck_2026_ = (!lean_is_exclusive(v_a_2012_)) as u8;
                    if v_isSharedCheck_2026_ == 0 {
                        v___x_2018_ = v_a_2012_;
                        v_isShared_2019_ = v_isSharedCheck_2026_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2016_);
                        lean_dec(v_a_2012_);
                        v___x_2018_ = lean_box(0);
                        v_isShared_2019_ = v_isSharedCheck_2026_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_2027_ = lean_ctor_get(v_a_2012_, 0);
                    v_isSharedCheck_2037_ = (!lean_is_exclusive(v_a_2012_)) as u8;
                    if v_isSharedCheck_2037_ == 0 {
                        v___x_2029_ = v_a_2012_;
                        v_isShared_2030_ = v_isSharedCheck_2037_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2027_);
                        lean_dec(v_a_2012_);
                        v___x_2029_ = lean_box(0);
                        v_isShared_2030_ = v_isSharedCheck_2037_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_2019_ == 0 {
                    v___x_2021_ = v___x_2018_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_2025_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2025_, 0, v_a_2016_);
                    v___x_2021_ = v_reuseFailAlloc_2025_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_2015_ == 0 {
                    lean_ctor_set(v___x_2014_, 0, v___x_2021_);
                    v___x_2023_ = v___x_2014_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2024_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2024_, 0, v___x_2021_);
                    v___x_2023_ = v_reuseFailAlloc_2024_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2023_;
            }
            5 => {
                if v_isShared_2030_ == 0 {
                    v___x_2032_ = v___x_2029_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2036_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_a_2027_);
                    v___x_2032_ = v_reuseFailAlloc_2036_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_2015_ == 0 {
                    lean_ctor_set(v___x_2014_, 0, v___x_2032_);
                    v___x_2034_ = v___x_2014_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2035_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2032_);
                    v___x_2034_ = v_reuseFailAlloc_2035_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2034_;
            }
            8 => {
                if v_isShared_2042_ == 0 {
                    v___x_2044_ = v___x_2041_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_a_2039_);
                    v___x_2044_ = v_reuseFailAlloc_2045_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_2044_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0___boxed(
    mut v_f_2047_: *mut LeanObject,
    mut v_s_2048_: *mut LeanObject,
    mut v_a_2049_: *mut LeanObject,
    mut v_b_2050_: *mut LeanObject,
    mut v___y_2051_: *mut LeanObject,
    mut v___y_2052_: *mut LeanObject,
    mut v___y_2053_: *mut LeanObject,
    mut v___y_2054_: *mut LeanObject,
    mut v___y_2055_: *mut LeanObject,
    mut v___y_2056_: *mut LeanObject,
    mut v___y_2057_: *mut LeanObject,
    mut v___y_2058_: *mut LeanObject,
    mut v___y_2059_: *mut LeanObject,
    mut v___y_2060_: *mut LeanObject,
    mut v___y_2061_: *mut LeanObject,
    mut v___y_2062_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2063_: *mut LeanObject = core::ptr::null_mut();
    v_res_2063_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0(v_f_2047_, v_s_2048_, v_a_2049_, v_b_2050_, v___y_2051_, v___y_2052_, v___y_2053_, v___y_2054_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_, v___y_2061_);
    lean_dec(v___y_2061_);
    lean_dec_ref(v___y_2060_);
    lean_dec(v___y_2059_);
    lean_dec_ref(v___y_2058_);
    lean_dec(v___y_2057_);
    lean_dec_ref(v___y_2056_);
    lean_dec(v___y_2055_);
    lean_dec_ref(v___y_2054_);
    lean_dec(v___y_2053_);
    lean_dec(v___y_2052_);
    lean_dec_ref(v___y_2051_);
    return v_res_2063_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(
    mut v_map_2064_: *mut LeanObject,
    mut v_init_2065_: *mut LeanObject,
    mut v_f_2066_: *mut LeanObject,
    mut v___y_2067_: *mut LeanObject,
    mut v___y_2068_: *mut LeanObject,
    mut v___y_2069_: *mut LeanObject,
    mut v___y_2070_: *mut LeanObject,
    mut v___y_2071_: *mut LeanObject,
    mut v___y_2072_: *mut LeanObject,
    mut v___y_2073_: *mut LeanObject,
    mut v___y_2074_: *mut LeanObject,
    mut v___y_2075_: *mut LeanObject,
    mut v___y_2076_: *mut LeanObject,
    mut v___y_2077_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_2079_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2081_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2084_: u8 = 0;
    let mut v_a_2085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2089_: u8 = 0;
    let mut v_a_2090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2092_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2093_: u8 = 0;
    let mut v___x_2095_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2096_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2097_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_2079_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 1);
                lean_closure_set(v___f_2079_, 0, v_f_2066_);
                lean_inc_ref(v_map_2064_);
                v___x_2080_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v___f_2079_, v_map_2064_, v_init_2065_, v___y_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_, v___y_2072_, v___y_2073_, v___y_2074_, v___y_2075_, v___y_2076_, v___y_2077_);
                if lean_obj_tag(v___x_2080_) == 0 {
                    v_a_2081_ = lean_ctor_get(v___x_2080_, 0);
                    v_isSharedCheck_2089_ = (!lean_is_exclusive(v___x_2080_)) as u8;
                    if v_isSharedCheck_2089_ == 0 {
                        v___x_2083_ = v___x_2080_;
                        v_isShared_2084_ = v_isSharedCheck_2089_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_2081_);
                        lean_dec(v___x_2080_);
                        v___x_2083_ = lean_box(0);
                        v_isShared_2084_ = v_isSharedCheck_2089_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_2090_ = lean_ctor_get(v___x_2080_, 0);
                    v_isSharedCheck_2097_ = (!lean_is_exclusive(v___x_2080_)) as u8;
                    if v_isSharedCheck_2097_ == 0 {
                        v___x_2092_ = v___x_2080_;
                        v_isShared_2093_ = v_isSharedCheck_2097_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_2090_);
                        lean_dec(v___x_2080_);
                        v___x_2092_ = lean_box(0);
                        v_isShared_2093_ = v_isSharedCheck_2097_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2085_ = lean_ctor_get(v_a_2081_, 0);
                lean_inc(v_a_2085_);
                lean_dec(v_a_2081_);
                if v_isShared_2084_ == 0 {
                    lean_ctor_set(v___x_2083_, 0, v_a_2085_);
                    v___x_2087_ = v___x_2083_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2088_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2088_, 0, v_a_2085_);
                    v___x_2087_ = v_reuseFailAlloc_2088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2087_;
            }
            3 => {
                if v_isShared_2093_ == 0 {
                    v___x_2095_ = v___x_2092_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2096_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2096_, 0, v_a_2090_);
                    v___x_2095_ = v_reuseFailAlloc_2096_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2095_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg___boxed(
    mut v_map_2098_: *mut LeanObject,
    mut v_init_2099_: *mut LeanObject,
    mut v_f_2100_: *mut LeanObject,
    mut v___y_2101_: *mut LeanObject,
    mut v___y_2102_: *mut LeanObject,
    mut v___y_2103_: *mut LeanObject,
    mut v___y_2104_: *mut LeanObject,
    mut v___y_2105_: *mut LeanObject,
    mut v___y_2106_: *mut LeanObject,
    mut v___y_2107_: *mut LeanObject,
    mut v___y_2108_: *mut LeanObject,
    mut v___y_2109_: *mut LeanObject,
    mut v___y_2110_: *mut LeanObject,
    mut v___y_2111_: *mut LeanObject,
    mut v___y_2112_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2113_: *mut LeanObject = core::ptr::null_mut();
    v_res_2113_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_map_2098_, v_init_2099_, v_f_2100_, v___y_2101_, v___y_2102_, v___y_2103_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_, v___y_2108_, v___y_2109_, v___y_2110_, v___y_2111_);
    lean_dec(v___y_2111_);
    lean_dec_ref(v___y_2110_);
    lean_dec(v___y_2109_);
    lean_dec_ref(v___y_2108_);
    lean_dec(v___y_2107_);
    lean_dec_ref(v___y_2106_);
    lean_dec(v___y_2105_);
    lean_dec_ref(v___y_2104_);
    lean_dec(v___y_2103_);
    lean_dec(v___y_2102_);
    lean_dec_ref(v___y_2101_);
    lean_dec_ref(v_map_2098_);
    return v_res_2113_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1()
-> *mut LeanObject {
    let mut v___x_2115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2118_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2119_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2120_: *mut LeanObject = core::ptr::null_mut();
    v___x_2115_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__0;
    v___x_2116_ = lean_unsigned_to_nat(2);
    v___x_2117_ = lean_unsigned_to_nat(23);
    v___x_2118_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__1;
    v___x_2119_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_2120_ = l_mkPanicMessageWithDecl(
        v___x_2119_,
        v___x_2118_,
        v___x_2117_,
        v___x_2116_,
        v___x_2115_,
    );
    return v___x_2120_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(
    mut v_a_2121_: *mut LeanObject,
    mut v_a_2122_: *mut LeanObject,
    mut v_a_2123_: *mut LeanObject,
    mut v_a_2124_: *mut LeanObject,
    mut v_a_2125_: *mut LeanObject,
    mut v_a_2126_: *mut LeanObject,
    mut v_a_2127_: *mut LeanObject,
    mut v_a_2128_: *mut LeanObject,
    mut v_a_2129_: *mut LeanObject,
    mut v_a_2130_: *mut LeanObject,
    mut v_a_2131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_toRing_2135_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_2136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_2137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_2138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2140_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2144_: u8 = 0;
    let mut v_size_2145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2146_: u8 = 0;
    let mut v___x_2147_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2153_: u8 = 0;
    let mut v_a_2154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2157_: u8 = 0;
    let mut v___x_2159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2161_: u8 = 0;
    let mut v_a_2162_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2164_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2165_: u8 = 0;
    let mut v___x_2167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2169_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2133_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_,
                    v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_,
                );
                if lean_obj_tag(v___x_2133_) == 0 {
                    v_a_2134_ = lean_ctor_get(v___x_2133_, 0);
                    lean_inc(v_a_2134_);
                    lean_dec_ref_known(v___x_2133_, 1);
                    v_toRing_2135_ = lean_ctor_get(v_a_2134_, 0);
                    lean_inc_ref(v_toRing_2135_);
                    lean_dec(v_a_2134_);
                    v_vars_2136_ = lean_ctor_get(v_toRing_2135_, 14);
                    lean_inc_ref_n(v_vars_2136_, 2);
                    v_varMap_2137_ = lean_ctor_get(v_toRing_2135_, 15);
                    lean_inc_ref(v_varMap_2137_);
                    lean_dec_ref(v_toRing_2135_);
                    v___f_2138_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___boxed as *mut core::ffi::c_void, 15, 1);
                    lean_closure_set(v___f_2138_, 0, v_vars_2136_);
                    v___x_2139_ = lean_unsigned_to_nat(0);
                    v___x_2140_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_varMap_2137_, v___x_2139_, v___f_2138_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
                    lean_dec_ref(v_varMap_2137_);
                    if lean_obj_tag(v___x_2140_) == 0 {
                        v_a_2141_ = lean_ctor_get(v___x_2140_, 0);
                        v_isSharedCheck_2153_ = (!lean_is_exclusive(v___x_2140_)) as u8;
                        if v_isSharedCheck_2153_ == 0 {
                            v___x_2143_ = v___x_2140_;
                            v_isShared_2144_ = v_isSharedCheck_2153_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2141_);
                            lean_dec(v___x_2140_);
                            v___x_2143_ = lean_box(0);
                            v_isShared_2144_ = v_isSharedCheck_2153_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_vars_2136_);
                        v_a_2154_ = lean_ctor_get(v___x_2140_, 0);
                        v_isSharedCheck_2161_ = (!lean_is_exclusive(v___x_2140_)) as u8;
                        if v_isSharedCheck_2161_ == 0 {
                            v___x_2156_ = v___x_2140_;
                            v_isShared_2157_ = v_isSharedCheck_2161_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2154_);
                            lean_dec(v___x_2140_);
                            v___x_2156_ = lean_box(0);
                            v_isShared_2157_ = v_isSharedCheck_2161_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2162_ = lean_ctor_get(v___x_2133_, 0);
                    v_isSharedCheck_2169_ = (!lean_is_exclusive(v___x_2133_)) as u8;
                    if v_isSharedCheck_2169_ == 0 {
                        v___x_2164_ = v___x_2133_;
                        v_isShared_2165_ = v_isSharedCheck_2169_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2162_);
                        lean_dec(v___x_2133_);
                        v___x_2164_ = lean_box(0);
                        v_isShared_2165_ = v_isSharedCheck_2169_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_size_2145_ = lean_ctor_get(v_vars_2136_, 2);
                lean_inc(v_size_2145_);
                lean_dec_ref(v_vars_2136_);
                v___x_2146_ = lean_nat_dec_eq(v_size_2145_, v_a_2141_);
                lean_dec(v_a_2141_);
                lean_dec(v_size_2145_);
                if v___x_2146_ == 0 {
                    lean_del_object(v___x_2143_);
                    v___x_2147_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___closed__1);
                    v___x_2148_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_2147_, v_a_2121_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_, v_a_2128_, v_a_2129_, v_a_2130_, v_a_2131_);
                    return v___x_2148_;
                } else {
                    v___x_2149_ = lean_box(0);
                    if v_isShared_2144_ == 0 {
                        lean_ctor_set(v___x_2143_, 0, v___x_2149_);
                        v___x_2151_ = v___x_2143_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2152_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2152_, 0, v___x_2149_);
                        v___x_2151_ = v_reuseFailAlloc_2152_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2151_;
            }
            3 => {
                if v_isShared_2157_ == 0 {
                    v___x_2159_ = v___x_2156_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2160_, 0, v_a_2154_);
                    v___x_2159_ = v_reuseFailAlloc_2160_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2159_;
            }
            5 => {
                if v_isShared_2165_ == 0 {
                    v___x_2167_ = v___x_2164_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2168_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_a_2162_);
                    v___x_2167_ = v_reuseFailAlloc_2168_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2167_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___boxed(
    mut v_a_2170_: *mut LeanObject,
    mut v_a_2171_: *mut LeanObject,
    mut v_a_2172_: *mut LeanObject,
    mut v_a_2173_: *mut LeanObject,
    mut v_a_2174_: *mut LeanObject,
    mut v_a_2175_: *mut LeanObject,
    mut v_a_2176_: *mut LeanObject,
    mut v_a_2177_: *mut LeanObject,
    mut v_a_2178_: *mut LeanObject,
    mut v_a_2179_: *mut LeanObject,
    mut v_a_2180_: *mut LeanObject,
    mut v_a_2181_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2182_: *mut LeanObject = core::ptr::null_mut();
    v_res_2182_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(v_a_2170_, v_a_2171_, v_a_2172_, v_a_2173_, v_a_2174_, v_a_2175_, v_a_2176_, v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
    lean_dec(v_a_2180_);
    lean_dec_ref(v_a_2179_);
    lean_dec(v_a_2178_);
    lean_dec_ref(v_a_2177_);
    lean_dec(v_a_2176_);
    lean_dec_ref(v_a_2175_);
    lean_dec(v_a_2174_);
    lean_dec_ref(v_a_2173_);
    lean_dec(v_a_2172_);
    lean_dec(v_a_2171_);
    lean_dec_ref(v_a_2170_);
    return v_res_2182_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(
    mut v_00_u03c3_2183_: *mut LeanObject,
    mut v_00_u03b2_2184_: *mut LeanObject,
    mut v_map_2185_: *mut LeanObject,
    mut v_init_2186_: *mut LeanObject,
    mut v_f_2187_: *mut LeanObject,
    mut v___y_2188_: *mut LeanObject,
    mut v___y_2189_: *mut LeanObject,
    mut v___y_2190_: *mut LeanObject,
    mut v___y_2191_: *mut LeanObject,
    mut v___y_2192_: *mut LeanObject,
    mut v___y_2193_: *mut LeanObject,
    mut v___y_2194_: *mut LeanObject,
    mut v___y_2195_: *mut LeanObject,
    mut v___y_2196_: *mut LeanObject,
    mut v___y_2197_: *mut LeanObject,
    mut v___y_2198_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2200_: *mut LeanObject = core::ptr::null_mut();
    v___x_2200_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___redArg(v_map_2185_, v_init_2186_, v_f_2187_, v___y_2188_, v___y_2189_, v___y_2190_, v___y_2191_, v___y_2192_, v___y_2193_, v___y_2194_, v___y_2195_, v___y_2196_, v___y_2197_, v___y_2198_);
    return v___x_2200_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2201_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03b2_2202_: *mut LeanObject = *_args.add(1);
    let mut v_map_2203_: *mut LeanObject = *_args.add(2);
    let mut v_init_2204_: *mut LeanObject = *_args.add(3);
    let mut v_f_2205_: *mut LeanObject = *_args.add(4);
    let mut v___y_2206_: *mut LeanObject = *_args.add(5);
    let mut v___y_2207_: *mut LeanObject = *_args.add(6);
    let mut v___y_2208_: *mut LeanObject = *_args.add(7);
    let mut v___y_2209_: *mut LeanObject = *_args.add(8);
    let mut v___y_2210_: *mut LeanObject = *_args.add(9);
    let mut v___y_2211_: *mut LeanObject = *_args.add(10);
    let mut v___y_2212_: *mut LeanObject = *_args.add(11);
    let mut v___y_2213_: *mut LeanObject = *_args.add(12);
    let mut v___y_2214_: *mut LeanObject = *_args.add(13);
    let mut v___y_2215_: *mut LeanObject = *_args.add(14);
    let mut v___y_2216_: *mut LeanObject = *_args.add(15);
    let mut v___y_2217_: *mut LeanObject = *_args.add(16);
    let mut v_res_2218_: *mut LeanObject = core::ptr::null_mut();
    v_res_2218_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2(v_00_u03c3_2201_, v_00_u03b2_2202_, v_map_2203_, v_init_2204_, v_f_2205_, v___y_2206_, v___y_2207_, v___y_2208_, v___y_2209_, v___y_2210_, v___y_2211_, v___y_2212_, v___y_2213_, v___y_2214_, v___y_2215_, v___y_2216_);
    lean_dec(v___y_2216_);
    lean_dec_ref(v___y_2215_);
    lean_dec(v___y_2214_);
    lean_dec_ref(v___y_2213_);
    lean_dec(v___y_2212_);
    lean_dec_ref(v___y_2211_);
    lean_dec(v___y_2210_);
    lean_dec_ref(v___y_2209_);
    lean_dec(v___y_2208_);
    lean_dec(v___y_2207_);
    lean_dec_ref(v___y_2206_);
    lean_dec_ref(v_map_2203_);
    return v_res_2218_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(
    mut v_map_2219_: *mut LeanObject,
    mut v_f_2220_: *mut LeanObject,
    mut v_init_2221_: *mut LeanObject,
    mut v___y_2222_: *mut LeanObject,
    mut v___y_2223_: *mut LeanObject,
    mut v___y_2224_: *mut LeanObject,
    mut v___y_2225_: *mut LeanObject,
    mut v___y_2226_: *mut LeanObject,
    mut v___y_2227_: *mut LeanObject,
    mut v___y_2228_: *mut LeanObject,
    mut v___y_2229_: *mut LeanObject,
    mut v___y_2230_: *mut LeanObject,
    mut v___y_2231_: *mut LeanObject,
    mut v___y_2232_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2234_: *mut LeanObject = core::ptr::null_mut();
    v___x_2234_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2220_, v_map_2219_, v_init_2221_, v___y_2222_, v___y_2223_, v___y_2224_, v___y_2225_, v___y_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_, v___y_2231_, v___y_2232_);
    return v___x_2234_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg___boxed(
    mut v_map_2235_: *mut LeanObject,
    mut v_f_2236_: *mut LeanObject,
    mut v_init_2237_: *mut LeanObject,
    mut v___y_2238_: *mut LeanObject,
    mut v___y_2239_: *mut LeanObject,
    mut v___y_2240_: *mut LeanObject,
    mut v___y_2241_: *mut LeanObject,
    mut v___y_2242_: *mut LeanObject,
    mut v___y_2243_: *mut LeanObject,
    mut v___y_2244_: *mut LeanObject,
    mut v___y_2245_: *mut LeanObject,
    mut v___y_2246_: *mut LeanObject,
    mut v___y_2247_: *mut LeanObject,
    mut v___y_2248_: *mut LeanObject,
    mut v___y_2249_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2250_: *mut LeanObject = core::ptr::null_mut();
    v_res_2250_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___redArg(v_map_2235_, v_f_2236_, v_init_2237_, v___y_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_, v___y_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_, v___y_2248_);
    lean_dec(v___y_2248_);
    lean_dec_ref(v___y_2247_);
    lean_dec(v___y_2246_);
    lean_dec_ref(v___y_2245_);
    lean_dec(v___y_2244_);
    lean_dec_ref(v___y_2243_);
    lean_dec(v___y_2242_);
    lean_dec_ref(v___y_2241_);
    lean_dec(v___y_2240_);
    lean_dec(v___y_2239_);
    lean_dec_ref(v___y_2238_);
    return v_res_2250_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(
    mut v_00_u03c3_2251_: *mut LeanObject,
    mut v_00_u03c3_2252_: *mut LeanObject,
    mut v_00_u03b2_2253_: *mut LeanObject,
    mut v_map_2254_: *mut LeanObject,
    mut v_f_2255_: *mut LeanObject,
    mut v_init_2256_: *mut LeanObject,
    mut v___y_2257_: *mut LeanObject,
    mut v___y_2258_: *mut LeanObject,
    mut v___y_2259_: *mut LeanObject,
    mut v___y_2260_: *mut LeanObject,
    mut v___y_2261_: *mut LeanObject,
    mut v___y_2262_: *mut LeanObject,
    mut v___y_2263_: *mut LeanObject,
    mut v___y_2264_: *mut LeanObject,
    mut v___y_2265_: *mut LeanObject,
    mut v___y_2266_: *mut LeanObject,
    mut v___y_2267_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2269_: *mut LeanObject = core::ptr::null_mut();
    v___x_2269_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2255_, v_map_2254_, v_init_2256_, v___y_2257_, v___y_2258_, v___y_2259_, v___y_2260_, v___y_2261_, v___y_2262_, v___y_2263_, v___y_2264_, v___y_2265_, v___y_2266_, v___y_2267_);
    return v___x_2269_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2270_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_2271_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b2_2272_: *mut LeanObject = *_args.add(2);
    let mut v_map_2273_: *mut LeanObject = *_args.add(3);
    let mut v_f_2274_: *mut LeanObject = *_args.add(4);
    let mut v_init_2275_: *mut LeanObject = *_args.add(5);
    let mut v___y_2276_: *mut LeanObject = *_args.add(6);
    let mut v___y_2277_: *mut LeanObject = *_args.add(7);
    let mut v___y_2278_: *mut LeanObject = *_args.add(8);
    let mut v___y_2279_: *mut LeanObject = *_args.add(9);
    let mut v___y_2280_: *mut LeanObject = *_args.add(10);
    let mut v___y_2281_: *mut LeanObject = *_args.add(11);
    let mut v___y_2282_: *mut LeanObject = *_args.add(12);
    let mut v___y_2283_: *mut LeanObject = *_args.add(13);
    let mut v___y_2284_: *mut LeanObject = *_args.add(14);
    let mut v___y_2285_: *mut LeanObject = *_args.add(15);
    let mut v___y_2286_: *mut LeanObject = *_args.add(16);
    let mut v___y_2287_: *mut LeanObject = *_args.add(17);
    let mut v_res_2288_: *mut LeanObject = core::ptr::null_mut();
    v_res_2288_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2(v_00_u03c3_2270_, v_00_u03c3_2271_, v_00_u03b2_2272_, v_map_2273_, v_f_2274_, v_init_2275_, v___y_2276_, v___y_2277_, v___y_2278_, v___y_2279_, v___y_2280_, v___y_2281_, v___y_2282_, v___y_2283_, v___y_2284_, v___y_2285_, v___y_2286_);
    lean_dec(v___y_2286_);
    lean_dec_ref(v___y_2285_);
    lean_dec(v___y_2284_);
    lean_dec_ref(v___y_2283_);
    lean_dec(v___y_2282_);
    lean_dec_ref(v___y_2281_);
    lean_dec(v___y_2280_);
    lean_dec_ref(v___y_2279_);
    lean_dec(v___y_2278_);
    lean_dec(v___y_2277_);
    lean_dec_ref(v___y_2276_);
    return v_res_2288_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(
    mut v_00_u03c3_2289_: *mut LeanObject,
    mut v_00_u03c3_2290_: *mut LeanObject,
    mut v_00_u03b1_2291_: *mut LeanObject,
    mut v_00_u03b2_2292_: *mut LeanObject,
    mut v_f_2293_: *mut LeanObject,
    mut v_x_2294_: *mut LeanObject,
    mut v_x_2295_: *mut LeanObject,
    mut v___y_2296_: *mut LeanObject,
    mut v___y_2297_: *mut LeanObject,
    mut v___y_2298_: *mut LeanObject,
    mut v___y_2299_: *mut LeanObject,
    mut v___y_2300_: *mut LeanObject,
    mut v___y_2301_: *mut LeanObject,
    mut v___y_2302_: *mut LeanObject,
    mut v___y_2303_: *mut LeanObject,
    mut v___y_2304_: *mut LeanObject,
    mut v___y_2305_: *mut LeanObject,
    mut v___y_2306_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2308_: *mut LeanObject = core::ptr::null_mut();
    v___x_2308_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___redArg(v_f_2293_, v_x_2294_, v_x_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_, v___y_2305_, v___y_2306_);
    return v___x_2308_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2309_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_2310_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_2311_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_2312_: *mut LeanObject = *_args.add(3);
    let mut v_f_2313_: *mut LeanObject = *_args.add(4);
    let mut v_x_2314_: *mut LeanObject = *_args.add(5);
    let mut v_x_2315_: *mut LeanObject = *_args.add(6);
    let mut v___y_2316_: *mut LeanObject = *_args.add(7);
    let mut v___y_2317_: *mut LeanObject = *_args.add(8);
    let mut v___y_2318_: *mut LeanObject = *_args.add(9);
    let mut v___y_2319_: *mut LeanObject = *_args.add(10);
    let mut v___y_2320_: *mut LeanObject = *_args.add(11);
    let mut v___y_2321_: *mut LeanObject = *_args.add(12);
    let mut v___y_2322_: *mut LeanObject = *_args.add(13);
    let mut v___y_2323_: *mut LeanObject = *_args.add(14);
    let mut v___y_2324_: *mut LeanObject = *_args.add(15);
    let mut v___y_2325_: *mut LeanObject = *_args.add(16);
    let mut v___y_2326_: *mut LeanObject = *_args.add(17);
    let mut v___y_2327_: *mut LeanObject = *_args.add(18);
    let mut v_res_2328_: *mut LeanObject = core::ptr::null_mut();
    v_res_2328_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3(v_00_u03c3_2309_, v_00_u03c3_2310_, v_00_u03b1_2311_, v_00_u03b2_2312_, v_f_2313_, v_x_2314_, v_x_2315_, v___y_2316_, v___y_2317_, v___y_2318_, v___y_2319_, v___y_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_, v___y_2325_, v___y_2326_);
    lean_dec(v___y_2326_);
    lean_dec_ref(v___y_2325_);
    lean_dec(v___y_2324_);
    lean_dec_ref(v___y_2323_);
    lean_dec(v___y_2322_);
    lean_dec_ref(v___y_2321_);
    lean_dec(v___y_2320_);
    lean_dec_ref(v___y_2319_);
    lean_dec(v___y_2318_);
    lean_dec(v___y_2317_);
    lean_dec_ref(v___y_2316_);
    return v_res_2328_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(
    mut v_00_u03b1_2329_: *mut LeanObject,
    mut v_00_u03b2_2330_: *mut LeanObject,
    mut v_00_u03c3_2331_: *mut LeanObject,
    mut v_00_u03c3_2332_: *mut LeanObject,
    mut v_f_2333_: *mut LeanObject,
    mut v_as_2334_: *mut LeanObject,
    mut v_i_2335_: usize,
    mut v_stop_2336_: usize,
    mut v_b_2337_: *mut LeanObject,
    mut v___y_2338_: *mut LeanObject,
    mut v___y_2339_: *mut LeanObject,
    mut v___y_2340_: *mut LeanObject,
    mut v___y_2341_: *mut LeanObject,
    mut v___y_2342_: *mut LeanObject,
    mut v___y_2343_: *mut LeanObject,
    mut v___y_2344_: *mut LeanObject,
    mut v___y_2345_: *mut LeanObject,
    mut v___y_2346_: *mut LeanObject,
    mut v___y_2347_: *mut LeanObject,
    mut v___y_2348_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2350_: *mut LeanObject = core::ptr::null_mut();
    v___x_2350_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___redArg(v_f_2333_, v_as_2334_, v_i_2335_, v_stop_2336_, v_b_2337_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_, v___y_2342_, v___y_2343_, v___y_2344_, v___y_2345_, v___y_2346_, v___y_2347_, v___y_2348_);
    return v___x_2350_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_2351_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03b2_2352_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03c3_2353_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03c3_2354_: *mut LeanObject = *_args.add(3);
    let mut v_f_2355_: *mut LeanObject = *_args.add(4);
    let mut v_as_2356_: *mut LeanObject = *_args.add(5);
    let mut v_i_2357_: *mut LeanObject = *_args.add(6);
    let mut v_stop_2358_: *mut LeanObject = *_args.add(7);
    let mut v_b_2359_: *mut LeanObject = *_args.add(8);
    let mut v___y_2360_: *mut LeanObject = *_args.add(9);
    let mut v___y_2361_: *mut LeanObject = *_args.add(10);
    let mut v___y_2362_: *mut LeanObject = *_args.add(11);
    let mut v___y_2363_: *mut LeanObject = *_args.add(12);
    let mut v___y_2364_: *mut LeanObject = *_args.add(13);
    let mut v___y_2365_: *mut LeanObject = *_args.add(14);
    let mut v___y_2366_: *mut LeanObject = *_args.add(15);
    let mut v___y_2367_: *mut LeanObject = *_args.add(16);
    let mut v___y_2368_: *mut LeanObject = *_args.add(17);
    let mut v___y_2369_: *mut LeanObject = *_args.add(18);
    let mut v___y_2370_: *mut LeanObject = *_args.add(19);
    let mut v___y_2371_: *mut LeanObject = *_args.add(20);
    let mut v_i_boxed_2372_: usize = 0;
    let mut v_stop_boxed_2373_: usize = 0;
    let mut v_res_2374_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_2372_ = lean_unbox_usize(v_i_2357_);
    lean_dec(v_i_2357_);
    v_stop_boxed_2373_ = lean_unbox_usize(v_stop_2358_);
    lean_dec(v_stop_2358_);
    v_res_2374_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__4(v_00_u03b1_2351_, v_00_u03b2_2352_, v_00_u03c3_2353_, v_00_u03c3_2354_, v_f_2355_, v_as_2356_, v_i_boxed_2372_, v_stop_boxed_2373_, v_b_2359_, v___y_2360_, v___y_2361_, v___y_2362_, v___y_2363_, v___y_2364_, v___y_2365_, v___y_2366_, v___y_2367_, v___y_2368_, v___y_2369_, v___y_2370_);
    lean_dec(v___y_2370_);
    lean_dec_ref(v___y_2369_);
    lean_dec(v___y_2368_);
    lean_dec_ref(v___y_2367_);
    lean_dec(v___y_2366_);
    lean_dec_ref(v___y_2365_);
    lean_dec(v___y_2364_);
    lean_dec_ref(v___y_2363_);
    lean_dec(v___y_2362_);
    lean_dec(v___y_2361_);
    lean_dec_ref(v___y_2360_);
    lean_dec_ref(v_as_2356_);
    return v_res_2374_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(
    mut v_00_u03c3_2375_: *mut LeanObject,
    mut v_00_u03c3_2376_: *mut LeanObject,
    mut v_00_u03b1_2377_: *mut LeanObject,
    mut v_00_u03b2_2378_: *mut LeanObject,
    mut v_f_2379_: *mut LeanObject,
    mut v_keys_2380_: *mut LeanObject,
    mut v_vals_2381_: *mut LeanObject,
    mut v_heq_2382_: *mut LeanObject,
    mut v_i_2383_: *mut LeanObject,
    mut v_acc_2384_: *mut LeanObject,
    mut v___y_2385_: *mut LeanObject,
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
) -> *mut LeanObject {
    let mut v___x_2397_: *mut LeanObject = core::ptr::null_mut();
    v___x_2397_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___redArg(v_f_2379_, v_keys_2380_, v_vals_2381_, v_i_2383_, v_acc_2384_, v___y_2385_, v___y_2386_, v___y_2387_, v___y_2388_, v___y_2389_, v___y_2390_, v___y_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
    return v___x_2397_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_2398_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_2399_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_2400_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_2401_: *mut LeanObject = *_args.add(3);
    let mut v_f_2402_: *mut LeanObject = *_args.add(4);
    let mut v_keys_2403_: *mut LeanObject = *_args.add(5);
    let mut v_vals_2404_: *mut LeanObject = *_args.add(6);
    let mut v_heq_2405_: *mut LeanObject = *_args.add(7);
    let mut v_i_2406_: *mut LeanObject = *_args.add(8);
    let mut v_acc_2407_: *mut LeanObject = *_args.add(9);
    let mut v___y_2408_: *mut LeanObject = *_args.add(10);
    let mut v___y_2409_: *mut LeanObject = *_args.add(11);
    let mut v___y_2410_: *mut LeanObject = *_args.add(12);
    let mut v___y_2411_: *mut LeanObject = *_args.add(13);
    let mut v___y_2412_: *mut LeanObject = *_args.add(14);
    let mut v___y_2413_: *mut LeanObject = *_args.add(15);
    let mut v___y_2414_: *mut LeanObject = *_args.add(16);
    let mut v___y_2415_: *mut LeanObject = *_args.add(17);
    let mut v___y_2416_: *mut LeanObject = *_args.add(18);
    let mut v___y_2417_: *mut LeanObject = *_args.add(19);
    let mut v___y_2418_: *mut LeanObject = *_args.add(20);
    let mut v___y_2419_: *mut LeanObject = *_args.add(21);
    let mut v_res_2420_: *mut LeanObject = core::ptr::null_mut();
    v_res_2420_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__2_spec__2_spec__3_spec__5(v_00_u03c3_2398_, v_00_u03c3_2399_, v_00_u03b1_2400_, v_00_u03b2_2401_, v_f_2402_, v_keys_2403_, v_vals_2404_, v_heq_2405_, v_i_2406_, v_acc_2407_, v___y_2408_, v___y_2409_, v___y_2410_, v___y_2411_, v___y_2412_, v___y_2413_, v___y_2414_, v___y_2415_, v___y_2416_, v___y_2417_, v___y_2418_);
    lean_dec(v___y_2418_);
    lean_dec_ref(v___y_2417_);
    lean_dec(v___y_2416_);
    lean_dec_ref(v___y_2415_);
    lean_dec(v___y_2414_);
    lean_dec_ref(v___y_2413_);
    lean_dec(v___y_2412_);
    lean_dec_ref(v___y_2411_);
    lean_dec(v___y_2410_);
    lean_dec(v___y_2409_);
    lean_dec_ref(v___y_2408_);
    lean_dec_ref(v_vals_2404_);
    lean_dec_ref(v_keys_2403_);
    return v_res_2420_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2()
-> *mut LeanObject {
    let mut v___x_2423_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2424_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2426_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2428_: *mut LeanObject = core::ptr::null_mut();
    v___x_2423_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__1;
    v___x_2424_ = lean_unsigned_to_nat(2);
    v___x_2425_ = lean_unsigned_to_nat(29);
    v___x_2426_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0;
    v___x_2427_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_2428_ = l_mkPanicMessageWithDecl(
        v___x_2427_,
        v___x_2426_,
        v___x_2425_,
        v___x_2424_,
        v___x_2423_,
    );
    return v___x_2428_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4()
-> *mut LeanObject {
    let mut v___x_2430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2434_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2435_: *mut LeanObject = core::ptr::null_mut();
    v___x_2430_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__3;
    v___x_2431_ = lean_unsigned_to_nat(2);
    v___x_2432_ = lean_unsigned_to_nat(26);
    v___x_2433_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0;
    v___x_2434_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_2435_ = l_mkPanicMessageWithDecl(
        v___x_2434_,
        v___x_2433_,
        v___x_2432_,
        v___x_2431_,
        v___x_2430_,
    );
    return v___x_2435_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6()
-> *mut LeanObject {
    let mut v___x_2437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2440_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2442_: *mut LeanObject = core::ptr::null_mut();
    v___x_2437_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__5;
    v___x_2438_ = lean_unsigned_to_nat(2);
    v___x_2439_ = lean_unsigned_to_nat(27);
    v___x_2440_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0;
    v___x_2441_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_2442_ = l_mkPanicMessageWithDecl(
        v___x_2441_,
        v___x_2440_,
        v___x_2439_,
        v___x_2438_,
        v___x_2437_,
    );
    return v___x_2442_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8()
-> *mut LeanObject {
    let mut v___x_2444_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2445_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2446_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2448_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2449_: *mut LeanObject = core::ptr::null_mut();
    v___x_2444_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__7;
    v___x_2445_ = lean_unsigned_to_nat(2);
    v___x_2446_ = lean_unsigned_to_nat(28);
    v___x_2447_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__0;
    v___x_2448_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_2449_ = l_mkPanicMessageWithDecl(
        v___x_2448_,
        v___x_2447_,
        v___x_2446_,
        v___x_2445_,
        v___x_2444_,
    );
    return v___x_2449_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(
    mut v_p_2450_: *mut LeanObject,
    mut v_a_2451_: *mut LeanObject,
    mut v_a_2452_: *mut LeanObject,
    mut v_a_2453_: *mut LeanObject,
    mut v_a_2454_: *mut LeanObject,
    mut v_a_2455_: *mut LeanObject,
    mut v_a_2456_: *mut LeanObject,
    mut v_a_2457_: *mut LeanObject,
    mut v_a_2458_: *mut LeanObject,
    mut v_a_2459_: *mut LeanObject,
    mut v_a_2460_: *mut LeanObject,
    mut v_a_2461_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2464_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2466_: u8 = 0;
    let mut v___x_2467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2468_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2469_: u8 = 0;
    let mut v___x_2470_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2472_: u8 = 0;
    let mut v___x_2474_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2477_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2466_ = l_Lean_Grind_CommRing_Poly_isSorted(v_p_2450_);
                if v___x_2466_ == 0 {
                    v___x_2467_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__4);
                    v___x_2468_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_2467_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
                    return v___x_2468_;
                } else {
                    v___x_2469_ = l_Lean_Grind_CommRing_Poly_checkCoeffs(v_p_2450_);
                    if v___x_2469_ == 0 {
                        v___x_2470_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__6);
                        v___x_2471_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_2470_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
                        return v___x_2471_;
                    } else {
                        v___x_2472_ = l_Lean_Grind_CommRing_Poly_checkNoUnitMon(v_p_2450_);
                        if v___x_2472_ == 0 {
                            v___x_2476_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__8);
                            v___x_2477_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_2476_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
                            return v___x_2477_;
                        } else {
                            if lean_obj_tag(v_p_2450_) == 0 {
                                if v___x_2472_ == 0 {
                                    state = 2;
                                    continue;
                                } else {
                                    state = 1;
                                    continue;
                                }
                            } else {
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                v___x_2464_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___closed__2);
                v___x_2465_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_2464_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_, v_a_2461_);
                return v___x_2465_;
            }
            2 => {
                if v___x_2472_ == 0 {
                    state = 1;
                    continue;
                } else {
                    v___x_2474_ = lean_box(0);
                    v___x_2475_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2475_, 0, v___x_2474_);
                    return v___x_2475_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly___boxed(
    mut v_p_2478_: *mut LeanObject,
    mut v_a_2479_: *mut LeanObject,
    mut v_a_2480_: *mut LeanObject,
    mut v_a_2481_: *mut LeanObject,
    mut v_a_2482_: *mut LeanObject,
    mut v_a_2483_: *mut LeanObject,
    mut v_a_2484_: *mut LeanObject,
    mut v_a_2485_: *mut LeanObject,
    mut v_a_2486_: *mut LeanObject,
    mut v_a_2487_: *mut LeanObject,
    mut v_a_2488_: *mut LeanObject,
    mut v_a_2489_: *mut LeanObject,
    mut v_a_2490_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2491_: *mut LeanObject = core::ptr::null_mut();
    v_res_2491_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_2478_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
    lean_dec(v_a_2489_);
    lean_dec_ref(v_a_2488_);
    lean_dec(v_a_2487_);
    lean_dec_ref(v_a_2486_);
    lean_dec(v_a_2485_);
    lean_dec_ref(v_a_2484_);
    lean_dec(v_a_2483_);
    lean_dec_ref(v_a_2482_);
    lean_dec(v_a_2481_);
    lean_dec(v_a_2480_);
    lean_dec_ref(v_a_2479_);
    lean_dec_ref(v_p_2478_);
    return v_res_2491_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(
    mut v_as_x27_2492_: *mut LeanObject,
    mut v_b_2493_: *mut LeanObject,
    mut v___y_2494_: *mut LeanObject,
    mut v___y_2495_: *mut LeanObject,
    mut v___y_2496_: *mut LeanObject,
    mut v___y_2497_: *mut LeanObject,
    mut v___y_2498_: *mut LeanObject,
    mut v___y_2499_: *mut LeanObject,
    mut v___y_2500_: *mut LeanObject,
    mut v___y_2501_: *mut LeanObject,
    mut v___y_2502_: *mut LeanObject,
    mut v___y_2503_: *mut LeanObject,
    mut v___y_2504_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_head_2507_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_2508_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2509_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2510_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2511_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2512_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2517_: u8 = 0;
    let mut v___x_2519_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2521_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_as_x27_2492_) == 0 {
                    v___x_2506_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2506_, 0, v_b_2493_);
                    return v___x_2506_;
                } else {
                    v_head_2507_ = lean_ctor_get(v_as_x27_2492_, 0);
                    v_tail_2508_ = lean_ctor_get(v_as_x27_2492_, 1);
                    v_p_2509_ = lean_ctor_get(v_head_2507_, 0);
                    v___x_2510_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_2509_, v___y_2494_, v___y_2495_, v___y_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_, v___y_2504_);
                    if lean_obj_tag(v___x_2510_) == 0 {
                        lean_dec_ref_known(v___x_2510_, 1);
                        v___x_2511_ = lean_unsigned_to_nat(1);
                        v___x_2512_ = lean_nat_add(v_b_2493_, v___x_2511_);
                        lean_dec(v_b_2493_);
                        v_as_x27_2492_ = v_tail_2508_;
                        v_b_2493_ = v___x_2512_;
                        state = 0;
                        continue;
                    } else {
                        lean_dec(v_b_2493_);
                        v_a_2514_ = lean_ctor_get(v___x_2510_, 0);
                        v_isSharedCheck_2521_ = (!lean_is_exclusive(v___x_2510_)) as u8;
                        if v_isSharedCheck_2521_ == 0 {
                            v___x_2516_ = v___x_2510_;
                            v_isShared_2517_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2514_);
                            lean_dec(v___x_2510_);
                            v___x_2516_ = lean_box(0);
                            v_isShared_2517_ = v_isSharedCheck_2521_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2517_ == 0 {
                    v___x_2519_ = v___x_2516_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
                    v___x_2519_ = v_reuseFailAlloc_2520_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2519_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg___boxed(
    mut v_as_x27_2522_: *mut LeanObject,
    mut v_b_2523_: *mut LeanObject,
    mut v___y_2524_: *mut LeanObject,
    mut v___y_2525_: *mut LeanObject,
    mut v___y_2526_: *mut LeanObject,
    mut v___y_2527_: *mut LeanObject,
    mut v___y_2528_: *mut LeanObject,
    mut v___y_2529_: *mut LeanObject,
    mut v___y_2530_: *mut LeanObject,
    mut v___y_2531_: *mut LeanObject,
    mut v___y_2532_: *mut LeanObject,
    mut v___y_2533_: *mut LeanObject,
    mut v___y_2534_: *mut LeanObject,
    mut v___y_2535_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2536_: *mut LeanObject = core::ptr::null_mut();
    v_res_2536_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_as_x27_2522_, v_b_2523_, v___y_2524_, v___y_2525_, v___y_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_, v___y_2532_, v___y_2533_, v___y_2534_);
    lean_dec(v___y_2534_);
    lean_dec_ref(v___y_2533_);
    lean_dec(v___y_2532_);
    lean_dec_ref(v___y_2531_);
    lean_dec(v___y_2530_);
    lean_dec_ref(v___y_2529_);
    lean_dec(v___y_2528_);
    lean_dec_ref(v___y_2527_);
    lean_dec(v___y_2526_);
    lean_dec(v___y_2525_);
    lean_dec_ref(v___y_2524_);
    lean_dec(v_as_x27_2522_);
    return v_res_2536_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(
    mut v_a_2537_: *mut LeanObject,
    mut v_a_2538_: *mut LeanObject,
    mut v_a_2539_: *mut LeanObject,
    mut v_a_2540_: *mut LeanObject,
    mut v_a_2541_: *mut LeanObject,
    mut v_a_2542_: *mut LeanObject,
    mut v_a_2543_: *mut LeanObject,
    mut v_a_2544_: *mut LeanObject,
    mut v_a_2545_: *mut LeanObject,
    mut v_a_2546_: *mut LeanObject,
    mut v_a_2547_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2550_: *mut LeanObject = core::ptr::null_mut();
    let mut v_basis_2551_: *mut LeanObject = core::ptr::null_mut();
    let mut v_x_2552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2556_: u8 = 0;
    let mut v___x_2557_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2560_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2561_: u8 = 0;
    let mut v_unused_2562_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2563_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2565_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2566_: u8 = 0;
    let mut v___x_2568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2569_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2570_: u8 = 0;
    let mut v_a_2571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2573_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2574_: u8 = 0;
    let mut v___x_2576_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2578_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2549_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_,
                    v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_,
                );
                if lean_obj_tag(v___x_2549_) == 0 {
                    v_a_2550_ = lean_ctor_get(v___x_2549_, 0);
                    lean_inc(v_a_2550_);
                    lean_dec_ref_known(v___x_2549_, 1);
                    v_basis_2551_ = lean_ctor_get(v_a_2550_, 12);
                    lean_inc(v_basis_2551_);
                    lean_dec(v_a_2550_);
                    v_x_2552_ = lean_unsigned_to_nat(0);
                    v___x_2553_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_basis_2551_, v_x_2552_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_, v_a_2542_, v_a_2543_, v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
                    lean_dec(v_basis_2551_);
                    if lean_obj_tag(v___x_2553_) == 0 {
                        v_isSharedCheck_2561_ = (!lean_is_exclusive(v___x_2553_)) as u8;
                        if v_isSharedCheck_2561_ == 0 {
                            v_unused_2562_ = lean_ctor_get(v___x_2553_, 0);
                            lean_dec(v_unused_2562_);
                            v___x_2555_ = v___x_2553_;
                            v_isShared_2556_ = v_isSharedCheck_2561_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2553_);
                            v___x_2555_ = lean_box(0);
                            v_isShared_2556_ = v_isSharedCheck_2561_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2563_ = lean_ctor_get(v___x_2553_, 0);
                        v_isSharedCheck_2570_ = (!lean_is_exclusive(v___x_2553_)) as u8;
                        if v_isSharedCheck_2570_ == 0 {
                            v___x_2565_ = v___x_2553_;
                            v_isShared_2566_ = v_isSharedCheck_2570_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2563_);
                            lean_dec(v___x_2553_);
                            v___x_2565_ = lean_box(0);
                            v_isShared_2566_ = v_isSharedCheck_2570_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2571_ = lean_ctor_get(v___x_2549_, 0);
                    v_isSharedCheck_2578_ = (!lean_is_exclusive(v___x_2549_)) as u8;
                    if v_isSharedCheck_2578_ == 0 {
                        v___x_2573_ = v___x_2549_;
                        v_isShared_2574_ = v_isSharedCheck_2578_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2571_);
                        lean_dec(v___x_2549_);
                        v___x_2573_ = lean_box(0);
                        v_isShared_2574_ = v_isSharedCheck_2578_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_2557_ = lean_box(0);
                if v_isShared_2556_ == 0 {
                    lean_ctor_set(v___x_2555_, 0, v___x_2557_);
                    v___x_2559_ = v___x_2555_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
                    v___x_2559_ = v_reuseFailAlloc_2560_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2559_;
            }
            3 => {
                if v_isShared_2566_ == 0 {
                    v___x_2568_ = v___x_2565_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
                    v___x_2568_ = v_reuseFailAlloc_2569_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2568_;
            }
            5 => {
                if v_isShared_2574_ == 0 {
                    v___x_2576_ = v___x_2573_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2577_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2577_, 0, v_a_2571_);
                    v___x_2576_ = v_reuseFailAlloc_2577_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2576_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis___boxed(
    mut v_a_2579_: *mut LeanObject,
    mut v_a_2580_: *mut LeanObject,
    mut v_a_2581_: *mut LeanObject,
    mut v_a_2582_: *mut LeanObject,
    mut v_a_2583_: *mut LeanObject,
    mut v_a_2584_: *mut LeanObject,
    mut v_a_2585_: *mut LeanObject,
    mut v_a_2586_: *mut LeanObject,
    mut v_a_2587_: *mut LeanObject,
    mut v_a_2588_: *mut LeanObject,
    mut v_a_2589_: *mut LeanObject,
    mut v_a_2590_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2591_: *mut LeanObject = core::ptr::null_mut();
    v_res_2591_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_, v_a_2583_, v_a_2584_, v_a_2585_, v_a_2586_, v_a_2587_, v_a_2588_, v_a_2589_);
    lean_dec(v_a_2589_);
    lean_dec_ref(v_a_2588_);
    lean_dec(v_a_2587_);
    lean_dec_ref(v_a_2586_);
    lean_dec(v_a_2585_);
    lean_dec_ref(v_a_2584_);
    lean_dec(v_a_2583_);
    lean_dec_ref(v_a_2582_);
    lean_dec(v_a_2581_);
    lean_dec(v_a_2580_);
    lean_dec_ref(v_a_2579_);
    return v_res_2591_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(
    mut v_as_2592_: *mut LeanObject,
    mut v_as_x27_2593_: *mut LeanObject,
    mut v_b_2594_: *mut LeanObject,
    mut v_a_2595_: *mut LeanObject,
    mut v___y_2596_: *mut LeanObject,
    mut v___y_2597_: *mut LeanObject,
    mut v___y_2598_: *mut LeanObject,
    mut v___y_2599_: *mut LeanObject,
    mut v___y_2600_: *mut LeanObject,
    mut v___y_2601_: *mut LeanObject,
    mut v___y_2602_: *mut LeanObject,
    mut v___y_2603_: *mut LeanObject,
    mut v___y_2604_: *mut LeanObject,
    mut v___y_2605_: *mut LeanObject,
    mut v___y_2606_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2608_: *mut LeanObject = core::ptr::null_mut();
    v___x_2608_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___redArg(v_as_x27_2593_, v_b_2594_, v___y_2596_, v___y_2597_, v___y_2598_, v___y_2599_, v___y_2600_, v___y_2601_, v___y_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
    return v___x_2608_;
}
pub unsafe fn l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0___boxed(
    mut v_as_2609_: *mut LeanObject,
    mut v_as_x27_2610_: *mut LeanObject,
    mut v_b_2611_: *mut LeanObject,
    mut v_a_2612_: *mut LeanObject,
    mut v___y_2613_: *mut LeanObject,
    mut v___y_2614_: *mut LeanObject,
    mut v___y_2615_: *mut LeanObject,
    mut v___y_2616_: *mut LeanObject,
    mut v___y_2617_: *mut LeanObject,
    mut v___y_2618_: *mut LeanObject,
    mut v___y_2619_: *mut LeanObject,
    mut v___y_2620_: *mut LeanObject,
    mut v___y_2621_: *mut LeanObject,
    mut v___y_2622_: *mut LeanObject,
    mut v___y_2623_: *mut LeanObject,
    mut v___y_2624_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2625_: *mut LeanObject = core::ptr::null_mut();
    v_res_2625_ = l_List_forIn_x27_loop___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis_spec__0(v_as_2609_, v_as_x27_2610_, v_b_2611_, v_a_2612_, v___y_2613_, v___y_2614_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, v___y_2620_, v___y_2621_, v___y_2622_, v___y_2623_);
    lean_dec(v___y_2623_);
    lean_dec_ref(v___y_2622_);
    lean_dec(v___y_2621_);
    lean_dec_ref(v___y_2620_);
    lean_dec(v___y_2619_);
    lean_dec_ref(v___y_2618_);
    lean_dec(v___y_2617_);
    lean_dec_ref(v___y_2616_);
    lean_dec(v___y_2615_);
    lean_dec(v___y_2614_);
    lean_dec_ref(v___y_2613_);
    lean_dec(v_as_x27_2610_);
    lean_dec(v_as_2609_);
    return v_res_2625_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(
    mut v_init_2626_: *mut LeanObject,
    mut v_x_2627_: *mut LeanObject,
    mut v___y_2628_: *mut LeanObject,
    mut v___y_2629_: *mut LeanObject,
    mut v___y_2630_: *mut LeanObject,
    mut v___y_2631_: *mut LeanObject,
    mut v___y_2632_: *mut LeanObject,
    mut v___y_2633_: *mut LeanObject,
    mut v___y_2634_: *mut LeanObject,
    mut v___y_2635_: *mut LeanObject,
    mut v___y_2636_: *mut LeanObject,
    mut v___y_2637_: *mut LeanObject,
    mut v___y_2638_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_k_2640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_2641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_2642_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2643_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_2644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2645_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2646_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2648_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2650_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2651_: u8 = 0;
    let mut v___x_2653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2654_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2655_: u8 = 0;
    let mut v___x_2656_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2657_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_2627_) == 0 {
                    v_k_2640_ = lean_ctor_get(v_x_2627_, 1);
                    v_l_2641_ = lean_ctor_get(v_x_2627_, 3);
                    v_r_2642_ = lean_ctor_get(v_x_2627_, 4);
                    v___x_2643_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v_init_2626_, v_l_2641_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
                    if lean_obj_tag(v___x_2643_) == 0 {
                        lean_dec_ref_known(v___x_2643_, 1);
                        v_p_2644_ = lean_ctor_get(v_k_2640_, 0);
                        v___x_2645_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v_p_2644_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_, v___y_2632_, v___y_2633_, v___y_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
                        if lean_obj_tag(v___x_2645_) == 0 {
                            lean_dec_ref_known(v___x_2645_, 1);
                            v___x_2646_ = lean_box(0);
                            v_init_2626_ = v___x_2646_;
                            v_x_2627_ = v_r_2642_;
                            state = 0;
                            continue;
                        } else {
                            v_a_2648_ = lean_ctor_get(v___x_2645_, 0);
                            v_isSharedCheck_2655_ = (!lean_is_exclusive(v___x_2645_)) as u8;
                            if v_isSharedCheck_2655_ == 0 {
                                v___x_2650_ = v___x_2645_;
                                v_isShared_2651_ = v_isSharedCheck_2655_;
                                state = 1;
                                continue;
                            } else {
                                lean_inc(v_a_2648_);
                                lean_dec(v___x_2645_);
                                v___x_2650_ = lean_box(0);
                                v_isShared_2651_ = v_isSharedCheck_2655_;
                                state = 1;
                                continue;
                            }
                        }
                    } else {
                        return v___x_2643_;
                    }
                } else {
                    v___x_2656_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2656_, 0, v_init_2626_);
                    v___x_2657_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2657_, 0, v___x_2656_);
                    return v___x_2657_;
                }
            }
            1 => {
                if v_isShared_2651_ == 0 {
                    v___x_2653_ = v___x_2650_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2648_);
                    v___x_2653_ = v_reuseFailAlloc_2654_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2653_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0___boxed(
    mut v_init_2658_: *mut LeanObject,
    mut v_x_2659_: *mut LeanObject,
    mut v___y_2660_: *mut LeanObject,
    mut v___y_2661_: *mut LeanObject,
    mut v___y_2662_: *mut LeanObject,
    mut v___y_2663_: *mut LeanObject,
    mut v___y_2664_: *mut LeanObject,
    mut v___y_2665_: *mut LeanObject,
    mut v___y_2666_: *mut LeanObject,
    mut v___y_2667_: *mut LeanObject,
    mut v___y_2668_: *mut LeanObject,
    mut v___y_2669_: *mut LeanObject,
    mut v___y_2670_: *mut LeanObject,
    mut v___y_2671_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2672_: *mut LeanObject = core::ptr::null_mut();
    v_res_2672_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v_init_2658_, v_x_2659_, v___y_2660_, v___y_2661_, v___y_2662_, v___y_2663_, v___y_2664_, v___y_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_, v___y_2670_);
    lean_dec(v___y_2670_);
    lean_dec_ref(v___y_2669_);
    lean_dec(v___y_2668_);
    lean_dec_ref(v___y_2667_);
    lean_dec(v___y_2666_);
    lean_dec_ref(v___y_2665_);
    lean_dec(v___y_2664_);
    lean_dec_ref(v___y_2663_);
    lean_dec(v___y_2662_);
    lean_dec(v___y_2661_);
    lean_dec_ref(v___y_2660_);
    lean_dec(v_x_2659_);
    return v_res_2672_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(
    mut v_a_2673_: *mut LeanObject,
    mut v_a_2674_: *mut LeanObject,
    mut v_a_2675_: *mut LeanObject,
    mut v_a_2676_: *mut LeanObject,
    mut v_a_2677_: *mut LeanObject,
    mut v_a_2678_: *mut LeanObject,
    mut v_a_2679_: *mut LeanObject,
    mut v_a_2680_: *mut LeanObject,
    mut v_a_2681_: *mut LeanObject,
    mut v_a_2682_: *mut LeanObject,
    mut v_a_2683_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2686_: *mut LeanObject = core::ptr::null_mut();
    let mut v_queue_2687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2689_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2691_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2692_: u8 = 0;
    let mut v___x_2694_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2695_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2696_: u8 = 0;
    let mut v_unused_2697_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2698_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2701_: u8 = 0;
    let mut v___x_2703_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2704_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2705_: u8 = 0;
    let mut v_a_2706_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2708_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2709_: u8 = 0;
    let mut v___x_2711_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2712_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2713_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2685_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_,
                    v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_,
                );
                if lean_obj_tag(v___x_2685_) == 0 {
                    v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
                    lean_inc(v_a_2686_);
                    lean_dec_ref_known(v___x_2685_, 1);
                    v_queue_2687_ = lean_ctor_get(v_a_2686_, 11);
                    lean_inc(v_queue_2687_);
                    lean_dec(v_a_2686_);
                    v___x_2688_ = lean_box(0);
                    v___x_2689_ = l_Std_DTreeMap_Internal_Impl_forInStep___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue_spec__0(v___x_2688_, v_queue_2687_, v_a_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
                    lean_dec(v_queue_2687_);
                    if lean_obj_tag(v___x_2689_) == 0 {
                        v_isSharedCheck_2696_ = (!lean_is_exclusive(v___x_2689_)) as u8;
                        if v_isSharedCheck_2696_ == 0 {
                            v_unused_2697_ = lean_ctor_get(v___x_2689_, 0);
                            lean_dec(v_unused_2697_);
                            v___x_2691_ = v___x_2689_;
                            v_isShared_2692_ = v_isSharedCheck_2696_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_2689_);
                            v___x_2691_ = lean_box(0);
                            v_isShared_2692_ = v_isSharedCheck_2696_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2698_ = lean_ctor_get(v___x_2689_, 0);
                        v_isSharedCheck_2705_ = (!lean_is_exclusive(v___x_2689_)) as u8;
                        if v_isSharedCheck_2705_ == 0 {
                            v___x_2700_ = v___x_2689_;
                            v_isShared_2701_ = v_isSharedCheck_2705_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_2698_);
                            lean_dec(v___x_2689_);
                            v___x_2700_ = lean_box(0);
                            v_isShared_2701_ = v_isSharedCheck_2705_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_2706_ = lean_ctor_get(v___x_2685_, 0);
                    v_isSharedCheck_2713_ = (!lean_is_exclusive(v___x_2685_)) as u8;
                    if v_isSharedCheck_2713_ == 0 {
                        v___x_2708_ = v___x_2685_;
                        v_isShared_2709_ = v_isSharedCheck_2713_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_2706_);
                        lean_dec(v___x_2685_);
                        v___x_2708_ = lean_box(0);
                        v_isShared_2709_ = v_isSharedCheck_2713_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_2692_ == 0 {
                    lean_ctor_set(v___x_2691_, 0, v___x_2688_);
                    v___x_2694_ = v___x_2691_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2695_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2695_, 0, v___x_2688_);
                    v___x_2694_ = v_reuseFailAlloc_2695_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2694_;
            }
            3 => {
                if v_isShared_2701_ == 0 {
                    v___x_2703_ = v___x_2700_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2704_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2704_, 0, v_a_2698_);
                    v___x_2703_ = v_reuseFailAlloc_2704_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2703_;
            }
            5 => {
                if v_isShared_2709_ == 0 {
                    v___x_2711_ = v___x_2708_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_2712_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2712_, 0, v_a_2706_);
                    v___x_2711_ = v_reuseFailAlloc_2712_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_2711_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue___boxed(
    mut v_a_2714_: *mut LeanObject,
    mut v_a_2715_: *mut LeanObject,
    mut v_a_2716_: *mut LeanObject,
    mut v_a_2717_: *mut LeanObject,
    mut v_a_2718_: *mut LeanObject,
    mut v_a_2719_: *mut LeanObject,
    mut v_a_2720_: *mut LeanObject,
    mut v_a_2721_: *mut LeanObject,
    mut v_a_2722_: *mut LeanObject,
    mut v_a_2723_: *mut LeanObject,
    mut v_a_2724_: *mut LeanObject,
    mut v_a_2725_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2726_: *mut LeanObject = core::ptr::null_mut();
    v_res_2726_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(v_a_2714_, v_a_2715_, v_a_2716_, v_a_2717_, v_a_2718_, v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
    lean_dec(v_a_2724_);
    lean_dec_ref(v_a_2723_);
    lean_dec(v_a_2722_);
    lean_dec_ref(v_a_2721_);
    lean_dec(v_a_2720_);
    lean_dec_ref(v_a_2719_);
    lean_dec(v_a_2718_);
    lean_dec_ref(v_a_2717_);
    lean_dec(v_a_2716_);
    lean_dec(v_a_2715_);
    lean_dec_ref(v_a_2714_);
    return v_res_2726_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(
    mut v_as_2730_: *mut LeanObject,
    mut v_sz_2731_: usize,
    mut v_i_2732_: usize,
    mut v_b_2733_: *mut LeanObject,
    mut v___y_2734_: *mut LeanObject,
    mut v___y_2735_: *mut LeanObject,
    mut v___y_2736_: *mut LeanObject,
    mut v___y_2737_: *mut LeanObject,
    mut v___y_2738_: *mut LeanObject,
    mut v___y_2739_: *mut LeanObject,
    mut v___y_2740_: *mut LeanObject,
    mut v___y_2741_: *mut LeanObject,
    mut v___y_2742_: *mut LeanObject,
    mut v___y_2743_: *mut LeanObject,
    mut v___y_2744_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2746_: u8 = 0;
    let mut v___x_2747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_2749_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2751_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2753_: usize = 0;
    let mut v___x_2754_: usize = 0;
    let mut v_a_2756_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2759_: u8 = 0;
    let mut v___x_2761_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2762_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2763_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2746_ = lean_usize_dec_lt(v_i_2732_, v_sz_2731_);
                if v___x_2746_ == 0 {
                    v___x_2747_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2747_, 0, v_b_2733_);
                    return v___x_2747_;
                } else {
                    lean_dec_ref(v_b_2733_);
                    v_a_2748_ = lean_array_uget_borrowed(v_as_2730_, v_i_2732_);
                    v_d_2749_ = lean_ctor_get(v_a_2748_, 4);
                    v___x_2750_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_2749_);
                    v___x_2751_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_2750_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_, v___y_2738_, v___y_2739_, v___y_2740_, v___y_2741_, v___y_2742_, v___y_2743_, v___y_2744_);
                    lean_dec_ref(v___x_2750_);
                    if lean_obj_tag(v___x_2751_) == 0 {
                        lean_dec_ref_known(v___x_2751_, 1);
                        v___x_2752_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0;
                        v___x_2753_ = 1usize;
                        v___x_2754_ = lean_usize_add(v_i_2732_, v___x_2753_);
                        v_i_2732_ = v___x_2754_;
                        v_b_2733_ = v___x_2752_;
                        state = 0;
                        continue;
                    } else {
                        v_a_2756_ = lean_ctor_get(v___x_2751_, 0);
                        v_isSharedCheck_2763_ = (!lean_is_exclusive(v___x_2751_)) as u8;
                        if v_isSharedCheck_2763_ == 0 {
                            v___x_2758_ = v___x_2751_;
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2756_);
                            lean_dec(v___x_2751_);
                            v___x_2758_ = lean_box(0);
                            v_isShared_2759_ = v_isSharedCheck_2763_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2759_ == 0 {
                    v___x_2761_ = v___x_2758_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
                    v___x_2761_ = v_reuseFailAlloc_2762_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2761_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___boxed(
    mut v_as_2764_: *mut LeanObject,
    mut v_sz_2765_: *mut LeanObject,
    mut v_i_2766_: *mut LeanObject,
    mut v_b_2767_: *mut LeanObject,
    mut v___y_2768_: *mut LeanObject,
    mut v___y_2769_: *mut LeanObject,
    mut v___y_2770_: *mut LeanObject,
    mut v___y_2771_: *mut LeanObject,
    mut v___y_2772_: *mut LeanObject,
    mut v___y_2773_: *mut LeanObject,
    mut v___y_2774_: *mut LeanObject,
    mut v___y_2775_: *mut LeanObject,
    mut v___y_2776_: *mut LeanObject,
    mut v___y_2777_: *mut LeanObject,
    mut v___y_2778_: *mut LeanObject,
    mut v___y_2779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2780_: usize = 0;
    let mut v_i_boxed_2781_: usize = 0;
    let mut v_res_2782_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2780_ = lean_unbox_usize(v_sz_2765_);
    lean_dec(v_sz_2765_);
    v_i_boxed_2781_ = lean_unbox_usize(v_i_2766_);
    lean_dec(v_i_2766_);
    v_res_2782_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_2764_, v_sz_boxed_2780_, v_i_boxed_2781_, v_b_2767_, v___y_2768_, v___y_2769_, v___y_2770_, v___y_2771_, v___y_2772_, v___y_2773_, v___y_2774_, v___y_2775_, v___y_2776_, v___y_2777_, v___y_2778_);
    lean_dec(v___y_2778_);
    lean_dec_ref(v___y_2777_);
    lean_dec(v___y_2776_);
    lean_dec_ref(v___y_2775_);
    lean_dec(v___y_2774_);
    lean_dec_ref(v___y_2773_);
    lean_dec(v___y_2772_);
    lean_dec_ref(v___y_2771_);
    lean_dec(v___y_2770_);
    lean_dec(v___y_2769_);
    lean_dec_ref(v___y_2768_);
    lean_dec_ref(v_as_2764_);
    return v_res_2782_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(
    mut v_as_2783_: *mut LeanObject,
    mut v_sz_2784_: usize,
    mut v_i_2785_: usize,
    mut v_b_2786_: *mut LeanObject,
    mut v___y_2787_: *mut LeanObject,
    mut v___y_2788_: *mut LeanObject,
    mut v___y_2789_: *mut LeanObject,
    mut v___y_2790_: *mut LeanObject,
    mut v___y_2791_: *mut LeanObject,
    mut v___y_2792_: *mut LeanObject,
    mut v___y_2793_: *mut LeanObject,
    mut v___y_2794_: *mut LeanObject,
    mut v___y_2795_: *mut LeanObject,
    mut v___y_2796_: *mut LeanObject,
    mut v___y_2797_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2799_: u8 = 0;
    let mut v___x_2800_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_2802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2803_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2804_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2805_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2806_: usize = 0;
    let mut v___x_2807_: usize = 0;
    let mut v___x_2808_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2812_: u8 = 0;
    let mut v___x_2814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2799_ = lean_usize_dec_lt(v_i_2785_, v_sz_2784_);
                if v___x_2799_ == 0 {
                    v___x_2800_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2800_, 0, v_b_2786_);
                    return v___x_2800_;
                } else {
                    lean_dec_ref(v_b_2786_);
                    v_a_2801_ = lean_array_uget_borrowed(v_as_2783_, v_i_2785_);
                    v_d_2802_ = lean_ctor_get(v_a_2801_, 4);
                    v___x_2803_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_2802_);
                    v___x_2804_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_2803_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
                    lean_dec_ref(v___x_2803_);
                    if lean_obj_tag(v___x_2804_) == 0 {
                        lean_dec_ref_known(v___x_2804_, 1);
                        v___x_2805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3___closed__0;
                        v___x_2806_ = 1usize;
                        v___x_2807_ = lean_usize_add(v_i_2785_, v___x_2806_);
                        v___x_2808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2_spec__3(v_as_2783_, v_sz_2784_, v___x_2807_, v___x_2805_, v___y_2787_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, v___y_2792_, v___y_2793_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
                        return v___x_2808_;
                    } else {
                        v_a_2809_ = lean_ctor_get(v___x_2804_, 0);
                        v_isSharedCheck_2816_ = (!lean_is_exclusive(v___x_2804_)) as u8;
                        if v_isSharedCheck_2816_ == 0 {
                            v___x_2811_ = v___x_2804_;
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2809_);
                            lean_dec(v___x_2804_);
                            v___x_2811_ = lean_box(0);
                            v_isShared_2812_ = v_isSharedCheck_2816_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_2812_ == 0 {
                    v___x_2814_ = v___x_2811_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_2815_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_a_2809_);
                    v___x_2814_ = v_reuseFailAlloc_2815_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_2814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2___boxed(
    mut v_as_2817_: *mut LeanObject,
    mut v_sz_2818_: *mut LeanObject,
    mut v_i_2819_: *mut LeanObject,
    mut v_b_2820_: *mut LeanObject,
    mut v___y_2821_: *mut LeanObject,
    mut v___y_2822_: *mut LeanObject,
    mut v___y_2823_: *mut LeanObject,
    mut v___y_2824_: *mut LeanObject,
    mut v___y_2825_: *mut LeanObject,
    mut v___y_2826_: *mut LeanObject,
    mut v___y_2827_: *mut LeanObject,
    mut v___y_2828_: *mut LeanObject,
    mut v___y_2829_: *mut LeanObject,
    mut v___y_2830_: *mut LeanObject,
    mut v___y_2831_: *mut LeanObject,
    mut v___y_2832_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_2833_: usize = 0;
    let mut v_i_boxed_2834_: usize = 0;
    let mut v_res_2835_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2833_ = lean_unbox_usize(v_sz_2818_);
    lean_dec(v_sz_2818_);
    v_i_boxed_2834_ = lean_unbox_usize(v_i_2819_);
    lean_dec(v_i_2819_);
    v_res_2835_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(v_as_2817_, v_sz_boxed_2833_, v_i_boxed_2834_, v_b_2820_, v___y_2821_, v___y_2822_, v___y_2823_, v___y_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_, v___y_2830_, v___y_2831_);
    lean_dec(v___y_2831_);
    lean_dec_ref(v___y_2830_);
    lean_dec(v___y_2829_);
    lean_dec_ref(v___y_2828_);
    lean_dec(v___y_2827_);
    lean_dec_ref(v___y_2826_);
    lean_dec(v___y_2825_);
    lean_dec_ref(v___y_2824_);
    lean_dec(v___y_2823_);
    lean_dec(v___y_2822_);
    lean_dec_ref(v___y_2821_);
    lean_dec_ref(v_as_2817_);
    return v_res_2835_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(
    mut v_init_2836_: *mut LeanObject,
    mut v_n_2837_: *mut LeanObject,
    mut v_b_2838_: *mut LeanObject,
    mut v___y_2839_: *mut LeanObject,
    mut v___y_2840_: *mut LeanObject,
    mut v___y_2841_: *mut LeanObject,
    mut v___y_2842_: *mut LeanObject,
    mut v___y_2843_: *mut LeanObject,
    mut v___y_2844_: *mut LeanObject,
    mut v___y_2845_: *mut LeanObject,
    mut v___y_2846_: *mut LeanObject,
    mut v___y_2847_: *mut LeanObject,
    mut v___y_2848_: *mut LeanObject,
    mut v___y_2849_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_2851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2854_: usize = 0;
    let mut v___x_2855_: usize = 0;
    let mut v___x_2856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2859_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2860_: u8 = 0;
    let mut v_fst_2861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2870_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2871_: u8 = 0;
    let mut v_a_2872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2874_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2875_: u8 = 0;
    let mut v___x_2877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2878_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2879_: u8 = 0;
    let mut v_vs_2880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2882_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_2883_: usize = 0;
    let mut v___x_2884_: usize = 0;
    let mut v___x_2885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2888_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2889_: u8 = 0;
    let mut v_fst_2890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2892_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2895_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_2896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2899_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2900_: u8 = 0;
    let mut v_a_2901_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2903_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2904_: u8 = 0;
    let mut v___x_2906_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2907_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2908_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_2837_) == 0 {
                    v_cs_2851_ = lean_ctor_get(v_n_2837_, 0);
                    v___x_2852_ = lean_box(0);
                    v___x_2853_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2853_, 0, v___x_2852_);
                    lean_ctor_set(v___x_2853_, 1, v_b_2838_);
                    v_sz_2854_ = lean_array_size(v_cs_2851_);
                    v___x_2855_ = 0usize;
                    v___x_2856_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(v_init_2836_, v_cs_2851_, v_sz_2854_, v___x_2855_, v___x_2853_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
                    if lean_obj_tag(v___x_2856_) == 0 {
                        v_a_2857_ = lean_ctor_get(v___x_2856_, 0);
                        v_isSharedCheck_2871_ = (!lean_is_exclusive(v___x_2856_)) as u8;
                        if v_isSharedCheck_2871_ == 0 {
                            v___x_2859_ = v___x_2856_;
                            v_isShared_2860_ = v_isSharedCheck_2871_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_2857_);
                            lean_dec(v___x_2856_);
                            v___x_2859_ = lean_box(0);
                            v_isShared_2860_ = v_isSharedCheck_2871_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_2872_ = lean_ctor_get(v___x_2856_, 0);
                        v_isSharedCheck_2879_ = (!lean_is_exclusive(v___x_2856_)) as u8;
                        if v_isSharedCheck_2879_ == 0 {
                            v___x_2874_ = v___x_2856_;
                            v_isShared_2875_ = v_isSharedCheck_2879_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_2872_);
                            lean_dec(v___x_2856_);
                            v___x_2874_ = lean_box(0);
                            v_isShared_2875_ = v_isSharedCheck_2879_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_2880_ = lean_ctor_get(v_n_2837_, 0);
                    v___x_2881_ = lean_box(0);
                    v___x_2882_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_2882_, 0, v___x_2881_);
                    lean_ctor_set(v___x_2882_, 1, v_b_2838_);
                    v_sz_2883_ = lean_array_size(v_vs_2880_);
                    v___x_2884_ = 0usize;
                    v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__2(v_vs_2880_, v_sz_2883_, v___x_2884_, v___x_2882_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_, v___y_2847_, v___y_2848_, v___y_2849_);
                    if lean_obj_tag(v___x_2885_) == 0 {
                        v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
                        v_isSharedCheck_2900_ = (!lean_is_exclusive(v___x_2885_)) as u8;
                        if v_isSharedCheck_2900_ == 0 {
                            v___x_2888_ = v___x_2885_;
                            v_isShared_2889_ = v_isSharedCheck_2900_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_2886_);
                            lean_dec(v___x_2885_);
                            v___x_2888_ = lean_box(0);
                            v_isShared_2889_ = v_isSharedCheck_2900_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_2901_ = lean_ctor_get(v___x_2885_, 0);
                        v_isSharedCheck_2908_ = (!lean_is_exclusive(v___x_2885_)) as u8;
                        if v_isSharedCheck_2908_ == 0 {
                            v___x_2903_ = v___x_2885_;
                            v_isShared_2904_ = v_isSharedCheck_2908_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_2901_);
                            lean_dec(v___x_2885_);
                            v___x_2903_ = lean_box(0);
                            v_isShared_2904_ = v_isSharedCheck_2908_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_2861_ = lean_ctor_get(v_a_2857_, 0);
                if lean_obj_tag(v_fst_2861_) == 0 {
                    v_snd_2862_ = lean_ctor_get(v_a_2857_, 1);
                    lean_inc(v_snd_2862_);
                    lean_dec(v_a_2857_);
                    v___x_2863_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2863_, 0, v_snd_2862_);
                    if v_isShared_2860_ == 0 {
                        lean_ctor_set(v___x_2859_, 0, v___x_2863_);
                        v___x_2865_ = v___x_2859_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_2866_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2866_, 0, v___x_2863_);
                        v___x_2865_ = v_reuseFailAlloc_2866_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2861_);
                    lean_dec(v_a_2857_);
                    v_val_2867_ = lean_ctor_get(v_fst_2861_, 0);
                    lean_inc(v_val_2867_);
                    lean_dec_ref_known(v_fst_2861_, 1);
                    if v_isShared_2860_ == 0 {
                        lean_ctor_set(v___x_2859_, 0, v_val_2867_);
                        v___x_2869_ = v___x_2859_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2870_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2870_, 0, v_val_2867_);
                        v___x_2869_ = v_reuseFailAlloc_2870_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_2865_;
            }
            3 => {
                return v___x_2869_;
            }
            4 => {
                if v_isShared_2875_ == 0 {
                    v___x_2877_ = v___x_2874_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_2878_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2878_, 0, v_a_2872_);
                    v___x_2877_ = v_reuseFailAlloc_2878_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_2877_;
            }
            6 => {
                v_fst_2890_ = lean_ctor_get(v_a_2886_, 0);
                if lean_obj_tag(v_fst_2890_) == 0 {
                    v_snd_2891_ = lean_ctor_get(v_a_2886_, 1);
                    lean_inc(v_snd_2891_);
                    lean_dec(v_a_2886_);
                    v___x_2892_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2892_, 0, v_snd_2891_);
                    if v_isShared_2889_ == 0 {
                        lean_ctor_set(v___x_2888_, 0, v___x_2892_);
                        v___x_2894_ = v___x_2888_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_2895_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2895_, 0, v___x_2892_);
                        v___x_2894_ = v_reuseFailAlloc_2895_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_2890_);
                    lean_dec(v_a_2886_);
                    v_val_2896_ = lean_ctor_get(v_fst_2890_, 0);
                    lean_inc(v_val_2896_);
                    lean_dec_ref_known(v_fst_2890_, 1);
                    if v_isShared_2889_ == 0 {
                        lean_ctor_set(v___x_2888_, 0, v_val_2896_);
                        v___x_2898_ = v___x_2888_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2899_, 0, v_val_2896_);
                        v___x_2898_ = v_reuseFailAlloc_2899_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_2894_;
            }
            8 => {
                return v___x_2898_;
            }
            9 => {
                if v_isShared_2904_ == 0 {
                    v___x_2906_ = v___x_2903_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_2907_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2907_, 0, v_a_2901_);
                    v___x_2906_ = v_reuseFailAlloc_2907_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_2906_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(
    mut v_init_2909_: *mut LeanObject,
    mut v_as_2910_: *mut LeanObject,
    mut v_sz_2911_: usize,
    mut v_i_2912_: usize,
    mut v_b_2913_: *mut LeanObject,
    mut v___y_2914_: *mut LeanObject,
    mut v___y_2915_: *mut LeanObject,
    mut v___y_2916_: *mut LeanObject,
    mut v___y_2917_: *mut LeanObject,
    mut v___y_2918_: *mut LeanObject,
    mut v___y_2919_: *mut LeanObject,
    mut v___y_2920_: *mut LeanObject,
    mut v___y_2921_: *mut LeanObject,
    mut v___y_2922_: *mut LeanObject,
    mut v___y_2923_: *mut LeanObject,
    mut v___y_2924_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_2926_: u8 = 0;
    let mut v___x_2927_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_2928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2931_: u8 = 0;
    let mut v_a_2932_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2933_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2937_: u8 = 0;
    let mut v___x_2938_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2940_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2942_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2943_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2944_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_2945_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2946_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2948_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2949_: usize = 0;
    let mut v___x_2950_: usize = 0;
    let mut v_reuseFailAlloc_2952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2953_: u8 = 0;
    let mut v_a_2954_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_2957_: u8 = 0;
    let mut v___x_2959_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_2960_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_2961_: u8 = 0;
    let mut v_isSharedCheck_2962_: u8 = 0;
    let mut v_unused_2963_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_2926_ = lean_usize_dec_lt(v_i_2912_, v_sz_2911_);
                if v___x_2926_ == 0 {
                    v___x_2927_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_2927_, 0, v_b_2913_);
                    return v___x_2927_;
                } else {
                    v_snd_2928_ = lean_ctor_get(v_b_2913_, 1);
                    v_isSharedCheck_2962_ = (!lean_is_exclusive(v_b_2913_)) as u8;
                    if v_isSharedCheck_2962_ == 0 {
                        v_unused_2963_ = lean_ctor_get(v_b_2913_, 0);
                        lean_dec(v_unused_2963_);
                        v___x_2930_ = v_b_2913_;
                        v_isShared_2931_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_2928_);
                        lean_dec(v_b_2913_);
                        v___x_2930_ = lean_box(0);
                        v_isShared_2931_ = v_isSharedCheck_2962_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_2932_ = lean_array_uget_borrowed(v_as_2910_, v_i_2912_);
                lean_inc(v_snd_2928_);
                v___x_2933_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_2909_, v_a_2932_, v_snd_2928_, v___y_2914_, v___y_2915_, v___y_2916_, v___y_2917_, v___y_2918_, v___y_2919_, v___y_2920_, v___y_2921_, v___y_2922_, v___y_2923_, v___y_2924_);
                if lean_obj_tag(v___x_2933_) == 0 {
                    v_a_2934_ = lean_ctor_get(v___x_2933_, 0);
                    v_isSharedCheck_2953_ = (!lean_is_exclusive(v___x_2933_)) as u8;
                    if v_isSharedCheck_2953_ == 0 {
                        v___x_2936_ = v___x_2933_;
                        v_isShared_2937_ = v_isSharedCheck_2953_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_2934_);
                        lean_dec(v___x_2933_);
                        v___x_2936_ = lean_box(0);
                        v_isShared_2937_ = v_isSharedCheck_2953_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2930_);
                    lean_dec(v_snd_2928_);
                    v_a_2954_ = lean_ctor_get(v___x_2933_, 0);
                    v_isSharedCheck_2961_ = (!lean_is_exclusive(v___x_2933_)) as u8;
                    if v_isSharedCheck_2961_ == 0 {
                        v___x_2956_ = v___x_2933_;
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_2954_);
                        lean_dec(v___x_2933_);
                        v___x_2956_ = lean_box(0);
                        v_isShared_2957_ = v_isSharedCheck_2961_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_2934_) == 0 {
                    v___x_2938_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_2938_, 0, v_a_2934_);
                    if v_isShared_2931_ == 0 {
                        lean_ctor_set(v___x_2930_, 0, v___x_2938_);
                        v___x_2940_ = v___x_2930_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_2944_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2944_, 0, v___x_2938_);
                        lean_ctor_set(v_reuseFailAlloc_2944_, 1, v_snd_2928_);
                        v___x_2940_ = v_reuseFailAlloc_2944_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_2936_);
                    lean_dec(v_snd_2928_);
                    v_a_2945_ = lean_ctor_get(v_a_2934_, 0);
                    lean_inc(v_a_2945_);
                    lean_dec_ref_known(v_a_2934_, 1);
                    v___x_2946_ = lean_box(0);
                    if v_isShared_2931_ == 0 {
                        lean_ctor_set(v___x_2930_, 1, v_a_2945_);
                        lean_ctor_set(v___x_2930_, 0, v___x_2946_);
                        v___x_2948_ = v___x_2930_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_2952_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_2952_, 0, v___x_2946_);
                        lean_ctor_set(v_reuseFailAlloc_2952_, 1, v_a_2945_);
                        v___x_2948_ = v_reuseFailAlloc_2952_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_2937_ == 0 {
                    lean_ctor_set(v___x_2936_, 0, v___x_2940_);
                    v___x_2942_ = v___x_2936_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_2943_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2943_, 0, v___x_2940_);
                    v___x_2942_ = v_reuseFailAlloc_2943_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_2942_;
            }
            5 => {
                v___x_2949_ = 1usize;
                v___x_2950_ = lean_usize_add(v_i_2912_, v___x_2949_);
                v_i_2912_ = v___x_2950_;
                v_b_2913_ = v___x_2948_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_2957_ == 0 {
                    v___x_2959_ = v___x_2956_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_2960_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_2960_, 0, v_a_2954_);
                    v___x_2959_ = v_reuseFailAlloc_2960_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_2959_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_2964_: *mut LeanObject = *_args.add(0);
    let mut v_as_2965_: *mut LeanObject = *_args.add(1);
    let mut v_sz_2966_: *mut LeanObject = *_args.add(2);
    let mut v_i_2967_: *mut LeanObject = *_args.add(3);
    let mut v_b_2968_: *mut LeanObject = *_args.add(4);
    let mut v___y_2969_: *mut LeanObject = *_args.add(5);
    let mut v___y_2970_: *mut LeanObject = *_args.add(6);
    let mut v___y_2971_: *mut LeanObject = *_args.add(7);
    let mut v___y_2972_: *mut LeanObject = *_args.add(8);
    let mut v___y_2973_: *mut LeanObject = *_args.add(9);
    let mut v___y_2974_: *mut LeanObject = *_args.add(10);
    let mut v___y_2975_: *mut LeanObject = *_args.add(11);
    let mut v___y_2976_: *mut LeanObject = *_args.add(12);
    let mut v___y_2977_: *mut LeanObject = *_args.add(13);
    let mut v___y_2978_: *mut LeanObject = *_args.add(14);
    let mut v___y_2979_: *mut LeanObject = *_args.add(15);
    let mut v___y_2980_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_2981_: usize = 0;
    let mut v_i_boxed_2982_: usize = 0;
    let mut v_res_2983_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_2981_ = lean_unbox_usize(v_sz_2966_);
    lean_dec(v_sz_2966_);
    v_i_boxed_2982_ = lean_unbox_usize(v_i_2967_);
    lean_dec(v_i_2967_);
    v_res_2983_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0_spec__1(v_init_2964_, v_as_2965_, v_sz_boxed_2981_, v_i_boxed_2982_, v_b_2968_, v___y_2969_, v___y_2970_, v___y_2971_, v___y_2972_, v___y_2973_, v___y_2974_, v___y_2975_, v___y_2976_, v___y_2977_, v___y_2978_, v___y_2979_);
    lean_dec(v___y_2979_);
    lean_dec_ref(v___y_2978_);
    lean_dec(v___y_2977_);
    lean_dec_ref(v___y_2976_);
    lean_dec(v___y_2975_);
    lean_dec_ref(v___y_2974_);
    lean_dec(v___y_2973_);
    lean_dec_ref(v___y_2972_);
    lean_dec(v___y_2971_);
    lean_dec(v___y_2970_);
    lean_dec_ref(v___y_2969_);
    lean_dec_ref(v_as_2965_);
    return v_res_2983_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0___boxed(
    mut v_init_2984_: *mut LeanObject,
    mut v_n_2985_: *mut LeanObject,
    mut v_b_2986_: *mut LeanObject,
    mut v___y_2987_: *mut LeanObject,
    mut v___y_2988_: *mut LeanObject,
    mut v___y_2989_: *mut LeanObject,
    mut v___y_2990_: *mut LeanObject,
    mut v___y_2991_: *mut LeanObject,
    mut v___y_2992_: *mut LeanObject,
    mut v___y_2993_: *mut LeanObject,
    mut v___y_2994_: *mut LeanObject,
    mut v___y_2995_: *mut LeanObject,
    mut v___y_2996_: *mut LeanObject,
    mut v___y_2997_: *mut LeanObject,
    mut v___y_2998_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_2999_: *mut LeanObject = core::ptr::null_mut();
    v_res_2999_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_2984_, v_n_2985_, v_b_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_, v___y_2991_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_, v___y_2996_, v___y_2997_);
    lean_dec(v___y_2997_);
    lean_dec_ref(v___y_2996_);
    lean_dec(v___y_2995_);
    lean_dec_ref(v___y_2994_);
    lean_dec(v___y_2993_);
    lean_dec_ref(v___y_2992_);
    lean_dec(v___y_2991_);
    lean_dec_ref(v___y_2990_);
    lean_dec(v___y_2989_);
    lean_dec(v___y_2988_);
    lean_dec_ref(v___y_2987_);
    lean_dec_ref(v_n_2985_);
    return v_res_2999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(
    mut v_as_3003_: *mut LeanObject,
    mut v_sz_3004_: usize,
    mut v_i_3005_: usize,
    mut v_b_3006_: *mut LeanObject,
    mut v___y_3007_: *mut LeanObject,
    mut v___y_3008_: *mut LeanObject,
    mut v___y_3009_: *mut LeanObject,
    mut v___y_3010_: *mut LeanObject,
    mut v___y_3011_: *mut LeanObject,
    mut v___y_3012_: *mut LeanObject,
    mut v___y_3013_: *mut LeanObject,
    mut v___y_3014_: *mut LeanObject,
    mut v___y_3015_: *mut LeanObject,
    mut v___y_3016_: *mut LeanObject,
    mut v___y_3017_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3019_: u8 = 0;
    let mut v___x_3020_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_3022_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3026_: usize = 0;
    let mut v___x_3027_: usize = 0;
    let mut v_a_3029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3032_: u8 = 0;
    let mut v___x_3034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3035_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3036_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3019_ = lean_usize_dec_lt(v_i_3005_, v_sz_3004_);
                if v___x_3019_ == 0 {
                    v___x_3020_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3020_, 0, v_b_3006_);
                    return v___x_3020_;
                } else {
                    lean_dec_ref(v_b_3006_);
                    v_a_3021_ = lean_array_uget_borrowed(v_as_3003_, v_i_3005_);
                    v_d_3022_ = lean_ctor_get(v_a_3021_, 4);
                    v___x_3023_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_3022_);
                    v___x_3024_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_3023_, v___y_3007_, v___y_3008_, v___y_3009_, v___y_3010_, v___y_3011_, v___y_3012_, v___y_3013_, v___y_3014_, v___y_3015_, v___y_3016_, v___y_3017_);
                    lean_dec_ref(v___x_3023_);
                    if lean_obj_tag(v___x_3024_) == 0 {
                        lean_dec_ref_known(v___x_3024_, 1);
                        v___x_3025_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0;
                        v___x_3026_ = 1usize;
                        v___x_3027_ = lean_usize_add(v_i_3005_, v___x_3026_);
                        v_i_3005_ = v___x_3027_;
                        v_b_3006_ = v___x_3025_;
                        state = 0;
                        continue;
                    } else {
                        v_a_3029_ = lean_ctor_get(v___x_3024_, 0);
                        v_isSharedCheck_3036_ = (!lean_is_exclusive(v___x_3024_)) as u8;
                        if v_isSharedCheck_3036_ == 0 {
                            v___x_3031_ = v___x_3024_;
                            v_isShared_3032_ = v_isSharedCheck_3036_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3029_);
                            lean_dec(v___x_3024_);
                            v___x_3031_ = lean_box(0);
                            v_isShared_3032_ = v_isSharedCheck_3036_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3032_ == 0 {
                    v___x_3034_ = v___x_3031_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
                    v___x_3034_ = v_reuseFailAlloc_3035_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3034_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___boxed(
    mut v_as_3037_: *mut LeanObject,
    mut v_sz_3038_: *mut LeanObject,
    mut v_i_3039_: *mut LeanObject,
    mut v_b_3040_: *mut LeanObject,
    mut v___y_3041_: *mut LeanObject,
    mut v___y_3042_: *mut LeanObject,
    mut v___y_3043_: *mut LeanObject,
    mut v___y_3044_: *mut LeanObject,
    mut v___y_3045_: *mut LeanObject,
    mut v___y_3046_: *mut LeanObject,
    mut v___y_3047_: *mut LeanObject,
    mut v___y_3048_: *mut LeanObject,
    mut v___y_3049_: *mut LeanObject,
    mut v___y_3050_: *mut LeanObject,
    mut v___y_3051_: *mut LeanObject,
    mut v___y_3052_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3053_: usize = 0;
    let mut v_i_boxed_3054_: usize = 0;
    let mut v_res_3055_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3053_ = lean_unbox_usize(v_sz_3038_);
    lean_dec(v_sz_3038_);
    v_i_boxed_3054_ = lean_unbox_usize(v_i_3039_);
    lean_dec(v_i_3039_);
    v_res_3055_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(v_as_3037_, v_sz_boxed_3053_, v_i_boxed_3054_, v_b_3040_, v___y_3041_, v___y_3042_, v___y_3043_, v___y_3044_, v___y_3045_, v___y_3046_, v___y_3047_, v___y_3048_, v___y_3049_, v___y_3050_, v___y_3051_);
    lean_dec(v___y_3051_);
    lean_dec_ref(v___y_3050_);
    lean_dec(v___y_3049_);
    lean_dec_ref(v___y_3048_);
    lean_dec(v___y_3047_);
    lean_dec_ref(v___y_3046_);
    lean_dec(v___y_3045_);
    lean_dec_ref(v___y_3044_);
    lean_dec(v___y_3043_);
    lean_dec(v___y_3042_);
    lean_dec_ref(v___y_3041_);
    lean_dec_ref(v_as_3037_);
    return v_res_3055_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(
    mut v_as_3056_: *mut LeanObject,
    mut v_sz_3057_: usize,
    mut v_i_3058_: usize,
    mut v_b_3059_: *mut LeanObject,
    mut v___y_3060_: *mut LeanObject,
    mut v___y_3061_: *mut LeanObject,
    mut v___y_3062_: *mut LeanObject,
    mut v___y_3063_: *mut LeanObject,
    mut v___y_3064_: *mut LeanObject,
    mut v___y_3065_: *mut LeanObject,
    mut v___y_3066_: *mut LeanObject,
    mut v___y_3067_: *mut LeanObject,
    mut v___y_3068_: *mut LeanObject,
    mut v___y_3069_: *mut LeanObject,
    mut v___y_3070_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3072_: u8 = 0;
    let mut v___x_3073_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3074_: *mut LeanObject = core::ptr::null_mut();
    let mut v_d_3075_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3076_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3077_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3079_: usize = 0;
    let mut v___x_3080_: usize = 0;
    let mut v___x_3081_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3082_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3085_: u8 = 0;
    let mut v___x_3087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3088_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3089_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3072_ = lean_usize_dec_lt(v_i_3058_, v_sz_3057_);
                if v___x_3072_ == 0 {
                    v___x_3073_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3073_, 0, v_b_3059_);
                    return v___x_3073_;
                } else {
                    lean_dec_ref(v_b_3059_);
                    v_a_3074_ = lean_array_uget_borrowed(v_as_3056_, v_i_3058_);
                    v_d_3075_ = lean_ctor_get(v_a_3074_, 4);
                    v___x_3076_ = l_Lean_Meta_Grind_Arith_CommRing_PolyDerivation_p(v_d_3075_);
                    v___x_3077_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkPoly(v___x_3076_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
                    lean_dec_ref(v___x_3076_);
                    if lean_obj_tag(v___x_3077_) == 0 {
                        lean_dec_ref_known(v___x_3077_, 1);
                        v___x_3078_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4___closed__0;
                        v___x_3079_ = 1usize;
                        v___x_3080_ = lean_usize_add(v_i_3058_, v___x_3079_);
                        v___x_3081_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1_spec__4(v_as_3056_, v_sz_3057_, v___x_3080_, v___x_3078_, v___y_3060_, v___y_3061_, v___y_3062_, v___y_3063_, v___y_3064_, v___y_3065_, v___y_3066_, v___y_3067_, v___y_3068_, v___y_3069_, v___y_3070_);
                        return v___x_3081_;
                    } else {
                        v_a_3082_ = lean_ctor_get(v___x_3077_, 0);
                        v_isSharedCheck_3089_ = (!lean_is_exclusive(v___x_3077_)) as u8;
                        if v_isSharedCheck_3089_ == 0 {
                            v___x_3084_ = v___x_3077_;
                            v_isShared_3085_ = v_isSharedCheck_3089_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3082_);
                            lean_dec(v___x_3077_);
                            v___x_3084_ = lean_box(0);
                            v_isShared_3085_ = v_isSharedCheck_3089_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3085_ == 0 {
                    v___x_3087_ = v___x_3084_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3088_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3088_, 0, v_a_3082_);
                    v___x_3087_ = v_reuseFailAlloc_3088_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3087_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1___boxed(
    mut v_as_3090_: *mut LeanObject,
    mut v_sz_3091_: *mut LeanObject,
    mut v_i_3092_: *mut LeanObject,
    mut v_b_3093_: *mut LeanObject,
    mut v___y_3094_: *mut LeanObject,
    mut v___y_3095_: *mut LeanObject,
    mut v___y_3096_: *mut LeanObject,
    mut v___y_3097_: *mut LeanObject,
    mut v___y_3098_: *mut LeanObject,
    mut v___y_3099_: *mut LeanObject,
    mut v___y_3100_: *mut LeanObject,
    mut v___y_3101_: *mut LeanObject,
    mut v___y_3102_: *mut LeanObject,
    mut v___y_3103_: *mut LeanObject,
    mut v___y_3104_: *mut LeanObject,
    mut v___y_3105_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_3106_: usize = 0;
    let mut v_i_boxed_3107_: usize = 0;
    let mut v_res_3108_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_3106_ = lean_unbox_usize(v_sz_3091_);
    lean_dec(v_sz_3091_);
    v_i_boxed_3107_ = lean_unbox_usize(v_i_3092_);
    lean_dec(v_i_3092_);
    v_res_3108_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(v_as_3090_, v_sz_boxed_3106_, v_i_boxed_3107_, v_b_3093_, v___y_3094_, v___y_3095_, v___y_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_, v___y_3103_, v___y_3104_);
    lean_dec(v___y_3104_);
    lean_dec_ref(v___y_3103_);
    lean_dec(v___y_3102_);
    lean_dec_ref(v___y_3101_);
    lean_dec(v___y_3100_);
    lean_dec_ref(v___y_3099_);
    lean_dec(v___y_3098_);
    lean_dec_ref(v___y_3097_);
    lean_dec(v___y_3096_);
    lean_dec(v___y_3095_);
    lean_dec_ref(v___y_3094_);
    lean_dec_ref(v_as_3090_);
    return v_res_3108_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(
    mut v_t_3109_: *mut LeanObject,
    mut v_init_3110_: *mut LeanObject,
    mut v___y_3111_: *mut LeanObject,
    mut v___y_3112_: *mut LeanObject,
    mut v___y_3113_: *mut LeanObject,
    mut v___y_3114_: *mut LeanObject,
    mut v___y_3115_: *mut LeanObject,
    mut v___y_3116_: *mut LeanObject,
    mut v___y_3117_: *mut LeanObject,
    mut v___y_3118_: *mut LeanObject,
    mut v___y_3119_: *mut LeanObject,
    mut v___y_3120_: *mut LeanObject,
    mut v___y_3121_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_3123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_3124_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3125_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3126_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3128_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3129_: u8 = 0;
    let mut v_a_3130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3133_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3136_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_3137_: usize = 0;
    let mut v___x_3138_: usize = 0;
    let mut v___x_3139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3142_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3143_: u8 = 0;
    let mut v_fst_3144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_3145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3149_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3151_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3153_: u8 = 0;
    let mut v_a_3154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3157_: u8 = 0;
    let mut v___x_3159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3161_: u8 = 0;
    let mut v_isSharedCheck_3162_: u8 = 0;
    let mut v_a_3163_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3165_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3166_: u8 = 0;
    let mut v___x_3168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3169_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3170_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_3123_ = lean_ctor_get(v_t_3109_, 0);
                v_tail_3124_ = lean_ctor_get(v_t_3109_, 1);
                v___x_3125_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__0(v_init_3110_, v_root_3123_, v_init_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
                if lean_obj_tag(v___x_3125_) == 0 {
                    v_a_3126_ = lean_ctor_get(v___x_3125_, 0);
                    v_isSharedCheck_3162_ = (!lean_is_exclusive(v___x_3125_)) as u8;
                    if v_isSharedCheck_3162_ == 0 {
                        v___x_3128_ = v___x_3125_;
                        v_isShared_3129_ = v_isSharedCheck_3162_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_3126_);
                        lean_dec(v___x_3125_);
                        v___x_3128_ = lean_box(0);
                        v_isShared_3129_ = v_isSharedCheck_3162_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_3163_ = lean_ctor_get(v___x_3125_, 0);
                    v_isSharedCheck_3170_ = (!lean_is_exclusive(v___x_3125_)) as u8;
                    if v_isSharedCheck_3170_ == 0 {
                        v___x_3165_ = v___x_3125_;
                        v_isShared_3166_ = v_isSharedCheck_3170_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_3163_);
                        lean_dec(v___x_3125_);
                        v___x_3165_ = lean_box(0);
                        v_isShared_3166_ = v_isSharedCheck_3170_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_3126_) == 0 {
                    v_a_3130_ = lean_ctor_get(v_a_3126_, 0);
                    lean_inc(v_a_3130_);
                    lean_dec_ref_known(v_a_3126_, 1);
                    if v_isShared_3129_ == 0 {
                        lean_ctor_set(v___x_3128_, 0, v_a_3130_);
                        v___x_3132_ = v___x_3128_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3133_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3130_);
                        v___x_3132_ = v_reuseFailAlloc_3133_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_3128_);
                    v_a_3134_ = lean_ctor_get(v_a_3126_, 0);
                    lean_inc(v_a_3134_);
                    lean_dec_ref_known(v_a_3126_, 1);
                    v___x_3135_ = lean_box(0);
                    v___x_3136_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_3136_, 0, v___x_3135_);
                    lean_ctor_set(v___x_3136_, 1, v_a_3134_);
                    v_sz_3137_ = lean_array_size(v_tail_3124_);
                    v___x_3138_ = 0usize;
                    v___x_3139_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0_spec__1(v_tail_3124_, v_sz_3137_, v___x_3138_, v___x_3136_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_, v___y_3116_, v___y_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
                    if lean_obj_tag(v___x_3139_) == 0 {
                        v_a_3140_ = lean_ctor_get(v___x_3139_, 0);
                        v_isSharedCheck_3153_ = (!lean_is_exclusive(v___x_3139_)) as u8;
                        if v_isSharedCheck_3153_ == 0 {
                            v___x_3142_ = v___x_3139_;
                            v_isShared_3143_ = v_isSharedCheck_3153_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3140_);
                            lean_dec(v___x_3139_);
                            v___x_3142_ = lean_box(0);
                            v_isShared_3143_ = v_isSharedCheck_3153_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_3154_ = lean_ctor_get(v___x_3139_, 0);
                        v_isSharedCheck_3161_ = (!lean_is_exclusive(v___x_3139_)) as u8;
                        if v_isSharedCheck_3161_ == 0 {
                            v___x_3156_ = v___x_3139_;
                            v_isShared_3157_ = v_isSharedCheck_3161_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_3154_);
                            lean_dec(v___x_3139_);
                            v___x_3156_ = lean_box(0);
                            v_isShared_3157_ = v_isSharedCheck_3161_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_3132_;
            }
            3 => {
                v_fst_3144_ = lean_ctor_get(v_a_3140_, 0);
                if lean_obj_tag(v_fst_3144_) == 0 {
                    v_snd_3145_ = lean_ctor_get(v_a_3140_, 1);
                    lean_inc(v_snd_3145_);
                    lean_dec(v_a_3140_);
                    if v_isShared_3143_ == 0 {
                        lean_ctor_set(v___x_3142_, 0, v_snd_3145_);
                        v___x_3147_ = v___x_3142_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_snd_3145_);
                        v___x_3147_ = v_reuseFailAlloc_3148_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_3144_);
                    lean_dec(v_a_3140_);
                    v_val_3149_ = lean_ctor_get(v_fst_3144_, 0);
                    lean_inc(v_val_3149_);
                    lean_dec_ref_known(v_fst_3144_, 1);
                    if v_isShared_3143_ == 0 {
                        lean_ctor_set(v___x_3142_, 0, v_val_3149_);
                        v___x_3151_ = v___x_3142_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_3152_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3152_, 0, v_val_3149_);
                        v___x_3151_ = v_reuseFailAlloc_3152_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_3147_;
            }
            5 => {
                return v___x_3151_;
            }
            6 => {
                if v_isShared_3157_ == 0 {
                    v___x_3159_ = v___x_3156_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_3160_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3160_, 0, v_a_3154_);
                    v___x_3159_ = v_reuseFailAlloc_3160_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_3159_;
            }
            8 => {
                if v_isShared_3166_ == 0 {
                    v___x_3168_ = v___x_3165_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_3169_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3169_, 0, v_a_3163_);
                    v___x_3168_ = v_reuseFailAlloc_3169_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_3168_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0___boxed(
    mut v_t_3171_: *mut LeanObject,
    mut v_init_3172_: *mut LeanObject,
    mut v___y_3173_: *mut LeanObject,
    mut v___y_3174_: *mut LeanObject,
    mut v___y_3175_: *mut LeanObject,
    mut v___y_3176_: *mut LeanObject,
    mut v___y_3177_: *mut LeanObject,
    mut v___y_3178_: *mut LeanObject,
    mut v___y_3179_: *mut LeanObject,
    mut v___y_3180_: *mut LeanObject,
    mut v___y_3181_: *mut LeanObject,
    mut v___y_3182_: *mut LeanObject,
    mut v___y_3183_: *mut LeanObject,
    mut v___y_3184_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3185_: *mut LeanObject = core::ptr::null_mut();
    v_res_3185_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(v_t_3171_, v_init_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_, v___y_3177_, v___y_3178_, v___y_3179_, v___y_3180_, v___y_3181_, v___y_3182_, v___y_3183_);
    lean_dec(v___y_3183_);
    lean_dec_ref(v___y_3182_);
    lean_dec(v___y_3181_);
    lean_dec_ref(v___y_3180_);
    lean_dec(v___y_3179_);
    lean_dec_ref(v___y_3178_);
    lean_dec(v___y_3177_);
    lean_dec_ref(v___y_3176_);
    lean_dec(v___y_3175_);
    lean_dec(v___y_3174_);
    lean_dec_ref(v___y_3173_);
    lean_dec_ref(v_t_3171_);
    return v_res_3185_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(
    mut v_a_3186_: *mut LeanObject,
    mut v_a_3187_: *mut LeanObject,
    mut v_a_3188_: *mut LeanObject,
    mut v_a_3189_: *mut LeanObject,
    mut v_a_3190_: *mut LeanObject,
    mut v_a_3191_: *mut LeanObject,
    mut v_a_3192_: *mut LeanObject,
    mut v_a_3193_: *mut LeanObject,
    mut v_a_3194_: *mut LeanObject,
    mut v_a_3195_: *mut LeanObject,
    mut v_a_3196_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3198_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3199_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_3200_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3201_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3202_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3204_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3205_: u8 = 0;
    let mut v___x_3207_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3209_: u8 = 0;
    let mut v_unused_3210_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3211_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3213_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3214_: u8 = 0;
    let mut v___x_3216_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3217_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3218_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3198_ = l_Lean_Meta_Grind_Arith_CommRing_RingM_getCommRing(
                    v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_,
                    v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_,
                );
                if lean_obj_tag(v___x_3198_) == 0 {
                    v_a_3199_ = lean_ctor_get(v___x_3198_, 0);
                    lean_inc(v_a_3199_);
                    lean_dec_ref_known(v___x_3198_, 1);
                    v_diseqs_3200_ = lean_ctor_get(v_a_3199_, 13);
                    lean_inc_ref(v_diseqs_3200_);
                    lean_dec(v_a_3199_);
                    v___x_3201_ = lean_box(0);
                    v___x_3202_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs_spec__0(v_diseqs_3200_, v___x_3201_, v_a_3186_, v_a_3187_, v_a_3188_, v_a_3189_, v_a_3190_, v_a_3191_, v_a_3192_, v_a_3193_, v_a_3194_, v_a_3195_, v_a_3196_);
                    lean_dec_ref(v_diseqs_3200_);
                    if lean_obj_tag(v___x_3202_) == 0 {
                        v_isSharedCheck_3209_ = (!lean_is_exclusive(v___x_3202_)) as u8;
                        if v_isSharedCheck_3209_ == 0 {
                            v_unused_3210_ = lean_ctor_get(v___x_3202_, 0);
                            lean_dec(v_unused_3210_);
                            v___x_3204_ = v___x_3202_;
                            v_isShared_3205_ = v_isSharedCheck_3209_;
                            state = 1;
                            continue;
                        } else {
                            lean_dec(v___x_3202_);
                            v___x_3204_ = lean_box(0);
                            v_isShared_3205_ = v_isSharedCheck_3209_;
                            state = 1;
                            continue;
                        }
                    } else {
                        return v___x_3202_;
                    }
                } else {
                    v_a_3211_ = lean_ctor_get(v___x_3198_, 0);
                    v_isSharedCheck_3218_ = (!lean_is_exclusive(v___x_3198_)) as u8;
                    if v_isSharedCheck_3218_ == 0 {
                        v___x_3213_ = v___x_3198_;
                        v_isShared_3214_ = v_isSharedCheck_3218_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_3211_);
                        lean_dec(v___x_3198_);
                        v___x_3213_ = lean_box(0);
                        v_isShared_3214_ = v_isSharedCheck_3218_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_3205_ == 0 {
                    lean_ctor_set(v___x_3204_, 0, v___x_3201_);
                    v___x_3207_ = v___x_3204_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3208_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3201_);
                    v___x_3207_ = v_reuseFailAlloc_3208_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3207_;
            }
            3 => {
                if v_isShared_3214_ == 0 {
                    v___x_3216_ = v___x_3213_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
                    v___x_3216_ = v_reuseFailAlloc_3217_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3216_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs___boxed(
    mut v_a_3219_: *mut LeanObject,
    mut v_a_3220_: *mut LeanObject,
    mut v_a_3221_: *mut LeanObject,
    mut v_a_3222_: *mut LeanObject,
    mut v_a_3223_: *mut LeanObject,
    mut v_a_3224_: *mut LeanObject,
    mut v_a_3225_: *mut LeanObject,
    mut v_a_3226_: *mut LeanObject,
    mut v_a_3227_: *mut LeanObject,
    mut v_a_3228_: *mut LeanObject,
    mut v_a_3229_: *mut LeanObject,
    mut v_a_3230_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3231_: *mut LeanObject = core::ptr::null_mut();
    v_res_3231_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(v_a_3219_, v_a_3220_, v_a_3221_, v_a_3222_, v_a_3223_, v_a_3224_, v_a_3225_, v_a_3226_, v_a_3227_, v_a_3228_, v_a_3229_);
    lean_dec(v_a_3229_);
    lean_dec_ref(v_a_3228_);
    lean_dec(v_a_3227_);
    lean_dec_ref(v_a_3226_);
    lean_dec(v_a_3225_);
    lean_dec_ref(v_a_3224_);
    lean_dec(v_a_3223_);
    lean_dec_ref(v_a_3222_);
    lean_dec(v_a_3221_);
    lean_dec(v_a_3220_);
    lean_dec_ref(v_a_3219_);
    return v_res_3231_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(
    mut v_a_3232_: *mut LeanObject,
    mut v_a_3233_: *mut LeanObject,
    mut v_a_3234_: *mut LeanObject,
    mut v_a_3235_: *mut LeanObject,
    mut v_a_3236_: *mut LeanObject,
    mut v_a_3237_: *mut LeanObject,
    mut v_a_3238_: *mut LeanObject,
    mut v_a_3239_: *mut LeanObject,
    mut v_a_3240_: *mut LeanObject,
    mut v_a_3241_: *mut LeanObject,
    mut v_a_3242_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3244_: *mut LeanObject = core::ptr::null_mut();
    v___x_3244_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars(v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
    if lean_obj_tag(v___x_3244_) == 0 {
        let mut v___x_3245_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_3244_, 1);
        v___x_3245_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkBasis(v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
        if lean_obj_tag(v___x_3245_) == 0 {
            let mut v___x_3246_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_3245_, 1);
            v___x_3246_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkQueue(v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
            if lean_obj_tag(v___x_3246_) == 0 {
                let mut v___x_3247_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_3246_, 1);
                v___x_3247_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkDiseqs(v_a_3232_, v_a_3233_, v_a_3234_, v_a_3235_, v_a_3236_, v_a_3237_, v_a_3238_, v_a_3239_, v_a_3240_, v_a_3241_, v_a_3242_);
                return v___x_3247_;
            } else {
                return v___x_3246_;
            }
        } else {
            return v___x_3245_;
        }
    } else {
        return v___x_3244_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs___boxed(
    mut v_a_3248_: *mut LeanObject,
    mut v_a_3249_: *mut LeanObject,
    mut v_a_3250_: *mut LeanObject,
    mut v_a_3251_: *mut LeanObject,
    mut v_a_3252_: *mut LeanObject,
    mut v_a_3253_: *mut LeanObject,
    mut v_a_3254_: *mut LeanObject,
    mut v_a_3255_: *mut LeanObject,
    mut v_a_3256_: *mut LeanObject,
    mut v_a_3257_: *mut LeanObject,
    mut v_a_3258_: *mut LeanObject,
    mut v_a_3259_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3260_: *mut LeanObject = core::ptr::null_mut();
    v_res_3260_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(v_a_3248_, v_a_3249_, v_a_3250_, v_a_3251_, v_a_3252_, v_a_3253_, v_a_3254_, v_a_3255_, v_a_3256_, v_a_3257_, v_a_3258_);
    lean_dec(v_a_3258_);
    lean_dec_ref(v_a_3257_);
    lean_dec(v_a_3256_);
    lean_dec_ref(v_a_3255_);
    lean_dec(v_a_3254_);
    lean_dec_ref(v_a_3253_);
    lean_dec(v_a_3252_);
    lean_dec_ref(v_a_3251_);
    lean_dec(v_a_3250_);
    lean_dec(v_a_3249_);
    lean_dec_ref(v_a_3248_);
    return v_res_3260_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_3263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3268_: *mut LeanObject = core::ptr::null_mut();
    v___x_3263_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__1;
    v___x_3264_ = lean_unsigned_to_nat(6);
    v___x_3265_ = lean_unsigned_to_nat(55);
    v___x_3266_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__0;
    v___x_3267_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars___lam__0___closed__0;
    v___x_3268_ = l_mkPanicMessageWithDecl(
        v___x_3267_,
        v___x_3266_,
        v___x_3265_,
        v___x_3264_,
        v___x_3263_,
    );
    return v___x_3268_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(
    mut v_upperBound_3269_: *mut LeanObject,
    mut v_a_3270_: *mut LeanObject,
    mut v_b_3271_: *mut LeanObject,
    mut v___y_3272_: *mut LeanObject,
    mut v___y_3273_: *mut LeanObject,
    mut v___y_3274_: *mut LeanObject,
    mut v___y_3275_: *mut LeanObject,
    mut v___y_3276_: *mut LeanObject,
    mut v___y_3277_: *mut LeanObject,
    mut v___y_3278_: *mut LeanObject,
    mut v___y_3279_: *mut LeanObject,
    mut v___y_3280_: *mut LeanObject,
    mut v___y_3281_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3283_: u8 = 0;
    let mut v___x_3284_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3287_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3291_: u8 = 0;
    let mut v___x_3292_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3293_: u8 = 0;
    let mut v___x_3294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3295_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3296_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3283_ = lean_nat_dec_lt(v_a_3270_, v_upperBound_3269_);
                if v___x_3283_ == 0 {
                    lean_dec(v_a_3270_);
                    v___x_3284_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3284_, 0, v_b_3271_);
                    return v___x_3284_;
                } else {
                    v___x_3285_ = lean_box(0);
                    v___x_3291_ = 0;
                    lean_inc(v_a_3270_);
                    v___x_3292_ = lean_alloc_ctor(0, 1, (1) as u32);
                    lean_ctor_set(v___x_3292_, 0, v_a_3270_);
                    lean_ctor_set_uint8(
                        v___x_3292_,
                        (core::mem::size_of::<*mut LeanObject>() * 1) as u32,
                        v___x_3291_,
                    );
                    v___x_3293_ = lean_nat_dec_eq(v_a_3270_, v_a_3270_);
                    if v___x_3293_ == 0 {
                        v___x_3294_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___closed__2);
                        v___x_3295_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkVars_spec__0(v___x_3294_, v___x_3292_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
                        lean_dec_ref_known(v___x_3292_, 1);
                        v___y_3287_ = v___x_3295_;
                        state = 1;
                        continue;
                    } else {
                        v___x_3296_ = l___private_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv_0__Lean_Meta_Grind_Arith_CommRing_checkRingInvs(v___x_3292_, v___y_3272_, v___y_3273_, v___y_3274_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_, v___y_3280_, v___y_3281_);
                        lean_dec_ref_known(v___x_3292_, 1);
                        v___y_3287_ = v___x_3296_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_3287_) == 0 {
                    lean_dec_ref_known(v___y_3287_, 1);
                    v___x_3288_ = lean_unsigned_to_nat(1);
                    v___x_3289_ = lean_nat_add(v_a_3270_, v___x_3288_);
                    lean_dec(v_a_3270_);
                    v_a_3270_ = v___x_3289_;
                    v_b_3271_ = v___x_3285_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_3270_);
                    return v___y_3287_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg___boxed(
    mut v_upperBound_3297_: *mut LeanObject,
    mut v_a_3298_: *mut LeanObject,
    mut v_b_3299_: *mut LeanObject,
    mut v___y_3300_: *mut LeanObject,
    mut v___y_3301_: *mut LeanObject,
    mut v___y_3302_: *mut LeanObject,
    mut v___y_3303_: *mut LeanObject,
    mut v___y_3304_: *mut LeanObject,
    mut v___y_3305_: *mut LeanObject,
    mut v___y_3306_: *mut LeanObject,
    mut v___y_3307_: *mut LeanObject,
    mut v___y_3308_: *mut LeanObject,
    mut v___y_3309_: *mut LeanObject,
    mut v___y_3310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3311_: *mut LeanObject = core::ptr::null_mut();
    v_res_3311_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v_upperBound_3297_, v_a_3298_, v_b_3299_, v___y_3300_, v___y_3301_, v___y_3302_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_, v___y_3308_, v___y_3309_);
    lean_dec(v___y_3309_);
    lean_dec_ref(v___y_3308_);
    lean_dec(v___y_3307_);
    lean_dec_ref(v___y_3306_);
    lean_dec(v___y_3305_);
    lean_dec_ref(v___y_3304_);
    lean_dec(v___y_3303_);
    lean_dec_ref(v___y_3302_);
    lean_dec(v___y_3301_);
    lean_dec(v___y_3300_);
    lean_dec(v_upperBound_3297_);
    return v_res_3311_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(
    mut v_a_3312_: *mut LeanObject,
    mut v_a_3313_: *mut LeanObject,
    mut v_a_3314_: *mut LeanObject,
    mut v_a_3315_: *mut LeanObject,
    mut v_a_3316_: *mut LeanObject,
    mut v_a_3317_: *mut LeanObject,
    mut v_a_3318_: *mut LeanObject,
    mut v_a_3319_: *mut LeanObject,
    mut v_a_3320_: *mut LeanObject,
    mut v_a_3321_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_debug_3323_: u8 = 0;
    let mut v___x_3324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3325_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_rings_3328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3335_: u8 = 0;
    let mut v___x_3337_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3338_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3339_: u8 = 0;
    let mut v_unused_3340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3341_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3344_: u8 = 0;
    let mut v___x_3346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3348_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_debug_3323_ = lean_ctor_get_uint8(
                    v_a_3314_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                );
                if v_debug_3323_ == 0 {
                    v___x_3324_ = lean_box(0);
                    v___x_3325_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3325_, 0, v___x_3324_);
                    return v___x_3325_;
                } else {
                    v___x_3326_ =
                        l_Lean_Meta_Grind_Arith_CommRing_get_x27___redArg(v_a_3312_, v_a_3320_);
                    if lean_obj_tag(v___x_3326_) == 0 {
                        v_a_3327_ = lean_ctor_get(v___x_3326_, 0);
                        lean_inc(v_a_3327_);
                        lean_dec_ref_known(v___x_3326_, 1);
                        v_rings_3328_ = lean_ctor_get(v_a_3327_, 0);
                        lean_inc_ref(v_rings_3328_);
                        lean_dec(v_a_3327_);
                        v___x_3329_ = lean_array_get_size(v_rings_3328_);
                        lean_dec_ref(v_rings_3328_);
                        v___x_3330_ = lean_unsigned_to_nat(0);
                        v___x_3331_ = lean_box(0);
                        v___x_3332_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v___x_3329_, v___x_3330_, v___x_3331_, v_a_3312_, v_a_3313_, v_a_3314_, v_a_3315_, v_a_3316_, v_a_3317_, v_a_3318_, v_a_3319_, v_a_3320_, v_a_3321_);
                        if lean_obj_tag(v___x_3332_) == 0 {
                            v_isSharedCheck_3339_ = (!lean_is_exclusive(v___x_3332_)) as u8;
                            if v_isSharedCheck_3339_ == 0 {
                                v_unused_3340_ = lean_ctor_get(v___x_3332_, 0);
                                lean_dec(v_unused_3340_);
                                v___x_3334_ = v___x_3332_;
                                v_isShared_3335_ = v_isSharedCheck_3339_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_3332_);
                                v___x_3334_ = lean_box(0);
                                v_isShared_3335_ = v_isSharedCheck_3339_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_3332_;
                        }
                    } else {
                        v_a_3341_ = lean_ctor_get(v___x_3326_, 0);
                        v_isSharedCheck_3348_ = (!lean_is_exclusive(v___x_3326_)) as u8;
                        if v_isSharedCheck_3348_ == 0 {
                            v___x_3343_ = v___x_3326_;
                            v_isShared_3344_ = v_isSharedCheck_3348_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_3341_);
                            lean_dec(v___x_3326_);
                            v___x_3343_ = lean_box(0);
                            v_isShared_3344_ = v_isSharedCheck_3348_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_3335_ == 0 {
                    lean_ctor_set(v___x_3334_, 0, v___x_3331_);
                    v___x_3337_ = v___x_3334_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3338_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3331_);
                    v___x_3337_ = v_reuseFailAlloc_3338_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3337_;
            }
            3 => {
                if v_isShared_3344_ == 0 {
                    v___x_3346_ = v___x_3343_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_3347_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3347_, 0, v_a_3341_);
                    v___x_3346_ = v_reuseFailAlloc_3347_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_3346_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_CommRing_checkInvariants___boxed(
    mut v_a_3349_: *mut LeanObject,
    mut v_a_3350_: *mut LeanObject,
    mut v_a_3351_: *mut LeanObject,
    mut v_a_3352_: *mut LeanObject,
    mut v_a_3353_: *mut LeanObject,
    mut v_a_3354_: *mut LeanObject,
    mut v_a_3355_: *mut LeanObject,
    mut v_a_3356_: *mut LeanObject,
    mut v_a_3357_: *mut LeanObject,
    mut v_a_3358_: *mut LeanObject,
    mut v_a_3359_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3360_: *mut LeanObject = core::ptr::null_mut();
    v_res_3360_ = l_Lean_Meta_Grind_Arith_CommRing_checkInvariants(
        v_a_3349_, v_a_3350_, v_a_3351_, v_a_3352_, v_a_3353_, v_a_3354_, v_a_3355_, v_a_3356_,
        v_a_3357_, v_a_3358_,
    );
    lean_dec(v_a_3358_);
    lean_dec_ref(v_a_3357_);
    lean_dec(v_a_3356_);
    lean_dec_ref(v_a_3355_);
    lean_dec(v_a_3354_);
    lean_dec_ref(v_a_3353_);
    lean_dec(v_a_3352_);
    lean_dec_ref(v_a_3351_);
    lean_dec(v_a_3350_);
    lean_dec(v_a_3349_);
    return v_res_3360_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(
    mut v_upperBound_3361_: *mut LeanObject,
    mut v_inst_3362_: *mut LeanObject,
    mut v_R_3363_: *mut LeanObject,
    mut v_a_3364_: *mut LeanObject,
    mut v_b_3365_: *mut LeanObject,
    mut v_c_3366_: *mut LeanObject,
    mut v___y_3367_: *mut LeanObject,
    mut v___y_3368_: *mut LeanObject,
    mut v___y_3369_: *mut LeanObject,
    mut v___y_3370_: *mut LeanObject,
    mut v___y_3371_: *mut LeanObject,
    mut v___y_3372_: *mut LeanObject,
    mut v___y_3373_: *mut LeanObject,
    mut v___y_3374_: *mut LeanObject,
    mut v___y_3375_: *mut LeanObject,
    mut v___y_3376_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3378_: *mut LeanObject = core::ptr::null_mut();
    v___x_3378_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___redArg(v_upperBound_3361_, v_a_3364_, v_b_3365_, v___y_3367_, v___y_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_, v___y_3374_, v___y_3375_, v___y_3376_);
    return v___x_3378_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_3379_: *mut LeanObject = *_args.add(0);
    let mut v_inst_3380_: *mut LeanObject = *_args.add(1);
    let mut v_R_3381_: *mut LeanObject = *_args.add(2);
    let mut v_a_3382_: *mut LeanObject = *_args.add(3);
    let mut v_b_3383_: *mut LeanObject = *_args.add(4);
    let mut v_c_3384_: *mut LeanObject = *_args.add(5);
    let mut v___y_3385_: *mut LeanObject = *_args.add(6);
    let mut v___y_3386_: *mut LeanObject = *_args.add(7);
    let mut v___y_3387_: *mut LeanObject = *_args.add(8);
    let mut v___y_3388_: *mut LeanObject = *_args.add(9);
    let mut v___y_3389_: *mut LeanObject = *_args.add(10);
    let mut v___y_3390_: *mut LeanObject = *_args.add(11);
    let mut v___y_3391_: *mut LeanObject = *_args.add(12);
    let mut v___y_3392_: *mut LeanObject = *_args.add(13);
    let mut v___y_3393_: *mut LeanObject = *_args.add(14);
    let mut v___y_3394_: *mut LeanObject = *_args.add(15);
    let mut v___y_3395_: *mut LeanObject = *_args.add(16);
    let mut v_res_3396_: *mut LeanObject = core::ptr::null_mut();
    v_res_3396_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_CommRing_checkInvariants_spec__0(v_upperBound_3379_, v_inst_3380_, v_R_3381_, v_a_3382_, v_b_3383_, v_c_3384_, v___y_3385_, v___y_3386_, v___y_3387_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_, v___y_3392_, v___y_3393_, v___y_3394_);
    lean_dec(v___y_3394_);
    lean_dec_ref(v___y_3393_);
    lean_dec(v___y_3392_);
    lean_dec_ref(v___y_3391_);
    lean_dec(v___y_3390_);
    lean_dec_ref(v___y_3389_);
    lean_dec(v___y_3388_);
    lean_dec_ref(v___y_3387_);
    lean_dec(v___y_3386_);
    lean_dec(v___y_3385_);
    lean_dec(v_upperBound_3379_);
    return v_res_3396_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(
    builtin: u8,
) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin: u8) -> *mut LeanObject {
    let mut res: *mut LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return lean_io_result_mk_ok(lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingM(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = initialize_Lean_Meta_Sym_Arith_Poly(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin);
}
