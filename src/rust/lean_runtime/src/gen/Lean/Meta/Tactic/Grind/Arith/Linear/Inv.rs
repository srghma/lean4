// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Inv
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.Linear.Util
use crate::r#gen::Init::Prelude::l_instInhabitedForall___redArg___lam__0___boxed;
use crate::r#gen::Init::Util::l_mkPanicMessageWithDecl;
use crate::r#gen::Lean::Data::PersistentArray::l_Lean_PersistentArray_get_x21___redArg;
use crate::r#gen::Lean::Expr::l_Lean_instInhabitedExpr;
use crate::r#gen::Lean::Meta::Sym::ExprPtr::l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1;
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::LinearM::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
    l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct,
    l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Arith::Linear::Util::{
    initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util, l_Lean_Meta_Grind_Arith_Linear_eliminated,
    l_Lean_Meta_Grind_Arith_Linear_getOccursOf, l_Lean_Meta_Grind_Arith_Linear_inconsistent,
    runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util,
};
use crate::r#gen::Lean::Meta::Tactic::Grind::Types::l_Lean_Meta_Grind_instInhabitedGoalM;
use crate::lean_imports_rs::Init::Data::Array::Basic::{lean_array_size, lean_array_uget_borrowed};
use crate::lean_imports_rs::Init::Data::Int::Basic::{
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_to_int,
};
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
    lean_ctor_set, lean_ctor_set_tag, lean_dec, lean_dec_ref, lean_dec_ref_known, lean_del_object,
    lean_inc, lean_inc_ref, lean_inc_ref_n, lean_io_result_is_error, lean_io_result_mk_ok,
    lean_is_exclusive, lean_obj_once, lean_obj_tag, lean_unbox, lean_unbox_usize,
    lean_unsigned_to_nat,
};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value: LeanStringObject<40> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value: LeanStringObject<89> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 79, 99, 99, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value: LeanStringObject<123> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 123, m_capacity: 123, m_length: 122, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 50, 57, 56, 50, 52, 51, 48, 53, 52, 51, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 53, 46, 48, 32, 41, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 121, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value: LeanStringObject<92> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 78, 111, 69, 108, 105, 109, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value: LeanStringObject<110> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 110, m_capacity: 110, m_length: 109, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 51, 52, 49, 49, 54, 57, 48, 48, 51, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 51, 51, 46, 48, 32, 41, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value: LeanStringObject<89> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 67, 110, 115, 116, 114, 79, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value: LeanStringObject<30> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 32, 61, 61, 32, 121, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value: LeanStringObject<34> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value: LeanStringObject<35> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value: LeanStringObject<38> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 99, 104, 101, 99, 107, 67, 111, 101, 102, 102, 115, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value: LeanStringObject<94> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 76, 101, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 76, 111, 119, 101, 114, 32, 61, 61, 32, 40, 97, 32, 60, 32, 48, 41, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value) as *mut LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value: LeanStringObject<92> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 76, 111, 119, 101, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 108, 111, 119, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value: LeanStringObject<92> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 85, 112, 112, 101, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 117, 112, 112, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value: LeanCtorObject<2> = LeanCtorObject { m_header: LeanObject { rc: 0, cs_size: (core::mem::size_of::<LeanObject>() + core::mem::size_of::<*mut LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut LeanObject,((( 0 as usize) << 1) | 1) as *mut LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value: LeanStringObject<97> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 68, 105, 115, 101, 113, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value) as *mut LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value: LeanStringObject<53> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 100, 105, 115, 101, 113, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2: *mut LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value: LeanStringObject<90> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 90, m_capacity: 90, m_length: 89, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value: LeanStringObject<48> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 120, 112, 114, 32, 101, 120, 112, 114, 39, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3: *mut LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value: LeanStringObject<42> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110, 117, 109, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0: *mut LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value) as *mut LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1: *mut LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value: LeanStringObject<45> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 73, 110, 118, 97, 114, 105, 97, 110, 116, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value) as *mut LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value: LeanStringObject<126> = LeanStringObject { m_header: LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 51, 49, 49, 57, 50, 50, 53, 55, 54, 52, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 48, 46, 48, 32, 41, 32, 61, 61, 32, 115, 116, 114, 117, 99, 116, 73, 100, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1: *mut LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value) as *mut LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once: LeanOnceCell = LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2: *mut LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
    mut v_a_3623_: *mut LeanObject,
    mut v_a_3624_: *mut LeanObject,
) -> u8 {
    let mut v___x_3625_: u8 = 0;
    let mut v_v_3626_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3627_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3631_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_3632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3638_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_a_3624_) == 0 {
                    lean_dec(v_a_3623_);
                    v___x_3625_ = 1;
                    return v___x_3625_;
                } else {
                    if lean_obj_tag(v_a_3623_) == 0 {
                        v_v_3626_ = lean_ctor_get(v_a_3624_, 1);
                        v_p_3627_ = lean_ctor_get(v_a_3624_, 2);
                        lean_inc(v_v_3626_);
                        v___x_3628_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v___x_3628_, 0, v_v_3626_);
                        v_a_3623_ = v___x_3628_;
                        v_a_3624_ = v_p_3627_;
                        state = 0;
                        continue;
                    } else {
                        v_v_3630_ = lean_ctor_get(v_a_3624_, 1);
                        v_p_3631_ = lean_ctor_get(v_a_3624_, 2);
                        v_val_3632_ = lean_ctor_get(v_a_3623_, 0);
                        v_isSharedCheck_3641_ = (!lean_is_exclusive(v_a_3623_)) as u8;
                        if v_isSharedCheck_3641_ == 0 {
                            v___x_3634_ = v_a_3623_;
                            v_isShared_3635_ = v_isSharedCheck_3641_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_val_3632_);
                            lean_dec(v_a_3623_);
                            v___x_3634_ = lean_box(0);
                            v_isShared_3635_ = v_isSharedCheck_3641_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3636_ = lean_nat_dec_lt(v_v_3630_, v_val_3632_);
                lean_dec(v_val_3632_);
                if v___x_3636_ == 0 {
                    lean_del_object(v___x_3634_);
                    return v___x_3636_;
                } else {
                    lean_inc(v_v_3630_);
                    if v_isShared_3635_ == 0 {
                        lean_ctor_set(v___x_3634_, 0, v_v_3630_);
                        v___x_3638_ = v___x_3634_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3640_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_v_3630_);
                        v___x_3638_ = v_reuseFailAlloc_3640_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                v_a_3623_ = v___x_3638_;
                v_a_3624_ = v_p_3631_;
                state = 0;
                continue;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go___boxed(
    mut v_a_3642_: *mut LeanObject,
    mut v_a_3643_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3644_: u8 = 0;
    let mut v_r_3645_: *mut LeanObject = core::ptr::null_mut();
    v_res_3644_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
            v_a_3642_, v_a_3643_,
        );
    lean_dec(v_a_3643_);
    v_r_3645_ = lean_box((v_res_3644_) as usize);
    return v_r_3645_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(
    mut v_p_3646_: *mut LeanObject,
) -> u8 {
    let mut v___x_3647_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    v___x_3647_ = lean_box(0);
    v___x_3648_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
            v___x_3647_,
            v_p_3646_,
        );
    return v___x_3648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted___boxed(
    mut v_p_3649_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3650_: u8 = 0;
    let mut v_r_3651_: *mut LeanObject = core::ptr::null_mut();
    v_res_3650_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(
            v_p_3649_,
        );
    lean_dec(v_p_3649_);
    v_r_3651_ = lean_box((v_res_3650_) as usize);
    return v_r_3651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0()
-> *mut LeanObject {
    let mut v___x_3652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut LeanObject = core::ptr::null_mut();
    v___x_3652_ = lean_unsigned_to_nat(0);
    v___x_3653_ = lean_nat_to_int(v___x_3652_);
    return v___x_3653_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(
    mut v_x_3654_: *mut LeanObject,
) -> u8 {
    let mut v___x_3655_: u8 = 0;
    let mut v_k_3656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3657_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_3654_) == 0 {
                    v___x_3655_ = 1;
                    return v___x_3655_;
                } else {
                    v_k_3656_ = lean_ctor_get(v_x_3654_, 0);
                    v_p_3657_ = lean_ctor_get(v_x_3654_, 2);
                    v___x_3658_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
                    v___x_3659_ = lean_int_dec_eq(v_k_3656_, v___x_3658_);
                    if v___x_3659_ == 0 {
                        v_x_3654_ = v_p_3657_;
                        state = 0;
                        continue;
                    } else {
                        v___x_3661_ = 0;
                        return v___x_3661_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___boxed(
    mut v_x_3662_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3663_: u8 = 0;
    let mut v_r_3664_: *mut LeanObject = core::ptr::null_mut();
    v_res_3663_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(
            v_x_3662_,
        );
    lean_dec(v_x_3662_);
    v_r_3664_ = lean_box((v_res_3663_) as usize);
    return v_r_3664_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0()
-> *mut LeanObject {
    let mut v___x_3665_: *mut LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_3665_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(
    mut v_msg_3666_: *mut LeanObject,
    mut v___y_3667_: *mut LeanObject,
    mut v___y_3668_: *mut LeanObject,
    mut v___y_3669_: *mut LeanObject,
    mut v___y_3670_: *mut LeanObject,
    mut v___y_3671_: *mut LeanObject,
    mut v___y_3672_: *mut LeanObject,
    mut v___y_3673_: *mut LeanObject,
    mut v___y_3674_: *mut LeanObject,
    mut v___y_3675_: *mut LeanObject,
    mut v___y_3676_: *mut LeanObject,
    mut v___y_3677_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3679_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_2201__overap_3681_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut LeanObject = core::ptr::null_mut();
    v___x_3679_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0);
    v___f_3680_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3680_, 0, v___x_3679_);
    v___x_2201__overap_3681_ = lean_panic_fn_borrowed(v___f_3680_, v_msg_3666_);
    lean_dec_ref(v___f_3680_);
    lean_inc(v___y_3677_);
    lean_inc_ref(v___y_3676_);
    lean_inc(v___y_3675_);
    lean_inc_ref(v___y_3674_);
    lean_inc(v___y_3673_);
    lean_inc_ref(v___y_3672_);
    lean_inc(v___y_3671_);
    lean_inc_ref(v___y_3670_);
    lean_inc(v___y_3669_);
    lean_inc(v___y_3668_);
    lean_inc(v___y_3667_);
    v___x_3682_ = lean_apply_12(
        v___x_2201__overap_3681_,
        v___y_3667_,
        v___y_3668_,
        v___y_3669_,
        v___y_3670_,
        v___y_3671_,
        v___y_3672_,
        v___y_3673_,
        v___y_3674_,
        v___y_3675_,
        v___y_3676_,
        v___y_3677_,
        lean_box(0),
    );
    return v___x_3682_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___boxed(
    mut v_msg_3683_: *mut LeanObject,
    mut v___y_3684_: *mut LeanObject,
    mut v___y_3685_: *mut LeanObject,
    mut v___y_3686_: *mut LeanObject,
    mut v___y_3687_: *mut LeanObject,
    mut v___y_3688_: *mut LeanObject,
    mut v___y_3689_: *mut LeanObject,
    mut v___y_3690_: *mut LeanObject,
    mut v___y_3691_: *mut LeanObject,
    mut v___y_3692_: *mut LeanObject,
    mut v___y_3693_: *mut LeanObject,
    mut v___y_3694_: *mut LeanObject,
    mut v___y_3695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3696_: *mut LeanObject = core::ptr::null_mut();
    v_res_3696_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v_msg_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
    lean_dec(v___y_3694_);
    lean_dec_ref(v___y_3693_);
    lean_dec(v___y_3692_);
    lean_dec_ref(v___y_3691_);
    lean_dec(v___y_3690_);
    lean_dec_ref(v___y_3689_);
    lean_dec(v___y_3688_);
    lean_dec_ref(v___y_3687_);
    lean_dec(v___y_3686_);
    lean_dec(v___y_3685_);
    lean_dec(v___y_3684_);
    return v_res_3696_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(
    mut v_k_3697_: *mut LeanObject,
    mut v_t_3698_: *mut LeanObject,
) -> u8 {
    let mut v_k_3699_: *mut LeanObject = core::ptr::null_mut();
    let mut v_l_3700_: *mut LeanObject = core::ptr::null_mut();
    let mut v_r_3701_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: u8 = 0;
    let mut v___x_3706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_t_3698_) == 0 {
                    v_k_3699_ = lean_ctor_get(v_t_3698_, 1);
                    v_l_3700_ = lean_ctor_get(v_t_3698_, 3);
                    v_r_3701_ = lean_ctor_get(v_t_3698_, 4);
                    v___x_3702_ = lean_nat_dec_lt(v_k_3697_, v_k_3699_);
                    if v___x_3702_ == 0 {
                        v___x_3703_ = lean_nat_dec_eq(v_k_3697_, v_k_3699_);
                        if v___x_3703_ == 0 {
                            v_t_3698_ = v_r_3701_;
                            state = 0;
                            continue;
                        } else {
                            return v___x_3703_;
                        }
                    } else {
                        v_t_3698_ = v_l_3700_;
                        state = 0;
                        continue;
                    }
                } else {
                    v___x_3706_ = 0;
                    return v___x_3706_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg___boxed(
    mut v_k_3707_: *mut LeanObject,
    mut v_t_3708_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3709_: u8 = 0;
    let mut v_r_3710_: *mut LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_3707_, v_t_3708_);
    lean_dec(v_t_3708_);
    lean_dec(v_k_3707_);
    v_r_3710_ = lean_box((v_res_3709_) as usize);
    return v_r_3710_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3()
-> *mut LeanObject {
    let mut v___x_3714_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut LeanObject = core::ptr::null_mut();
    v___x_3714_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2;
    v___x_3715_ = lean_unsigned_to_nat(4);
    v___x_3716_ = lean_unsigned_to_nat(32);
    v___x_3717_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1;
    v___x_3718_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_3719_ = l_mkPanicMessageWithDecl(
        v___x_3718_,
        v___x_3717_,
        v___x_3716_,
        v___x_3715_,
        v___x_3714_,
    );
    return v___x_3719_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(
    mut v_y_3720_: *mut LeanObject,
    mut v_p_3721_: *mut LeanObject,
    mut v_a_3722_: *mut LeanObject,
    mut v_a_3723_: *mut LeanObject,
    mut v_a_3724_: *mut LeanObject,
    mut v_a_3725_: *mut LeanObject,
    mut v_a_3726_: *mut LeanObject,
    mut v_a_3727_: *mut LeanObject,
    mut v_a_3728_: *mut LeanObject,
    mut v_a_3729_: *mut LeanObject,
    mut v_a_3730_: *mut LeanObject,
    mut v_a_3731_: *mut LeanObject,
    mut v_a_3732_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_3734_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3735_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3742_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3747_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3748_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v___x_3750_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_3721_) == 1 {
                    v_v_3734_ = lean_ctor_get(v_p_3721_, 1);
                    v_p_3735_ = lean_ctor_get(v_p_3721_, 2);
                    v___x_3736_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(
                        v_v_3734_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_,
                        v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_,
                    );
                    if lean_obj_tag(v___x_3736_) == 0 {
                        v_a_3737_ = lean_ctor_get(v___x_3736_, 0);
                        lean_inc(v_a_3737_);
                        lean_dec_ref_known(v___x_3736_, 1);
                        v___x_3738_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_y_3720_, v_a_3737_);
                        lean_dec(v_a_3737_);
                        if v___x_3738_ == 0 {
                            v___x_3739_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3);
                            v___x_3740_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3739_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
                            return v___x_3740_;
                        } else {
                            v_p_3721_ = v_p_3735_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_a_3742_ = lean_ctor_get(v___x_3736_, 0);
                        v_isSharedCheck_3749_ = (!lean_is_exclusive(v___x_3736_)) as u8;
                        if v_isSharedCheck_3749_ == 0 {
                            v___x_3744_ = v___x_3736_;
                            v_isShared_3745_ = v_isSharedCheck_3749_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3742_);
                            lean_dec(v___x_3736_);
                            v___x_3744_ = lean_box(0);
                            v_isShared_3745_ = v_isSharedCheck_3749_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3750_ = lean_box(0);
                    v___x_3751_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3751_, 0, v___x_3750_);
                    return v___x_3751_;
                }
            }
            1 => {
                if v_isShared_3745_ == 0 {
                    v___x_3747_ = v___x_3744_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3748_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
                    v___x_3747_ = v_reuseFailAlloc_3748_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3747_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___boxed(
    mut v_y_3752_: *mut LeanObject,
    mut v_p_3753_: *mut LeanObject,
    mut v_a_3754_: *mut LeanObject,
    mut v_a_3755_: *mut LeanObject,
    mut v_a_3756_: *mut LeanObject,
    mut v_a_3757_: *mut LeanObject,
    mut v_a_3758_: *mut LeanObject,
    mut v_a_3759_: *mut LeanObject,
    mut v_a_3760_: *mut LeanObject,
    mut v_a_3761_: *mut LeanObject,
    mut v_a_3762_: *mut LeanObject,
    mut v_a_3763_: *mut LeanObject,
    mut v_a_3764_: *mut LeanObject,
    mut v_a_3765_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3766_: *mut LeanObject = core::ptr::null_mut();
    v_res_3766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_y_3752_, v_p_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
    lean_dec(v_a_3764_);
    lean_dec_ref(v_a_3763_);
    lean_dec(v_a_3762_);
    lean_dec_ref(v_a_3761_);
    lean_dec(v_a_3760_);
    lean_dec_ref(v_a_3759_);
    lean_dec(v_a_3758_);
    lean_dec_ref(v_a_3757_);
    lean_dec(v_a_3756_);
    lean_dec(v_a_3755_);
    lean_dec(v_a_3754_);
    lean_dec(v_p_3753_);
    lean_dec(v_y_3752_);
    return v_res_3766_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(
    mut v_00_u03b2_3767_: *mut LeanObject,
    mut v_k_3768_: *mut LeanObject,
    mut v_t_3769_: *mut LeanObject,
) -> u8 {
    let mut v___x_3770_: u8 = 0;
    v___x_3770_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_3768_, v_t_3769_);
    return v___x_3770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___boxed(
    mut v_00_u03b2_3771_: *mut LeanObject,
    mut v_k_3772_: *mut LeanObject,
    mut v_t_3773_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3774_: u8 = 0;
    let mut v_r_3775_: *mut LeanObject = core::ptr::null_mut();
    v_res_3774_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(v_00_u03b2_3771_, v_k_3772_, v_t_3773_);
    lean_dec(v_t_3773_);
    lean_dec(v_k_3772_);
    v_r_3775_ = lean_box((v_res_3774_) as usize);
    return v_r_3775_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(
    mut v_p_3776_: *mut LeanObject,
    mut v_a_3777_: *mut LeanObject,
    mut v_a_3778_: *mut LeanObject,
    mut v_a_3779_: *mut LeanObject,
    mut v_a_3780_: *mut LeanObject,
    mut v_a_3781_: *mut LeanObject,
    mut v_a_3782_: *mut LeanObject,
    mut v_a_3783_: *mut LeanObject,
    mut v_a_3784_: *mut LeanObject,
    mut v_a_3785_: *mut LeanObject,
    mut v_a_3786_: *mut LeanObject,
    mut v_a_3787_: *mut LeanObject,
) -> *mut LeanObject {
    if lean_obj_tag(v_p_3776_) == 1 {
        let mut v_v_3789_: *mut LeanObject = core::ptr::null_mut();
        let mut v_p_3790_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3791_: *mut LeanObject = core::ptr::null_mut();
        v_v_3789_ = lean_ctor_get(v_p_3776_, 1);
        v_p_3790_ = lean_ctor_get(v_p_3776_, 2);
        v___x_3791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_v_3789_, v_p_3790_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
        return v___x_3791_;
    } else {
        let mut v___x_3792_: *mut LeanObject = core::ptr::null_mut();
        let mut v___x_3793_: *mut LeanObject = core::ptr::null_mut();
        v___x_3792_ = lean_box(0);
        v___x_3793_ = lean_alloc_ctor(0, 1, (0) as u32);
        lean_ctor_set(v___x_3793_, 0, v___x_3792_);
        return v___x_3793_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs___boxed(
    mut v_p_3794_: *mut LeanObject,
    mut v_a_3795_: *mut LeanObject,
    mut v_a_3796_: *mut LeanObject,
    mut v_a_3797_: *mut LeanObject,
    mut v_a_3798_: *mut LeanObject,
    mut v_a_3799_: *mut LeanObject,
    mut v_a_3800_: *mut LeanObject,
    mut v_a_3801_: *mut LeanObject,
    mut v_a_3802_: *mut LeanObject,
    mut v_a_3803_: *mut LeanObject,
    mut v_a_3804_: *mut LeanObject,
    mut v_a_3805_: *mut LeanObject,
    mut v_a_3806_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3807_: *mut LeanObject = core::ptr::null_mut();
    v_res_3807_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(
            v_p_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_,
            v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_,
        );
    lean_dec(v_a_3805_);
    lean_dec_ref(v_a_3804_);
    lean_dec(v_a_3803_);
    lean_dec_ref(v_a_3802_);
    lean_dec(v_a_3801_);
    lean_dec_ref(v_a_3800_);
    lean_dec(v_a_3799_);
    lean_dec_ref(v_a_3798_);
    lean_dec(v_a_3797_);
    lean_dec(v_a_3796_);
    lean_dec(v_a_3795_);
    lean_dec(v_p_3794_);
    return v_res_3807_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2()
-> *mut LeanObject {
    let mut v___x_3810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut LeanObject = core::ptr::null_mut();
    v___x_3810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1;
    v___x_3811_ = lean_unsigned_to_nat(2);
    v___x_3812_ = lean_unsigned_to_nat(38);
    v___x_3813_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0;
    v___x_3814_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_3815_ = l_mkPanicMessageWithDecl(
        v___x_3814_,
        v___x_3813_,
        v___x_3812_,
        v___x_3811_,
        v___x_3810_,
    );
    return v___x_3815_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(
    mut v_p_3816_: *mut LeanObject,
    mut v_a_3817_: *mut LeanObject,
    mut v_a_3818_: *mut LeanObject,
    mut v_a_3819_: *mut LeanObject,
    mut v_a_3820_: *mut LeanObject,
    mut v_a_3821_: *mut LeanObject,
    mut v_a_3822_: *mut LeanObject,
    mut v_a_3823_: *mut LeanObject,
    mut v_a_3824_: *mut LeanObject,
    mut v_a_3825_: *mut LeanObject,
    mut v_a_3826_: *mut LeanObject,
    mut v_a_3827_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_v_3829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_3830_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3835_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3837_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3842_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v___x_3845_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_p_3816_) == 1 {
                    v_v_3829_ = lean_ctor_get(v_p_3816_, 1);
                    v_p_3830_ = lean_ctor_get(v_p_3816_, 2);
                    v___x_3831_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(
                        v_v_3829_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_,
                        v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_,
                    );
                    if lean_obj_tag(v___x_3831_) == 0 {
                        v_a_3832_ = lean_ctor_get(v___x_3831_, 0);
                        lean_inc(v_a_3832_);
                        lean_dec_ref_known(v___x_3831_, 1);
                        v___x_3833_ = (lean_unbox(v_a_3832_) as u8);
                        lean_dec(v_a_3832_);
                        if v___x_3833_ == 0 {
                            v_p_3816_ = v_p_3830_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3835_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2);
                            v___x_3836_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3835_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
                            return v___x_3836_;
                        }
                    } else {
                        v_a_3837_ = lean_ctor_get(v___x_3831_, 0);
                        v_isSharedCheck_3844_ = (!lean_is_exclusive(v___x_3831_)) as u8;
                        if v_isSharedCheck_3844_ == 0 {
                            v___x_3839_ = v___x_3831_;
                            v_isShared_3840_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_3837_);
                            lean_dec(v___x_3831_);
                            v___x_3839_ = lean_box(0);
                            v_isShared_3840_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3845_ = lean_box(0);
                    v___x_3846_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_3846_, 0, v___x_3845_);
                    return v___x_3846_;
                }
            }
            1 => {
                if v_isShared_3840_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
                    v___x_3842_ = v_reuseFailAlloc_3843_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_3842_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___boxed(
    mut v_p_3847_: *mut LeanObject,
    mut v_a_3848_: *mut LeanObject,
    mut v_a_3849_: *mut LeanObject,
    mut v_a_3850_: *mut LeanObject,
    mut v_a_3851_: *mut LeanObject,
    mut v_a_3852_: *mut LeanObject,
    mut v_a_3853_: *mut LeanObject,
    mut v_a_3854_: *mut LeanObject,
    mut v_a_3855_: *mut LeanObject,
    mut v_a_3856_: *mut LeanObject,
    mut v_a_3857_: *mut LeanObject,
    mut v_a_3858_: *mut LeanObject,
    mut v_a_3859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3860_: *mut LeanObject = core::ptr::null_mut();
    v_res_3860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
    lean_dec(v_a_3858_);
    lean_dec_ref(v_a_3857_);
    lean_dec(v_a_3856_);
    lean_dec_ref(v_a_3855_);
    lean_dec(v_a_3854_);
    lean_dec_ref(v_a_3853_);
    lean_dec(v_a_3852_);
    lean_dec_ref(v_a_3851_);
    lean_dec(v_a_3850_);
    lean_dec(v_a_3849_);
    lean_dec(v_a_3848_);
    lean_dec(v_p_3847_);
    return v_res_3860_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2()
-> *mut LeanObject {
    let mut v___x_3863_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut LeanObject = core::ptr::null_mut();
    v___x_3863_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1;
    v___x_3864_ = lean_unsigned_to_nat(2);
    v___x_3865_ = lean_unsigned_to_nat(49);
    v___x_3866_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0;
    v___x_3867_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_3868_ = l_mkPanicMessageWithDecl(
        v___x_3867_,
        v___x_3866_,
        v___x_3865_,
        v___x_3864_,
        v___x_3863_,
    );
    return v___x_3868_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4()
-> *mut LeanObject {
    let mut v___x_3870_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut LeanObject = core::ptr::null_mut();
    v___x_3870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_3871_ = lean_unsigned_to_nat(24);
    v___x_3872_ = lean_unsigned_to_nat(48);
    v___x_3873_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0;
    v___x_3874_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_3875_ = l_mkPanicMessageWithDecl(
        v___x_3874_,
        v___x_3873_,
        v___x_3872_,
        v___x_3871_,
        v___x_3870_,
    );
    return v___x_3875_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6()
-> *mut LeanObject {
    let mut v___x_3877_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut LeanObject = core::ptr::null_mut();
    v___x_3877_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5;
    v___x_3878_ = lean_unsigned_to_nat(2);
    v___x_3879_ = lean_unsigned_to_nat(42);
    v___x_3880_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0;
    v___x_3881_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_3882_ = l_mkPanicMessageWithDecl(
        v___x_3881_,
        v___x_3880_,
        v___x_3879_,
        v___x_3878_,
        v___x_3877_,
    );
    return v___x_3882_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8()
-> *mut LeanObject {
    let mut v___x_3884_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut LeanObject = core::ptr::null_mut();
    v___x_3884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7;
    v___x_3885_ = lean_unsigned_to_nat(2);
    v___x_3886_ = lean_unsigned_to_nat(43);
    v___x_3887_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0;
    v___x_3888_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_3889_ = l_mkPanicMessageWithDecl(
        v___x_3888_,
        v___x_3887_,
        v___x_3886_,
        v___x_3885_,
        v___x_3884_,
    );
    return v___x_3889_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(
    mut v_p_3890_: *mut LeanObject,
    mut v_x_3891_: *mut LeanObject,
    mut v_a_3892_: *mut LeanObject,
    mut v_a_3893_: *mut LeanObject,
    mut v_a_3894_: *mut LeanObject,
    mut v_a_3895_: *mut LeanObject,
    mut v_a_3896_: *mut LeanObject,
    mut v_a_3897_: *mut LeanObject,
    mut v_a_3898_: *mut LeanObject,
    mut v_a_3899_: *mut LeanObject,
    mut v_a_3900_: *mut LeanObject,
    mut v_a_3901_: *mut LeanObject,
    mut v_a_3902_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___y_3905_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_3916_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3931_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3941_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(v_p_3890_);
                if v___x_3924_ == 0 {
                    v___x_3925_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6);
                    v___x_3926_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3925_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                    return v___x_3926_;
                } else {
                    v___x_3927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(v_p_3890_);
                    if v___x_3927_ == 0 {
                        v___x_3928_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8);
                        v___x_3929_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3928_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                        return v___x_3929_;
                    } else {
                        v___x_3930_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(
                            v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_,
                            v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_,
                        );
                        if lean_obj_tag(v___x_3930_) == 0 {
                            v_a_3931_ = lean_ctor_get(v___x_3930_, 0);
                            lean_inc(v_a_3931_);
                            lean_dec_ref_known(v___x_3930_, 1);
                            v___x_3932_ = (lean_unbox(v_a_3931_) as u8);
                            lean_dec(v_a_3931_);
                            if v___x_3932_ == 0 {
                                v___x_3933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_3890_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                                if lean_obj_tag(v___x_3933_) == 0 {
                                    lean_dec_ref_known(v___x_3933_, 1);
                                    v___x_3934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(v_p_3890_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                                    if lean_obj_tag(v___x_3934_) == 0 {
                                        lean_dec_ref_known(v___x_3934_, 1);
                                        v___y_3905_ = v_a_3892_;
                                        v___y_3906_ = v_a_3893_;
                                        v___y_3907_ = v_a_3894_;
                                        v___y_3908_ = v_a_3895_;
                                        v___y_3909_ = v_a_3896_;
                                        v___y_3910_ = v_a_3897_;
                                        v___y_3911_ = v_a_3898_;
                                        v___y_3912_ = v_a_3899_;
                                        v___y_3913_ = v_a_3900_;
                                        v___y_3914_ = v_a_3901_;
                                        v___y_3915_ = v_a_3902_;
                                        state = 1;
                                        continue;
                                    } else {
                                        return v___x_3934_;
                                    }
                                } else {
                                    return v___x_3933_;
                                }
                            } else {
                                v___y_3905_ = v_a_3892_;
                                v___y_3906_ = v_a_3893_;
                                v___y_3907_ = v_a_3894_;
                                v___y_3908_ = v_a_3895_;
                                v___y_3909_ = v_a_3896_;
                                v___y_3910_ = v_a_3897_;
                                v___y_3911_ = v_a_3898_;
                                v___y_3912_ = v_a_3899_;
                                v___y_3913_ = v_a_3900_;
                                v___y_3914_ = v_a_3901_;
                                v___y_3915_ = v_a_3902_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_3935_ = lean_ctor_get(v___x_3930_, 0);
                            v_isSharedCheck_3942_ = (!lean_is_exclusive(v___x_3930_)) as u8;
                            if v_isSharedCheck_3942_ == 0 {
                                v___x_3937_ = v___x_3930_;
                                v_isShared_3938_ = v_isSharedCheck_3942_;
                                state = 2;
                                continue;
                            } else {
                                lean_inc(v_a_3935_);
                                lean_dec(v___x_3930_);
                                v___x_3937_ = lean_box(0);
                                v_isShared_3938_ = v_isSharedCheck_3942_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_p_3890_) == 1 {
                    v_v_3916_ = lean_ctor_get(v_p_3890_, 1);
                    v___x_3917_ = lean_nat_dec_eq(v_x_3891_, v_v_3916_);
                    if v___x_3917_ == 0 {
                        v___x_3918_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2);
                        v___x_3919_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3918_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
                        return v___x_3919_;
                    } else {
                        v___x_3920_ = lean_box(0);
                        v___x_3921_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v___x_3921_, 0, v___x_3920_);
                        return v___x_3921_;
                    }
                } else {
                    v___x_3922_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4);
                    v___x_3923_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3922_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
                    return v___x_3923_;
                }
            }
            2 => {
                if v_isShared_3938_ == 0 {
                    v___x_3940_ = v___x_3937_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_3941_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
                    v___x_3940_ = v_reuseFailAlloc_3941_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_3940_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___boxed(
    mut v_p_3943_: *mut LeanObject,
    mut v_x_3944_: *mut LeanObject,
    mut v_a_3945_: *mut LeanObject,
    mut v_a_3946_: *mut LeanObject,
    mut v_a_3947_: *mut LeanObject,
    mut v_a_3948_: *mut LeanObject,
    mut v_a_3949_: *mut LeanObject,
    mut v_a_3950_: *mut LeanObject,
    mut v_a_3951_: *mut LeanObject,
    mut v_a_3952_: *mut LeanObject,
    mut v_a_3953_: *mut LeanObject,
    mut v_a_3954_: *mut LeanObject,
    mut v_a_3955_: *mut LeanObject,
    mut v_a_3956_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3957_: *mut LeanObject = core::ptr::null_mut();
    v_res_3957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_3943_, v_x_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
    lean_dec(v_a_3955_);
    lean_dec_ref(v_a_3954_);
    lean_dec(v_a_3953_);
    lean_dec_ref(v_a_3952_);
    lean_dec(v_a_3951_);
    lean_dec_ref(v_a_3950_);
    lean_dec(v_a_3949_);
    lean_dec_ref(v_a_3948_);
    lean_dec(v_a_3947_);
    lean_dec(v_a_3946_);
    lean_dec(v_a_3945_);
    lean_dec(v_x_3944_);
    lean_dec(v_p_3943_);
    return v_res_3957_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_3958_: *mut LeanObject = core::ptr::null_mut();
    v___x_3958_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_3958_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(
    mut v_msg_3959_: *mut LeanObject,
    mut v___y_3960_: *mut LeanObject,
    mut v___y_3961_: *mut LeanObject,
    mut v___y_3962_: *mut LeanObject,
    mut v___y_3963_: *mut LeanObject,
    mut v___y_3964_: *mut LeanObject,
    mut v___y_3965_: *mut LeanObject,
    mut v___y_3966_: *mut LeanObject,
    mut v___y_3967_: *mut LeanObject,
    mut v___y_3968_: *mut LeanObject,
    mut v___y_3969_: *mut LeanObject,
    mut v___y_3970_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_3972_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_3973_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4606__overap_3974_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut LeanObject = core::ptr::null_mut();
    v___x_3972_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0);
    v___f_3973_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_3973_, 0, v___x_3972_);
    v___x_4606__overap_3974_ = lean_panic_fn_borrowed(v___f_3973_, v_msg_3959_);
    lean_dec_ref(v___f_3973_);
    lean_inc(v___y_3970_);
    lean_inc_ref(v___y_3969_);
    lean_inc(v___y_3968_);
    lean_inc_ref(v___y_3967_);
    lean_inc(v___y_3966_);
    lean_inc_ref(v___y_3965_);
    lean_inc(v___y_3964_);
    lean_inc_ref(v___y_3963_);
    lean_inc(v___y_3962_);
    lean_inc(v___y_3961_);
    lean_inc(v___y_3960_);
    v___x_3975_ = lean_apply_12(
        v___x_4606__overap_3974_,
        v___y_3960_,
        v___y_3961_,
        v___y_3962_,
        v___y_3963_,
        v___y_3964_,
        v___y_3965_,
        v___y_3966_,
        v___y_3967_,
        v___y_3968_,
        v___y_3969_,
        v___y_3970_,
        lean_box(0),
    );
    return v___x_3975_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___boxed(
    mut v_msg_3976_: *mut LeanObject,
    mut v___y_3977_: *mut LeanObject,
    mut v___y_3978_: *mut LeanObject,
    mut v___y_3979_: *mut LeanObject,
    mut v___y_3980_: *mut LeanObject,
    mut v___y_3981_: *mut LeanObject,
    mut v___y_3982_: *mut LeanObject,
    mut v___y_3983_: *mut LeanObject,
    mut v___y_3984_: *mut LeanObject,
    mut v___y_3985_: *mut LeanObject,
    mut v___y_3986_: *mut LeanObject,
    mut v___y_3987_: *mut LeanObject,
    mut v___y_3988_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_3989_: *mut LeanObject = core::ptr::null_mut();
    v_res_3989_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v_msg_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
    lean_dec(v___y_3987_);
    lean_dec_ref(v___y_3986_);
    lean_dec(v___y_3985_);
    lean_dec_ref(v___y_3984_);
    lean_dec(v___y_3983_);
    lean_dec_ref(v___y_3982_);
    lean_dec(v___y_3981_);
    lean_dec_ref(v___y_3980_);
    lean_dec(v___y_3979_);
    lean_dec(v___y_3978_);
    lean_dec(v___y_3977_);
    return v_res_3989_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2()
-> *mut LeanObject {
    let mut v___x_3992_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut LeanObject = core::ptr::null_mut();
    v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1;
    v___x_3993_ = lean_unsigned_to_nat(6);
    v___x_3994_ = lean_unsigned_to_nat(57);
    v___x_3995_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0;
    v___x_3996_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_3997_ = l_mkPanicMessageWithDecl(
        v___x_3996_,
        v___x_3995_,
        v___x_3994_,
        v___x_3993_,
        v___x_3992_,
    );
    return v___x_3997_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3()
-> *mut LeanObject {
    let mut v___x_3998_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut LeanObject = core::ptr::null_mut();
    v___x_3998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_3999_ = lean_unsigned_to_nat(30);
    v___x_4000_ = lean_unsigned_to_nat(56);
    v___x_4001_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0;
    v___x_4002_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_4003_ = l_mkPanicMessageWithDecl(
        v___x_4002_,
        v___x_4001_,
        v___x_4000_,
        v___x_3999_,
        v___x_3998_,
    );
    return v___x_4003_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(
    mut v_____s_4004_: *mut LeanObject,
    mut v_isLower_4005_: u8,
    mut v_as_4006_: *mut LeanObject,
    mut v_sz_4007_: usize,
    mut v_i_4008_: usize,
    mut v_b_4009_: *mut LeanObject,
    mut v___y_4010_: *mut LeanObject,
    mut v___y_4011_: *mut LeanObject,
    mut v___y_4012_: *mut LeanObject,
    mut v___y_4013_: *mut LeanObject,
    mut v___y_4014_: *mut LeanObject,
    mut v___y_4015_: *mut LeanObject,
    mut v___y_4016_: *mut LeanObject,
    mut v___y_4017_: *mut LeanObject,
    mut v___y_4018_: *mut LeanObject,
    mut v___y_4019_: *mut LeanObject,
    mut v___y_4020_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v_a_4028_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4029_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4033_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: usize = 0;
    let mut v___x_4037_: usize = 0;
    let mut v_reuseFailAlloc_4039_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4053_: u8 = 0;
    let mut v_a_4054_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v___x_4059_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut v___x_4062_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4064_: u8 = 0;
    let mut v_k_4065_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: u8 = 0;
    let mut v___x_4068_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4073_: u8 = 0;
    let mut v___x_4075_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_unused_4087_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4022_ = lean_usize_dec_lt(v_i_4008_, v_sz_4007_);
                if v___x_4022_ == 0 {
                    v___x_4023_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4023_, 0, v_b_4009_);
                    return v___x_4023_;
                } else {
                    v_snd_4024_ = lean_ctor_get(v_b_4009_, 1);
                    v_isSharedCheck_4086_ = (!lean_is_exclusive(v_b_4009_)) as u8;
                    if v_isSharedCheck_4086_ == 0 {
                        v_unused_4087_ = lean_ctor_get(v_b_4009_, 0);
                        lean_dec(v_unused_4087_);
                        v___x_4026_ = v_b_4009_;
                        v_isShared_4027_ = v_isSharedCheck_4086_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4024_);
                        lean_dec(v_b_4009_);
                        v___x_4026_ = lean_box(0);
                        v_isShared_4027_ = v_isSharedCheck_4086_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4028_ = lean_array_uget_borrowed(v_as_4006_, v_i_4008_);
                v_p_4029_ = lean_ctor_get(v_a_4028_, 0);
                v___x_4030_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4029_, v_____s_4004_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                if lean_obj_tag(v___x_4030_) == 0 {
                    lean_dec_ref_known(v___x_4030_, 1);
                    v___x_4031_ = lean_box(0);
                    v___x_4062_ = lean_box(0);
                    if lean_obj_tag(v_p_4029_) == 1 {
                        v_k_4065_ = lean_ctor_get(v_p_4029_, 0);
                        v___x_4066_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
                        v___x_4067_ = lean_int_dec_lt(v_k_4065_, v___x_4066_);
                        if v_isLower_4005_ == 0 {
                            if v___x_4067_ == 0 {
                                v___y_4064_ = v___x_4022_;
                                state = 9;
                                continue;
                            } else {
                                state = 4;
                                continue;
                            }
                        } else {
                            v___y_4064_ = v___x_4067_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4024_);
                        v___x_4068_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4069_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4068_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                        if lean_obj_tag(v___x_4069_) == 0 {
                            lean_dec_ref_known(v___x_4069_, 1);
                            v_a_4033_ = v___x_4062_;
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_4026_);
                            v_a_4070_ = lean_ctor_get(v___x_4069_, 0);
                            v_isSharedCheck_4077_ = (!lean_is_exclusive(v___x_4069_)) as u8;
                            if v_isSharedCheck_4077_ == 0 {
                                v___x_4072_ = v___x_4069_;
                                v_isShared_4073_ = v_isSharedCheck_4077_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_4070_);
                                lean_dec(v___x_4069_);
                                v___x_4072_ = lean_box(0);
                                v_isShared_4073_ = v_isSharedCheck_4077_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4026_);
                    lean_dec(v_snd_4024_);
                    v_a_4078_ = lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4085_ = (!lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4085_ == 0 {
                        v___x_4080_ = v___x_4030_;
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_4078_);
                        lean_dec(v___x_4030_);
                        v___x_4080_ = lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4027_ == 0 {
                    lean_ctor_set(v___x_4026_, 1, v_a_4033_);
                    lean_ctor_set(v___x_4026_, 0, v___x_4031_);
                    v___x_4035_ = v___x_4026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4039_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4031_);
                    lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_a_4033_);
                    v___x_4035_ = v_reuseFailAlloc_4039_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4036_ = 1usize;
                v___x_4037_ = lean_usize_add(v_i_4008_, v___x_4036_);
                v_i_4008_ = v___x_4037_;
                v_b_4009_ = v___x_4035_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4041_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4042_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4041_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                if lean_obj_tag(v___x_4042_) == 0 {
                    v_a_4043_ = lean_ctor_get(v___x_4042_, 0);
                    v_isSharedCheck_4053_ = (!lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4053_ == 0 {
                        v___x_4045_ = v___x_4042_;
                        v_isShared_4046_ = v_isSharedCheck_4053_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4043_);
                        lean_dec(v___x_4042_);
                        v___x_4045_ = lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4053_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4026_);
                    lean_dec(v_snd_4024_);
                    v_a_4054_ = lean_ctor_get(v___x_4042_, 0);
                    v_isSharedCheck_4061_ = (!lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4061_ == 0 {
                        v___x_4056_ = v___x_4042_;
                        v_isShared_4057_ = v_isSharedCheck_4061_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4054_);
                        lean_dec(v___x_4042_);
                        v___x_4056_ = lean_box(0);
                        v_isShared_4057_ = v_isSharedCheck_4061_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_4043_) == 0 {
                    lean_del_object(v___x_4026_);
                    v___x_4047_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4047_, 0, v_a_4043_);
                    v___x_4048_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4048_, 0, v___x_4047_);
                    lean_ctor_set(v___x_4048_, 1, v_snd_4024_);
                    if v_isShared_4046_ == 0 {
                        lean_ctor_set(v___x_4045_, 0, v___x_4048_);
                        v___x_4050_ = v___x_4045_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4051_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
                        v___x_4050_ = v_reuseFailAlloc_4051_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4045_);
                    lean_dec(v_snd_4024_);
                    v_a_4052_ = lean_ctor_get(v_a_4043_, 0);
                    lean_inc(v_a_4052_);
                    lean_dec_ref_known(v_a_4043_, 1);
                    v_a_4033_ = v_a_4052_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                return v___x_4050_;
            }
            7 => {
                if v_isShared_4057_ == 0 {
                    v___x_4059_ = v___x_4056_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4060_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
                    v___x_4059_ = v_reuseFailAlloc_4060_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4059_;
            }
            9 => {
                if v___y_4064_ == 0 {
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_snd_4024_);
                    v_a_4033_ = v___x_4062_;
                    state = 2;
                    continue;
                }
            }
            10 => {
                if v_isShared_4073_ == 0 {
                    v___x_4075_ = v___x_4072_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4076_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
                    v___x_4075_ = v_reuseFailAlloc_4076_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4075_;
            }
            12 => {
                if v_isShared_4081_ == 0 {
                    v___x_4083_ = v___x_4080_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4084_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
                    v___x_4083_ = v_reuseFailAlloc_4084_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4083_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_4088_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_4089_: *mut LeanObject = *_args.add(1);
    let mut v_as_4090_: *mut LeanObject = *_args.add(2);
    let mut v_sz_4091_: *mut LeanObject = *_args.add(3);
    let mut v_i_4092_: *mut LeanObject = *_args.add(4);
    let mut v_b_4093_: *mut LeanObject = *_args.add(5);
    let mut v___y_4094_: *mut LeanObject = *_args.add(6);
    let mut v___y_4095_: *mut LeanObject = *_args.add(7);
    let mut v___y_4096_: *mut LeanObject = *_args.add(8);
    let mut v___y_4097_: *mut LeanObject = *_args.add(9);
    let mut v___y_4098_: *mut LeanObject = *_args.add(10);
    let mut v___y_4099_: *mut LeanObject = *_args.add(11);
    let mut v___y_4100_: *mut LeanObject = *_args.add(12);
    let mut v___y_4101_: *mut LeanObject = *_args.add(13);
    let mut v___y_4102_: *mut LeanObject = *_args.add(14);
    let mut v___y_4103_: *mut LeanObject = *_args.add(15);
    let mut v___y_4104_: *mut LeanObject = *_args.add(16);
    let mut v___y_4105_: *mut LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4106_: u8 = 0;
    let mut v_sz_boxed_4107_: usize = 0;
    let mut v_i_boxed_4108_: usize = 0;
    let mut v_res_4109_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4106_ = (lean_unbox(v_isLower_4089_) as u8);
    v_sz_boxed_4107_ = lean_unbox_usize(v_sz_4091_);
    lean_dec(v_sz_4091_);
    v_i_boxed_4108_ = lean_unbox_usize(v_i_4092_);
    lean_dec(v_i_4092_);
    v_res_4109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_4088_, v_isLower_boxed_4106_, v_as_4090_, v_sz_boxed_4107_, v_i_boxed_4108_, v_b_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
    lean_dec(v___y_4104_);
    lean_dec_ref(v___y_4103_);
    lean_dec(v___y_4102_);
    lean_dec_ref(v___y_4101_);
    lean_dec(v___y_4100_);
    lean_dec_ref(v___y_4099_);
    lean_dec(v___y_4098_);
    lean_dec_ref(v___y_4097_);
    lean_dec(v___y_4096_);
    lean_dec(v___y_4095_);
    lean_dec(v___y_4094_);
    lean_dec_ref(v_as_4090_);
    lean_dec(v_____s_4088_);
    return v_res_4109_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(
    mut v_____s_4110_: *mut LeanObject,
    mut v_isLower_4111_: u8,
    mut v_as_4112_: *mut LeanObject,
    mut v_sz_4113_: usize,
    mut v_i_4114_: usize,
    mut v_b_4115_: *mut LeanObject,
    mut v___y_4116_: *mut LeanObject,
    mut v___y_4117_: *mut LeanObject,
    mut v___y_4118_: *mut LeanObject,
    mut v___y_4119_: *mut LeanObject,
    mut v___y_4120_: *mut LeanObject,
    mut v___y_4121_: *mut LeanObject,
    mut v___y_4122_: *mut LeanObject,
    mut v___y_4123_: *mut LeanObject,
    mut v___y_4124_: *mut LeanObject,
    mut v___y_4125_: *mut LeanObject,
    mut v___y_4126_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4128_: u8 = 0;
    let mut v___x_4129_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v_a_4134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: usize = 0;
    let mut v___x_4144_: usize = 0;
    let mut v___x_4145_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v_a_4161_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v___y_4170_: u8 = 0;
    let mut v_k_4171_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut LeanObject = core::ptr::null_mut();
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
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v_unused_4193_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4128_ = lean_usize_dec_lt(v_i_4114_, v_sz_4113_);
                if v___x_4128_ == 0 {
                    v___x_4129_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4129_, 0, v_b_4115_);
                    return v___x_4129_;
                } else {
                    v_snd_4130_ = lean_ctor_get(v_b_4115_, 1);
                    v_isSharedCheck_4192_ = (!lean_is_exclusive(v_b_4115_)) as u8;
                    if v_isSharedCheck_4192_ == 0 {
                        v_unused_4193_ = lean_ctor_get(v_b_4115_, 0);
                        lean_dec(v_unused_4193_);
                        v___x_4132_ = v_b_4115_;
                        v_isShared_4133_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4130_);
                        lean_dec(v_b_4115_);
                        v___x_4132_ = lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4134_ = lean_array_uget_borrowed(v_as_4112_, v_i_4114_);
                v_p_4135_ = lean_ctor_get(v_a_4134_, 0);
                v___x_4136_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4135_, v_____s_4110_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                if lean_obj_tag(v___x_4136_) == 0 {
                    lean_dec_ref_known(v___x_4136_, 1);
                    v___x_4137_ = lean_box(0);
                    v___x_4138_ = lean_box(0);
                    if lean_obj_tag(v_p_4135_) == 1 {
                        v_k_4171_ = lean_ctor_get(v_p_4135_, 0);
                        v___x_4172_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
                        v___x_4173_ = lean_int_dec_lt(v_k_4171_, v___x_4172_);
                        if v_isLower_4111_ == 0 {
                            if v___x_4173_ == 0 {
                                v___y_4170_ = v___x_4128_;
                                state = 9;
                                continue;
                            } else {
                                state = 4;
                                continue;
                            }
                        } else {
                            v___y_4170_ = v___x_4173_;
                            state = 9;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4130_);
                        v___x_4174_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4175_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4174_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        if lean_obj_tag(v___x_4175_) == 0 {
                            lean_dec_ref_known(v___x_4175_, 1);
                            v_a_4140_ = v___x_4137_;
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_4132_);
                            v_a_4176_ = lean_ctor_get(v___x_4175_, 0);
                            v_isSharedCheck_4183_ = (!lean_is_exclusive(v___x_4175_)) as u8;
                            if v_isSharedCheck_4183_ == 0 {
                                v___x_4178_ = v___x_4175_;
                                v_isShared_4179_ = v_isSharedCheck_4183_;
                                state = 10;
                                continue;
                            } else {
                                lean_inc(v_a_4176_);
                                lean_dec(v___x_4175_);
                                v___x_4178_ = lean_box(0);
                                v_isShared_4179_ = v_isSharedCheck_4183_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4132_);
                    lean_dec(v_snd_4130_);
                    v_a_4184_ = lean_ctor_get(v___x_4136_, 0);
                    v_isSharedCheck_4191_ = (!lean_is_exclusive(v___x_4136_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4186_ = v___x_4136_;
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 12;
                        continue;
                    } else {
                        lean_inc(v_a_4184_);
                        lean_dec(v___x_4136_);
                        v___x_4186_ = lean_box(0);
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4133_ == 0 {
                    lean_ctor_set(v___x_4132_, 1, v_a_4140_);
                    lean_ctor_set(v___x_4132_, 0, v___x_4138_);
                    v___x_4142_ = v___x_4132_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4138_);
                    lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_a_4140_);
                    v___x_4142_ = v_reuseFailAlloc_4146_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4143_ = 1usize;
                v___x_4144_ = lean_usize_add(v_i_4114_, v___x_4143_);
                v___x_4145_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_4110_, v_isLower_4111_, v_as_4112_, v_sz_4113_, v___x_4144_, v___x_4142_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                return v___x_4145_;
            }
            4 => {
                v___x_4148_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4149_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4148_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                if lean_obj_tag(v___x_4149_) == 0 {
                    v_a_4150_ = lean_ctor_get(v___x_4149_, 0);
                    v_isSharedCheck_4160_ = (!lean_is_exclusive(v___x_4149_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4152_ = v___x_4149_;
                        v_isShared_4153_ = v_isSharedCheck_4160_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4150_);
                        lean_dec(v___x_4149_);
                        v___x_4152_ = lean_box(0);
                        v_isShared_4153_ = v_isSharedCheck_4160_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4132_);
                    lean_dec(v_snd_4130_);
                    v_a_4161_ = lean_ctor_get(v___x_4149_, 0);
                    v_isSharedCheck_4168_ = (!lean_is_exclusive(v___x_4149_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4163_ = v___x_4149_;
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 7;
                        continue;
                    } else {
                        lean_inc(v_a_4161_);
                        lean_dec(v___x_4149_);
                        v___x_4163_ = lean_box(0);
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_4150_) == 0 {
                    lean_del_object(v___x_4132_);
                    v___x_4154_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4154_, 0, v_a_4150_);
                    v___x_4155_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4155_, 0, v___x_4154_);
                    lean_ctor_set(v___x_4155_, 1, v_snd_4130_);
                    if v_isShared_4153_ == 0 {
                        lean_ctor_set(v___x_4152_, 0, v___x_4155_);
                        v___x_4157_ = v___x_4152_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4158_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
                        v___x_4157_ = v_reuseFailAlloc_4158_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4152_);
                    lean_dec(v_snd_4130_);
                    v_a_4159_ = lean_ctor_get(v_a_4150_, 0);
                    lean_inc(v_a_4159_);
                    lean_dec_ref_known(v_a_4150_, 1);
                    v_a_4140_ = v_a_4159_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                return v___x_4157_;
            }
            7 => {
                if v_isShared_4164_ == 0 {
                    v___x_4166_ = v___x_4163_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4167_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
                    v___x_4166_ = v_reuseFailAlloc_4167_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4166_;
            }
            9 => {
                if v___y_4170_ == 0 {
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_snd_4130_);
                    v_a_4140_ = v___x_4137_;
                    state = 2;
                    continue;
                }
            }
            10 => {
                if v_isShared_4179_ == 0 {
                    v___x_4181_ = v___x_4178_;
                    state = 11;
                    continue;
                } else {
                    v_reuseFailAlloc_4182_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
                    v___x_4181_ = v_reuseFailAlloc_4182_;
                    state = 11;
                    continue;
                }
            }
            11 => {
                return v___x_4181_;
            }
            12 => {
                if v_isShared_4187_ == 0 {
                    v___x_4189_ = v___x_4186_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4190_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
                    v___x_4189_ = v_reuseFailAlloc_4190_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4189_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_4194_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_4195_: *mut LeanObject = *_args.add(1);
    let mut v_as_4196_: *mut LeanObject = *_args.add(2);
    let mut v_sz_4197_: *mut LeanObject = *_args.add(3);
    let mut v_i_4198_: *mut LeanObject = *_args.add(4);
    let mut v_b_4199_: *mut LeanObject = *_args.add(5);
    let mut v___y_4200_: *mut LeanObject = *_args.add(6);
    let mut v___y_4201_: *mut LeanObject = *_args.add(7);
    let mut v___y_4202_: *mut LeanObject = *_args.add(8);
    let mut v___y_4203_: *mut LeanObject = *_args.add(9);
    let mut v___y_4204_: *mut LeanObject = *_args.add(10);
    let mut v___y_4205_: *mut LeanObject = *_args.add(11);
    let mut v___y_4206_: *mut LeanObject = *_args.add(12);
    let mut v___y_4207_: *mut LeanObject = *_args.add(13);
    let mut v___y_4208_: *mut LeanObject = *_args.add(14);
    let mut v___y_4209_: *mut LeanObject = *_args.add(15);
    let mut v___y_4210_: *mut LeanObject = *_args.add(16);
    let mut v___y_4211_: *mut LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4212_: u8 = 0;
    let mut v_sz_boxed_4213_: usize = 0;
    let mut v_i_boxed_4214_: usize = 0;
    let mut v_res_4215_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4212_ = (lean_unbox(v_isLower_4195_) as u8);
    v_sz_boxed_4213_ = lean_unbox_usize(v_sz_4197_);
    lean_dec(v_sz_4197_);
    v_i_boxed_4214_ = lean_unbox_usize(v_i_4198_);
    lean_dec(v_i_4198_);
    v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_4194_, v_isLower_boxed_4212_, v_as_4196_, v_sz_boxed_4213_, v_i_boxed_4214_, v_b_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
    lean_dec(v___y_4210_);
    lean_dec_ref(v___y_4209_);
    lean_dec(v___y_4208_);
    lean_dec_ref(v___y_4207_);
    lean_dec(v___y_4206_);
    lean_dec_ref(v___y_4205_);
    lean_dec(v___y_4204_);
    lean_dec_ref(v___y_4203_);
    lean_dec(v___y_4202_);
    lean_dec(v___y_4201_);
    lean_dec(v___y_4200_);
    lean_dec_ref(v_as_4196_);
    lean_dec(v_____s_4194_);
    return v_res_4215_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(
    mut v_init_4216_: *mut LeanObject,
    mut v_____s_4217_: *mut LeanObject,
    mut v_isLower_4218_: u8,
    mut v_n_4219_: *mut LeanObject,
    mut v_b_4220_: *mut LeanObject,
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
    let mut v_cs_4233_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4236_: usize = 0;
    let mut v___x_4237_: usize = 0;
    let mut v___x_4238_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v_fst_4243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4244_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4248_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4249_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v_a_4254_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4257_: u8 = 0;
    let mut v___x_4259_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4260_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4261_: u8 = 0;
    let mut v_vs_4262_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4265_: usize = 0;
    let mut v___x_4266_: usize = 0;
    let mut v___x_4267_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4268_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v_fst_4272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4273_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4278_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v_a_4283_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v___x_4288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4289_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_4219_) == 0 {
                    v_cs_4233_ = lean_ctor_get(v_n_4219_, 0);
                    v___x_4234_ = lean_box(0);
                    v___x_4235_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4235_, 0, v___x_4234_);
                    lean_ctor_set(v___x_4235_, 1, v_b_4220_);
                    v_sz_4236_ = lean_array_size(v_cs_4233_);
                    v___x_4237_ = 0usize;
                    v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_4216_, v_____s_4217_, v_isLower_4218_, v_cs_4233_, v_sz_4236_, v___x_4237_, v___x_4235_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
                    if lean_obj_tag(v___x_4238_) == 0 {
                        v_a_4239_ = lean_ctor_get(v___x_4238_, 0);
                        v_isSharedCheck_4253_ = (!lean_is_exclusive(v___x_4238_)) as u8;
                        if v_isSharedCheck_4253_ == 0 {
                            v___x_4241_ = v___x_4238_;
                            v_isShared_4242_ = v_isSharedCheck_4253_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4239_);
                            lean_dec(v___x_4238_);
                            v___x_4241_ = lean_box(0);
                            v_isShared_4242_ = v_isSharedCheck_4253_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4254_ = lean_ctor_get(v___x_4238_, 0);
                        v_isSharedCheck_4261_ = (!lean_is_exclusive(v___x_4238_)) as u8;
                        if v_isSharedCheck_4261_ == 0 {
                            v___x_4256_ = v___x_4238_;
                            v_isShared_4257_ = v_isSharedCheck_4261_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4254_);
                            lean_dec(v___x_4238_);
                            v___x_4256_ = lean_box(0);
                            v_isShared_4257_ = v_isSharedCheck_4261_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4262_ = lean_ctor_get(v_n_4219_, 0);
                    v___x_4263_ = lean_box(0);
                    v___x_4264_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4264_, 0, v___x_4263_);
                    lean_ctor_set(v___x_4264_, 1, v_b_4220_);
                    v_sz_4265_ = lean_array_size(v_vs_4262_);
                    v___x_4266_ = 0usize;
                    v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_4217_, v_isLower_4218_, v_vs_4262_, v_sz_4265_, v___x_4266_, v___x_4264_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
                    if lean_obj_tag(v___x_4267_) == 0 {
                        v_a_4268_ = lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4282_ = (!lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4282_ == 0 {
                            v___x_4270_ = v___x_4267_;
                            v_isShared_4271_ = v_isSharedCheck_4282_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4268_);
                            lean_dec(v___x_4267_);
                            v___x_4270_ = lean_box(0);
                            v_isShared_4271_ = v_isSharedCheck_4282_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4283_ = lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4290_ = (!lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4290_ == 0 {
                            v___x_4285_ = v___x_4267_;
                            v_isShared_4286_ = v_isSharedCheck_4290_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4283_);
                            lean_dec(v___x_4267_);
                            v___x_4285_ = lean_box(0);
                            v_isShared_4286_ = v_isSharedCheck_4290_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4243_ = lean_ctor_get(v_a_4239_, 0);
                if lean_obj_tag(v_fst_4243_) == 0 {
                    v_snd_4244_ = lean_ctor_get(v_a_4239_, 1);
                    lean_inc(v_snd_4244_);
                    lean_dec(v_a_4239_);
                    v___x_4245_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4245_, 0, v_snd_4244_);
                    if v_isShared_4242_ == 0 {
                        lean_ctor_set(v___x_4241_, 0, v___x_4245_);
                        v___x_4247_ = v___x_4241_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4248_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
                        v___x_4247_ = v_reuseFailAlloc_4248_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4243_);
                    lean_dec(v_a_4239_);
                    v_val_4249_ = lean_ctor_get(v_fst_4243_, 0);
                    lean_inc(v_val_4249_);
                    lean_dec_ref_known(v_fst_4243_, 1);
                    if v_isShared_4242_ == 0 {
                        lean_ctor_set(v___x_4241_, 0, v_val_4249_);
                        v___x_4251_ = v___x_4241_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4252_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_val_4249_);
                        v___x_4251_ = v_reuseFailAlloc_4252_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4247_;
            }
            3 => {
                return v___x_4251_;
            }
            4 => {
                if v_isShared_4257_ == 0 {
                    v___x_4259_ = v___x_4256_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4260_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
                    v___x_4259_ = v_reuseFailAlloc_4260_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4259_;
            }
            6 => {
                v_fst_4272_ = lean_ctor_get(v_a_4268_, 0);
                if lean_obj_tag(v_fst_4272_) == 0 {
                    v_snd_4273_ = lean_ctor_get(v_a_4268_, 1);
                    lean_inc(v_snd_4273_);
                    lean_dec(v_a_4268_);
                    v___x_4274_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4274_, 0, v_snd_4273_);
                    if v_isShared_4271_ == 0 {
                        lean_ctor_set(v___x_4270_, 0, v___x_4274_);
                        v___x_4276_ = v___x_4270_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4277_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
                        v___x_4276_ = v_reuseFailAlloc_4277_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4272_);
                    lean_dec(v_a_4268_);
                    v_val_4278_ = lean_ctor_get(v_fst_4272_, 0);
                    lean_inc(v_val_4278_);
                    lean_dec_ref_known(v_fst_4272_, 1);
                    if v_isShared_4271_ == 0 {
                        lean_ctor_set(v___x_4270_, 0, v_val_4278_);
                        v___x_4280_ = v___x_4270_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4281_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_val_4278_);
                        v___x_4280_ = v_reuseFailAlloc_4281_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4276_;
            }
            8 => {
                return v___x_4280_;
            }
            9 => {
                if v_isShared_4286_ == 0 {
                    v___x_4288_ = v___x_4285_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4289_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
                    v___x_4288_ = v_reuseFailAlloc_4289_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4288_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(
    mut v_init_4291_: *mut LeanObject,
    mut v_____s_4292_: *mut LeanObject,
    mut v_isLower_4293_: u8,
    mut v_as_4294_: *mut LeanObject,
    mut v_sz_4295_: usize,
    mut v_i_4296_: usize,
    mut v_b_4297_: *mut LeanObject,
    mut v___y_4298_: *mut LeanObject,
    mut v___y_4299_: *mut LeanObject,
    mut v___y_4300_: *mut LeanObject,
    mut v___y_4301_: *mut LeanObject,
    mut v___y_4302_: *mut LeanObject,
    mut v___y_4303_: *mut LeanObject,
    mut v___y_4304_: *mut LeanObject,
    mut v___y_4305_: *mut LeanObject,
    mut v___y_4306_: *mut LeanObject,
    mut v___y_4307_: *mut LeanObject,
    mut v___y_4308_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4312_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v_a_4316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4322_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: usize = 0;
    let mut v___x_4334_: usize = 0;
    let mut v_reuseFailAlloc_4336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v_a_4338_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4341_: u8 = 0;
    let mut v___x_4343_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_unused_4347_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4310_ = lean_usize_dec_lt(v_i_4296_, v_sz_4295_);
                if v___x_4310_ == 0 {
                    v___x_4311_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4311_, 0, v_b_4297_);
                    return v___x_4311_;
                } else {
                    v_snd_4312_ = lean_ctor_get(v_b_4297_, 1);
                    v_isSharedCheck_4346_ = (!lean_is_exclusive(v_b_4297_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v_unused_4347_ = lean_ctor_get(v_b_4297_, 0);
                        lean_dec(v_unused_4347_);
                        v___x_4314_ = v_b_4297_;
                        v_isShared_4315_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4312_);
                        lean_dec(v_b_4297_);
                        v___x_4314_ = lean_box(0);
                        v_isShared_4315_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4316_ = lean_array_uget_borrowed(v_as_4294_, v_i_4296_);
                lean_inc(v_snd_4312_);
                v___x_4317_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4291_, v_____s_4292_, v_isLower_4293_, v_a_4316_, v_snd_4312_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
                if lean_obj_tag(v___x_4317_) == 0 {
                    v_a_4318_ = lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4337_ = (!lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4320_ = v___x_4317_;
                        v_isShared_4321_ = v_isSharedCheck_4337_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4318_);
                        lean_dec(v___x_4317_);
                        v___x_4320_ = lean_box(0);
                        v_isShared_4321_ = v_isSharedCheck_4337_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4314_);
                    lean_dec(v_snd_4312_);
                    v_a_4338_ = lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4345_ = (!lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4345_ == 0 {
                        v___x_4340_ = v___x_4317_;
                        v_isShared_4341_ = v_isSharedCheck_4345_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4338_);
                        lean_dec(v___x_4317_);
                        v___x_4340_ = lean_box(0);
                        v_isShared_4341_ = v_isSharedCheck_4345_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4318_) == 0 {
                    v___x_4322_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4322_, 0, v_a_4318_);
                    if v_isShared_4315_ == 0 {
                        lean_ctor_set(v___x_4314_, 0, v___x_4322_);
                        v___x_4324_ = v___x_4314_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4328_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4322_);
                        lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_snd_4312_);
                        v___x_4324_ = v_reuseFailAlloc_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4320_);
                    lean_dec(v_snd_4312_);
                    v_a_4329_ = lean_ctor_get(v_a_4318_, 0);
                    lean_inc(v_a_4329_);
                    lean_dec_ref_known(v_a_4318_, 1);
                    v___x_4330_ = lean_box(0);
                    if v_isShared_4315_ == 0 {
                        lean_ctor_set(v___x_4314_, 1, v_a_4329_);
                        lean_ctor_set(v___x_4314_, 0, v___x_4330_);
                        v___x_4332_ = v___x_4314_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4336_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4330_);
                        lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_a_4329_);
                        v___x_4332_ = v_reuseFailAlloc_4336_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4321_ == 0 {
                    lean_ctor_set(v___x_4320_, 0, v___x_4324_);
                    v___x_4326_ = v___x_4320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
                    v___x_4326_ = v_reuseFailAlloc_4327_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4326_;
            }
            5 => {
                v___x_4333_ = 1usize;
                v___x_4334_ = lean_usize_add(v_i_4296_, v___x_4333_);
                v_i_4296_ = v___x_4334_;
                v_b_4297_ = v___x_4332_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4341_ == 0 {
                    v___x_4343_ = v___x_4340_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4344_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
                    v___x_4343_ = v_reuseFailAlloc_4344_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4343_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_4348_: *mut LeanObject = *_args.add(0);
    let mut v_____s_4349_: *mut LeanObject = *_args.add(1);
    let mut v_isLower_4350_: *mut LeanObject = *_args.add(2);
    let mut v_as_4351_: *mut LeanObject = *_args.add(3);
    let mut v_sz_4352_: *mut LeanObject = *_args.add(4);
    let mut v_i_4353_: *mut LeanObject = *_args.add(5);
    let mut v_b_4354_: *mut LeanObject = *_args.add(6);
    let mut v___y_4355_: *mut LeanObject = *_args.add(7);
    let mut v___y_4356_: *mut LeanObject = *_args.add(8);
    let mut v___y_4357_: *mut LeanObject = *_args.add(9);
    let mut v___y_4358_: *mut LeanObject = *_args.add(10);
    let mut v___y_4359_: *mut LeanObject = *_args.add(11);
    let mut v___y_4360_: *mut LeanObject = *_args.add(12);
    let mut v___y_4361_: *mut LeanObject = *_args.add(13);
    let mut v___y_4362_: *mut LeanObject = *_args.add(14);
    let mut v___y_4363_: *mut LeanObject = *_args.add(15);
    let mut v___y_4364_: *mut LeanObject = *_args.add(16);
    let mut v___y_4365_: *mut LeanObject = *_args.add(17);
    let mut v___y_4366_: *mut LeanObject = *_args.add(18);
    let mut v_isLower_boxed_4367_: u8 = 0;
    let mut v_sz_boxed_4368_: usize = 0;
    let mut v_i_boxed_4369_: usize = 0;
    let mut v_res_4370_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4367_ = (lean_unbox(v_isLower_4350_) as u8);
    v_sz_boxed_4368_ = lean_unbox_usize(v_sz_4352_);
    lean_dec(v_sz_4352_);
    v_i_boxed_4369_ = lean_unbox_usize(v_i_4353_);
    lean_dec(v_i_4353_);
    v_res_4370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_4348_, v_____s_4349_, v_isLower_boxed_4367_, v_as_4351_, v_sz_boxed_4368_, v_i_boxed_4369_, v_b_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
    lean_dec(v___y_4365_);
    lean_dec_ref(v___y_4364_);
    lean_dec(v___y_4363_);
    lean_dec_ref(v___y_4362_);
    lean_dec(v___y_4361_);
    lean_dec_ref(v___y_4360_);
    lean_dec(v___y_4359_);
    lean_dec_ref(v___y_4358_);
    lean_dec(v___y_4357_);
    lean_dec(v___y_4356_);
    lean_dec(v___y_4355_);
    lean_dec_ref(v_as_4351_);
    lean_dec(v_____s_4349_);
    return v_res_4370_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_4371_: *mut LeanObject = *_args.add(0);
    let mut v_____s_4372_: *mut LeanObject = *_args.add(1);
    let mut v_isLower_4373_: *mut LeanObject = *_args.add(2);
    let mut v_n_4374_: *mut LeanObject = *_args.add(3);
    let mut v_b_4375_: *mut LeanObject = *_args.add(4);
    let mut v___y_4376_: *mut LeanObject = *_args.add(5);
    let mut v___y_4377_: *mut LeanObject = *_args.add(6);
    let mut v___y_4378_: *mut LeanObject = *_args.add(7);
    let mut v___y_4379_: *mut LeanObject = *_args.add(8);
    let mut v___y_4380_: *mut LeanObject = *_args.add(9);
    let mut v___y_4381_: *mut LeanObject = *_args.add(10);
    let mut v___y_4382_: *mut LeanObject = *_args.add(11);
    let mut v___y_4383_: *mut LeanObject = *_args.add(12);
    let mut v___y_4384_: *mut LeanObject = *_args.add(13);
    let mut v___y_4385_: *mut LeanObject = *_args.add(14);
    let mut v___y_4386_: *mut LeanObject = *_args.add(15);
    let mut v___y_4387_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4388_: u8 = 0;
    let mut v_res_4389_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4388_ = (lean_unbox(v_isLower_4373_) as u8);
    v_res_4389_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4371_, v_____s_4372_, v_isLower_boxed_4388_, v_n_4374_, v_b_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
    lean_dec(v___y_4386_);
    lean_dec_ref(v___y_4385_);
    lean_dec(v___y_4384_);
    lean_dec_ref(v___y_4383_);
    lean_dec(v___y_4382_);
    lean_dec_ref(v___y_4381_);
    lean_dec(v___y_4380_);
    lean_dec_ref(v___y_4379_);
    lean_dec(v___y_4378_);
    lean_dec(v___y_4377_);
    lean_dec(v___y_4376_);
    lean_dec_ref(v_n_4374_);
    lean_dec(v_____s_4372_);
    return v_res_4389_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(
    mut v_____s_4390_: *mut LeanObject,
    mut v_isLower_4391_: u8,
    mut v_as_4392_: *mut LeanObject,
    mut v_sz_4393_: usize,
    mut v_i_4394_: usize,
    mut v_b_4395_: *mut LeanObject,
    mut v___y_4396_: *mut LeanObject,
    mut v___y_4397_: *mut LeanObject,
    mut v___y_4398_: *mut LeanObject,
    mut v___y_4399_: *mut LeanObject,
    mut v___y_4400_: *mut LeanObject,
    mut v___y_4401_: *mut LeanObject,
    mut v___y_4402_: *mut LeanObject,
    mut v___y_4403_: *mut LeanObject,
    mut v___y_4404_: *mut LeanObject,
    mut v___y_4405_: *mut LeanObject,
    mut v___y_4406_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4413_: u8 = 0;
    let mut v_a_4414_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4415_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: usize = 0;
    let mut v___x_4423_: usize = 0;
    let mut v_reuseFailAlloc_4425_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v_a_4433_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4436_: u8 = 0;
    let mut v___x_4438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v_a_4445_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4446_: u8 = 0;
    let mut v_a_4447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4450_: u8 = 0;
    let mut v___x_4452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut v___x_4455_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_4457_: u8 = 0;
    let mut v_k_4458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v___x_4468_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_a_4471_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4476_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_unused_4480_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4408_ = lean_usize_dec_lt(v_i_4394_, v_sz_4393_);
                if v___x_4408_ == 0 {
                    v___x_4409_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4409_, 0, v_b_4395_);
                    return v___x_4409_;
                } else {
                    v_snd_4410_ = lean_ctor_get(v_b_4395_, 1);
                    v_isSharedCheck_4479_ = (!lean_is_exclusive(v_b_4395_)) as u8;
                    if v_isSharedCheck_4479_ == 0 {
                        v_unused_4480_ = lean_ctor_get(v_b_4395_, 0);
                        lean_dec(v_unused_4480_);
                        v___x_4412_ = v_b_4395_;
                        v_isShared_4413_ = v_isSharedCheck_4479_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4410_);
                        lean_dec(v_b_4395_);
                        v___x_4412_ = lean_box(0);
                        v_isShared_4413_ = v_isSharedCheck_4479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4414_ = lean_array_uget_borrowed(v_as_4392_, v_i_4394_);
                v_p_4415_ = lean_ctor_get(v_a_4414_, 0);
                v___x_4416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4415_, v_____s_4390_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                if lean_obj_tag(v___x_4416_) == 0 {
                    lean_dec_ref_known(v___x_4416_, 1);
                    v___x_4417_ = lean_box(0);
                    v___x_4455_ = lean_box(0);
                    if lean_obj_tag(v_p_4415_) == 1 {
                        v_k_4458_ = lean_ctor_get(v_p_4415_, 0);
                        v___x_4459_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
                        v___x_4460_ = lean_int_dec_lt(v_k_4458_, v___x_4459_);
                        if v_isLower_4391_ == 0 {
                            if v___x_4460_ == 0 {
                                v___y_4457_ = v___x_4408_;
                                state = 11;
                                continue;
                            } else {
                                state = 4;
                                continue;
                            }
                        } else {
                            v___y_4457_ = v___x_4460_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4410_);
                        v___x_4461_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4462_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4461_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                        if lean_obj_tag(v___x_4462_) == 0 {
                            lean_dec_ref_known(v___x_4462_, 1);
                            v_a_4419_ = v___x_4455_;
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_4412_);
                            v_a_4463_ = lean_ctor_get(v___x_4462_, 0);
                            v_isSharedCheck_4470_ = (!lean_is_exclusive(v___x_4462_)) as u8;
                            if v_isSharedCheck_4470_ == 0 {
                                v___x_4465_ = v___x_4462_;
                                v_isShared_4466_ = v_isSharedCheck_4470_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_4463_);
                                lean_dec(v___x_4462_);
                                v___x_4465_ = lean_box(0);
                                v_isShared_4466_ = v_isSharedCheck_4470_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4412_);
                    lean_dec(v_snd_4410_);
                    v_a_4471_ = lean_ctor_get(v___x_4416_, 0);
                    v_isSharedCheck_4478_ = (!lean_is_exclusive(v___x_4416_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4473_ = v___x_4416_;
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_4471_);
                        lean_dec(v___x_4416_);
                        v___x_4473_ = lean_box(0);
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4413_ == 0 {
                    lean_ctor_set(v___x_4412_, 1, v_a_4419_);
                    lean_ctor_set(v___x_4412_, 0, v___x_4417_);
                    v___x_4421_ = v___x_4412_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4417_);
                    lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_a_4419_);
                    v___x_4421_ = v_reuseFailAlloc_4425_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4422_ = 1usize;
                v___x_4423_ = lean_usize_add(v_i_4394_, v___x_4422_);
                v_i_4394_ = v___x_4423_;
                v_b_4395_ = v___x_4421_;
                state = 0;
                continue;
            }
            4 => {
                v___x_4427_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4428_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4427_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                if lean_obj_tag(v___x_4428_) == 0 {
                    v_a_4429_ = lean_ctor_get(v___x_4428_, 0);
                    v_isSharedCheck_4446_ = (!lean_is_exclusive(v___x_4428_)) as u8;
                    if v_isSharedCheck_4446_ == 0 {
                        v___x_4431_ = v___x_4428_;
                        v_isShared_4432_ = v_isSharedCheck_4446_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4429_);
                        lean_dec(v___x_4428_);
                        v___x_4431_ = lean_box(0);
                        v_isShared_4432_ = v_isSharedCheck_4446_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4412_);
                    lean_dec(v_snd_4410_);
                    v_a_4447_ = lean_ctor_get(v___x_4428_, 0);
                    v_isSharedCheck_4454_ = (!lean_is_exclusive(v___x_4428_)) as u8;
                    if v_isSharedCheck_4454_ == 0 {
                        v___x_4449_ = v___x_4428_;
                        v_isShared_4450_ = v_isSharedCheck_4454_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4447_);
                        lean_dec(v___x_4428_);
                        v___x_4449_ = lean_box(0);
                        v_isShared_4450_ = v_isSharedCheck_4454_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_4429_) == 0 {
                    lean_del_object(v___x_4412_);
                    v_a_4433_ = lean_ctor_get(v_a_4429_, 0);
                    v_isSharedCheck_4444_ = (!lean_is_exclusive(v_a_4429_)) as u8;
                    if v_isSharedCheck_4444_ == 0 {
                        v___x_4435_ = v_a_4429_;
                        v_isShared_4436_ = v_isSharedCheck_4444_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4433_);
                        lean_dec(v_a_4429_);
                        v___x_4435_ = lean_box(0);
                        v_isShared_4436_ = v_isSharedCheck_4444_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4431_);
                    lean_dec(v_snd_4410_);
                    v_a_4445_ = lean_ctor_get(v_a_4429_, 0);
                    lean_inc(v_a_4445_);
                    lean_dec_ref_known(v_a_4429_, 1);
                    v_a_4419_ = v_a_4445_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_4436_ == 0 {
                    lean_ctor_set_tag(v___x_4435_, 1);
                    v___x_4438_ = v___x_4435_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4443_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4433_);
                    v___x_4438_ = v_reuseFailAlloc_4443_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4439_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4439_, 0, v___x_4438_);
                lean_ctor_set(v___x_4439_, 1, v_snd_4410_);
                if v_isShared_4432_ == 0 {
                    lean_ctor_set(v___x_4431_, 0, v___x_4439_);
                    v___x_4441_ = v___x_4431_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
                    v___x_4441_ = v_reuseFailAlloc_4442_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4441_;
            }
            9 => {
                if v_isShared_4450_ == 0 {
                    v___x_4452_ = v___x_4449_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
                    v___x_4452_ = v_reuseFailAlloc_4453_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4452_;
            }
            11 => {
                if v___y_4457_ == 0 {
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_snd_4410_);
                    v_a_4419_ = v___x_4455_;
                    state = 2;
                    continue;
                }
            }
            12 => {
                if v_isShared_4466_ == 0 {
                    v___x_4468_ = v___x_4465_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4469_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
                    v___x_4468_ = v_reuseFailAlloc_4469_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4468_;
            }
            14 => {
                if v_isShared_4474_ == 0 {
                    v___x_4476_ = v___x_4473_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
                    v___x_4476_ = v_reuseFailAlloc_4477_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4476_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_4481_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_4482_: *mut LeanObject = *_args.add(1);
    let mut v_as_4483_: *mut LeanObject = *_args.add(2);
    let mut v_sz_4484_: *mut LeanObject = *_args.add(3);
    let mut v_i_4485_: *mut LeanObject = *_args.add(4);
    let mut v_b_4486_: *mut LeanObject = *_args.add(5);
    let mut v___y_4487_: *mut LeanObject = *_args.add(6);
    let mut v___y_4488_: *mut LeanObject = *_args.add(7);
    let mut v___y_4489_: *mut LeanObject = *_args.add(8);
    let mut v___y_4490_: *mut LeanObject = *_args.add(9);
    let mut v___y_4491_: *mut LeanObject = *_args.add(10);
    let mut v___y_4492_: *mut LeanObject = *_args.add(11);
    let mut v___y_4493_: *mut LeanObject = *_args.add(12);
    let mut v___y_4494_: *mut LeanObject = *_args.add(13);
    let mut v___y_4495_: *mut LeanObject = *_args.add(14);
    let mut v___y_4496_: *mut LeanObject = *_args.add(15);
    let mut v___y_4497_: *mut LeanObject = *_args.add(16);
    let mut v___y_4498_: *mut LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4499_: u8 = 0;
    let mut v_sz_boxed_4500_: usize = 0;
    let mut v_i_boxed_4501_: usize = 0;
    let mut v_res_4502_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4499_ = (lean_unbox(v_isLower_4482_) as u8);
    v_sz_boxed_4500_ = lean_unbox_usize(v_sz_4484_);
    lean_dec(v_sz_4484_);
    v_i_boxed_4501_ = lean_unbox_usize(v_i_4485_);
    lean_dec(v_i_4485_);
    v_res_4502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_4481_, v_isLower_boxed_4499_, v_as_4483_, v_sz_boxed_4500_, v_i_boxed_4501_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
    lean_dec(v___y_4497_);
    lean_dec_ref(v___y_4496_);
    lean_dec(v___y_4495_);
    lean_dec_ref(v___y_4494_);
    lean_dec(v___y_4493_);
    lean_dec_ref(v___y_4492_);
    lean_dec(v___y_4491_);
    lean_dec_ref(v___y_4490_);
    lean_dec(v___y_4489_);
    lean_dec(v___y_4488_);
    lean_dec(v___y_4487_);
    lean_dec_ref(v_as_4483_);
    lean_dec(v_____s_4481_);
    return v_res_4502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(
    mut v_____s_4503_: *mut LeanObject,
    mut v_isLower_4504_: u8,
    mut v_as_4505_: *mut LeanObject,
    mut v_sz_4506_: usize,
    mut v_i_4507_: usize,
    mut v_b_4508_: *mut LeanObject,
    mut v___y_4509_: *mut LeanObject,
    mut v___y_4510_: *mut LeanObject,
    mut v___y_4511_: *mut LeanObject,
    mut v___y_4512_: *mut LeanObject,
    mut v___y_4513_: *mut LeanObject,
    mut v___y_4514_: *mut LeanObject,
    mut v___y_4515_: *mut LeanObject,
    mut v___y_4516_: *mut LeanObject,
    mut v___y_4517_: *mut LeanObject,
    mut v___y_4518_: *mut LeanObject,
    mut v___y_4519_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4521_: u8 = 0;
    let mut v___x_4522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v_a_4527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_4528_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4533_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: usize = 0;
    let mut v___x_4537_: usize = 0;
    let mut v___x_4538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4546_: u8 = 0;
    let mut v_a_4547_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v___x_4552_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_a_4559_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v_a_4561_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v___x_4566_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v___y_4570_: u8 = 0;
    let mut v_k_4571_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4581_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4582_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4583_: u8 = 0;
    let mut v_a_4584_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4591_: u8 = 0;
    let mut v_isSharedCheck_4592_: u8 = 0;
    let mut v_unused_4593_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4521_ = lean_usize_dec_lt(v_i_4507_, v_sz_4506_);
                if v___x_4521_ == 0 {
                    v___x_4522_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4522_, 0, v_b_4508_);
                    return v___x_4522_;
                } else {
                    v_snd_4523_ = lean_ctor_get(v_b_4508_, 1);
                    v_isSharedCheck_4592_ = (!lean_is_exclusive(v_b_4508_)) as u8;
                    if v_isSharedCheck_4592_ == 0 {
                        v_unused_4593_ = lean_ctor_get(v_b_4508_, 0);
                        lean_dec(v_unused_4593_);
                        v___x_4525_ = v_b_4508_;
                        v_isShared_4526_ = v_isSharedCheck_4592_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4523_);
                        lean_dec(v_b_4508_);
                        v___x_4525_ = lean_box(0);
                        v_isShared_4526_ = v_isSharedCheck_4592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4527_ = lean_array_uget_borrowed(v_as_4505_, v_i_4507_);
                v_p_4528_ = lean_ctor_get(v_a_4527_, 0);
                v___x_4529_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4528_, v_____s_4503_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                if lean_obj_tag(v___x_4529_) == 0 {
                    lean_dec_ref_known(v___x_4529_, 1);
                    v___x_4530_ = lean_box(0);
                    v___x_4531_ = lean_box(0);
                    if lean_obj_tag(v_p_4528_) == 1 {
                        v_k_4571_ = lean_ctor_get(v_p_4528_, 0);
                        v___x_4572_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
                        v___x_4573_ = lean_int_dec_lt(v_k_4571_, v___x_4572_);
                        if v_isLower_4504_ == 0 {
                            if v___x_4573_ == 0 {
                                v___y_4570_ = v___x_4521_;
                                state = 11;
                                continue;
                            } else {
                                state = 4;
                                continue;
                            }
                        } else {
                            v___y_4570_ = v___x_4573_;
                            state = 11;
                            continue;
                        }
                    } else {
                        lean_dec(v_snd_4523_);
                        v___x_4574_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4575_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4574_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                        if lean_obj_tag(v___x_4575_) == 0 {
                            lean_dec_ref_known(v___x_4575_, 1);
                            v_a_4533_ = v___x_4530_;
                            state = 2;
                            continue;
                        } else {
                            lean_del_object(v___x_4525_);
                            v_a_4576_ = lean_ctor_get(v___x_4575_, 0);
                            v_isSharedCheck_4583_ = (!lean_is_exclusive(v___x_4575_)) as u8;
                            if v_isSharedCheck_4583_ == 0 {
                                v___x_4578_ = v___x_4575_;
                                v_isShared_4579_ = v_isSharedCheck_4583_;
                                state = 12;
                                continue;
                            } else {
                                lean_inc(v_a_4576_);
                                lean_dec(v___x_4575_);
                                v___x_4578_ = lean_box(0);
                                v_isShared_4579_ = v_isSharedCheck_4583_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    lean_del_object(v___x_4525_);
                    lean_dec(v_snd_4523_);
                    v_a_4584_ = lean_ctor_get(v___x_4529_, 0);
                    v_isSharedCheck_4591_ = (!lean_is_exclusive(v___x_4529_)) as u8;
                    if v_isSharedCheck_4591_ == 0 {
                        v___x_4586_ = v___x_4529_;
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 14;
                        continue;
                    } else {
                        lean_inc(v_a_4584_);
                        lean_dec(v___x_4529_);
                        v___x_4586_ = lean_box(0);
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4526_ == 0 {
                    lean_ctor_set(v___x_4525_, 1, v_a_4533_);
                    lean_ctor_set(v___x_4525_, 0, v___x_4531_);
                    v___x_4535_ = v___x_4525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4531_);
                    lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_a_4533_);
                    v___x_4535_ = v_reuseFailAlloc_4539_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                v___x_4536_ = 1usize;
                v___x_4537_ = lean_usize_add(v_i_4507_, v___x_4536_);
                v___x_4538_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_4503_, v_isLower_4504_, v_as_4505_, v_sz_4506_, v___x_4537_, v___x_4535_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                return v___x_4538_;
            }
            4 => {
                v___x_4541_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4542_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4541_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                if lean_obj_tag(v___x_4542_) == 0 {
                    v_a_4543_ = lean_ctor_get(v___x_4542_, 0);
                    v_isSharedCheck_4560_ = (!lean_is_exclusive(v___x_4542_)) as u8;
                    if v_isSharedCheck_4560_ == 0 {
                        v___x_4545_ = v___x_4542_;
                        v_isShared_4546_ = v_isSharedCheck_4560_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_4543_);
                        lean_dec(v___x_4542_);
                        v___x_4545_ = lean_box(0);
                        v_isShared_4546_ = v_isSharedCheck_4560_;
                        state = 5;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4525_);
                    lean_dec(v_snd_4523_);
                    v_a_4561_ = lean_ctor_get(v___x_4542_, 0);
                    v_isSharedCheck_4568_ = (!lean_is_exclusive(v___x_4542_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4563_ = v___x_4542_;
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 9;
                        continue;
                    } else {
                        lean_inc(v_a_4561_);
                        lean_dec(v___x_4542_);
                        v___x_4563_ = lean_box(0);
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if lean_obj_tag(v_a_4543_) == 0 {
                    lean_del_object(v___x_4525_);
                    v_a_4547_ = lean_ctor_get(v_a_4543_, 0);
                    v_isSharedCheck_4558_ = (!lean_is_exclusive(v_a_4543_)) as u8;
                    if v_isSharedCheck_4558_ == 0 {
                        v___x_4549_ = v_a_4543_;
                        v_isShared_4550_ = v_isSharedCheck_4558_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4547_);
                        lean_dec(v_a_4543_);
                        v___x_4549_ = lean_box(0);
                        v_isShared_4550_ = v_isSharedCheck_4558_;
                        state = 6;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4545_);
                    lean_dec(v_snd_4523_);
                    v_a_4559_ = lean_ctor_get(v_a_4543_, 0);
                    lean_inc(v_a_4559_);
                    lean_dec_ref_known(v_a_4543_, 1);
                    v_a_4533_ = v_a_4559_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_4550_ == 0 {
                    lean_ctor_set_tag(v___x_4549_, 1);
                    v___x_4552_ = v___x_4549_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4547_);
                    v___x_4552_ = v_reuseFailAlloc_4557_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4553_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_4553_, 0, v___x_4552_);
                lean_ctor_set(v___x_4553_, 1, v_snd_4523_);
                if v_isShared_4546_ == 0 {
                    lean_ctor_set(v___x_4545_, 0, v___x_4553_);
                    v___x_4555_ = v___x_4545_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
                    v___x_4555_ = v_reuseFailAlloc_4556_;
                    state = 8;
                    continue;
                }
            }
            8 => {
                return v___x_4555_;
            }
            9 => {
                if v_isShared_4564_ == 0 {
                    v___x_4566_ = v___x_4563_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4567_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
                    v___x_4566_ = v_reuseFailAlloc_4567_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4566_;
            }
            11 => {
                if v___y_4570_ == 0 {
                    state = 4;
                    continue;
                } else {
                    lean_dec(v_snd_4523_);
                    v_a_4533_ = v___x_4530_;
                    state = 2;
                    continue;
                }
            }
            12 => {
                if v_isShared_4579_ == 0 {
                    v___x_4581_ = v___x_4578_;
                    state = 13;
                    continue;
                } else {
                    v_reuseFailAlloc_4582_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
                    v___x_4581_ = v_reuseFailAlloc_4582_;
                    state = 13;
                    continue;
                }
            }
            13 => {
                return v___x_4581_;
            }
            14 => {
                if v_isShared_4587_ == 0 {
                    v___x_4589_ = v___x_4586_;
                    state = 15;
                    continue;
                } else {
                    v_reuseFailAlloc_4590_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
                    v___x_4589_ = v_reuseFailAlloc_4590_;
                    state = 15;
                    continue;
                }
            }
            15 => {
                return v___x_4589_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_4594_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_4595_: *mut LeanObject = *_args.add(1);
    let mut v_as_4596_: *mut LeanObject = *_args.add(2);
    let mut v_sz_4597_: *mut LeanObject = *_args.add(3);
    let mut v_i_4598_: *mut LeanObject = *_args.add(4);
    let mut v_b_4599_: *mut LeanObject = *_args.add(5);
    let mut v___y_4600_: *mut LeanObject = *_args.add(6);
    let mut v___y_4601_: *mut LeanObject = *_args.add(7);
    let mut v___y_4602_: *mut LeanObject = *_args.add(8);
    let mut v___y_4603_: *mut LeanObject = *_args.add(9);
    let mut v___y_4604_: *mut LeanObject = *_args.add(10);
    let mut v___y_4605_: *mut LeanObject = *_args.add(11);
    let mut v___y_4606_: *mut LeanObject = *_args.add(12);
    let mut v___y_4607_: *mut LeanObject = *_args.add(13);
    let mut v___y_4608_: *mut LeanObject = *_args.add(14);
    let mut v___y_4609_: *mut LeanObject = *_args.add(15);
    let mut v___y_4610_: *mut LeanObject = *_args.add(16);
    let mut v___y_4611_: *mut LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4612_: u8 = 0;
    let mut v_sz_boxed_4613_: usize = 0;
    let mut v_i_boxed_4614_: usize = 0;
    let mut v_res_4615_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4612_ = (lean_unbox(v_isLower_4595_) as u8);
    v_sz_boxed_4613_ = lean_unbox_usize(v_sz_4597_);
    lean_dec(v_sz_4597_);
    v_i_boxed_4614_ = lean_unbox_usize(v_i_4598_);
    lean_dec(v_i_4598_);
    v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_4594_, v_isLower_boxed_4612_, v_as_4596_, v_sz_boxed_4613_, v_i_boxed_4614_, v_b_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
    lean_dec(v___y_4610_);
    lean_dec_ref(v___y_4609_);
    lean_dec(v___y_4608_);
    lean_dec_ref(v___y_4607_);
    lean_dec(v___y_4606_);
    lean_dec_ref(v___y_4605_);
    lean_dec(v___y_4604_);
    lean_dec_ref(v___y_4603_);
    lean_dec(v___y_4602_);
    lean_dec(v___y_4601_);
    lean_dec(v___y_4600_);
    lean_dec_ref(v_as_4596_);
    lean_dec(v_____s_4594_);
    return v_res_4615_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(
    mut v_____s_4616_: *mut LeanObject,
    mut v_isLower_4617_: u8,
    mut v_t_4618_: *mut LeanObject,
    mut v_init_4619_: *mut LeanObject,
    mut v___y_4620_: *mut LeanObject,
    mut v___y_4621_: *mut LeanObject,
    mut v___y_4622_: *mut LeanObject,
    mut v___y_4623_: *mut LeanObject,
    mut v___y_4624_: *mut LeanObject,
    mut v___y_4625_: *mut LeanObject,
    mut v___y_4626_: *mut LeanObject,
    mut v___y_4627_: *mut LeanObject,
    mut v___y_4628_: *mut LeanObject,
    mut v___y_4629_: *mut LeanObject,
    mut v___y_4630_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_4632_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_4633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v_a_4639_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4646_: usize = 0;
    let mut v___x_4647_: usize = 0;
    let mut v___x_4648_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4649_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v_fst_4653_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4654_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4657_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4658_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_a_4663_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4668_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v_isSharedCheck_4671_: u8 = 0;
    let mut v_a_4672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4632_ = lean_ctor_get(v_t_4618_, 0);
                v_tail_4633_ = lean_ctor_get(v_t_4618_, 1);
                v___x_4634_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4619_, v_____s_4616_, v_isLower_4617_, v_root_4632_, v_init_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                if lean_obj_tag(v___x_4634_) == 0 {
                    v_a_4635_ = lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4671_ = (!lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4671_ == 0 {
                        v___x_4637_ = v___x_4634_;
                        v_isShared_4638_ = v_isSharedCheck_4671_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_4635_);
                        lean_dec(v___x_4634_);
                        v___x_4637_ = lean_box(0);
                        v_isShared_4638_ = v_isSharedCheck_4671_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4672_ = lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4679_ = (!lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4679_ == 0 {
                        v___x_4674_ = v___x_4634_;
                        v_isShared_4675_ = v_isSharedCheck_4679_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_4672_);
                        lean_dec(v___x_4634_);
                        v___x_4674_ = lean_box(0);
                        v_isShared_4675_ = v_isSharedCheck_4679_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_4635_) == 0 {
                    v_a_4639_ = lean_ctor_get(v_a_4635_, 0);
                    lean_inc(v_a_4639_);
                    lean_dec_ref_known(v_a_4635_, 1);
                    if v_isShared_4638_ == 0 {
                        lean_ctor_set(v___x_4637_, 0, v_a_4639_);
                        v___x_4641_ = v___x_4637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4642_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4639_);
                        v___x_4641_ = v_reuseFailAlloc_4642_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4637_);
                    v_a_4643_ = lean_ctor_get(v_a_4635_, 0);
                    lean_inc(v_a_4643_);
                    lean_dec_ref_known(v_a_4635_, 1);
                    v___x_4644_ = lean_box(0);
                    v___x_4645_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4645_, 0, v___x_4644_);
                    lean_ctor_set(v___x_4645_, 1, v_a_4643_);
                    v_sz_4646_ = lean_array_size(v_tail_4633_);
                    v___x_4647_ = 0usize;
                    v___x_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_4616_, v_isLower_4617_, v_tail_4633_, v_sz_4646_, v___x_4647_, v___x_4645_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                    if lean_obj_tag(v___x_4648_) == 0 {
                        v_a_4649_ = lean_ctor_get(v___x_4648_, 0);
                        v_isSharedCheck_4662_ = (!lean_is_exclusive(v___x_4648_)) as u8;
                        if v_isSharedCheck_4662_ == 0 {
                            v___x_4651_ = v___x_4648_;
                            v_isShared_4652_ = v_isSharedCheck_4662_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_4649_);
                            lean_dec(v___x_4648_);
                            v___x_4651_ = lean_box(0);
                            v_isShared_4652_ = v_isSharedCheck_4662_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4663_ = lean_ctor_get(v___x_4648_, 0);
                        v_isSharedCheck_4670_ = (!lean_is_exclusive(v___x_4648_)) as u8;
                        if v_isSharedCheck_4670_ == 0 {
                            v___x_4665_ = v___x_4648_;
                            v_isShared_4666_ = v_isSharedCheck_4670_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4663_);
                            lean_dec(v___x_4648_);
                            v___x_4665_ = lean_box(0);
                            v_isShared_4666_ = v_isSharedCheck_4670_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_4641_;
            }
            3 => {
                v_fst_4653_ = lean_ctor_get(v_a_4649_, 0);
                if lean_obj_tag(v_fst_4653_) == 0 {
                    v_snd_4654_ = lean_ctor_get(v_a_4649_, 1);
                    lean_inc(v_snd_4654_);
                    lean_dec(v_a_4649_);
                    if v_isShared_4652_ == 0 {
                        lean_ctor_set(v___x_4651_, 0, v_snd_4654_);
                        v___x_4656_ = v___x_4651_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4657_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_snd_4654_);
                        v___x_4656_ = v_reuseFailAlloc_4657_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4653_);
                    lean_dec(v_a_4649_);
                    v_val_4658_ = lean_ctor_get(v_fst_4653_, 0);
                    lean_inc(v_val_4658_);
                    lean_dec_ref_known(v_fst_4653_, 1);
                    if v_isShared_4652_ == 0 {
                        lean_ctor_set(v___x_4651_, 0, v_val_4658_);
                        v___x_4660_ = v___x_4651_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4661_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_val_4658_);
                        v___x_4660_ = v_reuseFailAlloc_4661_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_4656_;
            }
            5 => {
                return v___x_4660_;
            }
            6 => {
                if v_isShared_4666_ == 0 {
                    v___x_4668_ = v___x_4665_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4669_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
                    v___x_4668_ = v_reuseFailAlloc_4669_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4668_;
            }
            8 => {
                if v_isShared_4675_ == 0 {
                    v___x_4677_ = v___x_4674_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_4678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
                    v___x_4677_ = v_reuseFailAlloc_4678_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_4677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1___boxed(
    mut v_____s_4680_: *mut LeanObject,
    mut v_isLower_4681_: *mut LeanObject,
    mut v_t_4682_: *mut LeanObject,
    mut v_init_4683_: *mut LeanObject,
    mut v___y_4684_: *mut LeanObject,
    mut v___y_4685_: *mut LeanObject,
    mut v___y_4686_: *mut LeanObject,
    mut v___y_4687_: *mut LeanObject,
    mut v___y_4688_: *mut LeanObject,
    mut v___y_4689_: *mut LeanObject,
    mut v___y_4690_: *mut LeanObject,
    mut v___y_4691_: *mut LeanObject,
    mut v___y_4692_: *mut LeanObject,
    mut v___y_4693_: *mut LeanObject,
    mut v___y_4694_: *mut LeanObject,
    mut v___y_4695_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_4696_: u8 = 0;
    let mut v_res_4697_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4696_ = (lean_unbox(v_isLower_4681_) as u8);
    v_res_4697_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_____s_4680_, v_isLower_boxed_4696_, v_t_4682_, v_init_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
    lean_dec(v___y_4694_);
    lean_dec_ref(v___y_4693_);
    lean_dec(v___y_4692_);
    lean_dec_ref(v___y_4691_);
    lean_dec(v___y_4690_);
    lean_dec_ref(v___y_4689_);
    lean_dec(v___y_4688_);
    lean_dec_ref(v___y_4687_);
    lean_dec(v___y_4686_);
    lean_dec(v___y_4685_);
    lean_dec(v___y_4684_);
    lean_dec_ref(v_t_4682_);
    lean_dec(v_____s_4680_);
    return v_res_4697_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(
    mut v_isLower_4698_: u8,
    mut v_as_4699_: *mut LeanObject,
    mut v_sz_4700_: usize,
    mut v_i_4701_: usize,
    mut v_b_4702_: *mut LeanObject,
    mut v___y_4703_: *mut LeanObject,
    mut v___y_4704_: *mut LeanObject,
    mut v___y_4705_: *mut LeanObject,
    mut v___y_4706_: *mut LeanObject,
    mut v___y_4707_: *mut LeanObject,
    mut v___y_4708_: *mut LeanObject,
    mut v___y_4709_: *mut LeanObject,
    mut v___y_4710_: *mut LeanObject,
    mut v___y_4711_: *mut LeanObject,
    mut v___y_4712_: *mut LeanObject,
    mut v___y_4713_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4715_: u8 = 0;
    let mut v___x_4716_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4717_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v_a_4721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: usize = 0;
    let mut v___x_4730_: usize = 0;
    let mut v_reuseFailAlloc_4732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4738_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_unused_4742_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4715_ = lean_usize_dec_lt(v_i_4701_, v_sz_4700_);
                if v___x_4715_ == 0 {
                    v___x_4716_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4716_, 0, v_b_4702_);
                    return v___x_4716_;
                } else {
                    v_snd_4717_ = lean_ctor_get(v_b_4702_, 1);
                    v_isSharedCheck_4741_ = (!lean_is_exclusive(v_b_4702_)) as u8;
                    if v_isSharedCheck_4741_ == 0 {
                        v_unused_4742_ = lean_ctor_get(v_b_4702_, 0);
                        lean_dec(v_unused_4742_);
                        v___x_4719_ = v_b_4702_;
                        v_isShared_4720_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4717_);
                        lean_dec(v_b_4702_);
                        v___x_4719_ = lean_box(0);
                        v_isShared_4720_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4721_ = lean_array_uget_borrowed(v_as_4699_, v_i_4701_);
                v___x_4722_ = lean_box(0);
                v___x_4723_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_4717_, v_isLower_4698_, v_a_4721_, v___x_4722_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
                if lean_obj_tag(v___x_4723_) == 0 {
                    lean_dec_ref_known(v___x_4723_, 1);
                    v___x_4724_ = lean_box(0);
                    v___x_4725_ = lean_unsigned_to_nat(1);
                    v___x_4726_ = lean_nat_add(v_snd_4717_, v___x_4725_);
                    lean_dec(v_snd_4717_);
                    if v_isShared_4720_ == 0 {
                        lean_ctor_set(v___x_4719_, 1, v___x_4726_);
                        lean_ctor_set(v___x_4719_, 0, v___x_4724_);
                        v___x_4728_ = v___x_4719_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4724_);
                        lean_ctor_set(v_reuseFailAlloc_4732_, 1, v___x_4726_);
                        v___x_4728_ = v_reuseFailAlloc_4732_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4719_);
                    lean_dec(v_snd_4717_);
                    v_a_4733_ = lean_ctor_get(v___x_4723_, 0);
                    v_isSharedCheck_4740_ = (!lean_is_exclusive(v___x_4723_)) as u8;
                    if v_isSharedCheck_4740_ == 0 {
                        v___x_4735_ = v___x_4723_;
                        v_isShared_4736_ = v_isSharedCheck_4740_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4733_);
                        lean_dec(v___x_4723_);
                        v___x_4735_ = lean_box(0);
                        v_isShared_4736_ = v_isSharedCheck_4740_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4729_ = 1usize;
                v___x_4730_ = lean_usize_add(v_i_4701_, v___x_4729_);
                v_i_4701_ = v___x_4730_;
                v_b_4702_ = v___x_4728_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_4736_ == 0 {
                    v___x_4738_ = v___x_4735_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4739_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
                    v___x_4738_ = v_reuseFailAlloc_4739_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4738_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_4743_: *mut LeanObject = *_args.add(0);
    let mut v_as_4744_: *mut LeanObject = *_args.add(1);
    let mut v_sz_4745_: *mut LeanObject = *_args.add(2);
    let mut v_i_4746_: *mut LeanObject = *_args.add(3);
    let mut v_b_4747_: *mut LeanObject = *_args.add(4);
    let mut v___y_4748_: *mut LeanObject = *_args.add(5);
    let mut v___y_4749_: *mut LeanObject = *_args.add(6);
    let mut v___y_4750_: *mut LeanObject = *_args.add(7);
    let mut v___y_4751_: *mut LeanObject = *_args.add(8);
    let mut v___y_4752_: *mut LeanObject = *_args.add(9);
    let mut v___y_4753_: *mut LeanObject = *_args.add(10);
    let mut v___y_4754_: *mut LeanObject = *_args.add(11);
    let mut v___y_4755_: *mut LeanObject = *_args.add(12);
    let mut v___y_4756_: *mut LeanObject = *_args.add(13);
    let mut v___y_4757_: *mut LeanObject = *_args.add(14);
    let mut v___y_4758_: *mut LeanObject = *_args.add(15);
    let mut v___y_4759_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4760_: u8 = 0;
    let mut v_sz_boxed_4761_: usize = 0;
    let mut v_i_boxed_4762_: usize = 0;
    let mut v_res_4763_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4760_ = (lean_unbox(v_isLower_4743_) as u8);
    v_sz_boxed_4761_ = lean_unbox_usize(v_sz_4745_);
    lean_dec(v_sz_4745_);
    v_i_boxed_4762_ = lean_unbox_usize(v_i_4746_);
    lean_dec(v_i_4746_);
    v_res_4763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_4760_, v_as_4744_, v_sz_boxed_4761_, v_i_boxed_4762_, v_b_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_);
    lean_dec(v___y_4758_);
    lean_dec_ref(v___y_4757_);
    lean_dec(v___y_4756_);
    lean_dec_ref(v___y_4755_);
    lean_dec(v___y_4754_);
    lean_dec_ref(v___y_4753_);
    lean_dec(v___y_4752_);
    lean_dec_ref(v___y_4751_);
    lean_dec(v___y_4750_);
    lean_dec(v___y_4749_);
    lean_dec(v___y_4748_);
    lean_dec_ref(v_as_4744_);
    return v_res_4763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(
    mut v_isLower_4764_: u8,
    mut v_as_4765_: *mut LeanObject,
    mut v_sz_4766_: usize,
    mut v_i_4767_: usize,
    mut v_b_4768_: *mut LeanObject,
    mut v___y_4769_: *mut LeanObject,
    mut v___y_4770_: *mut LeanObject,
    mut v___y_4771_: *mut LeanObject,
    mut v___y_4772_: *mut LeanObject,
    mut v___y_4773_: *mut LeanObject,
    mut v___y_4774_: *mut LeanObject,
    mut v___y_4775_: *mut LeanObject,
    mut v___y_4776_: *mut LeanObject,
    mut v___y_4777_: *mut LeanObject,
    mut v___y_4778_: *mut LeanObject,
    mut v___y_4779_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4783_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4786_: u8 = 0;
    let mut v_a_4787_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: usize = 0;
    let mut v___x_4796_: usize = 0;
    let mut v___x_4797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4802_: u8 = 0;
    let mut v___x_4804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v_unused_4808_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4781_ = lean_usize_dec_lt(v_i_4767_, v_sz_4766_);
                if v___x_4781_ == 0 {
                    v___x_4782_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4782_, 0, v_b_4768_);
                    return v___x_4782_;
                } else {
                    v_snd_4783_ = lean_ctor_get(v_b_4768_, 1);
                    v_isSharedCheck_4807_ = (!lean_is_exclusive(v_b_4768_)) as u8;
                    if v_isSharedCheck_4807_ == 0 {
                        v_unused_4808_ = lean_ctor_get(v_b_4768_, 0);
                        lean_dec(v_unused_4808_);
                        v___x_4785_ = v_b_4768_;
                        v_isShared_4786_ = v_isSharedCheck_4807_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4783_);
                        lean_dec(v_b_4768_);
                        v___x_4785_ = lean_box(0);
                        v_isShared_4786_ = v_isSharedCheck_4807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4787_ = lean_array_uget_borrowed(v_as_4765_, v_i_4767_);
                v___x_4788_ = lean_box(0);
                v___x_4789_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_4783_, v_isLower_4764_, v_a_4787_, v___x_4788_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
                if lean_obj_tag(v___x_4789_) == 0 {
                    lean_dec_ref_known(v___x_4789_, 1);
                    v___x_4790_ = lean_box(0);
                    v___x_4791_ = lean_unsigned_to_nat(1);
                    v___x_4792_ = lean_nat_add(v_snd_4783_, v___x_4791_);
                    lean_dec(v_snd_4783_);
                    if v_isShared_4786_ == 0 {
                        lean_ctor_set(v___x_4785_, 1, v___x_4792_);
                        lean_ctor_set(v___x_4785_, 0, v___x_4790_);
                        v___x_4794_ = v___x_4785_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4798_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4790_);
                        lean_ctor_set(v_reuseFailAlloc_4798_, 1, v___x_4792_);
                        v___x_4794_ = v_reuseFailAlloc_4798_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4785_);
                    lean_dec(v_snd_4783_);
                    v_a_4799_ = lean_ctor_get(v___x_4789_, 0);
                    v_isSharedCheck_4806_ = (!lean_is_exclusive(v___x_4789_)) as u8;
                    if v_isSharedCheck_4806_ == 0 {
                        v___x_4801_ = v___x_4789_;
                        v_isShared_4802_ = v_isSharedCheck_4806_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_4799_);
                        lean_dec(v___x_4789_);
                        v___x_4801_ = lean_box(0);
                        v_isShared_4802_ = v_isSharedCheck_4806_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_4795_ = 1usize;
                v___x_4796_ = lean_usize_add(v_i_4767_, v___x_4795_);
                v___x_4797_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_4764_, v_as_4765_, v_sz_4766_, v___x_4796_, v___x_4794_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
                return v___x_4797_;
            }
            3 => {
                if v_isShared_4802_ == 0 {
                    v___x_4804_ = v___x_4801_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4805_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
                    v___x_4804_ = v_reuseFailAlloc_4805_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4804_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_4809_: *mut LeanObject = *_args.add(0);
    let mut v_as_4810_: *mut LeanObject = *_args.add(1);
    let mut v_sz_4811_: *mut LeanObject = *_args.add(2);
    let mut v_i_4812_: *mut LeanObject = *_args.add(3);
    let mut v_b_4813_: *mut LeanObject = *_args.add(4);
    let mut v___y_4814_: *mut LeanObject = *_args.add(5);
    let mut v___y_4815_: *mut LeanObject = *_args.add(6);
    let mut v___y_4816_: *mut LeanObject = *_args.add(7);
    let mut v___y_4817_: *mut LeanObject = *_args.add(8);
    let mut v___y_4818_: *mut LeanObject = *_args.add(9);
    let mut v___y_4819_: *mut LeanObject = *_args.add(10);
    let mut v___y_4820_: *mut LeanObject = *_args.add(11);
    let mut v___y_4821_: *mut LeanObject = *_args.add(12);
    let mut v___y_4822_: *mut LeanObject = *_args.add(13);
    let mut v___y_4823_: *mut LeanObject = *_args.add(14);
    let mut v___y_4824_: *mut LeanObject = *_args.add(15);
    let mut v___y_4825_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4826_: u8 = 0;
    let mut v_sz_boxed_4827_: usize = 0;
    let mut v_i_boxed_4828_: usize = 0;
    let mut v_res_4829_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4826_ = (lean_unbox(v_isLower_4809_) as u8);
    v_sz_boxed_4827_ = lean_unbox_usize(v_sz_4811_);
    lean_dec(v_sz_4811_);
    v_i_boxed_4828_ = lean_unbox_usize(v_i_4812_);
    lean_dec(v_i_4812_);
    v_res_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_4826_, v_as_4810_, v_sz_boxed_4827_, v_i_boxed_4828_, v_b_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
    lean_dec(v___y_4824_);
    lean_dec_ref(v___y_4823_);
    lean_dec(v___y_4822_);
    lean_dec_ref(v___y_4821_);
    lean_dec(v___y_4820_);
    lean_dec_ref(v___y_4819_);
    lean_dec(v___y_4818_);
    lean_dec_ref(v___y_4817_);
    lean_dec(v___y_4816_);
    lean_dec(v___y_4815_);
    lean_dec(v___y_4814_);
    lean_dec_ref(v_as_4810_);
    return v_res_4829_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(
    mut v_init_4830_: *mut LeanObject,
    mut v_isLower_4831_: u8,
    mut v_n_4832_: *mut LeanObject,
    mut v_b_4833_: *mut LeanObject,
    mut v___y_4834_: *mut LeanObject,
    mut v___y_4835_: *mut LeanObject,
    mut v___y_4836_: *mut LeanObject,
    mut v___y_4837_: *mut LeanObject,
    mut v___y_4838_: *mut LeanObject,
    mut v___y_4839_: *mut LeanObject,
    mut v___y_4840_: *mut LeanObject,
    mut v___y_4841_: *mut LeanObject,
    mut v___y_4842_: *mut LeanObject,
    mut v___y_4843_: *mut LeanObject,
    mut v___y_4844_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_4846_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4849_: usize = 0;
    let mut v___x_4850_: usize = 0;
    let mut v___x_4851_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v_fst_4856_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4865_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4866_: u8 = 0;
    let mut v_a_4867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v___x_4872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4874_: u8 = 0;
    let mut v_vs_4875_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_4878_: usize = 0;
    let mut v___x_4879_: usize = 0;
    let mut v___x_4880_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v_fst_4885_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4886_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_4891_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v_a_4896_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v___x_4901_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_4832_) == 0 {
                    v_cs_4846_ = lean_ctor_get(v_n_4832_, 0);
                    v___x_4847_ = lean_box(0);
                    v___x_4848_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4848_, 0, v___x_4847_);
                    lean_ctor_set(v___x_4848_, 1, v_b_4833_);
                    v_sz_4849_ = lean_array_size(v_cs_4846_);
                    v___x_4850_ = 0usize;
                    v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_4830_, v_isLower_4831_, v_cs_4846_, v_sz_4849_, v___x_4850_, v___x_4848_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
                    if lean_obj_tag(v___x_4851_) == 0 {
                        v_a_4852_ = lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4866_ = (!lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4866_ == 0 {
                            v___x_4854_ = v___x_4851_;
                            v_isShared_4855_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_4852_);
                            lean_dec(v___x_4851_);
                            v___x_4854_ = lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4867_ = lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4874_ = (!lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4874_ == 0 {
                            v___x_4869_ = v___x_4851_;
                            v_isShared_4870_ = v_isSharedCheck_4874_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_4867_);
                            lean_dec(v___x_4851_);
                            v___x_4869_ = lean_box(0);
                            v_isShared_4870_ = v_isSharedCheck_4874_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4875_ = lean_ctor_get(v_n_4832_, 0);
                    v___x_4876_ = lean_box(0);
                    v___x_4877_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_4877_, 0, v___x_4876_);
                    lean_ctor_set(v___x_4877_, 1, v_b_4833_);
                    v_sz_4878_ = lean_array_size(v_vs_4875_);
                    v___x_4879_ = 0usize;
                    v___x_4880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_4831_, v_vs_4875_, v_sz_4878_, v___x_4879_, v___x_4877_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
                    if lean_obj_tag(v___x_4880_) == 0 {
                        v_a_4881_ = lean_ctor_get(v___x_4880_, 0);
                        v_isSharedCheck_4895_ = (!lean_is_exclusive(v___x_4880_)) as u8;
                        if v_isSharedCheck_4895_ == 0 {
                            v___x_4883_ = v___x_4880_;
                            v_isShared_4884_ = v_isSharedCheck_4895_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_4881_);
                            lean_dec(v___x_4880_);
                            v___x_4883_ = lean_box(0);
                            v_isShared_4884_ = v_isSharedCheck_4895_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4896_ = lean_ctor_get(v___x_4880_, 0);
                        v_isSharedCheck_4903_ = (!lean_is_exclusive(v___x_4880_)) as u8;
                        if v_isSharedCheck_4903_ == 0 {
                            v___x_4898_ = v___x_4880_;
                            v_isShared_4899_ = v_isSharedCheck_4903_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_4896_);
                            lean_dec(v___x_4880_);
                            v___x_4898_ = lean_box(0);
                            v_isShared_4899_ = v_isSharedCheck_4903_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4856_ = lean_ctor_get(v_a_4852_, 0);
                if lean_obj_tag(v_fst_4856_) == 0 {
                    v_snd_4857_ = lean_ctor_get(v_a_4852_, 1);
                    lean_inc(v_snd_4857_);
                    lean_dec(v_a_4852_);
                    v___x_4858_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4858_, 0, v_snd_4857_);
                    if v_isShared_4855_ == 0 {
                        lean_ctor_set(v___x_4854_, 0, v___x_4858_);
                        v___x_4860_ = v___x_4854_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4861_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
                        v___x_4860_ = v_reuseFailAlloc_4861_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4856_);
                    lean_dec(v_a_4852_);
                    v_val_4862_ = lean_ctor_get(v_fst_4856_, 0);
                    lean_inc(v_val_4862_);
                    lean_dec_ref_known(v_fst_4856_, 1);
                    if v_isShared_4855_ == 0 {
                        lean_ctor_set(v___x_4854_, 0, v_val_4862_);
                        v___x_4864_ = v___x_4854_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4865_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_val_4862_);
                        v___x_4864_ = v_reuseFailAlloc_4865_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_4860_;
            }
            3 => {
                return v___x_4864_;
            }
            4 => {
                if v_isShared_4870_ == 0 {
                    v___x_4872_ = v___x_4869_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_4873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
                    v___x_4872_ = v_reuseFailAlloc_4873_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4872_;
            }
            6 => {
                v_fst_4885_ = lean_ctor_get(v_a_4881_, 0);
                if lean_obj_tag(v_fst_4885_) == 0 {
                    v_snd_4886_ = lean_ctor_get(v_a_4881_, 1);
                    lean_inc(v_snd_4886_);
                    lean_dec(v_a_4881_);
                    v___x_4887_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4887_, 0, v_snd_4886_);
                    if v_isShared_4884_ == 0 {
                        lean_ctor_set(v___x_4883_, 0, v___x_4887_);
                        v___x_4889_ = v___x_4883_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
                        v___x_4889_ = v_reuseFailAlloc_4890_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_4885_);
                    lean_dec(v_a_4881_);
                    v_val_4891_ = lean_ctor_get(v_fst_4885_, 0);
                    lean_inc(v_val_4891_);
                    lean_dec_ref_known(v_fst_4885_, 1);
                    if v_isShared_4884_ == 0 {
                        lean_ctor_set(v___x_4883_, 0, v_val_4891_);
                        v___x_4893_ = v___x_4883_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4894_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_val_4891_);
                        v___x_4893_ = v_reuseFailAlloc_4894_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_4889_;
            }
            8 => {
                return v___x_4893_;
            }
            9 => {
                if v_isShared_4899_ == 0 {
                    v___x_4901_ = v___x_4898_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_4902_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
                    v___x_4901_ = v_reuseFailAlloc_4902_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_4901_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(
    mut v_init_4904_: *mut LeanObject,
    mut v_isLower_4905_: u8,
    mut v_as_4906_: *mut LeanObject,
    mut v_sz_4907_: usize,
    mut v_i_4908_: usize,
    mut v_b_4909_: *mut LeanObject,
    mut v___y_4910_: *mut LeanObject,
    mut v___y_4911_: *mut LeanObject,
    mut v___y_4912_: *mut LeanObject,
    mut v___y_4913_: *mut LeanObject,
    mut v___y_4914_: *mut LeanObject,
    mut v___y_4915_: *mut LeanObject,
    mut v___y_4916_: *mut LeanObject,
    mut v___y_4917_: *mut LeanObject,
    mut v___y_4918_: *mut LeanObject,
    mut v___y_4919_: *mut LeanObject,
    mut v___y_4920_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_4922_: u8 = 0;
    let mut v___x_4923_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_4924_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v_a_4928_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v___x_4934_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4939_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4940_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: usize = 0;
    let mut v___x_4946_: usize = 0;
    let mut v_reuseFailAlloc_4948_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_a_4950_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut v_isSharedCheck_4958_: u8 = 0;
    let mut v_unused_4959_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4922_ = lean_usize_dec_lt(v_i_4908_, v_sz_4907_);
                if v___x_4922_ == 0 {
                    v___x_4923_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_4923_, 0, v_b_4909_);
                    return v___x_4923_;
                } else {
                    v_snd_4924_ = lean_ctor_get(v_b_4909_, 1);
                    v_isSharedCheck_4958_ = (!lean_is_exclusive(v_b_4909_)) as u8;
                    if v_isSharedCheck_4958_ == 0 {
                        v_unused_4959_ = lean_ctor_get(v_b_4909_, 0);
                        lean_dec(v_unused_4959_);
                        v___x_4926_ = v_b_4909_;
                        v_isShared_4927_ = v_isSharedCheck_4958_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_4924_);
                        lean_dec(v_b_4909_);
                        v___x_4926_ = lean_box(0);
                        v_isShared_4927_ = v_isSharedCheck_4958_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4928_ = lean_array_uget_borrowed(v_as_4906_, v_i_4908_);
                lean_inc(v_snd_4924_);
                v___x_4929_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_4904_, v_isLower_4905_, v_a_4928_, v_snd_4924_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
                if lean_obj_tag(v___x_4929_) == 0 {
                    v_a_4930_ = lean_ctor_get(v___x_4929_, 0);
                    v_isSharedCheck_4949_ = (!lean_is_exclusive(v___x_4929_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4932_ = v___x_4929_;
                        v_isShared_4933_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_4930_);
                        lean_dec(v___x_4929_);
                        v___x_4932_ = lean_box(0);
                        v_isShared_4933_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4926_);
                    lean_dec(v_snd_4924_);
                    v_a_4950_ = lean_ctor_get(v___x_4929_, 0);
                    v_isSharedCheck_4957_ = (!lean_is_exclusive(v___x_4929_)) as u8;
                    if v_isSharedCheck_4957_ == 0 {
                        v___x_4952_ = v___x_4929_;
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_4950_);
                        lean_dec(v___x_4929_);
                        v___x_4952_ = lean_box(0);
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_4930_) == 0 {
                    v___x_4934_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_4934_, 0, v_a_4930_);
                    if v_isShared_4927_ == 0 {
                        lean_ctor_set(v___x_4926_, 0, v___x_4934_);
                        v___x_4936_ = v___x_4926_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4934_);
                        lean_ctor_set(v_reuseFailAlloc_4940_, 1, v_snd_4924_);
                        v___x_4936_ = v_reuseFailAlloc_4940_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_4932_);
                    lean_dec(v_snd_4924_);
                    v_a_4941_ = lean_ctor_get(v_a_4930_, 0);
                    lean_inc(v_a_4941_);
                    lean_dec_ref_known(v_a_4930_, 1);
                    v___x_4942_ = lean_box(0);
                    if v_isShared_4927_ == 0 {
                        lean_ctor_set(v___x_4926_, 1, v_a_4941_);
                        lean_ctor_set(v___x_4926_, 0, v___x_4942_);
                        v___x_4944_ = v___x_4926_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4948_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4942_);
                        lean_ctor_set(v_reuseFailAlloc_4948_, 1, v_a_4941_);
                        v___x_4944_ = v_reuseFailAlloc_4948_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4933_ == 0 {
                    lean_ctor_set(v___x_4932_, 0, v___x_4936_);
                    v___x_4938_ = v___x_4932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4936_);
                    v___x_4938_ = v_reuseFailAlloc_4939_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_4938_;
            }
            5 => {
                v___x_4945_ = 1usize;
                v___x_4946_ = lean_usize_add(v_i_4908_, v___x_4945_);
                v_i_4908_ = v___x_4946_;
                v_b_4909_ = v___x_4944_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_4953_ == 0 {
                    v___x_4955_ = v___x_4952_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4956_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
                    v___x_4955_ = v_reuseFailAlloc_4956_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_4955_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_4960_: *mut LeanObject = *_args.add(0);
    let mut v_isLower_4961_: *mut LeanObject = *_args.add(1);
    let mut v_as_4962_: *mut LeanObject = *_args.add(2);
    let mut v_sz_4963_: *mut LeanObject = *_args.add(3);
    let mut v_i_4964_: *mut LeanObject = *_args.add(4);
    let mut v_b_4965_: *mut LeanObject = *_args.add(5);
    let mut v___y_4966_: *mut LeanObject = *_args.add(6);
    let mut v___y_4967_: *mut LeanObject = *_args.add(7);
    let mut v___y_4968_: *mut LeanObject = *_args.add(8);
    let mut v___y_4969_: *mut LeanObject = *_args.add(9);
    let mut v___y_4970_: *mut LeanObject = *_args.add(10);
    let mut v___y_4971_: *mut LeanObject = *_args.add(11);
    let mut v___y_4972_: *mut LeanObject = *_args.add(12);
    let mut v___y_4973_: *mut LeanObject = *_args.add(13);
    let mut v___y_4974_: *mut LeanObject = *_args.add(14);
    let mut v___y_4975_: *mut LeanObject = *_args.add(15);
    let mut v___y_4976_: *mut LeanObject = *_args.add(16);
    let mut v___y_4977_: *mut LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4978_: u8 = 0;
    let mut v_sz_boxed_4979_: usize = 0;
    let mut v_i_boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4978_ = (lean_unbox(v_isLower_4961_) as u8);
    v_sz_boxed_4979_ = lean_unbox_usize(v_sz_4963_);
    lean_dec(v_sz_4963_);
    v_i_boxed_4980_ = lean_unbox_usize(v_i_4964_);
    lean_dec(v_i_4964_);
    v_res_4981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_4960_, v_isLower_boxed_4978_, v_as_4962_, v_sz_boxed_4979_, v_i_boxed_4980_, v_b_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
    lean_dec(v___y_4976_);
    lean_dec_ref(v___y_4975_);
    lean_dec(v___y_4974_);
    lean_dec_ref(v___y_4973_);
    lean_dec(v___y_4972_);
    lean_dec_ref(v___y_4971_);
    lean_dec(v___y_4970_);
    lean_dec_ref(v___y_4969_);
    lean_dec(v___y_4968_);
    lean_dec(v___y_4967_);
    lean_dec(v___y_4966_);
    lean_dec_ref(v_as_4962_);
    lean_dec(v_init_4960_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4___boxed(
    mut v_init_4982_: *mut LeanObject,
    mut v_isLower_4983_: *mut LeanObject,
    mut v_n_4984_: *mut LeanObject,
    mut v_b_4985_: *mut LeanObject,
    mut v___y_4986_: *mut LeanObject,
    mut v___y_4987_: *mut LeanObject,
    mut v___y_4988_: *mut LeanObject,
    mut v___y_4989_: *mut LeanObject,
    mut v___y_4990_: *mut LeanObject,
    mut v___y_4991_: *mut LeanObject,
    mut v___y_4992_: *mut LeanObject,
    mut v___y_4993_: *mut LeanObject,
    mut v___y_4994_: *mut LeanObject,
    mut v___y_4995_: *mut LeanObject,
    mut v___y_4996_: *mut LeanObject,
    mut v___y_4997_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_4998_: u8 = 0;
    let mut v_res_4999_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4998_ = (lean_unbox(v_isLower_4983_) as u8);
    v_res_4999_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_4982_, v_isLower_boxed_4998_, v_n_4984_, v_b_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
    lean_dec(v___y_4996_);
    lean_dec_ref(v___y_4995_);
    lean_dec(v___y_4994_);
    lean_dec_ref(v___y_4993_);
    lean_dec(v___y_4992_);
    lean_dec_ref(v___y_4991_);
    lean_dec(v___y_4990_);
    lean_dec_ref(v___y_4989_);
    lean_dec(v___y_4988_);
    lean_dec(v___y_4987_);
    lean_dec(v___y_4986_);
    lean_dec_ref(v_n_4984_);
    lean_dec(v_init_4982_);
    return v_res_4999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(
    mut v_isLower_5000_: u8,
    mut v_as_5001_: *mut LeanObject,
    mut v_sz_5002_: usize,
    mut v_i_5003_: usize,
    mut v_b_5004_: *mut LeanObject,
    mut v___y_5005_: *mut LeanObject,
    mut v___y_5006_: *mut LeanObject,
    mut v___y_5007_: *mut LeanObject,
    mut v___y_5008_: *mut LeanObject,
    mut v___y_5009_: *mut LeanObject,
    mut v___y_5010_: *mut LeanObject,
    mut v___y_5011_: *mut LeanObject,
    mut v___y_5012_: *mut LeanObject,
    mut v___y_5013_: *mut LeanObject,
    mut v___y_5014_: *mut LeanObject,
    mut v___y_5015_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5019_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5022_: u8 = 0;
    let mut v_a_5023_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: usize = 0;
    let mut v_reuseFailAlloc_5034_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5035_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___x_5040_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5041_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5042_: u8 = 0;
    let mut v_isSharedCheck_5043_: u8 = 0;
    let mut v_unused_5044_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5017_ = lean_usize_dec_lt(v_i_5003_, v_sz_5002_);
                if v___x_5017_ == 0 {
                    v___x_5018_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5018_, 0, v_b_5004_);
                    return v___x_5018_;
                } else {
                    v_snd_5019_ = lean_ctor_get(v_b_5004_, 1);
                    v_isSharedCheck_5043_ = (!lean_is_exclusive(v_b_5004_)) as u8;
                    if v_isSharedCheck_5043_ == 0 {
                        v_unused_5044_ = lean_ctor_get(v_b_5004_, 0);
                        lean_dec(v_unused_5044_);
                        v___x_5021_ = v_b_5004_;
                        v_isShared_5022_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5019_);
                        lean_dec(v_b_5004_);
                        v___x_5021_ = lean_box(0);
                        v_isShared_5022_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5023_ = lean_array_uget_borrowed(v_as_5001_, v_i_5003_);
                v___x_5024_ = lean_box(0);
                v___x_5025_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_5019_, v_isLower_5000_, v_a_5023_, v___x_5024_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
                if lean_obj_tag(v___x_5025_) == 0 {
                    lean_dec_ref_known(v___x_5025_, 1);
                    v___x_5026_ = lean_box(0);
                    v___x_5027_ = lean_unsigned_to_nat(1);
                    v___x_5028_ = lean_nat_add(v_snd_5019_, v___x_5027_);
                    lean_dec(v_snd_5019_);
                    if v_isShared_5022_ == 0 {
                        lean_ctor_set(v___x_5021_, 1, v___x_5028_);
                        lean_ctor_set(v___x_5021_, 0, v___x_5026_);
                        v___x_5030_ = v___x_5021_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5034_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5026_);
                        lean_ctor_set(v_reuseFailAlloc_5034_, 1, v___x_5028_);
                        v___x_5030_ = v_reuseFailAlloc_5034_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5021_);
                    lean_dec(v_snd_5019_);
                    v_a_5035_ = lean_ctor_get(v___x_5025_, 0);
                    v_isSharedCheck_5042_ = (!lean_is_exclusive(v___x_5025_)) as u8;
                    if v_isSharedCheck_5042_ == 0 {
                        v___x_5037_ = v___x_5025_;
                        v_isShared_5038_ = v_isSharedCheck_5042_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5035_);
                        lean_dec(v___x_5025_);
                        v___x_5037_ = lean_box(0);
                        v_isShared_5038_ = v_isSharedCheck_5042_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5031_ = 1usize;
                v___x_5032_ = lean_usize_add(v_i_5003_, v___x_5031_);
                v_i_5003_ = v___x_5032_;
                v_b_5004_ = v___x_5030_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5038_ == 0 {
                    v___x_5040_ = v___x_5037_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5041_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
                    v___x_5040_ = v_reuseFailAlloc_5041_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5040_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_5045_: *mut LeanObject = *_args.add(0);
    let mut v_as_5046_: *mut LeanObject = *_args.add(1);
    let mut v_sz_5047_: *mut LeanObject = *_args.add(2);
    let mut v_i_5048_: *mut LeanObject = *_args.add(3);
    let mut v_b_5049_: *mut LeanObject = *_args.add(4);
    let mut v___y_5050_: *mut LeanObject = *_args.add(5);
    let mut v___y_5051_: *mut LeanObject = *_args.add(6);
    let mut v___y_5052_: *mut LeanObject = *_args.add(7);
    let mut v___y_5053_: *mut LeanObject = *_args.add(8);
    let mut v___y_5054_: *mut LeanObject = *_args.add(9);
    let mut v___y_5055_: *mut LeanObject = *_args.add(10);
    let mut v___y_5056_: *mut LeanObject = *_args.add(11);
    let mut v___y_5057_: *mut LeanObject = *_args.add(12);
    let mut v___y_5058_: *mut LeanObject = *_args.add(13);
    let mut v___y_5059_: *mut LeanObject = *_args.add(14);
    let mut v___y_5060_: *mut LeanObject = *_args.add(15);
    let mut v___y_5061_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5062_: u8 = 0;
    let mut v_sz_boxed_5063_: usize = 0;
    let mut v_i_boxed_5064_: usize = 0;
    let mut v_res_5065_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5062_ = (lean_unbox(v_isLower_5045_) as u8);
    v_sz_boxed_5063_ = lean_unbox_usize(v_sz_5047_);
    lean_dec(v_sz_5047_);
    v_i_boxed_5064_ = lean_unbox_usize(v_i_5048_);
    lean_dec(v_i_5048_);
    v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_5062_, v_as_5046_, v_sz_boxed_5063_, v_i_boxed_5064_, v_b_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
    lean_dec(v___y_5060_);
    lean_dec_ref(v___y_5059_);
    lean_dec(v___y_5058_);
    lean_dec_ref(v___y_5057_);
    lean_dec(v___y_5056_);
    lean_dec_ref(v___y_5055_);
    lean_dec(v___y_5054_);
    lean_dec_ref(v___y_5053_);
    lean_dec(v___y_5052_);
    lean_dec(v___y_5051_);
    lean_dec(v___y_5050_);
    lean_dec_ref(v_as_5046_);
    return v_res_5065_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(
    mut v_isLower_5066_: u8,
    mut v_as_5067_: *mut LeanObject,
    mut v_sz_5068_: usize,
    mut v_i_5069_: usize,
    mut v_b_5070_: *mut LeanObject,
    mut v___y_5071_: *mut LeanObject,
    mut v___y_5072_: *mut LeanObject,
    mut v___y_5073_: *mut LeanObject,
    mut v___y_5074_: *mut LeanObject,
    mut v___y_5075_: *mut LeanObject,
    mut v___y_5076_: *mut LeanObject,
    mut v___y_5077_: *mut LeanObject,
    mut v___y_5078_: *mut LeanObject,
    mut v___y_5079_: *mut LeanObject,
    mut v___y_5080_: *mut LeanObject,
    mut v___y_5081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5085_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v_a_5089_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: usize = 0;
    let mut v___x_5098_: usize = 0;
    let mut v___x_5099_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5100_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5104_: u8 = 0;
    let mut v___x_5106_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5107_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut v_isSharedCheck_5109_: u8 = 0;
    let mut v_unused_5110_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5083_ = lean_usize_dec_lt(v_i_5069_, v_sz_5068_);
                if v___x_5083_ == 0 {
                    v___x_5084_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5084_, 0, v_b_5070_);
                    return v___x_5084_;
                } else {
                    v_snd_5085_ = lean_ctor_get(v_b_5070_, 1);
                    v_isSharedCheck_5109_ = (!lean_is_exclusive(v_b_5070_)) as u8;
                    if v_isSharedCheck_5109_ == 0 {
                        v_unused_5110_ = lean_ctor_get(v_b_5070_, 0);
                        lean_dec(v_unused_5110_);
                        v___x_5087_ = v_b_5070_;
                        v_isShared_5088_ = v_isSharedCheck_5109_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5085_);
                        lean_dec(v_b_5070_);
                        v___x_5087_ = lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5109_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5089_ = lean_array_uget_borrowed(v_as_5067_, v_i_5069_);
                v___x_5090_ = lean_box(0);
                v___x_5091_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_5085_, v_isLower_5066_, v_a_5089_, v___x_5090_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
                if lean_obj_tag(v___x_5091_) == 0 {
                    lean_dec_ref_known(v___x_5091_, 1);
                    v___x_5092_ = lean_box(0);
                    v___x_5093_ = lean_unsigned_to_nat(1);
                    v___x_5094_ = lean_nat_add(v_snd_5085_, v___x_5093_);
                    lean_dec(v_snd_5085_);
                    if v_isShared_5088_ == 0 {
                        lean_ctor_set(v___x_5087_, 1, v___x_5094_);
                        lean_ctor_set(v___x_5087_, 0, v___x_5092_);
                        v___x_5096_ = v___x_5087_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5100_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5092_);
                        lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5094_);
                        v___x_5096_ = v_reuseFailAlloc_5100_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5087_);
                    lean_dec(v_snd_5085_);
                    v_a_5101_ = lean_ctor_get(v___x_5091_, 0);
                    v_isSharedCheck_5108_ = (!lean_is_exclusive(v___x_5091_)) as u8;
                    if v_isSharedCheck_5108_ == 0 {
                        v___x_5103_ = v___x_5091_;
                        v_isShared_5104_ = v_isSharedCheck_5108_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5101_);
                        lean_dec(v___x_5091_);
                        v___x_5103_ = lean_box(0);
                        v_isShared_5104_ = v_isSharedCheck_5108_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5097_ = 1usize;
                v___x_5098_ = lean_usize_add(v_i_5069_, v___x_5097_);
                v___x_5099_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_5066_, v_as_5067_, v_sz_5068_, v___x_5098_, v___x_5096_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
                return v___x_5099_;
            }
            3 => {
                if v_isShared_5104_ == 0 {
                    v___x_5106_ = v___x_5103_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5107_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
                    v___x_5106_ = v_reuseFailAlloc_5107_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5106_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_5111_: *mut LeanObject = *_args.add(0);
    let mut v_as_5112_: *mut LeanObject = *_args.add(1);
    let mut v_sz_5113_: *mut LeanObject = *_args.add(2);
    let mut v_i_5114_: *mut LeanObject = *_args.add(3);
    let mut v_b_5115_: *mut LeanObject = *_args.add(4);
    let mut v___y_5116_: *mut LeanObject = *_args.add(5);
    let mut v___y_5117_: *mut LeanObject = *_args.add(6);
    let mut v___y_5118_: *mut LeanObject = *_args.add(7);
    let mut v___y_5119_: *mut LeanObject = *_args.add(8);
    let mut v___y_5120_: *mut LeanObject = *_args.add(9);
    let mut v___y_5121_: *mut LeanObject = *_args.add(10);
    let mut v___y_5122_: *mut LeanObject = *_args.add(11);
    let mut v___y_5123_: *mut LeanObject = *_args.add(12);
    let mut v___y_5124_: *mut LeanObject = *_args.add(13);
    let mut v___y_5125_: *mut LeanObject = *_args.add(14);
    let mut v___y_5126_: *mut LeanObject = *_args.add(15);
    let mut v___y_5127_: *mut LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5128_: u8 = 0;
    let mut v_sz_boxed_5129_: usize = 0;
    let mut v_i_boxed_5130_: usize = 0;
    let mut v_res_5131_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5128_ = (lean_unbox(v_isLower_5111_) as u8);
    v_sz_boxed_5129_ = lean_unbox_usize(v_sz_5113_);
    lean_dec(v_sz_5113_);
    v_i_boxed_5130_ = lean_unbox_usize(v_i_5114_);
    lean_dec(v_i_5114_);
    v_res_5131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_5128_, v_as_5112_, v_sz_boxed_5129_, v_i_boxed_5130_, v_b_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
    lean_dec(v___y_5126_);
    lean_dec_ref(v___y_5125_);
    lean_dec(v___y_5124_);
    lean_dec_ref(v___y_5123_);
    lean_dec(v___y_5122_);
    lean_dec_ref(v___y_5121_);
    lean_dec(v___y_5120_);
    lean_dec_ref(v___y_5119_);
    lean_dec(v___y_5118_);
    lean_dec(v___y_5117_);
    lean_dec(v___y_5116_);
    lean_dec_ref(v_as_5112_);
    return v_res_5131_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(
    mut v_isLower_5132_: u8,
    mut v_t_5133_: *mut LeanObject,
    mut v_init_5134_: *mut LeanObject,
    mut v___y_5135_: *mut LeanObject,
    mut v___y_5136_: *mut LeanObject,
    mut v___y_5137_: *mut LeanObject,
    mut v___y_5138_: *mut LeanObject,
    mut v___y_5139_: *mut LeanObject,
    mut v___y_5140_: *mut LeanObject,
    mut v___y_5141_: *mut LeanObject,
    mut v___y_5142_: *mut LeanObject,
    mut v___y_5143_: *mut LeanObject,
    mut v___y_5144_: *mut LeanObject,
    mut v___y_5145_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5148_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5153_: u8 = 0;
    let mut v_a_5154_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5157_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5161_: usize = 0;
    let mut v___x_5162_: usize = 0;
    let mut v___x_5163_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5164_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v_fst_5168_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5169_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5177_: u8 = 0;
    let mut v_a_5178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5181_: u8 = 0;
    let mut v___x_5183_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut v_a_5187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5147_ = lean_ctor_get(v_t_5133_, 0);
                v_tail_5148_ = lean_ctor_get(v_t_5133_, 1);
                lean_inc(v_init_5134_);
                v___x_5149_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_5134_, v_isLower_5132_, v_root_5147_, v_init_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
                lean_dec(v_init_5134_);
                if lean_obj_tag(v___x_5149_) == 0 {
                    v_a_5150_ = lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5186_ = (!lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5186_ == 0 {
                        v___x_5152_ = v___x_5149_;
                        v_isShared_5153_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5150_);
                        lean_dec(v___x_5149_);
                        v___x_5152_ = lean_box(0);
                        v_isShared_5153_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5187_ = lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5194_ = (!lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5194_ == 0 {
                        v___x_5189_ = v___x_5149_;
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5187_);
                        lean_dec(v___x_5149_);
                        v___x_5189_ = lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5150_) == 0 {
                    v_a_5154_ = lean_ctor_get(v_a_5150_, 0);
                    lean_inc(v_a_5154_);
                    lean_dec_ref_known(v_a_5150_, 1);
                    if v_isShared_5153_ == 0 {
                        lean_ctor_set(v___x_5152_, 0, v_a_5154_);
                        v___x_5156_ = v___x_5152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5157_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5154_);
                        v___x_5156_ = v_reuseFailAlloc_5157_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5152_);
                    v_a_5158_ = lean_ctor_get(v_a_5150_, 0);
                    lean_inc(v_a_5158_);
                    lean_dec_ref_known(v_a_5150_, 1);
                    v___x_5159_ = lean_box(0);
                    v___x_5160_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5160_, 0, v___x_5159_);
                    lean_ctor_set(v___x_5160_, 1, v_a_5158_);
                    v_sz_5161_ = lean_array_size(v_tail_5148_);
                    v___x_5162_ = 0usize;
                    v___x_5163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_5132_, v_tail_5148_, v_sz_5161_, v___x_5162_, v___x_5160_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
                    if lean_obj_tag(v___x_5163_) == 0 {
                        v_a_5164_ = lean_ctor_get(v___x_5163_, 0);
                        v_isSharedCheck_5177_ = (!lean_is_exclusive(v___x_5163_)) as u8;
                        if v_isSharedCheck_5177_ == 0 {
                            v___x_5166_ = v___x_5163_;
                            v_isShared_5167_ = v_isSharedCheck_5177_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5164_);
                            lean_dec(v___x_5163_);
                            v___x_5166_ = lean_box(0);
                            v_isShared_5167_ = v_isSharedCheck_5177_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5178_ = lean_ctor_get(v___x_5163_, 0);
                        v_isSharedCheck_5185_ = (!lean_is_exclusive(v___x_5163_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5180_ = v___x_5163_;
                            v_isShared_5181_ = v_isSharedCheck_5185_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5178_);
                            lean_dec(v___x_5163_);
                            v___x_5180_ = lean_box(0);
                            v_isShared_5181_ = v_isSharedCheck_5185_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5156_;
            }
            3 => {
                v_fst_5168_ = lean_ctor_get(v_a_5164_, 0);
                if lean_obj_tag(v_fst_5168_) == 0 {
                    v_snd_5169_ = lean_ctor_get(v_a_5164_, 1);
                    lean_inc(v_snd_5169_);
                    lean_dec(v_a_5164_);
                    if v_isShared_5167_ == 0 {
                        lean_ctor_set(v___x_5166_, 0, v_snd_5169_);
                        v___x_5171_ = v___x_5166_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5172_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_snd_5169_);
                        v___x_5171_ = v_reuseFailAlloc_5172_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5168_);
                    lean_dec(v_a_5164_);
                    v_val_5173_ = lean_ctor_get(v_fst_5168_, 0);
                    lean_inc(v_val_5173_);
                    lean_dec_ref_known(v_fst_5168_, 1);
                    if v_isShared_5167_ == 0 {
                        lean_ctor_set(v___x_5166_, 0, v_val_5173_);
                        v___x_5175_ = v___x_5166_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5176_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_val_5173_);
                        v___x_5175_ = v_reuseFailAlloc_5176_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5171_;
            }
            5 => {
                return v___x_5175_;
            }
            6 => {
                if v_isShared_5181_ == 0 {
                    v___x_5183_ = v___x_5180_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5184_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
                    v___x_5183_ = v_reuseFailAlloc_5184_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5183_;
            }
            8 => {
                if v_isShared_5190_ == 0 {
                    v___x_5192_ = v___x_5189_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5193_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
                    v___x_5192_ = v_reuseFailAlloc_5193_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5192_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2___boxed(
    mut v_isLower_5195_: *mut LeanObject,
    mut v_t_5196_: *mut LeanObject,
    mut v_init_5197_: *mut LeanObject,
    mut v___y_5198_: *mut LeanObject,
    mut v___y_5199_: *mut LeanObject,
    mut v___y_5200_: *mut LeanObject,
    mut v___y_5201_: *mut LeanObject,
    mut v___y_5202_: *mut LeanObject,
    mut v___y_5203_: *mut LeanObject,
    mut v___y_5204_: *mut LeanObject,
    mut v___y_5205_: *mut LeanObject,
    mut v___y_5206_: *mut LeanObject,
    mut v___y_5207_: *mut LeanObject,
    mut v___y_5208_: *mut LeanObject,
    mut v___y_5209_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_5210_: u8 = 0;
    let mut v_res_5211_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5210_ = (lean_unbox(v_isLower_5195_) as u8);
    v_res_5211_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_boxed_5210_, v_t_5196_, v_init_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
    lean_dec(v___y_5208_);
    lean_dec_ref(v___y_5207_);
    lean_dec(v___y_5206_);
    lean_dec_ref(v___y_5205_);
    lean_dec(v___y_5204_);
    lean_dec_ref(v___y_5203_);
    lean_dec(v___y_5202_);
    lean_dec_ref(v___y_5201_);
    lean_dec(v___y_5200_);
    lean_dec(v___y_5199_);
    lean_dec(v___y_5198_);
    lean_dec_ref(v_t_5196_);
    return v_res_5211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(
    mut v_css_5212_: *mut LeanObject,
    mut v_isLower_5213_: u8,
    mut v_a_5214_: *mut LeanObject,
    mut v_a_5215_: *mut LeanObject,
    mut v_a_5216_: *mut LeanObject,
    mut v_a_5217_: *mut LeanObject,
    mut v_a_5218_: *mut LeanObject,
    mut v_a_5219_: *mut LeanObject,
    mut v_a_5220_: *mut LeanObject,
    mut v_a_5221_: *mut LeanObject,
    mut v_a_5222_: *mut LeanObject,
    mut v_a_5223_: *mut LeanObject,
    mut v_a_5224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_x_5226_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5231_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5235_: u8 = 0;
    let mut v_unused_5236_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5237_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v___x_5242_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5243_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_5226_ = lean_unsigned_to_nat(0);
                v___x_5227_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_5213_, v_css_5212_, v_x_5226_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
                if lean_obj_tag(v___x_5227_) == 0 {
                    v_isSharedCheck_5235_ = (!lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5235_ == 0 {
                        v_unused_5236_ = lean_ctor_get(v___x_5227_, 0);
                        lean_dec(v_unused_5236_);
                        v___x_5229_ = v___x_5227_;
                        v_isShared_5230_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    } else {
                        lean_dec(v___x_5227_);
                        v___x_5229_ = lean_box(0);
                        v_isShared_5230_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5237_ = lean_ctor_get(v___x_5227_, 0);
                    v_isSharedCheck_5244_ = (!lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5244_ == 0 {
                        v___x_5239_ = v___x_5227_;
                        v_isShared_5240_ = v_isSharedCheck_5244_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5237_);
                        lean_dec(v___x_5227_);
                        v___x_5239_ = lean_box(0);
                        v_isShared_5240_ = v_isSharedCheck_5244_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5231_ = lean_box(0);
                if v_isShared_5230_ == 0 {
                    lean_ctor_set(v___x_5229_, 0, v___x_5231_);
                    v___x_5233_ = v___x_5229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5234_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
                    v___x_5233_ = v_reuseFailAlloc_5234_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5233_;
            }
            3 => {
                if v_isShared_5240_ == 0 {
                    v___x_5242_ = v___x_5239_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5243_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
                    v___x_5242_ = v_reuseFailAlloc_5243_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5242_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs___boxed(
    mut v_css_5245_: *mut LeanObject,
    mut v_isLower_5246_: *mut LeanObject,
    mut v_a_5247_: *mut LeanObject,
    mut v_a_5248_: *mut LeanObject,
    mut v_a_5249_: *mut LeanObject,
    mut v_a_5250_: *mut LeanObject,
    mut v_a_5251_: *mut LeanObject,
    mut v_a_5252_: *mut LeanObject,
    mut v_a_5253_: *mut LeanObject,
    mut v_a_5254_: *mut LeanObject,
    mut v_a_5255_: *mut LeanObject,
    mut v_a_5256_: *mut LeanObject,
    mut v_a_5257_: *mut LeanObject,
    mut v_a_5258_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_isLower_boxed_5259_: u8 = 0;
    let mut v_res_5260_: *mut LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5259_ = (lean_unbox(v_isLower_5246_) as u8);
    v_res_5260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_css_5245_, v_isLower_boxed_5259_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
    lean_dec(v_a_5257_);
    lean_dec_ref(v_a_5256_);
    lean_dec(v_a_5255_);
    lean_dec_ref(v_a_5254_);
    lean_dec(v_a_5253_);
    lean_dec_ref(v_a_5252_);
    lean_dec(v_a_5251_);
    lean_dec_ref(v_a_5250_);
    lean_dec(v_a_5249_);
    lean_dec(v_a_5248_);
    lean_dec(v_a_5247_);
    lean_dec_ref(v_css_5245_);
    return v_res_5260_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2()
-> *mut LeanObject {
    let mut v___x_5263_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut LeanObject = core::ptr::null_mut();
    v___x_5263_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1;
    v___x_5264_ = lean_unsigned_to_nat(2);
    v___x_5265_ = lean_unsigned_to_nat(63);
    v___x_5266_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0;
    v___x_5267_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_5268_ = l_mkPanicMessageWithDecl(
        v___x_5267_,
        v___x_5266_,
        v___x_5265_,
        v___x_5264_,
        v___x_5263_,
    );
    return v___x_5268_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(
    mut v_a_5269_: *mut LeanObject,
    mut v_a_5270_: *mut LeanObject,
    mut v_a_5271_: *mut LeanObject,
    mut v_a_5272_: *mut LeanObject,
    mut v_a_5273_: *mut LeanObject,
    mut v_a_5274_: *mut LeanObject,
    mut v_a_5275_: *mut LeanObject,
    mut v_a_5276_: *mut LeanObject,
    mut v_a_5277_: *mut LeanObject,
    mut v_a_5278_: *mut LeanObject,
    mut v_a_5279_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5281_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_lowers_5283_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_5284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5285_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5286_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5297_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5281_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_,
                    v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_,
                );
                if lean_obj_tag(v___x_5281_) == 0 {
                    v_a_5282_ = lean_ctor_get(v___x_5281_, 0);
                    lean_inc(v_a_5282_);
                    lean_dec_ref_known(v___x_5281_, 1);
                    v_lowers_5283_ = lean_ctor_get(v_a_5282_, 32);
                    lean_inc_ref(v_lowers_5283_);
                    v_vars_5284_ = lean_ctor_get(v_a_5282_, 30);
                    lean_inc_ref(v_vars_5284_);
                    lean_dec(v_a_5282_);
                    v_size_5285_ = lean_ctor_get(v_lowers_5283_, 2);
                    v_size_5286_ = lean_ctor_get(v_vars_5284_, 2);
                    lean_inc(v_size_5286_);
                    lean_dec_ref(v_vars_5284_);
                    v___x_5287_ = lean_nat_dec_eq(v_size_5285_, v_size_5286_);
                    lean_dec(v_size_5286_);
                    if v___x_5287_ == 0 {
                        lean_dec_ref(v_lowers_5283_);
                        v___x_5288_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2);
                        v___x_5289_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_5288_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
                        return v___x_5289_;
                    } else {
                        v___x_5290_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_lowers_5283_, v___x_5287_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
                        lean_dec_ref(v_lowers_5283_);
                        return v___x_5290_;
                    }
                } else {
                    v_a_5291_ = lean_ctor_get(v___x_5281_, 0);
                    v_isSharedCheck_5298_ = (!lean_is_exclusive(v___x_5281_)) as u8;
                    if v_isSharedCheck_5298_ == 0 {
                        v___x_5293_ = v___x_5281_;
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5291_);
                        lean_dec(v___x_5281_);
                        v___x_5293_ = lean_box(0);
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5294_ == 0 {
                    v___x_5296_ = v___x_5293_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5297_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
                    v___x_5296_ = v_reuseFailAlloc_5297_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5296_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___boxed(
    mut v_a_5299_: *mut LeanObject,
    mut v_a_5300_: *mut LeanObject,
    mut v_a_5301_: *mut LeanObject,
    mut v_a_5302_: *mut LeanObject,
    mut v_a_5303_: *mut LeanObject,
    mut v_a_5304_: *mut LeanObject,
    mut v_a_5305_: *mut LeanObject,
    mut v_a_5306_: *mut LeanObject,
    mut v_a_5307_: *mut LeanObject,
    mut v_a_5308_: *mut LeanObject,
    mut v_a_5309_: *mut LeanObject,
    mut v_a_5310_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5311_: *mut LeanObject = core::ptr::null_mut();
    v_res_5311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
    lean_dec(v_a_5309_);
    lean_dec_ref(v_a_5308_);
    lean_dec(v_a_5307_);
    lean_dec_ref(v_a_5306_);
    lean_dec(v_a_5305_);
    lean_dec_ref(v_a_5304_);
    lean_dec(v_a_5303_);
    lean_dec_ref(v_a_5302_);
    lean_dec(v_a_5301_);
    lean_dec(v_a_5300_);
    lean_dec(v_a_5299_);
    return v_res_5311_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2()
-> *mut LeanObject {
    let mut v___x_5314_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut LeanObject = core::ptr::null_mut();
    v___x_5314_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1;
    v___x_5315_ = lean_unsigned_to_nat(2);
    v___x_5316_ = lean_unsigned_to_nat(68);
    v___x_5317_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0;
    v___x_5318_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_5319_ = l_mkPanicMessageWithDecl(
        v___x_5318_,
        v___x_5317_,
        v___x_5316_,
        v___x_5315_,
        v___x_5314_,
    );
    return v___x_5319_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(
    mut v_a_5320_: *mut LeanObject,
    mut v_a_5321_: *mut LeanObject,
    mut v_a_5322_: *mut LeanObject,
    mut v_a_5323_: *mut LeanObject,
    mut v_a_5324_: *mut LeanObject,
    mut v_a_5325_: *mut LeanObject,
    mut v_a_5326_: *mut LeanObject,
    mut v_a_5327_: *mut LeanObject,
    mut v_a_5328_: *mut LeanObject,
    mut v_a_5329_: *mut LeanObject,
    mut v_a_5330_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5332_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5333_: *mut LeanObject = core::ptr::null_mut();
    let mut v_uppers_5334_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_5335_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5336_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_5337_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5343_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5332_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_,
                    v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_,
                );
                if lean_obj_tag(v___x_5332_) == 0 {
                    v_a_5333_ = lean_ctor_get(v___x_5332_, 0);
                    lean_inc(v_a_5333_);
                    lean_dec_ref_known(v___x_5332_, 1);
                    v_uppers_5334_ = lean_ctor_get(v_a_5333_, 33);
                    lean_inc_ref(v_uppers_5334_);
                    v_vars_5335_ = lean_ctor_get(v_a_5333_, 30);
                    lean_inc_ref(v_vars_5335_);
                    lean_dec(v_a_5333_);
                    v_size_5336_ = lean_ctor_get(v_uppers_5334_, 2);
                    v_size_5337_ = lean_ctor_get(v_vars_5335_, 2);
                    lean_inc(v_size_5337_);
                    lean_dec_ref(v_vars_5335_);
                    v___x_5338_ = lean_nat_dec_eq(v_size_5336_, v_size_5337_);
                    lean_dec(v_size_5337_);
                    if v___x_5338_ == 0 {
                        lean_dec_ref(v_uppers_5334_);
                        v___x_5339_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2);
                        v___x_5340_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_5339_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
                        return v___x_5340_;
                    } else {
                        v___x_5341_ = 0;
                        v___x_5342_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_uppers_5334_, v___x_5341_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
                        lean_dec_ref(v_uppers_5334_);
                        return v___x_5342_;
                    }
                } else {
                    v_a_5343_ = lean_ctor_get(v___x_5332_, 0);
                    v_isSharedCheck_5350_ = (!lean_is_exclusive(v___x_5332_)) as u8;
                    if v_isSharedCheck_5350_ == 0 {
                        v___x_5345_ = v___x_5332_;
                        v_isShared_5346_ = v_isSharedCheck_5350_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5343_);
                        lean_dec(v___x_5332_);
                        v___x_5345_ = lean_box(0);
                        v_isShared_5346_ = v_isSharedCheck_5350_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if v_isShared_5346_ == 0 {
                    v___x_5348_ = v___x_5345_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5349_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
                    v___x_5348_ = v_reuseFailAlloc_5349_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5348_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___boxed(
    mut v_a_5351_: *mut LeanObject,
    mut v_a_5352_: *mut LeanObject,
    mut v_a_5353_: *mut LeanObject,
    mut v_a_5354_: *mut LeanObject,
    mut v_a_5355_: *mut LeanObject,
    mut v_a_5356_: *mut LeanObject,
    mut v_a_5357_: *mut LeanObject,
    mut v_a_5358_: *mut LeanObject,
    mut v_a_5359_: *mut LeanObject,
    mut v_a_5360_: *mut LeanObject,
    mut v_a_5361_: *mut LeanObject,
    mut v_a_5362_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5363_: *mut LeanObject = core::ptr::null_mut();
    v_res_5363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_);
    lean_dec(v_a_5361_);
    lean_dec_ref(v_a_5360_);
    lean_dec(v_a_5359_);
    lean_dec_ref(v_a_5358_);
    lean_dec(v_a_5357_);
    lean_dec_ref(v_a_5356_);
    lean_dec(v_a_5355_);
    lean_dec_ref(v_a_5354_);
    lean_dec(v_a_5353_);
    lean_dec(v_a_5352_);
    lean_dec(v_a_5351_);
    return v_res_5363_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(
    mut v_____s_5367_: *mut LeanObject,
    mut v_as_5368_: *mut LeanObject,
    mut v_sz_5369_: usize,
    mut v_i_5370_: usize,
    mut v_b_5371_: *mut LeanObject,
    mut v___y_5372_: *mut LeanObject,
    mut v___y_5373_: *mut LeanObject,
    mut v___y_5374_: *mut LeanObject,
    mut v___y_5375_: *mut LeanObject,
    mut v___y_5376_: *mut LeanObject,
    mut v___y_5377_: *mut LeanObject,
    mut v___y_5378_: *mut LeanObject,
    mut v___y_5379_: *mut LeanObject,
    mut v___y_5380_: *mut LeanObject,
    mut v___y_5381_: *mut LeanObject,
    mut v___y_5382_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5384_: u8 = 0;
    let mut v___x_5385_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5386_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5387_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: usize = 0;
    let mut v___x_5391_: usize = 0;
    let mut v_a_5393_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5398_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5384_ = lean_usize_dec_lt(v_i_5370_, v_sz_5369_);
                if v___x_5384_ == 0 {
                    v___x_5385_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5385_, 0, v_b_5371_);
                    return v___x_5385_;
                } else {
                    lean_dec_ref(v_b_5371_);
                    v_a_5386_ = lean_array_uget_borrowed(v_as_5368_, v_i_5370_);
                    v_p_5387_ = lean_ctor_get(v_a_5386_, 0);
                    v___x_5388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5387_, v_____s_5367_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
                    if lean_obj_tag(v___x_5388_) == 0 {
                        lean_dec_ref_known(v___x_5388_, 1);
                        v___x_5389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_5390_ = 1usize;
                        v___x_5391_ = lean_usize_add(v_i_5370_, v___x_5390_);
                        v_i_5370_ = v___x_5391_;
                        v_b_5371_ = v___x_5389_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5393_ = lean_ctor_get(v___x_5388_, 0);
                        v_isSharedCheck_5400_ = (!lean_is_exclusive(v___x_5388_)) as u8;
                        if v_isSharedCheck_5400_ == 0 {
                            v___x_5395_ = v___x_5388_;
                            v_isShared_5396_ = v_isSharedCheck_5400_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5393_);
                            lean_dec(v___x_5388_);
                            v___x_5395_ = lean_box(0);
                            v_isShared_5396_ = v_isSharedCheck_5400_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5396_ == 0 {
                    v___x_5398_ = v___x_5395_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5399_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
                    v___x_5398_ = v_reuseFailAlloc_5399_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5398_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5401_: *mut LeanObject = *_args.add(0);
    let mut v_as_5402_: *mut LeanObject = *_args.add(1);
    let mut v_sz_5403_: *mut LeanObject = *_args.add(2);
    let mut v_i_5404_: *mut LeanObject = *_args.add(3);
    let mut v_b_5405_: *mut LeanObject = *_args.add(4);
    let mut v___y_5406_: *mut LeanObject = *_args.add(5);
    let mut v___y_5407_: *mut LeanObject = *_args.add(6);
    let mut v___y_5408_: *mut LeanObject = *_args.add(7);
    let mut v___y_5409_: *mut LeanObject = *_args.add(8);
    let mut v___y_5410_: *mut LeanObject = *_args.add(9);
    let mut v___y_5411_: *mut LeanObject = *_args.add(10);
    let mut v___y_5412_: *mut LeanObject = *_args.add(11);
    let mut v___y_5413_: *mut LeanObject = *_args.add(12);
    let mut v___y_5414_: *mut LeanObject = *_args.add(13);
    let mut v___y_5415_: *mut LeanObject = *_args.add(14);
    let mut v___y_5416_: *mut LeanObject = *_args.add(15);
    let mut v___y_5417_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5418_: usize = 0;
    let mut v_i_boxed_5419_: usize = 0;
    let mut v_res_5420_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5418_ = lean_unbox_usize(v_sz_5403_);
    lean_dec(v_sz_5403_);
    v_i_boxed_5419_ = lean_unbox_usize(v_i_5404_);
    lean_dec(v_i_5404_);
    v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_5401_, v_as_5402_, v_sz_boxed_5418_, v_i_boxed_5419_, v_b_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
    lean_dec(v___y_5416_);
    lean_dec_ref(v___y_5415_);
    lean_dec(v___y_5414_);
    lean_dec_ref(v___y_5413_);
    lean_dec(v___y_5412_);
    lean_dec_ref(v___y_5411_);
    lean_dec(v___y_5410_);
    lean_dec_ref(v___y_5409_);
    lean_dec(v___y_5408_);
    lean_dec(v___y_5407_);
    lean_dec(v___y_5406_);
    lean_dec_ref(v_as_5402_);
    lean_dec(v_____s_5401_);
    return v_res_5420_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(
    mut v_____s_5421_: *mut LeanObject,
    mut v_as_5422_: *mut LeanObject,
    mut v_sz_5423_: usize,
    mut v_i_5424_: usize,
    mut v_b_5425_: *mut LeanObject,
    mut v___y_5426_: *mut LeanObject,
    mut v___y_5427_: *mut LeanObject,
    mut v___y_5428_: *mut LeanObject,
    mut v___y_5429_: *mut LeanObject,
    mut v___y_5430_: *mut LeanObject,
    mut v___y_5431_: *mut LeanObject,
    mut v___y_5432_: *mut LeanObject,
    mut v___y_5433_: *mut LeanObject,
    mut v___y_5434_: *mut LeanObject,
    mut v___y_5435_: *mut LeanObject,
    mut v___y_5436_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5438_: u8 = 0;
    let mut v___x_5439_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5440_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5441_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: usize = 0;
    let mut v___x_5445_: usize = 0;
    let mut v___x_5446_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5452_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5438_ = lean_usize_dec_lt(v_i_5424_, v_sz_5423_);
                if v___x_5438_ == 0 {
                    v___x_5439_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5439_, 0, v_b_5425_);
                    return v___x_5439_;
                } else {
                    lean_dec_ref(v_b_5425_);
                    v_a_5440_ = lean_array_uget_borrowed(v_as_5422_, v_i_5424_);
                    v_p_5441_ = lean_ctor_get(v_a_5440_, 0);
                    v___x_5442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5441_, v_____s_5421_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
                    if lean_obj_tag(v___x_5442_) == 0 {
                        lean_dec_ref_known(v___x_5442_, 1);
                        v___x_5443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_5444_ = 1usize;
                        v___x_5445_ = lean_usize_add(v_i_5424_, v___x_5444_);
                        v___x_5446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_5421_, v_as_5422_, v_sz_5423_, v___x_5445_, v___x_5443_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
                        return v___x_5446_;
                    } else {
                        v_a_5447_ = lean_ctor_get(v___x_5442_, 0);
                        v_isSharedCheck_5454_ = (!lean_is_exclusive(v___x_5442_)) as u8;
                        if v_isSharedCheck_5454_ == 0 {
                            v___x_5449_ = v___x_5442_;
                            v_isShared_5450_ = v_isSharedCheck_5454_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5447_);
                            lean_dec(v___x_5442_);
                            v___x_5449_ = lean_box(0);
                            v_isShared_5450_ = v_isSharedCheck_5454_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5450_ == 0 {
                    v___x_5452_ = v___x_5449_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5453_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
                    v___x_5452_ = v_reuseFailAlloc_5453_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5452_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5455_: *mut LeanObject = *_args.add(0);
    let mut v_as_5456_: *mut LeanObject = *_args.add(1);
    let mut v_sz_5457_: *mut LeanObject = *_args.add(2);
    let mut v_i_5458_: *mut LeanObject = *_args.add(3);
    let mut v_b_5459_: *mut LeanObject = *_args.add(4);
    let mut v___y_5460_: *mut LeanObject = *_args.add(5);
    let mut v___y_5461_: *mut LeanObject = *_args.add(6);
    let mut v___y_5462_: *mut LeanObject = *_args.add(7);
    let mut v___y_5463_: *mut LeanObject = *_args.add(8);
    let mut v___y_5464_: *mut LeanObject = *_args.add(9);
    let mut v___y_5465_: *mut LeanObject = *_args.add(10);
    let mut v___y_5466_: *mut LeanObject = *_args.add(11);
    let mut v___y_5467_: *mut LeanObject = *_args.add(12);
    let mut v___y_5468_: *mut LeanObject = *_args.add(13);
    let mut v___y_5469_: *mut LeanObject = *_args.add(14);
    let mut v___y_5470_: *mut LeanObject = *_args.add(15);
    let mut v___y_5471_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5472_: usize = 0;
    let mut v_i_boxed_5473_: usize = 0;
    let mut v_res_5474_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5472_ = lean_unbox_usize(v_sz_5457_);
    lean_dec(v_sz_5457_);
    v_i_boxed_5473_ = lean_unbox_usize(v_i_5458_);
    lean_dec(v_i_5458_);
    v_res_5474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_5455_, v_as_5456_, v_sz_boxed_5472_, v_i_boxed_5473_, v_b_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
    lean_dec(v___y_5470_);
    lean_dec_ref(v___y_5469_);
    lean_dec(v___y_5468_);
    lean_dec_ref(v___y_5467_);
    lean_dec(v___y_5466_);
    lean_dec_ref(v___y_5465_);
    lean_dec(v___y_5464_);
    lean_dec_ref(v___y_5463_);
    lean_dec(v___y_5462_);
    lean_dec(v___y_5461_);
    lean_dec(v___y_5460_);
    lean_dec_ref(v_as_5456_);
    lean_dec(v_____s_5455_);
    return v_res_5474_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(
    mut v_init_5475_: *mut LeanObject,
    mut v_____s_5476_: *mut LeanObject,
    mut v_n_5477_: *mut LeanObject,
    mut v_b_5478_: *mut LeanObject,
    mut v___y_5479_: *mut LeanObject,
    mut v___y_5480_: *mut LeanObject,
    mut v___y_5481_: *mut LeanObject,
    mut v___y_5482_: *mut LeanObject,
    mut v___y_5483_: *mut LeanObject,
    mut v___y_5484_: *mut LeanObject,
    mut v___y_5485_: *mut LeanObject,
    mut v___y_5486_: *mut LeanObject,
    mut v___y_5487_: *mut LeanObject,
    mut v___y_5488_: *mut LeanObject,
    mut v___y_5489_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_5491_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5494_: usize = 0;
    let mut v___x_5495_: usize = 0;
    let mut v___x_5496_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5497_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5500_: u8 = 0;
    let mut v_fst_5501_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5502_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5506_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5507_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5510_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v_a_5512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v___x_5517_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5518_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5519_: u8 = 0;
    let mut v_vs_5520_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5523_: usize = 0;
    let mut v___x_5524_: usize = 0;
    let mut v___x_5525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5526_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5529_: u8 = 0;
    let mut v_fst_5530_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5531_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5536_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5540_: u8 = 0;
    let mut v_a_5541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_5477_) == 0 {
                    v_cs_5491_ = lean_ctor_get(v_n_5477_, 0);
                    v___x_5492_ = lean_box(0);
                    v___x_5493_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5493_, 0, v___x_5492_);
                    lean_ctor_set(v___x_5493_, 1, v_b_5478_);
                    v_sz_5494_ = lean_array_size(v_cs_5491_);
                    v___x_5495_ = 0usize;
                    v___x_5496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_5475_, v_____s_5476_, v_cs_5491_, v_sz_5494_, v___x_5495_, v___x_5493_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
                    if lean_obj_tag(v___x_5496_) == 0 {
                        v_a_5497_ = lean_ctor_get(v___x_5496_, 0);
                        v_isSharedCheck_5511_ = (!lean_is_exclusive(v___x_5496_)) as u8;
                        if v_isSharedCheck_5511_ == 0 {
                            v___x_5499_ = v___x_5496_;
                            v_isShared_5500_ = v_isSharedCheck_5511_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5497_);
                            lean_dec(v___x_5496_);
                            v___x_5499_ = lean_box(0);
                            v_isShared_5500_ = v_isSharedCheck_5511_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5512_ = lean_ctor_get(v___x_5496_, 0);
                        v_isSharedCheck_5519_ = (!lean_is_exclusive(v___x_5496_)) as u8;
                        if v_isSharedCheck_5519_ == 0 {
                            v___x_5514_ = v___x_5496_;
                            v_isShared_5515_ = v_isSharedCheck_5519_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_5512_);
                            lean_dec(v___x_5496_);
                            v___x_5514_ = lean_box(0);
                            v_isShared_5515_ = v_isSharedCheck_5519_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5520_ = lean_ctor_get(v_n_5477_, 0);
                    v___x_5521_ = lean_box(0);
                    v___x_5522_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5522_, 0, v___x_5521_);
                    lean_ctor_set(v___x_5522_, 1, v_b_5478_);
                    v_sz_5523_ = lean_array_size(v_vs_5520_);
                    v___x_5524_ = 0usize;
                    v___x_5525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_5476_, v_vs_5520_, v_sz_5523_, v___x_5524_, v___x_5522_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
                    if lean_obj_tag(v___x_5525_) == 0 {
                        v_a_5526_ = lean_ctor_get(v___x_5525_, 0);
                        v_isSharedCheck_5540_ = (!lean_is_exclusive(v___x_5525_)) as u8;
                        if v_isSharedCheck_5540_ == 0 {
                            v___x_5528_ = v___x_5525_;
                            v_isShared_5529_ = v_isSharedCheck_5540_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5526_);
                            lean_dec(v___x_5525_);
                            v___x_5528_ = lean_box(0);
                            v_isShared_5529_ = v_isSharedCheck_5540_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5541_ = lean_ctor_get(v___x_5525_, 0);
                        v_isSharedCheck_5548_ = (!lean_is_exclusive(v___x_5525_)) as u8;
                        if v_isSharedCheck_5548_ == 0 {
                            v___x_5543_ = v___x_5525_;
                            v_isShared_5544_ = v_isSharedCheck_5548_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_5541_);
                            lean_dec(v___x_5525_);
                            v___x_5543_ = lean_box(0);
                            v_isShared_5544_ = v_isSharedCheck_5548_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5501_ = lean_ctor_get(v_a_5497_, 0);
                if lean_obj_tag(v_fst_5501_) == 0 {
                    v_snd_5502_ = lean_ctor_get(v_a_5497_, 1);
                    lean_inc(v_snd_5502_);
                    lean_dec(v_a_5497_);
                    v___x_5503_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5503_, 0, v_snd_5502_);
                    if v_isShared_5500_ == 0 {
                        lean_ctor_set(v___x_5499_, 0, v___x_5503_);
                        v___x_5505_ = v___x_5499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5506_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5503_);
                        v___x_5505_ = v_reuseFailAlloc_5506_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5501_);
                    lean_dec(v_a_5497_);
                    v_val_5507_ = lean_ctor_get(v_fst_5501_, 0);
                    lean_inc(v_val_5507_);
                    lean_dec_ref_known(v_fst_5501_, 1);
                    if v_isShared_5500_ == 0 {
                        lean_ctor_set(v___x_5499_, 0, v_val_5507_);
                        v___x_5509_ = v___x_5499_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_val_5507_);
                        v___x_5509_ = v_reuseFailAlloc_5510_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_5505_;
            }
            3 => {
                return v___x_5509_;
            }
            4 => {
                if v_isShared_5515_ == 0 {
                    v___x_5517_ = v___x_5514_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_5518_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
                    v___x_5517_ = v_reuseFailAlloc_5518_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5517_;
            }
            6 => {
                v_fst_5530_ = lean_ctor_get(v_a_5526_, 0);
                if lean_obj_tag(v_fst_5530_) == 0 {
                    v_snd_5531_ = lean_ctor_get(v_a_5526_, 1);
                    lean_inc(v_snd_5531_);
                    lean_dec(v_a_5526_);
                    v___x_5532_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5532_, 0, v_snd_5531_);
                    if v_isShared_5529_ == 0 {
                        lean_ctor_set(v___x_5528_, 0, v___x_5532_);
                        v___x_5534_ = v___x_5528_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5535_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5535_, 0, v___x_5532_);
                        v___x_5534_ = v_reuseFailAlloc_5535_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5530_);
                    lean_dec(v_a_5526_);
                    v_val_5536_ = lean_ctor_get(v_fst_5530_, 0);
                    lean_inc(v_val_5536_);
                    lean_dec_ref_known(v_fst_5530_, 1);
                    if v_isShared_5529_ == 0 {
                        lean_ctor_set(v___x_5528_, 0, v_val_5536_);
                        v___x_5538_ = v___x_5528_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5539_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_val_5536_);
                        v___x_5538_ = v_reuseFailAlloc_5539_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_5534_;
            }
            8 => {
                return v___x_5538_;
            }
            9 => {
                if v_isShared_5544_ == 0 {
                    v___x_5546_ = v___x_5543_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_5547_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
                    v___x_5546_ = v_reuseFailAlloc_5547_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_5546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(
    mut v_init_5549_: *mut LeanObject,
    mut v_____s_5550_: *mut LeanObject,
    mut v_as_5551_: *mut LeanObject,
    mut v_sz_5552_: usize,
    mut v_i_5553_: usize,
    mut v_b_5554_: *mut LeanObject,
    mut v___y_5555_: *mut LeanObject,
    mut v___y_5556_: *mut LeanObject,
    mut v___y_5557_: *mut LeanObject,
    mut v___y_5558_: *mut LeanObject,
    mut v___y_5559_: *mut LeanObject,
    mut v___y_5560_: *mut LeanObject,
    mut v___y_5561_: *mut LeanObject,
    mut v___y_5562_: *mut LeanObject,
    mut v___y_5563_: *mut LeanObject,
    mut v___y_5564_: *mut LeanObject,
    mut v___y_5565_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5568_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5569_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5572_: u8 = 0;
    let mut v_a_5573_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5575_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5579_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5584_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: usize = 0;
    let mut v___x_5591_: usize = 0;
    let mut v_reuseFailAlloc_5593_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut v_a_5595_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v___x_5600_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_isSharedCheck_5603_: u8 = 0;
    let mut v_unused_5604_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5567_ = lean_usize_dec_lt(v_i_5553_, v_sz_5552_);
                if v___x_5567_ == 0 {
                    v___x_5568_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5568_, 0, v_b_5554_);
                    return v___x_5568_;
                } else {
                    v_snd_5569_ = lean_ctor_get(v_b_5554_, 1);
                    v_isSharedCheck_5603_ = (!lean_is_exclusive(v_b_5554_)) as u8;
                    if v_isSharedCheck_5603_ == 0 {
                        v_unused_5604_ = lean_ctor_get(v_b_5554_, 0);
                        lean_dec(v_unused_5604_);
                        v___x_5571_ = v_b_5554_;
                        v_isShared_5572_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5569_);
                        lean_dec(v_b_5554_);
                        v___x_5571_ = lean_box(0);
                        v_isShared_5572_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5573_ = lean_array_uget_borrowed(v_as_5551_, v_i_5553_);
                lean_inc(v_snd_5569_);
                v___x_5574_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5549_, v_____s_5550_, v_a_5573_, v_snd_5569_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
                if lean_obj_tag(v___x_5574_) == 0 {
                    v_a_5575_ = lean_ctor_get(v___x_5574_, 0);
                    v_isSharedCheck_5594_ = (!lean_is_exclusive(v___x_5574_)) as u8;
                    if v_isSharedCheck_5594_ == 0 {
                        v___x_5577_ = v___x_5574_;
                        v_isShared_5578_ = v_isSharedCheck_5594_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_5575_);
                        lean_dec(v___x_5574_);
                        v___x_5577_ = lean_box(0);
                        v_isShared_5578_ = v_isSharedCheck_5594_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5571_);
                    lean_dec(v_snd_5569_);
                    v_a_5595_ = lean_ctor_get(v___x_5574_, 0);
                    v_isSharedCheck_5602_ = (!lean_is_exclusive(v___x_5574_)) as u8;
                    if v_isSharedCheck_5602_ == 0 {
                        v___x_5597_ = v___x_5574_;
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_5595_);
                        lean_dec(v___x_5574_);
                        v___x_5597_ = lean_box(0);
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_5575_) == 0 {
                    v___x_5579_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_5579_, 0, v_a_5575_);
                    if v_isShared_5572_ == 0 {
                        lean_ctor_set(v___x_5571_, 0, v___x_5579_);
                        v___x_5581_ = v___x_5571_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5579_);
                        lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_snd_5569_);
                        v___x_5581_ = v_reuseFailAlloc_5585_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5577_);
                    lean_dec(v_snd_5569_);
                    v_a_5586_ = lean_ctor_get(v_a_5575_, 0);
                    lean_inc(v_a_5586_);
                    lean_dec_ref_known(v_a_5575_, 1);
                    v___x_5587_ = lean_box(0);
                    if v_isShared_5572_ == 0 {
                        lean_ctor_set(v___x_5571_, 1, v_a_5586_);
                        lean_ctor_set(v___x_5571_, 0, v___x_5587_);
                        v___x_5589_ = v___x_5571_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5593_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5587_);
                        lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_a_5586_);
                        v___x_5589_ = v_reuseFailAlloc_5593_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5578_ == 0 {
                    lean_ctor_set(v___x_5577_, 0, v___x_5581_);
                    v___x_5583_ = v___x_5577_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5581_);
                    v___x_5583_ = v_reuseFailAlloc_5584_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5583_;
            }
            5 => {
                v___x_5590_ = 1usize;
                v___x_5591_ = lean_usize_add(v_i_5553_, v___x_5590_);
                v_i_5553_ = v___x_5591_;
                v_b_5554_ = v___x_5589_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_5598_ == 0 {
                    v___x_5600_ = v___x_5597_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5601_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
                    v___x_5600_ = v_reuseFailAlloc_5601_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5600_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_5605_: *mut LeanObject = *_args.add(0);
    let mut v_____s_5606_: *mut LeanObject = *_args.add(1);
    let mut v_as_5607_: *mut LeanObject = *_args.add(2);
    let mut v_sz_5608_: *mut LeanObject = *_args.add(3);
    let mut v_i_5609_: *mut LeanObject = *_args.add(4);
    let mut v_b_5610_: *mut LeanObject = *_args.add(5);
    let mut v___y_5611_: *mut LeanObject = *_args.add(6);
    let mut v___y_5612_: *mut LeanObject = *_args.add(7);
    let mut v___y_5613_: *mut LeanObject = *_args.add(8);
    let mut v___y_5614_: *mut LeanObject = *_args.add(9);
    let mut v___y_5615_: *mut LeanObject = *_args.add(10);
    let mut v___y_5616_: *mut LeanObject = *_args.add(11);
    let mut v___y_5617_: *mut LeanObject = *_args.add(12);
    let mut v___y_5618_: *mut LeanObject = *_args.add(13);
    let mut v___y_5619_: *mut LeanObject = *_args.add(14);
    let mut v___y_5620_: *mut LeanObject = *_args.add(15);
    let mut v___y_5621_: *mut LeanObject = *_args.add(16);
    let mut v___y_5622_: *mut LeanObject = *_args.add(17);
    let mut v_sz_boxed_5623_: usize = 0;
    let mut v_i_boxed_5624_: usize = 0;
    let mut v_res_5625_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5623_ = lean_unbox_usize(v_sz_5608_);
    lean_dec(v_sz_5608_);
    v_i_boxed_5624_ = lean_unbox_usize(v_i_5609_);
    lean_dec(v_i_5609_);
    v_res_5625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_5605_, v_____s_5606_, v_as_5607_, v_sz_boxed_5623_, v_i_boxed_5624_, v_b_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    lean_dec(v___y_5621_);
    lean_dec_ref(v___y_5620_);
    lean_dec(v___y_5619_);
    lean_dec_ref(v___y_5618_);
    lean_dec(v___y_5617_);
    lean_dec_ref(v___y_5616_);
    lean_dec(v___y_5615_);
    lean_dec_ref(v___y_5614_);
    lean_dec(v___y_5613_);
    lean_dec(v___y_5612_);
    lean_dec(v___y_5611_);
    lean_dec_ref(v_as_5607_);
    lean_dec(v_____s_5606_);
    return v_res_5625_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0___boxed(
    mut v_init_5626_: *mut LeanObject,
    mut v_____s_5627_: *mut LeanObject,
    mut v_n_5628_: *mut LeanObject,
    mut v_b_5629_: *mut LeanObject,
    mut v___y_5630_: *mut LeanObject,
    mut v___y_5631_: *mut LeanObject,
    mut v___y_5632_: *mut LeanObject,
    mut v___y_5633_: *mut LeanObject,
    mut v___y_5634_: *mut LeanObject,
    mut v___y_5635_: *mut LeanObject,
    mut v___y_5636_: *mut LeanObject,
    mut v___y_5637_: *mut LeanObject,
    mut v___y_5638_: *mut LeanObject,
    mut v___y_5639_: *mut LeanObject,
    mut v___y_5640_: *mut LeanObject,
    mut v___y_5641_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5642_: *mut LeanObject = core::ptr::null_mut();
    v_res_5642_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5626_, v_____s_5627_, v_n_5628_, v_b_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
    lean_dec(v___y_5640_);
    lean_dec_ref(v___y_5639_);
    lean_dec(v___y_5638_);
    lean_dec_ref(v___y_5637_);
    lean_dec(v___y_5636_);
    lean_dec_ref(v___y_5635_);
    lean_dec(v___y_5634_);
    lean_dec_ref(v___y_5633_);
    lean_dec(v___y_5632_);
    lean_dec(v___y_5631_);
    lean_dec(v___y_5630_);
    lean_dec_ref(v_n_5628_);
    lean_dec(v_____s_5627_);
    return v_res_5642_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(
    mut v_____s_5646_: *mut LeanObject,
    mut v_as_5647_: *mut LeanObject,
    mut v_sz_5648_: usize,
    mut v_i_5649_: usize,
    mut v_b_5650_: *mut LeanObject,
    mut v___y_5651_: *mut LeanObject,
    mut v___y_5652_: *mut LeanObject,
    mut v___y_5653_: *mut LeanObject,
    mut v___y_5654_: *mut LeanObject,
    mut v___y_5655_: *mut LeanObject,
    mut v___y_5656_: *mut LeanObject,
    mut v___y_5657_: *mut LeanObject,
    mut v___y_5658_: *mut LeanObject,
    mut v___y_5659_: *mut LeanObject,
    mut v___y_5660_: *mut LeanObject,
    mut v___y_5661_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5663_: u8 = 0;
    let mut v___x_5664_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5665_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5666_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: usize = 0;
    let mut v___x_5670_: usize = 0;
    let mut v_a_5672_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5675_: u8 = 0;
    let mut v___x_5677_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5663_ = lean_usize_dec_lt(v_i_5649_, v_sz_5648_);
                if v___x_5663_ == 0 {
                    v___x_5664_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5664_, 0, v_b_5650_);
                    return v___x_5664_;
                } else {
                    lean_dec_ref(v_b_5650_);
                    v_a_5665_ = lean_array_uget_borrowed(v_as_5647_, v_i_5649_);
                    v_p_5666_ = lean_ctor_get(v_a_5665_, 0);
                    v___x_5667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5666_, v_____s_5646_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_);
                    if lean_obj_tag(v___x_5667_) == 0 {
                        lean_dec_ref_known(v___x_5667_, 1);
                        v___x_5668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_5669_ = 1usize;
                        v___x_5670_ = lean_usize_add(v_i_5649_, v___x_5669_);
                        v_i_5649_ = v___x_5670_;
                        v_b_5650_ = v___x_5668_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5672_ = lean_ctor_get(v___x_5667_, 0);
                        v_isSharedCheck_5679_ = (!lean_is_exclusive(v___x_5667_)) as u8;
                        if v_isSharedCheck_5679_ == 0 {
                            v___x_5674_ = v___x_5667_;
                            v_isShared_5675_ = v_isSharedCheck_5679_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5672_);
                            lean_dec(v___x_5667_);
                            v___x_5674_ = lean_box(0);
                            v_isShared_5675_ = v_isSharedCheck_5679_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5675_ == 0 {
                    v___x_5677_ = v___x_5674_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5678_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5672_);
                    v___x_5677_ = v_reuseFailAlloc_5678_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5677_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5680_: *mut LeanObject = *_args.add(0);
    let mut v_as_5681_: *mut LeanObject = *_args.add(1);
    let mut v_sz_5682_: *mut LeanObject = *_args.add(2);
    let mut v_i_5683_: *mut LeanObject = *_args.add(3);
    let mut v_b_5684_: *mut LeanObject = *_args.add(4);
    let mut v___y_5685_: *mut LeanObject = *_args.add(5);
    let mut v___y_5686_: *mut LeanObject = *_args.add(6);
    let mut v___y_5687_: *mut LeanObject = *_args.add(7);
    let mut v___y_5688_: *mut LeanObject = *_args.add(8);
    let mut v___y_5689_: *mut LeanObject = *_args.add(9);
    let mut v___y_5690_: *mut LeanObject = *_args.add(10);
    let mut v___y_5691_: *mut LeanObject = *_args.add(11);
    let mut v___y_5692_: *mut LeanObject = *_args.add(12);
    let mut v___y_5693_: *mut LeanObject = *_args.add(13);
    let mut v___y_5694_: *mut LeanObject = *_args.add(14);
    let mut v___y_5695_: *mut LeanObject = *_args.add(15);
    let mut v___y_5696_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5697_: usize = 0;
    let mut v_i_boxed_5698_: usize = 0;
    let mut v_res_5699_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5697_ = lean_unbox_usize(v_sz_5682_);
    lean_dec(v_sz_5682_);
    v_i_boxed_5698_ = lean_unbox_usize(v_i_5683_);
    lean_dec(v_i_5683_);
    v_res_5699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_5680_, v_as_5681_, v_sz_boxed_5697_, v_i_boxed_5698_, v_b_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_);
    lean_dec(v___y_5695_);
    lean_dec_ref(v___y_5694_);
    lean_dec(v___y_5693_);
    lean_dec_ref(v___y_5692_);
    lean_dec(v___y_5691_);
    lean_dec_ref(v___y_5690_);
    lean_dec(v___y_5689_);
    lean_dec_ref(v___y_5688_);
    lean_dec(v___y_5687_);
    lean_dec(v___y_5686_);
    lean_dec(v___y_5685_);
    lean_dec_ref(v_as_5681_);
    lean_dec(v_____s_5680_);
    return v_res_5699_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(
    mut v_____s_5700_: *mut LeanObject,
    mut v_as_5701_: *mut LeanObject,
    mut v_sz_5702_: usize,
    mut v_i_5703_: usize,
    mut v_b_5704_: *mut LeanObject,
    mut v___y_5705_: *mut LeanObject,
    mut v___y_5706_: *mut LeanObject,
    mut v___y_5707_: *mut LeanObject,
    mut v___y_5708_: *mut LeanObject,
    mut v___y_5709_: *mut LeanObject,
    mut v___y_5710_: *mut LeanObject,
    mut v___y_5711_: *mut LeanObject,
    mut v___y_5712_: *mut LeanObject,
    mut v___y_5713_: *mut LeanObject,
    mut v___y_5714_: *mut LeanObject,
    mut v___y_5715_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5717_: u8 = 0;
    let mut v___x_5718_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5719_: *mut LeanObject = core::ptr::null_mut();
    let mut v_p_5720_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: usize = 0;
    let mut v___x_5724_: usize = 0;
    let mut v___x_5725_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5729_: u8 = 0;
    let mut v___x_5731_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5717_ = lean_usize_dec_lt(v_i_5703_, v_sz_5702_);
                if v___x_5717_ == 0 {
                    v___x_5718_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5718_, 0, v_b_5704_);
                    return v___x_5718_;
                } else {
                    lean_dec_ref(v_b_5704_);
                    v_a_5719_ = lean_array_uget_borrowed(v_as_5701_, v_i_5703_);
                    v_p_5720_ = lean_ctor_get(v_a_5719_, 0);
                    v___x_5721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5720_, v_____s_5700_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
                    if lean_obj_tag(v___x_5721_) == 0 {
                        lean_dec_ref_known(v___x_5721_, 1);
                        v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_5723_ = 1usize;
                        v___x_5724_ = lean_usize_add(v_i_5703_, v___x_5723_);
                        v___x_5725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_5700_, v_as_5701_, v_sz_5702_, v___x_5724_, v___x_5722_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
                        return v___x_5725_;
                    } else {
                        v_a_5726_ = lean_ctor_get(v___x_5721_, 0);
                        v_isSharedCheck_5733_ = (!lean_is_exclusive(v___x_5721_)) as u8;
                        if v_isSharedCheck_5733_ == 0 {
                            v___x_5728_ = v___x_5721_;
                            v_isShared_5729_ = v_isSharedCheck_5733_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_5726_);
                            lean_dec(v___x_5721_);
                            v___x_5728_ = lean_box(0);
                            v_isShared_5729_ = v_isSharedCheck_5733_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_5729_ == 0 {
                    v___x_5731_ = v___x_5728_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5732_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_a_5726_);
                    v___x_5731_ = v_reuseFailAlloc_5732_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_5731_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_____s_5734_: *mut LeanObject = *_args.add(0);
    let mut v_as_5735_: *mut LeanObject = *_args.add(1);
    let mut v_sz_5736_: *mut LeanObject = *_args.add(2);
    let mut v_i_5737_: *mut LeanObject = *_args.add(3);
    let mut v_b_5738_: *mut LeanObject = *_args.add(4);
    let mut v___y_5739_: *mut LeanObject = *_args.add(5);
    let mut v___y_5740_: *mut LeanObject = *_args.add(6);
    let mut v___y_5741_: *mut LeanObject = *_args.add(7);
    let mut v___y_5742_: *mut LeanObject = *_args.add(8);
    let mut v___y_5743_: *mut LeanObject = *_args.add(9);
    let mut v___y_5744_: *mut LeanObject = *_args.add(10);
    let mut v___y_5745_: *mut LeanObject = *_args.add(11);
    let mut v___y_5746_: *mut LeanObject = *_args.add(12);
    let mut v___y_5747_: *mut LeanObject = *_args.add(13);
    let mut v___y_5748_: *mut LeanObject = *_args.add(14);
    let mut v___y_5749_: *mut LeanObject = *_args.add(15);
    let mut v___y_5750_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_5751_: usize = 0;
    let mut v_i_boxed_5752_: usize = 0;
    let mut v_res_5753_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5751_ = lean_unbox_usize(v_sz_5736_);
    lean_dec(v_sz_5736_);
    v_i_boxed_5752_ = lean_unbox_usize(v_i_5737_);
    lean_dec(v_i_5737_);
    v_res_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_5734_, v_as_5735_, v_sz_boxed_5751_, v_i_boxed_5752_, v_b_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_);
    lean_dec(v___y_5749_);
    lean_dec_ref(v___y_5748_);
    lean_dec(v___y_5747_);
    lean_dec_ref(v___y_5746_);
    lean_dec(v___y_5745_);
    lean_dec_ref(v___y_5744_);
    lean_dec(v___y_5743_);
    lean_dec_ref(v___y_5742_);
    lean_dec(v___y_5741_);
    lean_dec(v___y_5740_);
    lean_dec(v___y_5739_);
    lean_dec_ref(v_as_5735_);
    lean_dec(v_____s_5734_);
    return v_res_5753_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(
    mut v_____s_5754_: *mut LeanObject,
    mut v_t_5755_: *mut LeanObject,
    mut v_init_5756_: *mut LeanObject,
    mut v___y_5757_: *mut LeanObject,
    mut v___y_5758_: *mut LeanObject,
    mut v___y_5759_: *mut LeanObject,
    mut v___y_5760_: *mut LeanObject,
    mut v___y_5761_: *mut LeanObject,
    mut v___y_5762_: *mut LeanObject,
    mut v___y_5763_: *mut LeanObject,
    mut v___y_5764_: *mut LeanObject,
    mut v___y_5765_: *mut LeanObject,
    mut v___y_5766_: *mut LeanObject,
    mut v___y_5767_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_5769_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_5770_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5772_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v_a_5776_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5779_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_5783_: usize = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5785_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5786_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5789_: u8 = 0;
    let mut v_fst_5790_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5791_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_5795_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5798_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5799_: u8 = 0;
    let mut v_a_5800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5806_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v_a_5809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5812_: u8 = 0;
    let mut v___x_5814_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5815_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5769_ = lean_ctor_get(v_t_5755_, 0);
                v_tail_5770_ = lean_ctor_get(v_t_5755_, 1);
                v___x_5771_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5756_, v_____s_5754_, v_root_5769_, v_init_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                if lean_obj_tag(v___x_5771_) == 0 {
                    v_a_5772_ = lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5808_ = (!lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5808_ == 0 {
                        v___x_5774_ = v___x_5771_;
                        v_isShared_5775_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_5772_);
                        lean_dec(v___x_5771_);
                        v___x_5774_ = lean_box(0);
                        v_isShared_5775_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5809_ = lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5816_ = (!lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5816_ == 0 {
                        v___x_5811_ = v___x_5771_;
                        v_isShared_5812_ = v_isSharedCheck_5816_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_5809_);
                        lean_dec(v___x_5771_);
                        v___x_5811_ = lean_box(0);
                        v_isShared_5812_ = v_isSharedCheck_5816_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_5772_) == 0 {
                    v_a_5776_ = lean_ctor_get(v_a_5772_, 0);
                    lean_inc(v_a_5776_);
                    lean_dec_ref_known(v_a_5772_, 1);
                    if v_isShared_5775_ == 0 {
                        lean_ctor_set(v___x_5774_, 0, v_a_5776_);
                        v___x_5778_ = v___x_5774_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5779_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_a_5776_);
                        v___x_5778_ = v_reuseFailAlloc_5779_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5774_);
                    v_a_5780_ = lean_ctor_get(v_a_5772_, 0);
                    lean_inc(v_a_5780_);
                    lean_dec_ref_known(v_a_5772_, 1);
                    v___x_5781_ = lean_box(0);
                    v___x_5782_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_5782_, 0, v___x_5781_);
                    lean_ctor_set(v___x_5782_, 1, v_a_5780_);
                    v_sz_5783_ = lean_array_size(v_tail_5770_);
                    v___x_5784_ = 0usize;
                    v___x_5785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_5754_, v_tail_5770_, v_sz_5783_, v___x_5784_, v___x_5782_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                    if lean_obj_tag(v___x_5785_) == 0 {
                        v_a_5786_ = lean_ctor_get(v___x_5785_, 0);
                        v_isSharedCheck_5799_ = (!lean_is_exclusive(v___x_5785_)) as u8;
                        if v_isSharedCheck_5799_ == 0 {
                            v___x_5788_ = v___x_5785_;
                            v_isShared_5789_ = v_isSharedCheck_5799_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_5786_);
                            lean_dec(v___x_5785_);
                            v___x_5788_ = lean_box(0);
                            v_isShared_5789_ = v_isSharedCheck_5799_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5800_ = lean_ctor_get(v___x_5785_, 0);
                        v_isSharedCheck_5807_ = (!lean_is_exclusive(v___x_5785_)) as u8;
                        if v_isSharedCheck_5807_ == 0 {
                            v___x_5802_ = v___x_5785_;
                            v_isShared_5803_ = v_isSharedCheck_5807_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_5800_);
                            lean_dec(v___x_5785_);
                            v___x_5802_ = lean_box(0);
                            v_isShared_5803_ = v_isSharedCheck_5807_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_5778_;
            }
            3 => {
                v_fst_5790_ = lean_ctor_get(v_a_5786_, 0);
                if lean_obj_tag(v_fst_5790_) == 0 {
                    v_snd_5791_ = lean_ctor_get(v_a_5786_, 1);
                    lean_inc(v_snd_5791_);
                    lean_dec(v_a_5786_);
                    if v_isShared_5789_ == 0 {
                        lean_ctor_set(v___x_5788_, 0, v_snd_5791_);
                        v___x_5793_ = v___x_5788_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5794_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_snd_5791_);
                        v___x_5793_ = v_reuseFailAlloc_5794_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_5790_);
                    lean_dec(v_a_5786_);
                    v_val_5795_ = lean_ctor_get(v_fst_5790_, 0);
                    lean_inc(v_val_5795_);
                    lean_dec_ref_known(v_fst_5790_, 1);
                    if v_isShared_5789_ == 0 {
                        lean_ctor_set(v___x_5788_, 0, v_val_5795_);
                        v___x_5797_ = v___x_5788_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5798_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_val_5795_);
                        v___x_5797_ = v_reuseFailAlloc_5798_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_5793_;
            }
            5 => {
                return v___x_5797_;
            }
            6 => {
                if v_isShared_5803_ == 0 {
                    v___x_5805_ = v___x_5802_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_5806_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
                    v___x_5805_ = v_reuseFailAlloc_5806_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_5805_;
            }
            8 => {
                if v_isShared_5812_ == 0 {
                    v___x_5814_ = v___x_5811_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_5815_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_a_5809_);
                    v___x_5814_ = v_reuseFailAlloc_5815_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_5814_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0___boxed(
    mut v_____s_5817_: *mut LeanObject,
    mut v_t_5818_: *mut LeanObject,
    mut v_init_5819_: *mut LeanObject,
    mut v___y_5820_: *mut LeanObject,
    mut v___y_5821_: *mut LeanObject,
    mut v___y_5822_: *mut LeanObject,
    mut v___y_5823_: *mut LeanObject,
    mut v___y_5824_: *mut LeanObject,
    mut v___y_5825_: *mut LeanObject,
    mut v___y_5826_: *mut LeanObject,
    mut v___y_5827_: *mut LeanObject,
    mut v___y_5828_: *mut LeanObject,
    mut v___y_5829_: *mut LeanObject,
    mut v___y_5830_: *mut LeanObject,
    mut v___y_5831_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_5832_: *mut LeanObject = core::ptr::null_mut();
    v_res_5832_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_____s_5817_, v_t_5818_, v_init_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
    lean_dec(v___y_5830_);
    lean_dec_ref(v___y_5829_);
    lean_dec(v___y_5828_);
    lean_dec_ref(v___y_5827_);
    lean_dec(v___y_5826_);
    lean_dec_ref(v___y_5825_);
    lean_dec(v___y_5824_);
    lean_dec_ref(v___y_5823_);
    lean_dec(v___y_5822_);
    lean_dec(v___y_5821_);
    lean_dec(v___y_5820_);
    lean_dec_ref(v_t_5818_);
    lean_dec(v_____s_5817_);
    return v_res_5832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(
    mut v_as_5833_: *mut LeanObject,
    mut v_sz_5834_: usize,
    mut v_i_5835_: usize,
    mut v_b_5836_: *mut LeanObject,
    mut v___y_5837_: *mut LeanObject,
    mut v___y_5838_: *mut LeanObject,
    mut v___y_5839_: *mut LeanObject,
    mut v___y_5840_: *mut LeanObject,
    mut v___y_5841_: *mut LeanObject,
    mut v___y_5842_: *mut LeanObject,
    mut v___y_5843_: *mut LeanObject,
    mut v___y_5844_: *mut LeanObject,
    mut v___y_5845_: *mut LeanObject,
    mut v___y_5846_: *mut LeanObject,
    mut v___y_5847_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5849_: u8 = 0;
    let mut v___x_5850_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5851_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5854_: u8 = 0;
    let mut v_a_5855_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: usize = 0;
    let mut v___x_5864_: usize = 0;
    let mut v_reuseFailAlloc_5866_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5867_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5872_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut v_isSharedCheck_5875_: u8 = 0;
    let mut v_unused_5876_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5849_ = lean_usize_dec_lt(v_i_5835_, v_sz_5834_);
                if v___x_5849_ == 0 {
                    v___x_5850_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5850_, 0, v_b_5836_);
                    return v___x_5850_;
                } else {
                    v_snd_5851_ = lean_ctor_get(v_b_5836_, 1);
                    v_isSharedCheck_5875_ = (!lean_is_exclusive(v_b_5836_)) as u8;
                    if v_isSharedCheck_5875_ == 0 {
                        v_unused_5876_ = lean_ctor_get(v_b_5836_, 0);
                        lean_dec(v_unused_5876_);
                        v___x_5853_ = v_b_5836_;
                        v_isShared_5854_ = v_isSharedCheck_5875_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5851_);
                        lean_dec(v_b_5836_);
                        v___x_5853_ = lean_box(0);
                        v_isShared_5854_ = v_isSharedCheck_5875_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5855_ = lean_array_uget_borrowed(v_as_5833_, v_i_5835_);
                v___x_5856_ = lean_box(0);
                v___x_5857_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5851_, v_a_5855_, v___x_5856_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
                if lean_obj_tag(v___x_5857_) == 0 {
                    lean_dec_ref_known(v___x_5857_, 1);
                    v___x_5858_ = lean_box(0);
                    v___x_5859_ = lean_unsigned_to_nat(1);
                    v___x_5860_ = lean_nat_add(v_snd_5851_, v___x_5859_);
                    lean_dec(v_snd_5851_);
                    if v_isShared_5854_ == 0 {
                        lean_ctor_set(v___x_5853_, 1, v___x_5860_);
                        lean_ctor_set(v___x_5853_, 0, v___x_5858_);
                        v___x_5862_ = v___x_5853_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5866_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___x_5858_);
                        lean_ctor_set(v_reuseFailAlloc_5866_, 1, v___x_5860_);
                        v___x_5862_ = v_reuseFailAlloc_5866_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5853_);
                    lean_dec(v_snd_5851_);
                    v_a_5867_ = lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5874_ = (!lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5874_ == 0 {
                        v___x_5869_ = v___x_5857_;
                        v_isShared_5870_ = v_isSharedCheck_5874_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5867_);
                        lean_dec(v___x_5857_);
                        v___x_5869_ = lean_box(0);
                        v_isShared_5870_ = v_isSharedCheck_5874_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5863_ = 1usize;
                v___x_5864_ = lean_usize_add(v_i_5835_, v___x_5863_);
                v_i_5835_ = v___x_5864_;
                v_b_5836_ = v___x_5862_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5870_ == 0 {
                    v___x_5872_ = v___x_5869_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5873_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
                    v___x_5872_ = v_reuseFailAlloc_5873_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5872_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10___boxed(
    mut v_as_5877_: *mut LeanObject,
    mut v_sz_5878_: *mut LeanObject,
    mut v_i_5879_: *mut LeanObject,
    mut v_b_5880_: *mut LeanObject,
    mut v___y_5881_: *mut LeanObject,
    mut v___y_5882_: *mut LeanObject,
    mut v___y_5883_: *mut LeanObject,
    mut v___y_5884_: *mut LeanObject,
    mut v___y_5885_: *mut LeanObject,
    mut v___y_5886_: *mut LeanObject,
    mut v___y_5887_: *mut LeanObject,
    mut v___y_5888_: *mut LeanObject,
    mut v___y_5889_: *mut LeanObject,
    mut v___y_5890_: *mut LeanObject,
    mut v___y_5891_: *mut LeanObject,
    mut v___y_5892_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5893_: usize = 0;
    let mut v_i_boxed_5894_: usize = 0;
    let mut v_res_5895_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5893_ = lean_unbox_usize(v_sz_5878_);
    lean_dec(v_sz_5878_);
    v_i_boxed_5894_ = lean_unbox_usize(v_i_5879_);
    lean_dec(v_i_5879_);
    v_res_5895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_5877_, v_sz_boxed_5893_, v_i_boxed_5894_, v_b_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
    lean_dec(v___y_5891_);
    lean_dec_ref(v___y_5890_);
    lean_dec(v___y_5889_);
    lean_dec_ref(v___y_5888_);
    lean_dec(v___y_5887_);
    lean_dec_ref(v___y_5886_);
    lean_dec(v___y_5885_);
    lean_dec_ref(v___y_5884_);
    lean_dec(v___y_5883_);
    lean_dec(v___y_5882_);
    lean_dec(v___y_5881_);
    lean_dec_ref(v_as_5877_);
    return v_res_5895_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(
    mut v_as_5896_: *mut LeanObject,
    mut v_sz_5897_: usize,
    mut v_i_5898_: usize,
    mut v_b_5899_: *mut LeanObject,
    mut v___y_5900_: *mut LeanObject,
    mut v___y_5901_: *mut LeanObject,
    mut v___y_5902_: *mut LeanObject,
    mut v___y_5903_: *mut LeanObject,
    mut v___y_5904_: *mut LeanObject,
    mut v___y_5905_: *mut LeanObject,
    mut v___y_5906_: *mut LeanObject,
    mut v___y_5907_: *mut LeanObject,
    mut v___y_5908_: *mut LeanObject,
    mut v___y_5909_: *mut LeanObject,
    mut v___y_5910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5912_: u8 = 0;
    let mut v___x_5913_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5914_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v_a_5918_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: usize = 0;
    let mut v___x_5927_: usize = 0;
    let mut v___x_5928_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5929_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5930_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5933_: u8 = 0;
    let mut v___x_5935_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5936_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5937_: u8 = 0;
    let mut v_isSharedCheck_5938_: u8 = 0;
    let mut v_unused_5939_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5912_ = lean_usize_dec_lt(v_i_5898_, v_sz_5897_);
                if v___x_5912_ == 0 {
                    v___x_5913_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5913_, 0, v_b_5899_);
                    return v___x_5913_;
                } else {
                    v_snd_5914_ = lean_ctor_get(v_b_5899_, 1);
                    v_isSharedCheck_5938_ = (!lean_is_exclusive(v_b_5899_)) as u8;
                    if v_isSharedCheck_5938_ == 0 {
                        v_unused_5939_ = lean_ctor_get(v_b_5899_, 0);
                        lean_dec(v_unused_5939_);
                        v___x_5916_ = v_b_5899_;
                        v_isShared_5917_ = v_isSharedCheck_5938_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5914_);
                        lean_dec(v_b_5899_);
                        v___x_5916_ = lean_box(0);
                        v_isShared_5917_ = v_isSharedCheck_5938_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5918_ = lean_array_uget_borrowed(v_as_5896_, v_i_5898_);
                v___x_5919_ = lean_box(0);
                v___x_5920_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5914_, v_a_5918_, v___x_5919_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
                if lean_obj_tag(v___x_5920_) == 0 {
                    lean_dec_ref_known(v___x_5920_, 1);
                    v___x_5921_ = lean_box(0);
                    v___x_5922_ = lean_unsigned_to_nat(1);
                    v___x_5923_ = lean_nat_add(v_snd_5914_, v___x_5922_);
                    lean_dec(v_snd_5914_);
                    if v_isShared_5917_ == 0 {
                        lean_ctor_set(v___x_5916_, 1, v___x_5923_);
                        lean_ctor_set(v___x_5916_, 0, v___x_5921_);
                        v___x_5925_ = v___x_5916_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5929_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5921_);
                        lean_ctor_set(v_reuseFailAlloc_5929_, 1, v___x_5923_);
                        v___x_5925_ = v_reuseFailAlloc_5929_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5916_);
                    lean_dec(v_snd_5914_);
                    v_a_5930_ = lean_ctor_get(v___x_5920_, 0);
                    v_isSharedCheck_5937_ = (!lean_is_exclusive(v___x_5920_)) as u8;
                    if v_isSharedCheck_5937_ == 0 {
                        v___x_5932_ = v___x_5920_;
                        v_isShared_5933_ = v_isSharedCheck_5937_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5930_);
                        lean_dec(v___x_5920_);
                        v___x_5932_ = lean_box(0);
                        v_isShared_5933_ = v_isSharedCheck_5937_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5926_ = 1usize;
                v___x_5927_ = lean_usize_add(v_i_5898_, v___x_5926_);
                v___x_5928_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_5896_, v_sz_5897_, v___x_5927_, v___x_5925_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
                return v___x_5928_;
            }
            3 => {
                if v_isShared_5933_ == 0 {
                    v___x_5935_ = v___x_5932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5936_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_a_5930_);
                    v___x_5935_ = v_reuseFailAlloc_5936_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5935_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4___boxed(
    mut v_as_5940_: *mut LeanObject,
    mut v_sz_5941_: *mut LeanObject,
    mut v_i_5942_: *mut LeanObject,
    mut v_b_5943_: *mut LeanObject,
    mut v___y_5944_: *mut LeanObject,
    mut v___y_5945_: *mut LeanObject,
    mut v___y_5946_: *mut LeanObject,
    mut v___y_5947_: *mut LeanObject,
    mut v___y_5948_: *mut LeanObject,
    mut v___y_5949_: *mut LeanObject,
    mut v___y_5950_: *mut LeanObject,
    mut v___y_5951_: *mut LeanObject,
    mut v___y_5952_: *mut LeanObject,
    mut v___y_5953_: *mut LeanObject,
    mut v___y_5954_: *mut LeanObject,
    mut v___y_5955_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_5956_: usize = 0;
    let mut v_i_boxed_5957_: usize = 0;
    let mut v_res_5958_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_5956_ = lean_unbox_usize(v_sz_5941_);
    lean_dec(v_sz_5941_);
    v_i_boxed_5957_ = lean_unbox_usize(v_i_5942_);
    lean_dec(v_i_5942_);
    v_res_5958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_as_5940_, v_sz_boxed_5956_, v_i_boxed_5957_, v_b_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
    lean_dec(v___y_5954_);
    lean_dec_ref(v___y_5953_);
    lean_dec(v___y_5952_);
    lean_dec_ref(v___y_5951_);
    lean_dec(v___y_5950_);
    lean_dec_ref(v___y_5949_);
    lean_dec(v___y_5948_);
    lean_dec_ref(v___y_5947_);
    lean_dec(v___y_5946_);
    lean_dec(v___y_5945_);
    lean_dec(v___y_5944_);
    lean_dec_ref(v_as_5940_);
    return v_res_5958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(
    mut v_as_5959_: *mut LeanObject,
    mut v_sz_5960_: usize,
    mut v_i_5961_: usize,
    mut v_b_5962_: *mut LeanObject,
    mut v___y_5963_: *mut LeanObject,
    mut v___y_5964_: *mut LeanObject,
    mut v___y_5965_: *mut LeanObject,
    mut v___y_5966_: *mut LeanObject,
    mut v___y_5967_: *mut LeanObject,
    mut v___y_5968_: *mut LeanObject,
    mut v___y_5969_: *mut LeanObject,
    mut v___y_5970_: *mut LeanObject,
    mut v___y_5971_: *mut LeanObject,
    mut v___y_5972_: *mut LeanObject,
    mut v___y_5973_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_5975_: u8 = 0;
    let mut v___x_5976_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_5977_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5980_: u8 = 0;
    let mut v_a_5981_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: usize = 0;
    let mut v___x_5990_: usize = 0;
    let mut v_reuseFailAlloc_5992_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_5993_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_5996_: u8 = 0;
    let mut v___x_5998_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut v_isSharedCheck_6001_: u8 = 0;
    let mut v_unused_6002_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5975_ = lean_usize_dec_lt(v_i_5961_, v_sz_5960_);
                if v___x_5975_ == 0 {
                    v___x_5976_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_5976_, 0, v_b_5962_);
                    return v___x_5976_;
                } else {
                    v_snd_5977_ = lean_ctor_get(v_b_5962_, 1);
                    v_isSharedCheck_6001_ = (!lean_is_exclusive(v_b_5962_)) as u8;
                    if v_isSharedCheck_6001_ == 0 {
                        v_unused_6002_ = lean_ctor_get(v_b_5962_, 0);
                        lean_dec(v_unused_6002_);
                        v___x_5979_ = v_b_5962_;
                        v_isShared_5980_ = v_isSharedCheck_6001_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_5977_);
                        lean_dec(v_b_5962_);
                        v___x_5979_ = lean_box(0);
                        v_isShared_5980_ = v_isSharedCheck_6001_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5981_ = lean_array_uget_borrowed(v_as_5959_, v_i_5961_);
                v___x_5982_ = lean_box(0);
                v___x_5983_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5977_, v_a_5981_, v___x_5982_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_);
                if lean_obj_tag(v___x_5983_) == 0 {
                    lean_dec_ref_known(v___x_5983_, 1);
                    v___x_5984_ = lean_box(0);
                    v___x_5985_ = lean_unsigned_to_nat(1);
                    v___x_5986_ = lean_nat_add(v_snd_5977_, v___x_5985_);
                    lean_dec(v_snd_5977_);
                    if v_isShared_5980_ == 0 {
                        lean_ctor_set(v___x_5979_, 1, v___x_5986_);
                        lean_ctor_set(v___x_5979_, 0, v___x_5984_);
                        v___x_5988_ = v___x_5979_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5992_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5984_);
                        lean_ctor_set(v_reuseFailAlloc_5992_, 1, v___x_5986_);
                        v___x_5988_ = v_reuseFailAlloc_5992_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_5979_);
                    lean_dec(v_snd_5977_);
                    v_a_5993_ = lean_ctor_get(v___x_5983_, 0);
                    v_isSharedCheck_6000_ = (!lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6000_ == 0 {
                        v___x_5995_ = v___x_5983_;
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_5993_);
                        lean_dec(v___x_5983_);
                        v___x_5995_ = lean_box(0);
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_5989_ = 1usize;
                v___x_5990_ = lean_usize_add(v_i_5961_, v___x_5989_);
                v_i_5961_ = v___x_5990_;
                v_b_5962_ = v___x_5988_;
                state = 0;
                continue;
            }
            3 => {
                if v_isShared_5996_ == 0 {
                    v___x_5998_ = v___x_5995_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5999_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5993_);
                    v___x_5998_ = v_reuseFailAlloc_5999_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_5998_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10___boxed(
    mut v_as_6003_: *mut LeanObject,
    mut v_sz_6004_: *mut LeanObject,
    mut v_i_6005_: *mut LeanObject,
    mut v_b_6006_: *mut LeanObject,
    mut v___y_6007_: *mut LeanObject,
    mut v___y_6008_: *mut LeanObject,
    mut v___y_6009_: *mut LeanObject,
    mut v___y_6010_: *mut LeanObject,
    mut v___y_6011_: *mut LeanObject,
    mut v___y_6012_: *mut LeanObject,
    mut v___y_6013_: *mut LeanObject,
    mut v___y_6014_: *mut LeanObject,
    mut v___y_6015_: *mut LeanObject,
    mut v___y_6016_: *mut LeanObject,
    mut v___y_6017_: *mut LeanObject,
    mut v___y_6018_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6019_: usize = 0;
    let mut v_i_boxed_6020_: usize = 0;
    let mut v_res_6021_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6019_ = lean_unbox_usize(v_sz_6004_);
    lean_dec(v_sz_6004_);
    v_i_boxed_6020_ = lean_unbox_usize(v_i_6005_);
    lean_dec(v_i_6005_);
    v_res_6021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_6003_, v_sz_boxed_6019_, v_i_boxed_6020_, v_b_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_);
    lean_dec(v___y_6017_);
    lean_dec_ref(v___y_6016_);
    lean_dec(v___y_6015_);
    lean_dec_ref(v___y_6014_);
    lean_dec(v___y_6013_);
    lean_dec_ref(v___y_6012_);
    lean_dec(v___y_6011_);
    lean_dec_ref(v___y_6010_);
    lean_dec(v___y_6009_);
    lean_dec(v___y_6008_);
    lean_dec(v___y_6007_);
    lean_dec_ref(v_as_6003_);
    return v_res_6021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(
    mut v_as_6022_: *mut LeanObject,
    mut v_sz_6023_: usize,
    mut v_i_6024_: usize,
    mut v_b_6025_: *mut LeanObject,
    mut v___y_6026_: *mut LeanObject,
    mut v___y_6027_: *mut LeanObject,
    mut v___y_6028_: *mut LeanObject,
    mut v___y_6029_: *mut LeanObject,
    mut v___y_6030_: *mut LeanObject,
    mut v___y_6031_: *mut LeanObject,
    mut v___y_6032_: *mut LeanObject,
    mut v___y_6033_: *mut LeanObject,
    mut v___y_6034_: *mut LeanObject,
    mut v___y_6035_: *mut LeanObject,
    mut v___y_6036_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6038_: u8 = 0;
    let mut v___x_6039_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6040_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v_a_6044_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: usize = 0;
    let mut v___x_6054_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v_isSharedCheck_6064_: u8 = 0;
    let mut v_unused_6065_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6038_ = lean_usize_dec_lt(v_i_6024_, v_sz_6023_);
                if v___x_6038_ == 0 {
                    v___x_6039_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6039_, 0, v_b_6025_);
                    return v___x_6039_;
                } else {
                    v_snd_6040_ = lean_ctor_get(v_b_6025_, 1);
                    v_isSharedCheck_6064_ = (!lean_is_exclusive(v_b_6025_)) as u8;
                    if v_isSharedCheck_6064_ == 0 {
                        v_unused_6065_ = lean_ctor_get(v_b_6025_, 0);
                        lean_dec(v_unused_6065_);
                        v___x_6042_ = v_b_6025_;
                        v_isShared_6043_ = v_isSharedCheck_6064_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6040_);
                        lean_dec(v_b_6025_);
                        v___x_6042_ = lean_box(0);
                        v_isShared_6043_ = v_isSharedCheck_6064_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6044_ = lean_array_uget_borrowed(v_as_6022_, v_i_6024_);
                v___x_6045_ = lean_box(0);
                v___x_6046_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_6040_, v_a_6044_, v___x_6045_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
                if lean_obj_tag(v___x_6046_) == 0 {
                    lean_dec_ref_known(v___x_6046_, 1);
                    v___x_6047_ = lean_box(0);
                    v___x_6048_ = lean_unsigned_to_nat(1);
                    v___x_6049_ = lean_nat_add(v_snd_6040_, v___x_6048_);
                    lean_dec(v_snd_6040_);
                    if v_isShared_6043_ == 0 {
                        lean_ctor_set(v___x_6042_, 1, v___x_6049_);
                        lean_ctor_set(v___x_6042_, 0, v___x_6047_);
                        v___x_6051_ = v___x_6042_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6055_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6047_);
                        lean_ctor_set(v_reuseFailAlloc_6055_, 1, v___x_6049_);
                        v___x_6051_ = v_reuseFailAlloc_6055_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6042_);
                    lean_dec(v_snd_6040_);
                    v_a_6056_ = lean_ctor_get(v___x_6046_, 0);
                    v_isSharedCheck_6063_ = (!lean_is_exclusive(v___x_6046_)) as u8;
                    if v_isSharedCheck_6063_ == 0 {
                        v___x_6058_ = v___x_6046_;
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6056_);
                        lean_dec(v___x_6046_);
                        v___x_6058_ = lean_box(0);
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                v___x_6052_ = 1usize;
                v___x_6053_ = lean_usize_add(v_i_6024_, v___x_6052_);
                v___x_6054_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_6022_, v_sz_6023_, v___x_6053_, v___x_6051_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
                return v___x_6054_;
            }
            3 => {
                if v_isShared_6059_ == 0 {
                    v___x_6061_ = v___x_6058_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6062_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
                    v___x_6061_ = v_reuseFailAlloc_6062_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6061_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8___boxed(
    mut v_as_6066_: *mut LeanObject,
    mut v_sz_6067_: *mut LeanObject,
    mut v_i_6068_: *mut LeanObject,
    mut v_b_6069_: *mut LeanObject,
    mut v___y_6070_: *mut LeanObject,
    mut v___y_6071_: *mut LeanObject,
    mut v___y_6072_: *mut LeanObject,
    mut v___y_6073_: *mut LeanObject,
    mut v___y_6074_: *mut LeanObject,
    mut v___y_6075_: *mut LeanObject,
    mut v___y_6076_: *mut LeanObject,
    mut v___y_6077_: *mut LeanObject,
    mut v___y_6078_: *mut LeanObject,
    mut v___y_6079_: *mut LeanObject,
    mut v___y_6080_: *mut LeanObject,
    mut v___y_6081_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_sz_boxed_6082_: usize = 0;
    let mut v_i_boxed_6083_: usize = 0;
    let mut v_res_6084_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6082_ = lean_unbox_usize(v_sz_6067_);
    lean_dec(v_sz_6067_);
    v_i_boxed_6083_ = lean_unbox_usize(v_i_6068_);
    lean_dec(v_i_6068_);
    v_res_6084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_6066_, v_sz_boxed_6082_, v_i_boxed_6083_, v_b_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
    lean_dec(v___y_6080_);
    lean_dec_ref(v___y_6079_);
    lean_dec(v___y_6078_);
    lean_dec_ref(v___y_6077_);
    lean_dec(v___y_6076_);
    lean_dec_ref(v___y_6075_);
    lean_dec(v___y_6074_);
    lean_dec_ref(v___y_6073_);
    lean_dec(v___y_6072_);
    lean_dec(v___y_6071_);
    lean_dec(v___y_6070_);
    lean_dec_ref(v_as_6066_);
    return v_res_6084_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(
    mut v_init_6085_: *mut LeanObject,
    mut v_n_6086_: *mut LeanObject,
    mut v_b_6087_: *mut LeanObject,
    mut v___y_6088_: *mut LeanObject,
    mut v___y_6089_: *mut LeanObject,
    mut v___y_6090_: *mut LeanObject,
    mut v___y_6091_: *mut LeanObject,
    mut v___y_6092_: *mut LeanObject,
    mut v___y_6093_: *mut LeanObject,
    mut v___y_6094_: *mut LeanObject,
    mut v___y_6095_: *mut LeanObject,
    mut v___y_6096_: *mut LeanObject,
    mut v___y_6097_: *mut LeanObject,
    mut v___y_6098_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_cs_6100_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6103_: usize = 0;
    let mut v___x_6104_: usize = 0;
    let mut v___x_6105_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6106_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6109_: u8 = 0;
    let mut v_fst_6110_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6111_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6115_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6119_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6120_: u8 = 0;
    let mut v_a_6121_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6124_: u8 = 0;
    let mut v___x_6126_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6127_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6128_: u8 = 0;
    let mut v_vs_6129_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6132_: usize = 0;
    let mut v___x_6133_: usize = 0;
    let mut v___x_6134_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6138_: u8 = 0;
    let mut v_fst_6139_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6140_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6144_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6145_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6148_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6149_: u8 = 0;
    let mut v_a_6150_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6153_: u8 = 0;
    let mut v___x_6155_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6156_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_n_6086_) == 0 {
                    v_cs_6100_ = lean_ctor_get(v_n_6086_, 0);
                    v___x_6101_ = lean_box(0);
                    v___x_6102_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6102_, 0, v___x_6101_);
                    lean_ctor_set(v___x_6102_, 1, v_b_6087_);
                    v_sz_6103_ = lean_array_size(v_cs_6100_);
                    v___x_6104_ = 0usize;
                    v___x_6105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_6085_, v_cs_6100_, v_sz_6103_, v___x_6104_, v___x_6102_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
                    if lean_obj_tag(v___x_6105_) == 0 {
                        v_a_6106_ = lean_ctor_get(v___x_6105_, 0);
                        v_isSharedCheck_6120_ = (!lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6120_ == 0 {
                            v___x_6108_ = v___x_6105_;
                            v_isShared_6109_ = v_isSharedCheck_6120_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6106_);
                            lean_dec(v___x_6105_);
                            v___x_6108_ = lean_box(0);
                            v_isShared_6109_ = v_isSharedCheck_6120_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6121_ = lean_ctor_get(v___x_6105_, 0);
                        v_isSharedCheck_6128_ = (!lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6128_ == 0 {
                            v___x_6123_ = v___x_6105_;
                            v_isShared_6124_ = v_isSharedCheck_6128_;
                            state = 4;
                            continue;
                        } else {
                            lean_inc(v_a_6121_);
                            lean_dec(v___x_6105_);
                            v___x_6123_ = lean_box(0);
                            v_isShared_6124_ = v_isSharedCheck_6128_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6129_ = lean_ctor_get(v_n_6086_, 0);
                    v___x_6130_ = lean_box(0);
                    v___x_6131_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6131_, 0, v___x_6130_);
                    lean_ctor_set(v___x_6131_, 1, v_b_6087_);
                    v_sz_6132_ = lean_array_size(v_vs_6129_);
                    v___x_6133_ = 0usize;
                    v___x_6134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_6129_, v_sz_6132_, v___x_6133_, v___x_6131_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
                    if lean_obj_tag(v___x_6134_) == 0 {
                        v_a_6135_ = lean_ctor_get(v___x_6134_, 0);
                        v_isSharedCheck_6149_ = (!lean_is_exclusive(v___x_6134_)) as u8;
                        if v_isSharedCheck_6149_ == 0 {
                            v___x_6137_ = v___x_6134_;
                            v_isShared_6138_ = v_isSharedCheck_6149_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6135_);
                            lean_dec(v___x_6134_);
                            v___x_6137_ = lean_box(0);
                            v_isShared_6138_ = v_isSharedCheck_6149_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6150_ = lean_ctor_get(v___x_6134_, 0);
                        v_isSharedCheck_6157_ = (!lean_is_exclusive(v___x_6134_)) as u8;
                        if v_isSharedCheck_6157_ == 0 {
                            v___x_6152_ = v___x_6134_;
                            v_isShared_6153_ = v_isSharedCheck_6157_;
                            state = 9;
                            continue;
                        } else {
                            lean_inc(v_a_6150_);
                            lean_dec(v___x_6134_);
                            v___x_6152_ = lean_box(0);
                            v_isShared_6153_ = v_isSharedCheck_6157_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6110_ = lean_ctor_get(v_a_6106_, 0);
                if lean_obj_tag(v_fst_6110_) == 0 {
                    v_snd_6111_ = lean_ctor_get(v_a_6106_, 1);
                    lean_inc(v_snd_6111_);
                    lean_dec(v_a_6106_);
                    v___x_6112_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6112_, 0, v_snd_6111_);
                    if v_isShared_6109_ == 0 {
                        lean_ctor_set(v___x_6108_, 0, v___x_6112_);
                        v___x_6114_ = v___x_6108_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6115_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6115_, 0, v___x_6112_);
                        v___x_6114_ = v_reuseFailAlloc_6115_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6110_);
                    lean_dec(v_a_6106_);
                    v_val_6116_ = lean_ctor_get(v_fst_6110_, 0);
                    lean_inc(v_val_6116_);
                    lean_dec_ref_known(v_fst_6110_, 1);
                    if v_isShared_6109_ == 0 {
                        lean_ctor_set(v___x_6108_, 0, v_val_6116_);
                        v___x_6118_ = v___x_6108_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6119_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_val_6116_);
                        v___x_6118_ = v_reuseFailAlloc_6119_;
                        state = 3;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6114_;
            }
            3 => {
                return v___x_6118_;
            }
            4 => {
                if v_isShared_6124_ == 0 {
                    v___x_6126_ = v___x_6123_;
                    state = 5;
                    continue;
                } else {
                    v_reuseFailAlloc_6127_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
                    v___x_6126_ = v_reuseFailAlloc_6127_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6126_;
            }
            6 => {
                v_fst_6139_ = lean_ctor_get(v_a_6135_, 0);
                if lean_obj_tag(v_fst_6139_) == 0 {
                    v_snd_6140_ = lean_ctor_get(v_a_6135_, 1);
                    lean_inc(v_snd_6140_);
                    lean_dec(v_a_6135_);
                    v___x_6141_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6141_, 0, v_snd_6140_);
                    if v_isShared_6138_ == 0 {
                        lean_ctor_set(v___x_6137_, 0, v___x_6141_);
                        v___x_6143_ = v___x_6137_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6144_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6144_, 0, v___x_6141_);
                        v___x_6143_ = v_reuseFailAlloc_6144_;
                        state = 7;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6139_);
                    lean_dec(v_a_6135_);
                    v_val_6145_ = lean_ctor_get(v_fst_6139_, 0);
                    lean_inc(v_val_6145_);
                    lean_dec_ref_known(v_fst_6139_, 1);
                    if v_isShared_6138_ == 0 {
                        lean_ctor_set(v___x_6137_, 0, v_val_6145_);
                        v___x_6147_ = v___x_6137_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6148_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6148_, 0, v_val_6145_);
                        v___x_6147_ = v_reuseFailAlloc_6148_;
                        state = 8;
                        continue;
                    }
                }
            }
            7 => {
                return v___x_6143_;
            }
            8 => {
                return v___x_6147_;
            }
            9 => {
                if v_isShared_6153_ == 0 {
                    v___x_6155_ = v___x_6152_;
                    state = 10;
                    continue;
                } else {
                    v_reuseFailAlloc_6156_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6150_);
                    v___x_6155_ = v_reuseFailAlloc_6156_;
                    state = 10;
                    continue;
                }
            }
            10 => {
                return v___x_6155_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(
    mut v_init_6158_: *mut LeanObject,
    mut v_as_6159_: *mut LeanObject,
    mut v_sz_6160_: usize,
    mut v_i_6161_: usize,
    mut v_b_6162_: *mut LeanObject,
    mut v___y_6163_: *mut LeanObject,
    mut v___y_6164_: *mut LeanObject,
    mut v___y_6165_: *mut LeanObject,
    mut v___y_6166_: *mut LeanObject,
    mut v___y_6167_: *mut LeanObject,
    mut v___y_6168_: *mut LeanObject,
    mut v___y_6169_: *mut LeanObject,
    mut v___y_6170_: *mut LeanObject,
    mut v___y_6171_: *mut LeanObject,
    mut v___y_6172_: *mut LeanObject,
    mut v___y_6173_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6175_: u8 = 0;
    let mut v___x_6176_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v_a_6181_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6183_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6186_: u8 = 0;
    let mut v___x_6187_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6193_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: usize = 0;
    let mut v___x_6199_: usize = 0;
    let mut v_reuseFailAlloc_6201_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6202_: u8 = 0;
    let mut v_a_6203_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6206_: u8 = 0;
    let mut v___x_6208_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_isSharedCheck_6211_: u8 = 0;
    let mut v_unused_6212_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6175_ = lean_usize_dec_lt(v_i_6161_, v_sz_6160_);
                if v___x_6175_ == 0 {
                    v___x_6176_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6176_, 0, v_b_6162_);
                    return v___x_6176_;
                } else {
                    v_snd_6177_ = lean_ctor_get(v_b_6162_, 1);
                    v_isSharedCheck_6211_ = (!lean_is_exclusive(v_b_6162_)) as u8;
                    if v_isSharedCheck_6211_ == 0 {
                        v_unused_6212_ = lean_ctor_get(v_b_6162_, 0);
                        lean_dec(v_unused_6212_);
                        v___x_6179_ = v_b_6162_;
                        v_isShared_6180_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_snd_6177_);
                        lean_dec(v_b_6162_);
                        v___x_6179_ = lean_box(0);
                        v_isShared_6180_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6181_ = lean_array_uget_borrowed(v_as_6159_, v_i_6161_);
                lean_inc(v_snd_6177_);
                v___x_6182_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6158_, v_a_6181_, v_snd_6177_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                if lean_obj_tag(v___x_6182_) == 0 {
                    v_a_6183_ = lean_ctor_get(v___x_6182_, 0);
                    v_isSharedCheck_6202_ = (!lean_is_exclusive(v___x_6182_)) as u8;
                    if v_isSharedCheck_6202_ == 0 {
                        v___x_6185_ = v___x_6182_;
                        v_isShared_6186_ = v_isSharedCheck_6202_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6183_);
                        lean_dec(v___x_6182_);
                        v___x_6185_ = lean_box(0);
                        v_isShared_6186_ = v_isSharedCheck_6202_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6179_);
                    lean_dec(v_snd_6177_);
                    v_a_6203_ = lean_ctor_get(v___x_6182_, 0);
                    v_isSharedCheck_6210_ = (!lean_is_exclusive(v___x_6182_)) as u8;
                    if v_isSharedCheck_6210_ == 0 {
                        v___x_6205_ = v___x_6182_;
                        v_isShared_6206_ = v_isSharedCheck_6210_;
                        state = 6;
                        continue;
                    } else {
                        lean_inc(v_a_6203_);
                        lean_dec(v___x_6182_);
                        v___x_6205_ = lean_box(0);
                        v_isShared_6206_ = v_isSharedCheck_6210_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if lean_obj_tag(v_a_6183_) == 0 {
                    v___x_6187_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6187_, 0, v_a_6183_);
                    if v_isShared_6180_ == 0 {
                        lean_ctor_set(v___x_6179_, 0, v___x_6187_);
                        v___x_6189_ = v___x_6179_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6193_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6187_);
                        lean_ctor_set(v_reuseFailAlloc_6193_, 1, v_snd_6177_);
                        v___x_6189_ = v_reuseFailAlloc_6193_;
                        state = 3;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6185_);
                    lean_dec(v_snd_6177_);
                    v_a_6194_ = lean_ctor_get(v_a_6183_, 0);
                    lean_inc(v_a_6194_);
                    lean_dec_ref_known(v_a_6183_, 1);
                    v___x_6195_ = lean_box(0);
                    if v_isShared_6180_ == 0 {
                        lean_ctor_set(v___x_6179_, 1, v_a_6194_);
                        lean_ctor_set(v___x_6179_, 0, v___x_6195_);
                        v___x_6197_ = v___x_6179_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6201_ = lean_alloc_ctor(0, 2, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6201_, 0, v___x_6195_);
                        lean_ctor_set(v_reuseFailAlloc_6201_, 1, v_a_6194_);
                        v___x_6197_ = v_reuseFailAlloc_6201_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6186_ == 0 {
                    lean_ctor_set(v___x_6185_, 0, v___x_6189_);
                    v___x_6191_ = v___x_6185_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6192_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6189_);
                    v___x_6191_ = v_reuseFailAlloc_6192_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6191_;
            }
            5 => {
                v___x_6198_ = 1usize;
                v___x_6199_ = lean_usize_add(v_i_6161_, v___x_6198_);
                v_i_6161_ = v___x_6199_;
                v_b_6162_ = v___x_6197_;
                state = 0;
                continue;
            }
            6 => {
                if v_isShared_6206_ == 0 {
                    v___x_6208_ = v___x_6205_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6209_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
                    v___x_6208_ = v_reuseFailAlloc_6209_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6208_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_init_6213_: *mut LeanObject = *_args.add(0);
    let mut v_as_6214_: *mut LeanObject = *_args.add(1);
    let mut v_sz_6215_: *mut LeanObject = *_args.add(2);
    let mut v_i_6216_: *mut LeanObject = *_args.add(3);
    let mut v_b_6217_: *mut LeanObject = *_args.add(4);
    let mut v___y_6218_: *mut LeanObject = *_args.add(5);
    let mut v___y_6219_: *mut LeanObject = *_args.add(6);
    let mut v___y_6220_: *mut LeanObject = *_args.add(7);
    let mut v___y_6221_: *mut LeanObject = *_args.add(8);
    let mut v___y_6222_: *mut LeanObject = *_args.add(9);
    let mut v___y_6223_: *mut LeanObject = *_args.add(10);
    let mut v___y_6224_: *mut LeanObject = *_args.add(11);
    let mut v___y_6225_: *mut LeanObject = *_args.add(12);
    let mut v___y_6226_: *mut LeanObject = *_args.add(13);
    let mut v___y_6227_: *mut LeanObject = *_args.add(14);
    let mut v___y_6228_: *mut LeanObject = *_args.add(15);
    let mut v___y_6229_: *mut LeanObject = *_args.add(16);
    let mut v_sz_boxed_6230_: usize = 0;
    let mut v_i_boxed_6231_: usize = 0;
    let mut v_res_6232_: *mut LeanObject = core::ptr::null_mut();
    v_sz_boxed_6230_ = lean_unbox_usize(v_sz_6215_);
    lean_dec(v_sz_6215_);
    v_i_boxed_6231_ = lean_unbox_usize(v_i_6216_);
    lean_dec(v_i_6216_);
    v_res_6232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_6213_, v_as_6214_, v_sz_boxed_6230_, v_i_boxed_6231_, v_b_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
    lean_dec(v___y_6228_);
    lean_dec_ref(v___y_6227_);
    lean_dec(v___y_6226_);
    lean_dec_ref(v___y_6225_);
    lean_dec(v___y_6224_);
    lean_dec_ref(v___y_6223_);
    lean_dec(v___y_6222_);
    lean_dec_ref(v___y_6221_);
    lean_dec(v___y_6220_);
    lean_dec(v___y_6219_);
    lean_dec(v___y_6218_);
    lean_dec_ref(v_as_6214_);
    lean_dec(v_init_6213_);
    return v_res_6232_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3___boxed(
    mut v_init_6233_: *mut LeanObject,
    mut v_n_6234_: *mut LeanObject,
    mut v_b_6235_: *mut LeanObject,
    mut v___y_6236_: *mut LeanObject,
    mut v___y_6237_: *mut LeanObject,
    mut v___y_6238_: *mut LeanObject,
    mut v___y_6239_: *mut LeanObject,
    mut v___y_6240_: *mut LeanObject,
    mut v___y_6241_: *mut LeanObject,
    mut v___y_6242_: *mut LeanObject,
    mut v___y_6243_: *mut LeanObject,
    mut v___y_6244_: *mut LeanObject,
    mut v___y_6245_: *mut LeanObject,
    mut v___y_6246_: *mut LeanObject,
    mut v___y_6247_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6248_: *mut LeanObject = core::ptr::null_mut();
    v_res_6248_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6233_, v_n_6234_, v_b_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
    lean_dec(v___y_6246_);
    lean_dec_ref(v___y_6245_);
    lean_dec(v___y_6244_);
    lean_dec_ref(v___y_6243_);
    lean_dec(v___y_6242_);
    lean_dec_ref(v___y_6241_);
    lean_dec(v___y_6240_);
    lean_dec_ref(v___y_6239_);
    lean_dec(v___y_6238_);
    lean_dec(v___y_6237_);
    lean_dec(v___y_6236_);
    lean_dec_ref(v_n_6234_);
    lean_dec(v_init_6233_);
    return v_res_6248_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(
    mut v_t_6249_: *mut LeanObject,
    mut v_init_6250_: *mut LeanObject,
    mut v___y_6251_: *mut LeanObject,
    mut v___y_6252_: *mut LeanObject,
    mut v___y_6253_: *mut LeanObject,
    mut v___y_6254_: *mut LeanObject,
    mut v___y_6255_: *mut LeanObject,
    mut v___y_6256_: *mut LeanObject,
    mut v___y_6257_: *mut LeanObject,
    mut v___y_6258_: *mut LeanObject,
    mut v___y_6259_: *mut LeanObject,
    mut v___y_6260_: *mut LeanObject,
    mut v___y_6261_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_root_6263_: *mut LeanObject = core::ptr::null_mut();
    let mut v_tail_6264_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6266_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6269_: u8 = 0;
    let mut v_a_6270_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6273_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6274_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut LeanObject = core::ptr::null_mut();
    let mut v_sz_6277_: usize = 0;
    let mut v___x_6278_: usize = 0;
    let mut v___x_6279_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6280_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v_fst_6284_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6285_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6288_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6289_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6292_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6293_: u8 = 0;
    let mut v_a_6294_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6297_: u8 = 0;
    let mut v___x_6299_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6301_: u8 = 0;
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v_a_6303_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6263_ = lean_ctor_get(v_t_6249_, 0);
                v_tail_6264_ = lean_ctor_get(v_t_6249_, 1);
                lean_inc(v_init_6250_);
                v___x_6265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6250_, v_root_6263_, v_init_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
                lean_dec(v_init_6250_);
                if lean_obj_tag(v___x_6265_) == 0 {
                    v_a_6266_ = lean_ctor_get(v___x_6265_, 0);
                    v_isSharedCheck_6302_ = (!lean_is_exclusive(v___x_6265_)) as u8;
                    if v_isSharedCheck_6302_ == 0 {
                        v___x_6268_ = v___x_6265_;
                        v_isShared_6269_ = v_isSharedCheck_6302_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6266_);
                        lean_dec(v___x_6265_);
                        v___x_6268_ = lean_box(0);
                        v_isShared_6269_ = v_isSharedCheck_6302_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6303_ = lean_ctor_get(v___x_6265_, 0);
                    v_isSharedCheck_6310_ = (!lean_is_exclusive(v___x_6265_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v___x_6305_ = v___x_6265_;
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6303_);
                        lean_dec(v___x_6265_);
                        v___x_6305_ = lean_box(0);
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6266_) == 0 {
                    v_a_6270_ = lean_ctor_get(v_a_6266_, 0);
                    lean_inc(v_a_6270_);
                    lean_dec_ref_known(v_a_6266_, 1);
                    if v_isShared_6269_ == 0 {
                        lean_ctor_set(v___x_6268_, 0, v_a_6270_);
                        v___x_6272_ = v___x_6268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6273_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6270_);
                        v___x_6272_ = v_reuseFailAlloc_6273_;
                        state = 2;
                        continue;
                    }
                } else {
                    lean_del_object(v___x_6268_);
                    v_a_6274_ = lean_ctor_get(v_a_6266_, 0);
                    lean_inc(v_a_6274_);
                    lean_dec_ref_known(v_a_6266_, 1);
                    v___x_6275_ = lean_box(0);
                    v___x_6276_ = lean_alloc_ctor(0, 2, (0) as u32);
                    lean_ctor_set(v___x_6276_, 0, v___x_6275_);
                    lean_ctor_set(v___x_6276_, 1, v_a_6274_);
                    v_sz_6277_ = lean_array_size(v_tail_6264_);
                    v___x_6278_ = 0usize;
                    v___x_6279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_tail_6264_, v_sz_6277_, v___x_6278_, v___x_6276_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
                    if lean_obj_tag(v___x_6279_) == 0 {
                        v_a_6280_ = lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6293_ = (!lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6293_ == 0 {
                            v___x_6282_ = v___x_6279_;
                            v_isShared_6283_ = v_isSharedCheck_6293_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6280_);
                            lean_dec(v___x_6279_);
                            v___x_6282_ = lean_box(0);
                            v_isShared_6283_ = v_isSharedCheck_6293_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6294_ = lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6301_ = (!lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6301_ == 0 {
                            v___x_6296_ = v___x_6279_;
                            v_isShared_6297_ = v_isSharedCheck_6301_;
                            state = 6;
                            continue;
                        } else {
                            lean_inc(v_a_6294_);
                            lean_dec(v___x_6279_);
                            v___x_6296_ = lean_box(0);
                            v_isShared_6297_ = v_isSharedCheck_6301_;
                            state = 6;
                            continue;
                        }
                    }
                }
            }
            2 => {
                return v___x_6272_;
            }
            3 => {
                v_fst_6284_ = lean_ctor_get(v_a_6280_, 0);
                if lean_obj_tag(v_fst_6284_) == 0 {
                    v_snd_6285_ = lean_ctor_get(v_a_6280_, 1);
                    lean_inc(v_snd_6285_);
                    lean_dec(v_a_6280_);
                    if v_isShared_6283_ == 0 {
                        lean_ctor_set(v___x_6282_, 0, v_snd_6285_);
                        v___x_6287_ = v___x_6282_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6288_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_snd_6285_);
                        v___x_6287_ = v_reuseFailAlloc_6288_;
                        state = 4;
                        continue;
                    }
                } else {
                    lean_inc_ref(v_fst_6284_);
                    lean_dec(v_a_6280_);
                    v_val_6289_ = lean_ctor_get(v_fst_6284_, 0);
                    lean_inc(v_val_6289_);
                    lean_dec_ref_known(v_fst_6284_, 1);
                    if v_isShared_6283_ == 0 {
                        lean_ctor_set(v___x_6282_, 0, v_val_6289_);
                        v___x_6291_ = v___x_6282_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6292_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6292_, 0, v_val_6289_);
                        v___x_6291_ = v_reuseFailAlloc_6292_;
                        state = 5;
                        continue;
                    }
                }
            }
            4 => {
                return v___x_6287_;
            }
            5 => {
                return v___x_6291_;
            }
            6 => {
                if v_isShared_6297_ == 0 {
                    v___x_6299_ = v___x_6296_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6300_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6300_, 0, v_a_6294_);
                    v___x_6299_ = v_reuseFailAlloc_6300_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6299_;
            }
            8 => {
                if v_isShared_6306_ == 0 {
                    v___x_6308_ = v___x_6305_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6309_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6303_);
                    v___x_6308_ = v_reuseFailAlloc_6309_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6308_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1___boxed(
    mut v_t_6311_: *mut LeanObject,
    mut v_init_6312_: *mut LeanObject,
    mut v___y_6313_: *mut LeanObject,
    mut v___y_6314_: *mut LeanObject,
    mut v___y_6315_: *mut LeanObject,
    mut v___y_6316_: *mut LeanObject,
    mut v___y_6317_: *mut LeanObject,
    mut v___y_6318_: *mut LeanObject,
    mut v___y_6319_: *mut LeanObject,
    mut v___y_6320_: *mut LeanObject,
    mut v___y_6321_: *mut LeanObject,
    mut v___y_6322_: *mut LeanObject,
    mut v___y_6323_: *mut LeanObject,
    mut v___y_6324_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6325_: *mut LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_t_6311_, v_init_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
    lean_dec(v___y_6323_);
    lean_dec_ref(v___y_6322_);
    lean_dec(v___y_6321_);
    lean_dec_ref(v___y_6320_);
    lean_dec(v___y_6319_);
    lean_dec_ref(v___y_6318_);
    lean_dec(v___y_6317_);
    lean_dec_ref(v___y_6316_);
    lean_dec(v___y_6315_);
    lean_dec(v___y_6314_);
    lean_dec(v___y_6313_);
    lean_dec_ref(v_t_6311_);
    return v_res_6325_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2()
-> *mut LeanObject {
    let mut v___x_6328_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut LeanObject = core::ptr::null_mut();
    v___x_6328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1;
    v___x_6329_ = lean_unsigned_to_nat(2);
    v___x_6330_ = lean_unsigned_to_nat(73);
    v___x_6331_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0;
    v___x_6332_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_6333_ = l_mkPanicMessageWithDecl(
        v___x_6332_,
        v___x_6331_,
        v___x_6330_,
        v___x_6329_,
        v___x_6328_,
    );
    return v___x_6333_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(
    mut v_a_6334_: *mut LeanObject,
    mut v_a_6335_: *mut LeanObject,
    mut v_a_6336_: *mut LeanObject,
    mut v_a_6337_: *mut LeanObject,
    mut v_a_6338_: *mut LeanObject,
    mut v_a_6339_: *mut LeanObject,
    mut v_a_6340_: *mut LeanObject,
    mut v_a_6341_: *mut LeanObject,
    mut v_a_6342_: *mut LeanObject,
    mut v_a_6343_: *mut LeanObject,
    mut v_a_6344_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6346_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6347_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_6348_: *mut LeanObject = core::ptr::null_mut();
    let mut v_diseqs_6349_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6350_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6351_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v___x_6360_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6363_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6364_: u8 = 0;
    let mut v_unused_6365_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6366_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6369_: u8 = 0;
    let mut v___x_6371_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6373_: u8 = 0;
    let mut v_a_6374_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6377_: u8 = 0;
    let mut v___x_6379_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6346_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_,
                    v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_,
                );
                if lean_obj_tag(v___x_6346_) == 0 {
                    v_a_6347_ = lean_ctor_get(v___x_6346_, 0);
                    lean_inc(v_a_6347_);
                    lean_dec_ref_known(v___x_6346_, 1);
                    v_vars_6348_ = lean_ctor_get(v_a_6347_, 30);
                    lean_inc_ref(v_vars_6348_);
                    v_diseqs_6349_ = lean_ctor_get(v_a_6347_, 34);
                    lean_inc_ref(v_diseqs_6349_);
                    lean_dec(v_a_6347_);
                    v_size_6350_ = lean_ctor_get(v_vars_6348_, 2);
                    lean_inc(v_size_6350_);
                    lean_dec_ref(v_vars_6348_);
                    v_size_6351_ = lean_ctor_get(v_diseqs_6349_, 2);
                    v___x_6352_ = lean_nat_dec_eq(v_size_6350_, v_size_6351_);
                    lean_dec(v_size_6350_);
                    if v___x_6352_ == 0 {
                        lean_dec_ref(v_diseqs_6349_);
                        v___x_6353_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2);
                        v___x_6354_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6353_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_);
                        return v___x_6354_;
                    } else {
                        v___x_6355_ = lean_unsigned_to_nat(0);
                        v___x_6356_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_diseqs_6349_, v___x_6355_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_);
                        lean_dec_ref(v_diseqs_6349_);
                        if lean_obj_tag(v___x_6356_) == 0 {
                            v_isSharedCheck_6364_ = (!lean_is_exclusive(v___x_6356_)) as u8;
                            if v_isSharedCheck_6364_ == 0 {
                                v_unused_6365_ = lean_ctor_get(v___x_6356_, 0);
                                lean_dec(v_unused_6365_);
                                v___x_6358_ = v___x_6356_;
                                v_isShared_6359_ = v_isSharedCheck_6364_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_6356_);
                                v___x_6358_ = lean_box(0);
                                v_isShared_6359_ = v_isSharedCheck_6364_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_6366_ = lean_ctor_get(v___x_6356_, 0);
                            v_isSharedCheck_6373_ = (!lean_is_exclusive(v___x_6356_)) as u8;
                            if v_isSharedCheck_6373_ == 0 {
                                v___x_6368_ = v___x_6356_;
                                v_isShared_6369_ = v_isSharedCheck_6373_;
                                state = 3;
                                continue;
                            } else {
                                lean_inc(v_a_6366_);
                                lean_dec(v___x_6356_);
                                v___x_6368_ = lean_box(0);
                                v_isShared_6369_ = v_isSharedCheck_6373_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_6374_ = lean_ctor_get(v___x_6346_, 0);
                    v_isSharedCheck_6381_ = (!lean_is_exclusive(v___x_6346_)) as u8;
                    if v_isSharedCheck_6381_ == 0 {
                        v___x_6376_ = v___x_6346_;
                        v_isShared_6377_ = v_isSharedCheck_6381_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6374_);
                        lean_dec(v___x_6346_);
                        v___x_6376_ = lean_box(0);
                        v_isShared_6377_ = v_isSharedCheck_6381_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6360_ = lean_box(0);
                if v_isShared_6359_ == 0 {
                    lean_ctor_set(v___x_6358_, 0, v___x_6360_);
                    v___x_6362_ = v___x_6358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6363_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6363_, 0, v___x_6360_);
                    v___x_6362_ = v_reuseFailAlloc_6363_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6362_;
            }
            3 => {
                if v_isShared_6369_ == 0 {
                    v___x_6371_ = v___x_6368_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6372_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_a_6366_);
                    v___x_6371_ = v_reuseFailAlloc_6372_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6371_;
            }
            5 => {
                if v_isShared_6377_ == 0 {
                    v___x_6379_ = v___x_6376_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6380_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_a_6374_);
                    v___x_6379_ = v_reuseFailAlloc_6380_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6379_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___boxed(
    mut v_a_6382_: *mut LeanObject,
    mut v_a_6383_: *mut LeanObject,
    mut v_a_6384_: *mut LeanObject,
    mut v_a_6385_: *mut LeanObject,
    mut v_a_6386_: *mut LeanObject,
    mut v_a_6387_: *mut LeanObject,
    mut v_a_6388_: *mut LeanObject,
    mut v_a_6389_: *mut LeanObject,
    mut v_a_6390_: *mut LeanObject,
    mut v_a_6391_: *mut LeanObject,
    mut v_a_6392_: *mut LeanObject,
    mut v_a_6393_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6394_: *mut LeanObject = core::ptr::null_mut();
    v_res_6394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_6382_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
    lean_dec(v_a_6392_);
    lean_dec_ref(v_a_6391_);
    lean_dec(v_a_6390_);
    lean_dec_ref(v_a_6389_);
    lean_dec(v_a_6388_);
    lean_dec_ref(v_a_6387_);
    lean_dec(v_a_6386_);
    lean_dec_ref(v_a_6385_);
    lean_dec(v_a_6384_);
    lean_dec(v_a_6383_);
    lean_dec(v_a_6382_);
    return v_res_6394_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0()
-> *mut LeanObject {
    let mut v___x_6395_: *mut LeanObject = core::ptr::null_mut();
    v___x_6395_ = l_Lean_Meta_Grind_instInhabitedGoalM(lean_box(0));
    return v___x_6395_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(
    mut v_msg_6396_: *mut LeanObject,
    mut v___y_6397_: *mut LeanObject,
    mut v___y_6398_: *mut LeanObject,
    mut v___y_6399_: *mut LeanObject,
    mut v___y_6400_: *mut LeanObject,
    mut v___y_6401_: *mut LeanObject,
    mut v___y_6402_: *mut LeanObject,
    mut v___y_6403_: *mut LeanObject,
    mut v___y_6404_: *mut LeanObject,
    mut v___y_6405_: *mut LeanObject,
    mut v___y_6406_: *mut LeanObject,
    mut v___y_6407_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6409_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6410_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_5472__overap_6411_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut LeanObject = core::ptr::null_mut();
    v___x_6409_ = lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0);
    v___f_6410_ = lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    lean_closure_set(v___f_6410_, 0, v___x_6409_);
    v___x_5472__overap_6411_ = lean_panic_fn_borrowed(v___f_6410_, v_msg_6396_);
    lean_dec_ref(v___f_6410_);
    lean_inc(v___y_6407_);
    lean_inc_ref(v___y_6406_);
    lean_inc(v___y_6405_);
    lean_inc_ref(v___y_6404_);
    lean_inc(v___y_6403_);
    lean_inc_ref(v___y_6402_);
    lean_inc(v___y_6401_);
    lean_inc_ref(v___y_6400_);
    lean_inc(v___y_6399_);
    lean_inc(v___y_6398_);
    lean_inc(v___y_6397_);
    v___x_6412_ = lean_apply_12(
        v___x_5472__overap_6411_,
        v___y_6397_,
        v___y_6398_,
        v___y_6399_,
        v___y_6400_,
        v___y_6401_,
        v___y_6402_,
        v___y_6403_,
        v___y_6404_,
        v___y_6405_,
        v___y_6406_,
        v___y_6407_,
        lean_box(0),
    );
    return v___x_6412_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___boxed(
    mut v_msg_6413_: *mut LeanObject,
    mut v___y_6414_: *mut LeanObject,
    mut v___y_6415_: *mut LeanObject,
    mut v___y_6416_: *mut LeanObject,
    mut v___y_6417_: *mut LeanObject,
    mut v___y_6418_: *mut LeanObject,
    mut v___y_6419_: *mut LeanObject,
    mut v___y_6420_: *mut LeanObject,
    mut v___y_6421_: *mut LeanObject,
    mut v___y_6422_: *mut LeanObject,
    mut v___y_6423_: *mut LeanObject,
    mut v___y_6424_: *mut LeanObject,
    mut v___y_6425_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6426_: *mut LeanObject = core::ptr::null_mut();
    v_res_6426_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v_msg_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_);
    lean_dec(v___y_6424_);
    lean_dec_ref(v___y_6423_);
    lean_dec(v___y_6422_);
    lean_dec_ref(v___y_6421_);
    lean_dec(v___y_6420_);
    lean_dec_ref(v___y_6419_);
    lean_dec(v___y_6418_);
    lean_dec_ref(v___y_6417_);
    lean_dec(v___y_6416_);
    lean_dec(v___y_6415_);
    lean_dec(v___y_6414_);
    return v_res_6426_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1()
-> *mut LeanObject {
    let mut v___x_6428_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut LeanObject = core::ptr::null_mut();
    v___x_6428_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_6429_ = lean_unsigned_to_nat(6);
    v___x_6430_ = lean_unsigned_to_nat(89);
    v___x_6431_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0;
    v___x_6432_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_6433_ = l_mkPanicMessageWithDecl(
        v___x_6432_,
        v___x_6431_,
        v___x_6430_,
        v___x_6429_,
        v___x_6428_,
    );
    return v___x_6433_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3()
-> *mut LeanObject {
    let mut v___x_6435_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut LeanObject = core::ptr::null_mut();
    v___x_6435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2;
    v___x_6436_ = lean_unsigned_to_nat(6);
    v___x_6437_ = lean_unsigned_to_nat(87);
    v___x_6438_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0;
    v___x_6439_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_6440_ = l_mkPanicMessageWithDecl(
        v___x_6439_,
        v___x_6438_,
        v___x_6437_,
        v___x_6436_,
        v___x_6435_,
    );
    return v___x_6440_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(
    mut v_vars_6441_: *mut LeanObject,
    mut v_x_6442_: *mut LeanObject,
    mut v_____s_6443_: *mut LeanObject,
    mut v___y_6444_: *mut LeanObject,
    mut v___y_6445_: *mut LeanObject,
    mut v___y_6446_: *mut LeanObject,
    mut v___y_6447_: *mut LeanObject,
    mut v___y_6448_: *mut LeanObject,
    mut v___y_6449_: *mut LeanObject,
    mut v___y_6450_: *mut LeanObject,
    mut v___y_6451_: *mut LeanObject,
    mut v___y_6452_: *mut LeanObject,
    mut v___y_6453_: *mut LeanObject,
    mut v___y_6454_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6457_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut LeanObject = core::ptr::null_mut();
    let mut v_fst_6461_: *mut LeanObject = core::ptr::null_mut();
    let mut v_snd_6462_: *mut LeanObject = core::ptr::null_mut();
    let mut v_size_6463_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: u8 = 0;
    let mut v___x_6465_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6467_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6470_: u8 = 0;
    let mut v___x_6472_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6473_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6474_: u8 = 0;
    let mut v___x_6475_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6461_ = lean_ctor_get(v_x_6442_, 0);
                v_snd_6462_ = lean_ctor_get(v_x_6442_, 1);
                v_size_6463_ = lean_ctor_get(v_vars_6441_, 2);
                v___x_6464_ = lean_nat_dec_lt(v_snd_6462_, v_size_6463_);
                if v___x_6464_ == 0 {
                    v___x_6465_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1);
                    v___x_6466_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6465_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
                    if lean_obj_tag(v___x_6466_) == 0 {
                        lean_dec_ref_known(v___x_6466_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_6467_ = lean_ctor_get(v___x_6466_, 0);
                        v_isSharedCheck_6474_ = (!lean_is_exclusive(v___x_6466_)) as u8;
                        if v_isSharedCheck_6474_ == 0 {
                            v___x_6469_ = v___x_6466_;
                            v_isShared_6470_ = v_isSharedCheck_6474_;
                            state = 2;
                            continue;
                        } else {
                            lean_inc(v_a_6467_);
                            lean_dec(v___x_6466_);
                            v___x_6469_ = lean_box(0);
                            v_isShared_6470_ = v_isSharedCheck_6474_;
                            state = 2;
                            continue;
                        }
                    }
                } else {
                    v___x_6475_ = l_Lean_instInhabitedExpr;
                    v___x_6476_ = l_Lean_PersistentArray_get_x21___redArg(
                        v___x_6475_,
                        v_vars_6441_,
                        v_snd_6462_,
                    );
                    v___x_6477_ =
                        l___private_Lean_Meta_Sym_ExprPtr_0__Lean_Meta_Sym_isSameExpr_unsafe__1(
                            v_fst_6461_,
                            v___x_6476_,
                        );
                    lean_dec(v___x_6476_);
                    if v___x_6477_ == 0 {
                        v___x_6478_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3);
                        v___x_6479_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v___x_6478_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
                        return v___x_6479_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6457_ = lean_unsigned_to_nat(1);
                v___x_6458_ = lean_nat_add(v_____s_6443_, v___x_6457_);
                v___x_6459_ = lean_alloc_ctor(1, 1, (0) as u32);
                lean_ctor_set(v___x_6459_, 0, v___x_6458_);
                v___x_6460_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6460_, 0, v___x_6459_);
                return v___x_6460_;
            }
            2 => {
                if v_isShared_6470_ == 0 {
                    v___x_6472_ = v___x_6469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6473_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6467_);
                    v___x_6472_ = v_reuseFailAlloc_6473_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                return v___x_6472_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed(
    mut v_vars_6480_: *mut LeanObject,
    mut v_x_6481_: *mut LeanObject,
    mut v_____s_6482_: *mut LeanObject,
    mut v___y_6483_: *mut LeanObject,
    mut v___y_6484_: *mut LeanObject,
    mut v___y_6485_: *mut LeanObject,
    mut v___y_6486_: *mut LeanObject,
    mut v___y_6487_: *mut LeanObject,
    mut v___y_6488_: *mut LeanObject,
    mut v___y_6489_: *mut LeanObject,
    mut v___y_6490_: *mut LeanObject,
    mut v___y_6491_: *mut LeanObject,
    mut v___y_6492_: *mut LeanObject,
    mut v___y_6493_: *mut LeanObject,
    mut v___y_6494_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6495_: *mut LeanObject = core::ptr::null_mut();
    v_res_6495_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(v_vars_6480_, v_x_6481_, v_____s_6482_, v___y_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_);
    lean_dec(v___y_6493_);
    lean_dec_ref(v___y_6492_);
    lean_dec(v___y_6491_);
    lean_dec_ref(v___y_6490_);
    lean_dec(v___y_6489_);
    lean_dec_ref(v___y_6488_);
    lean_dec(v___y_6487_);
    lean_dec_ref(v___y_6486_);
    lean_dec(v___y_6485_);
    lean_dec(v___y_6484_);
    lean_dec(v___y_6483_);
    lean_dec(v_____s_6482_);
    lean_dec_ref(v_x_6481_);
    lean_dec_ref(v_vars_6480_);
    return v_res_6495_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(
    mut v_f_6496_: *mut LeanObject,
    mut v_s_6497_: *mut LeanObject,
    mut v_a_6498_: *mut LeanObject,
    mut v_b_6499_: *mut LeanObject,
    mut v___y_6500_: *mut LeanObject,
    mut v___y_6501_: *mut LeanObject,
    mut v___y_6502_: *mut LeanObject,
    mut v___y_6503_: *mut LeanObject,
    mut v___y_6504_: *mut LeanObject,
    mut v___y_6505_: *mut LeanObject,
    mut v___y_6506_: *mut LeanObject,
    mut v___y_6507_: *mut LeanObject,
    mut v___y_6508_: *mut LeanObject,
    mut v___y_6509_: *mut LeanObject,
    mut v___y_6510_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6512_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6514_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6517_: u8 = 0;
    let mut v_a_6518_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6521_: u8 = 0;
    let mut v___x_6523_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_a_6529_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___x_6534_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6537_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
    let mut v_isSharedCheck_6540_: u8 = 0;
    let mut v_a_6541_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6544_: u8 = 0;
    let mut v___x_6546_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6512_ = lean_alloc_ctor(0, 2, (0) as u32);
                lean_ctor_set(v___x_6512_, 0, v_a_6498_);
                lean_ctor_set(v___x_6512_, 1, v_b_6499_);
                lean_inc(v___y_6510_);
                lean_inc_ref(v___y_6509_);
                lean_inc(v___y_6508_);
                lean_inc_ref(v___y_6507_);
                lean_inc(v___y_6506_);
                lean_inc_ref(v___y_6505_);
                lean_inc(v___y_6504_);
                lean_inc_ref(v___y_6503_);
                lean_inc(v___y_6502_);
                lean_inc(v___y_6501_);
                lean_inc(v___y_6500_);
                v___x_6513_ = lean_apply_14(
                    v_f_6496_,
                    v___x_6512_,
                    v_s_6497_,
                    v___y_6500_,
                    v___y_6501_,
                    v___y_6502_,
                    v___y_6503_,
                    v___y_6504_,
                    v___y_6505_,
                    v___y_6506_,
                    v___y_6507_,
                    v___y_6508_,
                    v___y_6509_,
                    v___y_6510_,
                    lean_box(0),
                );
                if lean_obj_tag(v___x_6513_) == 0 {
                    v_a_6514_ = lean_ctor_get(v___x_6513_, 0);
                    v_isSharedCheck_6540_ = (!lean_is_exclusive(v___x_6513_)) as u8;
                    if v_isSharedCheck_6540_ == 0 {
                        v___x_6516_ = v___x_6513_;
                        v_isShared_6517_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6514_);
                        lean_dec(v___x_6513_);
                        v___x_6516_ = lean_box(0);
                        v_isShared_6517_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6541_ = lean_ctor_get(v___x_6513_, 0);
                    v_isSharedCheck_6548_ = (!lean_is_exclusive(v___x_6513_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v___x_6543_ = v___x_6513_;
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 8;
                        continue;
                    } else {
                        lean_inc(v_a_6541_);
                        lean_dec(v___x_6513_);
                        v___x_6543_ = lean_box(0);
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v_a_6514_) == 0 {
                    v_a_6518_ = lean_ctor_get(v_a_6514_, 0);
                    v_isSharedCheck_6528_ = (!lean_is_exclusive(v_a_6514_)) as u8;
                    if v_isSharedCheck_6528_ == 0 {
                        v___x_6520_ = v_a_6514_;
                        v_isShared_6521_ = v_isSharedCheck_6528_;
                        state = 2;
                        continue;
                    } else {
                        lean_inc(v_a_6518_);
                        lean_dec(v_a_6514_);
                        v___x_6520_ = lean_box(0);
                        v_isShared_6521_ = v_isSharedCheck_6528_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6529_ = lean_ctor_get(v_a_6514_, 0);
                    v_isSharedCheck_6539_ = (!lean_is_exclusive(v_a_6514_)) as u8;
                    if v_isSharedCheck_6539_ == 0 {
                        v___x_6531_ = v_a_6514_;
                        v_isShared_6532_ = v_isSharedCheck_6539_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6529_);
                        lean_dec(v_a_6514_);
                        v___x_6531_ = lean_box(0);
                        v_isShared_6532_ = v_isSharedCheck_6539_;
                        state = 5;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_6521_ == 0 {
                    v___x_6523_ = v___x_6520_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6527_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6518_);
                    v___x_6523_ = v_reuseFailAlloc_6527_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6517_ == 0 {
                    lean_ctor_set(v___x_6516_, 0, v___x_6523_);
                    v___x_6525_ = v___x_6516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6526_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6526_, 0, v___x_6523_);
                    v___x_6525_ = v_reuseFailAlloc_6526_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6525_;
            }
            5 => {
                if v_isShared_6532_ == 0 {
                    v___x_6534_ = v___x_6531_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6538_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6529_);
                    v___x_6534_ = v_reuseFailAlloc_6538_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6517_ == 0 {
                    lean_ctor_set(v___x_6516_, 0, v___x_6534_);
                    v___x_6536_ = v___x_6516_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6537_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6537_, 0, v___x_6534_);
                    v___x_6536_ = v_reuseFailAlloc_6537_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                return v___x_6536_;
            }
            8 => {
                if v_isShared_6544_ == 0 {
                    v___x_6546_ = v___x_6543_;
                    state = 9;
                    continue;
                } else {
                    v_reuseFailAlloc_6547_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
                    v___x_6546_ = v_reuseFailAlloc_6547_;
                    state = 9;
                    continue;
                }
            }
            9 => {
                return v___x_6546_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed(
    mut v_f_6549_: *mut LeanObject,
    mut v_s_6550_: *mut LeanObject,
    mut v_a_6551_: *mut LeanObject,
    mut v_b_6552_: *mut LeanObject,
    mut v___y_6553_: *mut LeanObject,
    mut v___y_6554_: *mut LeanObject,
    mut v___y_6555_: *mut LeanObject,
    mut v___y_6556_: *mut LeanObject,
    mut v___y_6557_: *mut LeanObject,
    mut v___y_6558_: *mut LeanObject,
    mut v___y_6559_: *mut LeanObject,
    mut v___y_6560_: *mut LeanObject,
    mut v___y_6561_: *mut LeanObject,
    mut v___y_6562_: *mut LeanObject,
    mut v___y_6563_: *mut LeanObject,
    mut v___y_6564_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6565_: *mut LeanObject = core::ptr::null_mut();
    v_res_6565_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(v_f_6549_, v_s_6550_, v_a_6551_, v_b_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_);
    lean_dec(v___y_6563_);
    lean_dec_ref(v___y_6562_);
    lean_dec(v___y_6561_);
    lean_dec_ref(v___y_6560_);
    lean_dec(v___y_6559_);
    lean_dec_ref(v___y_6558_);
    lean_dec(v___y_6557_);
    lean_dec_ref(v___y_6556_);
    lean_dec(v___y_6555_);
    lean_dec(v___y_6554_);
    lean_dec(v___y_6553_);
    return v_res_6565_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_f_6566_: *mut LeanObject,
    mut v_keys_6567_: *mut LeanObject,
    mut v_vals_6568_: *mut LeanObject,
    mut v_i_6569_: *mut LeanObject,
    mut v_acc_6570_: *mut LeanObject,
    mut v___y_6571_: *mut LeanObject,
    mut v___y_6572_: *mut LeanObject,
    mut v___y_6573_: *mut LeanObject,
    mut v___y_6574_: *mut LeanObject,
    mut v___y_6575_: *mut LeanObject,
    mut v___y_6576_: *mut LeanObject,
    mut v___y_6577_: *mut LeanObject,
    mut v___y_6578_: *mut LeanObject,
    mut v___y_6579_: *mut LeanObject,
    mut v___y_6580_: *mut LeanObject,
    mut v___y_6581_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6583_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut LeanObject = core::ptr::null_mut();
    let mut v_k_6587_: *mut LeanObject = core::ptr::null_mut();
    let mut v_v_6588_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6590_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6591_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6583_ = lean_array_get_size(v_keys_6567_);
                v___x_6584_ = lean_nat_dec_lt(v_i_6569_, v___x_6583_);
                if v___x_6584_ == 0 {
                    lean_dec(v_i_6569_);
                    lean_dec_ref(v_f_6566_);
                    v___x_6585_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6585_, 0, v_acc_6570_);
                    v___x_6586_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6586_, 0, v___x_6585_);
                    return v___x_6586_;
                } else {
                    v_k_6587_ = lean_array_fget_borrowed(v_keys_6567_, v_i_6569_);
                    v_v_6588_ = lean_array_fget_borrowed(v_vals_6568_, v_i_6569_);
                    lean_inc_ref(v_f_6566_);
                    lean_inc(v___y_6581_);
                    lean_inc_ref(v___y_6580_);
                    lean_inc(v___y_6579_);
                    lean_inc_ref(v___y_6578_);
                    lean_inc(v___y_6577_);
                    lean_inc_ref(v___y_6576_);
                    lean_inc(v___y_6575_);
                    lean_inc_ref(v___y_6574_);
                    lean_inc(v___y_6573_);
                    lean_inc(v___y_6572_);
                    lean_inc(v___y_6571_);
                    lean_inc(v_v_6588_);
                    lean_inc(v_k_6587_);
                    v___x_6589_ = lean_apply_15(
                        v_f_6566_,
                        v_acc_6570_,
                        v_k_6587_,
                        v_v_6588_,
                        v___y_6571_,
                        v___y_6572_,
                        v___y_6573_,
                        v___y_6574_,
                        v___y_6575_,
                        v___y_6576_,
                        v___y_6577_,
                        v___y_6578_,
                        v___y_6579_,
                        v___y_6580_,
                        v___y_6581_,
                        lean_box(0),
                    );
                    if lean_obj_tag(v___x_6589_) == 0 {
                        v_a_6590_ = lean_ctor_get(v___x_6589_, 0);
                        lean_inc(v_a_6590_);
                        if lean_obj_tag(v_a_6590_) == 0 {
                            lean_dec_ref_known(v_a_6590_, 1);
                            lean_dec(v_i_6569_);
                            lean_dec_ref(v_f_6566_);
                            return v___x_6589_;
                        } else {
                            lean_dec_ref_known(v___x_6589_, 1);
                            v_a_6591_ = lean_ctor_get(v_a_6590_, 0);
                            lean_inc(v_a_6591_);
                            lean_dec_ref_known(v_a_6590_, 1);
                            v___x_6592_ = lean_unsigned_to_nat(1);
                            v___x_6593_ = lean_nat_add(v_i_6569_, v___x_6592_);
                            lean_dec(v_i_6569_);
                            v_i_6569_ = v___x_6593_;
                            v_acc_6570_ = v_a_6591_;
                            state = 0;
                            continue;
                        }
                    } else {
                        lean_dec(v_i_6569_);
                        lean_dec_ref(v_f_6566_);
                        return v___x_6589_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_6595_: *mut LeanObject = *_args.add(0);
    let mut v_keys_6596_: *mut LeanObject = *_args.add(1);
    let mut v_vals_6597_: *mut LeanObject = *_args.add(2);
    let mut v_i_6598_: *mut LeanObject = *_args.add(3);
    let mut v_acc_6599_: *mut LeanObject = *_args.add(4);
    let mut v___y_6600_: *mut LeanObject = *_args.add(5);
    let mut v___y_6601_: *mut LeanObject = *_args.add(6);
    let mut v___y_6602_: *mut LeanObject = *_args.add(7);
    let mut v___y_6603_: *mut LeanObject = *_args.add(8);
    let mut v___y_6604_: *mut LeanObject = *_args.add(9);
    let mut v___y_6605_: *mut LeanObject = *_args.add(10);
    let mut v___y_6606_: *mut LeanObject = *_args.add(11);
    let mut v___y_6607_: *mut LeanObject = *_args.add(12);
    let mut v___y_6608_: *mut LeanObject = *_args.add(13);
    let mut v___y_6609_: *mut LeanObject = *_args.add(14);
    let mut v___y_6610_: *mut LeanObject = *_args.add(15);
    let mut v___y_6611_: *mut LeanObject = *_args.add(16);
    let mut v_res_6612_: *mut LeanObject = core::ptr::null_mut();
    v_res_6612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_6595_, v_keys_6596_, v_vals_6597_, v_i_6598_, v_acc_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
    lean_dec(v___y_6610_);
    lean_dec_ref(v___y_6609_);
    lean_dec(v___y_6608_);
    lean_dec_ref(v___y_6607_);
    lean_dec(v___y_6606_);
    lean_dec_ref(v___y_6605_);
    lean_dec(v___y_6604_);
    lean_dec_ref(v___y_6603_);
    lean_dec(v___y_6602_);
    lean_dec(v___y_6601_);
    lean_dec(v___y_6600_);
    lean_dec_ref(v_vals_6597_);
    lean_dec_ref(v_keys_6596_);
    return v_res_6612_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(
    mut v_f_6613_: *mut LeanObject,
    mut v_x_6614_: *mut LeanObject,
    mut v_x_6615_: *mut LeanObject,
    mut v___y_6616_: *mut LeanObject,
    mut v___y_6617_: *mut LeanObject,
    mut v___y_6618_: *mut LeanObject,
    mut v___y_6619_: *mut LeanObject,
    mut v___y_6620_: *mut LeanObject,
    mut v___y_6621_: *mut LeanObject,
    mut v___y_6622_: *mut LeanObject,
    mut v___y_6623_: *mut LeanObject,
    mut v___y_6624_: *mut LeanObject,
    mut v___y_6625_: *mut LeanObject,
    mut v___y_6626_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_es_6628_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6631_: u8 = 0;
    let mut v___x_6632_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: u8 = 0;
    let mut v___x_6636_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: u8 = 0;
    let mut v___x_6641_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6643_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: usize = 0;
    let mut v___x_6645_: usize = 0;
    let mut v___x_6646_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: usize = 0;
    let mut v___x_6648_: usize = 0;
    let mut v___x_6649_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6650_: u8 = 0;
    let mut v_ks_6651_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vs_6652_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if lean_obj_tag(v_x_6614_) == 0 {
                    v_es_6628_ = lean_ctor_get(v_x_6614_, 0);
                    v_isSharedCheck_6650_ = (!lean_is_exclusive(v_x_6614_)) as u8;
                    if v_isSharedCheck_6650_ == 0 {
                        v___x_6630_ = v_x_6614_;
                        v_isShared_6631_ = v_isSharedCheck_6650_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_es_6628_);
                        lean_dec(v_x_6614_);
                        v___x_6630_ = lean_box(0);
                        v_isShared_6631_ = v_isSharedCheck_6650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_6651_ = lean_ctor_get(v_x_6614_, 0);
                    lean_inc_ref(v_ks_6651_);
                    v_vs_6652_ = lean_ctor_get(v_x_6614_, 1);
                    lean_inc_ref(v_vs_6652_);
                    lean_dec_ref_known(v_x_6614_, 2);
                    v___x_6653_ = lean_unsigned_to_nat(0);
                    v___x_6654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_6613_, v_ks_6651_, v_vs_6652_, v___x_6653_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                    lean_dec_ref(v_vs_6652_);
                    lean_dec_ref(v_ks_6651_);
                    return v___x_6654_;
                }
            }
            1 => {
                v___x_6632_ = lean_unsigned_to_nat(0);
                v___x_6633_ = lean_array_get_size(v_es_6628_);
                v___x_6634_ = lean_nat_dec_lt(v___x_6632_, v___x_6633_);
                if v___x_6634_ == 0 {
                    lean_dec_ref(v_es_6628_);
                    lean_dec_ref(v_f_6613_);
                    if v_isShared_6631_ == 0 {
                        lean_ctor_set_tag(v___x_6630_, 1);
                        lean_ctor_set(v___x_6630_, 0, v_x_6615_);
                        v___x_6636_ = v___x_6630_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6638_ = lean_alloc_ctor(1, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_x_6615_);
                        v___x_6636_ = v_reuseFailAlloc_6638_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6639_ = lean_nat_dec_le(v___x_6633_, v___x_6633_);
                    if v___x_6639_ == 0 {
                        if v___x_6634_ == 0 {
                            lean_dec_ref(v_es_6628_);
                            lean_dec_ref(v_f_6613_);
                            if v_isShared_6631_ == 0 {
                                lean_ctor_set_tag(v___x_6630_, 1);
                                lean_ctor_set(v___x_6630_, 0, v_x_6615_);
                                v___x_6641_ = v___x_6630_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6643_ = lean_alloc_ctor(1, 1, (0) as u32);
                                lean_ctor_set(v_reuseFailAlloc_6643_, 0, v_x_6615_);
                                v___x_6641_ = v_reuseFailAlloc_6643_;
                                state = 3;
                                continue;
                            }
                        } else {
                            lean_del_object(v___x_6630_);
                            v___x_6644_ = 0usize;
                            v___x_6645_ = lean_usize_of_nat(v___x_6633_);
                            v___x_6646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6613_, v_es_6628_, v___x_6644_, v___x_6645_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                            lean_dec_ref(v_es_6628_);
                            return v___x_6646_;
                        }
                    } else {
                        lean_del_object(v___x_6630_);
                        v___x_6647_ = 0usize;
                        v___x_6648_ = lean_usize_of_nat(v___x_6633_);
                        v___x_6649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6613_, v_es_6628_, v___x_6647_, v___x_6648_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                        lean_dec_ref(v_es_6628_);
                        return v___x_6649_;
                    }
                }
            }
            2 => {
                v___x_6637_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6637_, 0, v___x_6636_);
                return v___x_6637_;
            }
            3 => {
                v___x_6642_ = lean_alloc_ctor(0, 1, (0) as u32);
                lean_ctor_set(v___x_6642_, 0, v___x_6641_);
                return v___x_6642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_f_6655_: *mut LeanObject,
    mut v_as_6656_: *mut LeanObject,
    mut v_i_6657_: usize,
    mut v_stop_6658_: usize,
    mut v_b_6659_: *mut LeanObject,
    mut v___y_6660_: *mut LeanObject,
    mut v___y_6661_: *mut LeanObject,
    mut v___y_6662_: *mut LeanObject,
    mut v___y_6663_: *mut LeanObject,
    mut v___y_6664_: *mut LeanObject,
    mut v___y_6665_: *mut LeanObject,
    mut v___y_6666_: *mut LeanObject,
    mut v___y_6667_: *mut LeanObject,
    mut v___y_6668_: *mut LeanObject,
    mut v___y_6669_: *mut LeanObject,
    mut v___y_6670_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_a_6673_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: usize = 0;
    let mut v___x_6675_: usize = 0;
    let mut v___y_6678_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6679_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6680_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: u8 = 0;
    let mut v___x_6682_: *mut LeanObject = core::ptr::null_mut();
    let mut v_key_6683_: *mut LeanObject = core::ptr::null_mut();
    let mut v_val_6684_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut LeanObject = core::ptr::null_mut();
    let mut v_node_6686_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6681_ = lean_usize_dec_eq(v_i_6657_, v_stop_6658_);
                if v___x_6681_ == 0 {
                    v___x_6682_ = lean_array_uget_borrowed(v_as_6656_, v_i_6657_);
                    match lean_obj_tag(v___x_6682_) {
                        0 => {
                            v_key_6683_ = lean_ctor_get(v___x_6682_, 0);
                            v_val_6684_ = lean_ctor_get(v___x_6682_, 1);
                            lean_inc_ref(v_f_6655_);
                            lean_inc(v___y_6670_);
                            lean_inc_ref(v___y_6669_);
                            lean_inc(v___y_6668_);
                            lean_inc_ref(v___y_6667_);
                            lean_inc(v___y_6666_);
                            lean_inc_ref(v___y_6665_);
                            lean_inc(v___y_6664_);
                            lean_inc_ref(v___y_6663_);
                            lean_inc(v___y_6662_);
                            lean_inc(v___y_6661_);
                            lean_inc(v___y_6660_);
                            lean_inc(v_val_6684_);
                            lean_inc(v_key_6683_);
                            v___x_6685_ = lean_apply_15(
                                v_f_6655_,
                                v_b_6659_,
                                v_key_6683_,
                                v_val_6684_,
                                v___y_6660_,
                                v___y_6661_,
                                v___y_6662_,
                                v___y_6663_,
                                v___y_6664_,
                                v___y_6665_,
                                v___y_6666_,
                                v___y_6667_,
                                v___y_6668_,
                                v___y_6669_,
                                v___y_6670_,
                                lean_box(0),
                            );
                            v___y_6678_ = v___x_6685_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_6686_ = lean_ctor_get(v___x_6682_, 0);
                            lean_inc(v_node_6686_);
                            lean_inc_ref(v_f_6655_);
                            v___x_6687_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6655_, v_node_6686_, v_b_6659_, v___y_6660_, v___y_6661_, v___y_6662_, v___y_6663_, v___y_6664_, v___y_6665_, v___y_6666_, v___y_6667_, v___y_6668_, v___y_6669_, v___y_6670_);
                            v___y_6678_ = v___x_6687_;
                            state = 2;
                            continue;
                        }
                        _ => {
                            v_a_6673_ = v_b_6659_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    lean_dec_ref(v_f_6655_);
                    v___x_6688_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v___x_6688_, 0, v_b_6659_);
                    v___x_6689_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_6689_, 0, v___x_6688_);
                    return v___x_6689_;
                }
            }
            1 => {
                v___x_6674_ = 1usize;
                v___x_6675_ = lean_usize_add(v_i_6657_, v___x_6674_);
                v_i_6657_ = v___x_6675_;
                v_b_6659_ = v_a_6673_;
                state = 0;
                continue;
            }
            2 => {
                if lean_obj_tag(v___y_6678_) == 0 {
                    v_a_6679_ = lean_ctor_get(v___y_6678_, 0);
                    if lean_obj_tag(v_a_6679_) == 0 {
                        lean_dec_ref(v_f_6655_);
                        return v___y_6678_;
                    } else {
                        lean_inc_ref(v_a_6679_);
                        lean_dec_ref_known(v___y_6678_, 1);
                        v_a_6680_ = lean_ctor_get(v_a_6679_, 0);
                        lean_inc(v_a_6680_);
                        lean_dec_ref_known(v_a_6679_, 1);
                        v_a_6673_ = v_a_6680_;
                        state = 1;
                        continue;
                    }
                } else {
                    lean_dec_ref(v_f_6655_);
                    return v___y_6678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_f_6690_: *mut LeanObject = *_args.add(0);
    let mut v_as_6691_: *mut LeanObject = *_args.add(1);
    let mut v_i_6692_: *mut LeanObject = *_args.add(2);
    let mut v_stop_6693_: *mut LeanObject = *_args.add(3);
    let mut v_b_6694_: *mut LeanObject = *_args.add(4);
    let mut v___y_6695_: *mut LeanObject = *_args.add(5);
    let mut v___y_6696_: *mut LeanObject = *_args.add(6);
    let mut v___y_6697_: *mut LeanObject = *_args.add(7);
    let mut v___y_6698_: *mut LeanObject = *_args.add(8);
    let mut v___y_6699_: *mut LeanObject = *_args.add(9);
    let mut v___y_6700_: *mut LeanObject = *_args.add(10);
    let mut v___y_6701_: *mut LeanObject = *_args.add(11);
    let mut v___y_6702_: *mut LeanObject = *_args.add(12);
    let mut v___y_6703_: *mut LeanObject = *_args.add(13);
    let mut v___y_6704_: *mut LeanObject = *_args.add(14);
    let mut v___y_6705_: *mut LeanObject = *_args.add(15);
    let mut v___y_6706_: *mut LeanObject = *_args.add(16);
    let mut v_i_boxed_6707_: usize = 0;
    let mut v_stop_boxed_6708_: usize = 0;
    let mut v_res_6709_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_6707_ = lean_unbox_usize(v_i_6692_);
    lean_dec(v_i_6692_);
    v_stop_boxed_6708_ = lean_unbox_usize(v_stop_6693_);
    lean_dec(v_stop_6693_);
    v_res_6709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6690_, v_as_6691_, v_i_boxed_6707_, v_stop_boxed_6708_, v_b_6694_, v___y_6695_, v___y_6696_, v___y_6697_, v___y_6698_, v___y_6699_, v___y_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
    lean_dec(v___y_6705_);
    lean_dec_ref(v___y_6704_);
    lean_dec(v___y_6703_);
    lean_dec_ref(v___y_6702_);
    lean_dec(v___y_6701_);
    lean_dec_ref(v___y_6700_);
    lean_dec(v___y_6699_);
    lean_dec_ref(v___y_6698_);
    lean_dec(v___y_6697_);
    lean_dec(v___y_6696_);
    lean_dec(v___y_6695_);
    lean_dec_ref(v_as_6691_);
    return v_res_6709_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_6710_: *mut LeanObject,
    mut v_x_6711_: *mut LeanObject,
    mut v_x_6712_: *mut LeanObject,
    mut v___y_6713_: *mut LeanObject,
    mut v___y_6714_: *mut LeanObject,
    mut v___y_6715_: *mut LeanObject,
    mut v___y_6716_: *mut LeanObject,
    mut v___y_6717_: *mut LeanObject,
    mut v___y_6718_: *mut LeanObject,
    mut v___y_6719_: *mut LeanObject,
    mut v___y_6720_: *mut LeanObject,
    mut v___y_6721_: *mut LeanObject,
    mut v___y_6722_: *mut LeanObject,
    mut v___y_6723_: *mut LeanObject,
    mut v___y_6724_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6725_: *mut LeanObject = core::ptr::null_mut();
    v_res_6725_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6710_, v_x_6711_, v_x_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
    lean_dec(v___y_6723_);
    lean_dec_ref(v___y_6722_);
    lean_dec(v___y_6721_);
    lean_dec_ref(v___y_6720_);
    lean_dec(v___y_6719_);
    lean_dec_ref(v___y_6718_);
    lean_dec(v___y_6717_);
    lean_dec_ref(v___y_6716_);
    lean_dec(v___y_6715_);
    lean_dec(v___y_6714_);
    lean_dec(v___y_6713_);
    return v_res_6725_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(
    mut v_map_6726_: *mut LeanObject,
    mut v_init_6727_: *mut LeanObject,
    mut v_f_6728_: *mut LeanObject,
    mut v___y_6729_: *mut LeanObject,
    mut v___y_6730_: *mut LeanObject,
    mut v___y_6731_: *mut LeanObject,
    mut v___y_6732_: *mut LeanObject,
    mut v___y_6733_: *mut LeanObject,
    mut v___y_6734_: *mut LeanObject,
    mut v___y_6735_: *mut LeanObject,
    mut v___y_6736_: *mut LeanObject,
    mut v___y_6737_: *mut LeanObject,
    mut v___y_6738_: *mut LeanObject,
    mut v___y_6739_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___f_6741_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6743_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6746_: u8 = 0;
    let mut v_a_6747_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6751_: u8 = 0;
    let mut v_a_6752_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6755_: u8 = 0;
    let mut v___x_6757_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6758_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6741_ = lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 1);
                lean_closure_set(v___f_6741_, 0, v_f_6728_);
                lean_inc_ref(v_map_6726_);
                v___x_6742_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v___f_6741_, v_map_6726_, v_init_6727_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_, v___y_6734_, v___y_6735_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_);
                if lean_obj_tag(v___x_6742_) == 0 {
                    v_a_6743_ = lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6751_ = (!lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6751_ == 0 {
                        v___x_6745_ = v___x_6742_;
                        v_isShared_6746_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    } else {
                        lean_inc(v_a_6743_);
                        lean_dec(v___x_6742_);
                        v___x_6745_ = lean_box(0);
                        v_isShared_6746_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6752_ = lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6759_ = (!lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6759_ == 0 {
                        v___x_6754_ = v___x_6742_;
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 3;
                        continue;
                    } else {
                        lean_inc(v_a_6752_);
                        lean_dec(v___x_6742_);
                        v___x_6754_ = lean_box(0);
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6747_ = lean_ctor_get(v_a_6743_, 0);
                lean_inc(v_a_6747_);
                lean_dec(v_a_6743_);
                if v_isShared_6746_ == 0 {
                    lean_ctor_set(v___x_6745_, 0, v_a_6747_);
                    v___x_6749_ = v___x_6745_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6750_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_a_6747_);
                    v___x_6749_ = v_reuseFailAlloc_6750_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_6749_;
            }
            3 => {
                if v_isShared_6755_ == 0 {
                    v___x_6757_ = v___x_6754_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6758_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6752_);
                    v___x_6757_ = v_reuseFailAlloc_6758_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6757_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___boxed(
    mut v_map_6760_: *mut LeanObject,
    mut v_init_6761_: *mut LeanObject,
    mut v_f_6762_: *mut LeanObject,
    mut v___y_6763_: *mut LeanObject,
    mut v___y_6764_: *mut LeanObject,
    mut v___y_6765_: *mut LeanObject,
    mut v___y_6766_: *mut LeanObject,
    mut v___y_6767_: *mut LeanObject,
    mut v___y_6768_: *mut LeanObject,
    mut v___y_6769_: *mut LeanObject,
    mut v___y_6770_: *mut LeanObject,
    mut v___y_6771_: *mut LeanObject,
    mut v___y_6772_: *mut LeanObject,
    mut v___y_6773_: *mut LeanObject,
    mut v___y_6774_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6775_: *mut LeanObject = core::ptr::null_mut();
    v_res_6775_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_6760_, v_init_6761_, v_f_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_, v___y_6773_);
    lean_dec(v___y_6773_);
    lean_dec_ref(v___y_6772_);
    lean_dec(v___y_6771_);
    lean_dec_ref(v___y_6770_);
    lean_dec(v___y_6769_);
    lean_dec_ref(v___y_6768_);
    lean_dec(v___y_6767_);
    lean_dec_ref(v___y_6766_);
    lean_dec(v___y_6765_);
    lean_dec(v___y_6764_);
    lean_dec(v___y_6763_);
    lean_dec_ref(v_map_6760_);
    return v_res_6775_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1()
-> *mut LeanObject {
    let mut v___x_6777_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut LeanObject = core::ptr::null_mut();
    v___x_6777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0;
    v___x_6778_ = lean_unsigned_to_nat(2);
    v___x_6779_ = lean_unsigned_to_nat(91);
    v___x_6780_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0;
    v___x_6781_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_6782_ = l_mkPanicMessageWithDecl(
        v___x_6781_,
        v___x_6780_,
        v___x_6779_,
        v___x_6778_,
        v___x_6777_,
    );
    return v___x_6782_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(
    mut v_a_6783_: *mut LeanObject,
    mut v_a_6784_: *mut LeanObject,
    mut v_a_6785_: *mut LeanObject,
    mut v_a_6786_: *mut LeanObject,
    mut v_a_6787_: *mut LeanObject,
    mut v_a_6788_: *mut LeanObject,
    mut v_a_6789_: *mut LeanObject,
    mut v_a_6790_: *mut LeanObject,
    mut v_a_6791_: *mut LeanObject,
    mut v_a_6792_: *mut LeanObject,
    mut v_a_6793_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6795_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6796_: *mut LeanObject = core::ptr::null_mut();
    let mut v_vars_6797_: *mut LeanObject = core::ptr::null_mut();
    let mut v_varMap_6798_: *mut LeanObject = core::ptr::null_mut();
    let mut v___f_6799_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_6802_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6805_: u8 = 0;
    let mut v_size_6806_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    let mut v___x_6808_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6813_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6814_: u8 = 0;
    let mut v_a_6815_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6818_: u8 = 0;
    let mut v___x_6820_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6821_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6822_: u8 = 0;
    let mut v_a_6823_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_6826_: u8 = 0;
    let mut v___x_6828_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6829_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6795_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_,
                    v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_,
                );
                if lean_obj_tag(v___x_6795_) == 0 {
                    v_a_6796_ = lean_ctor_get(v___x_6795_, 0);
                    lean_inc(v_a_6796_);
                    lean_dec_ref_known(v___x_6795_, 1);
                    v_vars_6797_ = lean_ctor_get(v_a_6796_, 30);
                    lean_inc_ref_n(v_vars_6797_, 2);
                    v_varMap_6798_ = lean_ctor_get(v_a_6796_, 31);
                    lean_inc_ref(v_varMap_6798_);
                    lean_dec(v_a_6796_);
                    v___f_6799_ = lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed as *mut core::ffi::c_void, 15, 1);
                    lean_closure_set(v___f_6799_, 0, v_vars_6797_);
                    v___x_6800_ = lean_unsigned_to_nat(0);
                    v___x_6801_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_varMap_6798_, v___x_6800_, v___f_6799_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
                    lean_dec_ref(v_varMap_6798_);
                    if lean_obj_tag(v___x_6801_) == 0 {
                        v_a_6802_ = lean_ctor_get(v___x_6801_, 0);
                        v_isSharedCheck_6814_ = (!lean_is_exclusive(v___x_6801_)) as u8;
                        if v_isSharedCheck_6814_ == 0 {
                            v___x_6804_ = v___x_6801_;
                            v_isShared_6805_ = v_isSharedCheck_6814_;
                            state = 1;
                            continue;
                        } else {
                            lean_inc(v_a_6802_);
                            lean_dec(v___x_6801_);
                            v___x_6804_ = lean_box(0);
                            v_isShared_6805_ = v_isSharedCheck_6814_;
                            state = 1;
                            continue;
                        }
                    } else {
                        lean_dec_ref(v_vars_6797_);
                        v_a_6815_ = lean_ctor_get(v___x_6801_, 0);
                        v_isSharedCheck_6822_ = (!lean_is_exclusive(v___x_6801_)) as u8;
                        if v_isSharedCheck_6822_ == 0 {
                            v___x_6817_ = v___x_6801_;
                            v_isShared_6818_ = v_isSharedCheck_6822_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_6815_);
                            lean_dec(v___x_6801_);
                            v___x_6817_ = lean_box(0);
                            v_isShared_6818_ = v_isSharedCheck_6822_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_6823_ = lean_ctor_get(v___x_6795_, 0);
                    v_isSharedCheck_6830_ = (!lean_is_exclusive(v___x_6795_)) as u8;
                    if v_isSharedCheck_6830_ == 0 {
                        v___x_6825_ = v___x_6795_;
                        v_isShared_6826_ = v_isSharedCheck_6830_;
                        state = 5;
                        continue;
                    } else {
                        lean_inc(v_a_6823_);
                        lean_dec(v___x_6795_);
                        v___x_6825_ = lean_box(0);
                        v_isShared_6826_ = v_isSharedCheck_6830_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_size_6806_ = lean_ctor_get(v_vars_6797_, 2);
                lean_inc(v_size_6806_);
                lean_dec_ref(v_vars_6797_);
                v___x_6807_ = lean_nat_dec_eq(v_size_6806_, v_a_6802_);
                lean_dec(v_a_6802_);
                lean_dec(v_size_6806_);
                if v___x_6807_ == 0 {
                    lean_del_object(v___x_6804_);
                    v___x_6808_ = lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1);
                    v___x_6809_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6808_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
                    return v___x_6809_;
                } else {
                    v___x_6810_ = lean_box(0);
                    if v_isShared_6805_ == 0 {
                        lean_ctor_set(v___x_6804_, 0, v___x_6810_);
                        v___x_6812_ = v___x_6804_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6813_ = lean_alloc_ctor(0, 1, (0) as u32);
                        lean_ctor_set(v_reuseFailAlloc_6813_, 0, v___x_6810_);
                        v___x_6812_ = v_reuseFailAlloc_6813_;
                        state = 2;
                        continue;
                    }
                }
            }
            2 => {
                return v___x_6812_;
            }
            3 => {
                if v_isShared_6818_ == 0 {
                    v___x_6820_ = v___x_6817_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6821_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_a_6815_);
                    v___x_6820_ = v_reuseFailAlloc_6821_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_6820_;
            }
            5 => {
                if v_isShared_6826_ == 0 {
                    v___x_6828_ = v___x_6825_;
                    state = 6;
                    continue;
                } else {
                    v_reuseFailAlloc_6829_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_6829_, 0, v_a_6823_);
                    v___x_6828_ = v_reuseFailAlloc_6829_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                return v___x_6828_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___boxed(
    mut v_a_6831_: *mut LeanObject,
    mut v_a_6832_: *mut LeanObject,
    mut v_a_6833_: *mut LeanObject,
    mut v_a_6834_: *mut LeanObject,
    mut v_a_6835_: *mut LeanObject,
    mut v_a_6836_: *mut LeanObject,
    mut v_a_6837_: *mut LeanObject,
    mut v_a_6838_: *mut LeanObject,
    mut v_a_6839_: *mut LeanObject,
    mut v_a_6840_: *mut LeanObject,
    mut v_a_6841_: *mut LeanObject,
    mut v_a_6842_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6843_: *mut LeanObject = core::ptr::null_mut();
    v_res_6843_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_6831_, v_a_6832_, v_a_6833_, v_a_6834_, v_a_6835_, v_a_6836_, v_a_6837_, v_a_6838_, v_a_6839_, v_a_6840_, v_a_6841_);
    lean_dec(v_a_6841_);
    lean_dec_ref(v_a_6840_);
    lean_dec(v_a_6839_);
    lean_dec_ref(v_a_6838_);
    lean_dec(v_a_6837_);
    lean_dec_ref(v_a_6836_);
    lean_dec(v_a_6835_);
    lean_dec_ref(v_a_6834_);
    lean_dec(v_a_6833_);
    lean_dec(v_a_6832_);
    lean_dec(v_a_6831_);
    return v_res_6843_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(
    mut v_00_u03c3_6844_: *mut LeanObject,
    mut v_00_u03b2_6845_: *mut LeanObject,
    mut v_map_6846_: *mut LeanObject,
    mut v_init_6847_: *mut LeanObject,
    mut v_f_6848_: *mut LeanObject,
    mut v___y_6849_: *mut LeanObject,
    mut v___y_6850_: *mut LeanObject,
    mut v___y_6851_: *mut LeanObject,
    mut v___y_6852_: *mut LeanObject,
    mut v___y_6853_: *mut LeanObject,
    mut v___y_6854_: *mut LeanObject,
    mut v___y_6855_: *mut LeanObject,
    mut v___y_6856_: *mut LeanObject,
    mut v___y_6857_: *mut LeanObject,
    mut v___y_6858_: *mut LeanObject,
    mut v___y_6859_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6861_: *mut LeanObject = core::ptr::null_mut();
    v___x_6861_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_6846_, v_init_6847_, v_f_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_);
    return v___x_6861_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_6862_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03b2_6863_: *mut LeanObject = *_args.add(1);
    let mut v_map_6864_: *mut LeanObject = *_args.add(2);
    let mut v_init_6865_: *mut LeanObject = *_args.add(3);
    let mut v_f_6866_: *mut LeanObject = *_args.add(4);
    let mut v___y_6867_: *mut LeanObject = *_args.add(5);
    let mut v___y_6868_: *mut LeanObject = *_args.add(6);
    let mut v___y_6869_: *mut LeanObject = *_args.add(7);
    let mut v___y_6870_: *mut LeanObject = *_args.add(8);
    let mut v___y_6871_: *mut LeanObject = *_args.add(9);
    let mut v___y_6872_: *mut LeanObject = *_args.add(10);
    let mut v___y_6873_: *mut LeanObject = *_args.add(11);
    let mut v___y_6874_: *mut LeanObject = *_args.add(12);
    let mut v___y_6875_: *mut LeanObject = *_args.add(13);
    let mut v___y_6876_: *mut LeanObject = *_args.add(14);
    let mut v___y_6877_: *mut LeanObject = *_args.add(15);
    let mut v___y_6878_: *mut LeanObject = *_args.add(16);
    let mut v_res_6879_: *mut LeanObject = core::ptr::null_mut();
    v_res_6879_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(v_00_u03c3_6862_, v_00_u03b2_6863_, v_map_6864_, v_init_6865_, v_f_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_);
    lean_dec(v___y_6877_);
    lean_dec_ref(v___y_6876_);
    lean_dec(v___y_6875_);
    lean_dec_ref(v___y_6874_);
    lean_dec(v___y_6873_);
    lean_dec_ref(v___y_6872_);
    lean_dec(v___y_6871_);
    lean_dec_ref(v___y_6870_);
    lean_dec(v___y_6869_);
    lean_dec(v___y_6868_);
    lean_dec(v___y_6867_);
    lean_dec_ref(v_map_6864_);
    return v_res_6879_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(
    mut v_map_6880_: *mut LeanObject,
    mut v_f_6881_: *mut LeanObject,
    mut v_init_6882_: *mut LeanObject,
    mut v___y_6883_: *mut LeanObject,
    mut v___y_6884_: *mut LeanObject,
    mut v___y_6885_: *mut LeanObject,
    mut v___y_6886_: *mut LeanObject,
    mut v___y_6887_: *mut LeanObject,
    mut v___y_6888_: *mut LeanObject,
    mut v___y_6889_: *mut LeanObject,
    mut v___y_6890_: *mut LeanObject,
    mut v___y_6891_: *mut LeanObject,
    mut v___y_6892_: *mut LeanObject,
    mut v___y_6893_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6895_: *mut LeanObject = core::ptr::null_mut();
    v___x_6895_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6881_, v_map_6880_, v_init_6882_, v___y_6883_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_);
    return v___x_6895_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg___boxed(
    mut v_map_6896_: *mut LeanObject,
    mut v_f_6897_: *mut LeanObject,
    mut v_init_6898_: *mut LeanObject,
    mut v___y_6899_: *mut LeanObject,
    mut v___y_6900_: *mut LeanObject,
    mut v___y_6901_: *mut LeanObject,
    mut v___y_6902_: *mut LeanObject,
    mut v___y_6903_: *mut LeanObject,
    mut v___y_6904_: *mut LeanObject,
    mut v___y_6905_: *mut LeanObject,
    mut v___y_6906_: *mut LeanObject,
    mut v___y_6907_: *mut LeanObject,
    mut v___y_6908_: *mut LeanObject,
    mut v___y_6909_: *mut LeanObject,
    mut v___y_6910_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_6911_: *mut LeanObject = core::ptr::null_mut();
    v_res_6911_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(v_map_6896_, v_f_6897_, v_init_6898_, v___y_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_);
    lean_dec(v___y_6909_);
    lean_dec_ref(v___y_6908_);
    lean_dec(v___y_6907_);
    lean_dec_ref(v___y_6906_);
    lean_dec(v___y_6905_);
    lean_dec_ref(v___y_6904_);
    lean_dec(v___y_6903_);
    lean_dec_ref(v___y_6902_);
    lean_dec(v___y_6901_);
    lean_dec(v___y_6900_);
    lean_dec(v___y_6899_);
    return v_res_6911_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(
    mut v_00_u03c3_6912_: *mut LeanObject,
    mut v_00_u03c3_6913_: *mut LeanObject,
    mut v_00_u03b2_6914_: *mut LeanObject,
    mut v_map_6915_: *mut LeanObject,
    mut v_f_6916_: *mut LeanObject,
    mut v_init_6917_: *mut LeanObject,
    mut v___y_6918_: *mut LeanObject,
    mut v___y_6919_: *mut LeanObject,
    mut v___y_6920_: *mut LeanObject,
    mut v___y_6921_: *mut LeanObject,
    mut v___y_6922_: *mut LeanObject,
    mut v___y_6923_: *mut LeanObject,
    mut v___y_6924_: *mut LeanObject,
    mut v___y_6925_: *mut LeanObject,
    mut v___y_6926_: *mut LeanObject,
    mut v___y_6927_: *mut LeanObject,
    mut v___y_6928_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6930_: *mut LeanObject = core::ptr::null_mut();
    v___x_6930_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6916_, v_map_6915_, v_init_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_, v___y_6922_, v___y_6923_, v___y_6924_, v___y_6925_, v___y_6926_, v___y_6927_, v___y_6928_);
    return v___x_6930_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_6931_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_6932_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b2_6933_: *mut LeanObject = *_args.add(2);
    let mut v_map_6934_: *mut LeanObject = *_args.add(3);
    let mut v_f_6935_: *mut LeanObject = *_args.add(4);
    let mut v_init_6936_: *mut LeanObject = *_args.add(5);
    let mut v___y_6937_: *mut LeanObject = *_args.add(6);
    let mut v___y_6938_: *mut LeanObject = *_args.add(7);
    let mut v___y_6939_: *mut LeanObject = *_args.add(8);
    let mut v___y_6940_: *mut LeanObject = *_args.add(9);
    let mut v___y_6941_: *mut LeanObject = *_args.add(10);
    let mut v___y_6942_: *mut LeanObject = *_args.add(11);
    let mut v___y_6943_: *mut LeanObject = *_args.add(12);
    let mut v___y_6944_: *mut LeanObject = *_args.add(13);
    let mut v___y_6945_: *mut LeanObject = *_args.add(14);
    let mut v___y_6946_: *mut LeanObject = *_args.add(15);
    let mut v___y_6947_: *mut LeanObject = *_args.add(16);
    let mut v___y_6948_: *mut LeanObject = *_args.add(17);
    let mut v_res_6949_: *mut LeanObject = core::ptr::null_mut();
    v_res_6949_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(v_00_u03c3_6931_, v_00_u03c3_6932_, v_00_u03b2_6933_, v_map_6934_, v_f_6935_, v_init_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
    lean_dec(v___y_6947_);
    lean_dec_ref(v___y_6946_);
    lean_dec(v___y_6945_);
    lean_dec_ref(v___y_6944_);
    lean_dec(v___y_6943_);
    lean_dec_ref(v___y_6942_);
    lean_dec(v___y_6941_);
    lean_dec_ref(v___y_6940_);
    lean_dec(v___y_6939_);
    lean_dec(v___y_6938_);
    lean_dec(v___y_6937_);
    return v_res_6949_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(
    mut v_00_u03c3_6950_: *mut LeanObject,
    mut v_00_u03c3_6951_: *mut LeanObject,
    mut v_00_u03b1_6952_: *mut LeanObject,
    mut v_00_u03b2_6953_: *mut LeanObject,
    mut v_f_6954_: *mut LeanObject,
    mut v_x_6955_: *mut LeanObject,
    mut v_x_6956_: *mut LeanObject,
    mut v___y_6957_: *mut LeanObject,
    mut v___y_6958_: *mut LeanObject,
    mut v___y_6959_: *mut LeanObject,
    mut v___y_6960_: *mut LeanObject,
    mut v___y_6961_: *mut LeanObject,
    mut v___y_6962_: *mut LeanObject,
    mut v___y_6963_: *mut LeanObject,
    mut v___y_6964_: *mut LeanObject,
    mut v___y_6965_: *mut LeanObject,
    mut v___y_6966_: *mut LeanObject,
    mut v___y_6967_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_6969_: *mut LeanObject = core::ptr::null_mut();
    v___x_6969_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6954_, v_x_6955_, v_x_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_);
    return v___x_6969_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_6970_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_6971_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_6972_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_6973_: *mut LeanObject = *_args.add(3);
    let mut v_f_6974_: *mut LeanObject = *_args.add(4);
    let mut v_x_6975_: *mut LeanObject = *_args.add(5);
    let mut v_x_6976_: *mut LeanObject = *_args.add(6);
    let mut v___y_6977_: *mut LeanObject = *_args.add(7);
    let mut v___y_6978_: *mut LeanObject = *_args.add(8);
    let mut v___y_6979_: *mut LeanObject = *_args.add(9);
    let mut v___y_6980_: *mut LeanObject = *_args.add(10);
    let mut v___y_6981_: *mut LeanObject = *_args.add(11);
    let mut v___y_6982_: *mut LeanObject = *_args.add(12);
    let mut v___y_6983_: *mut LeanObject = *_args.add(13);
    let mut v___y_6984_: *mut LeanObject = *_args.add(14);
    let mut v___y_6985_: *mut LeanObject = *_args.add(15);
    let mut v___y_6986_: *mut LeanObject = *_args.add(16);
    let mut v___y_6987_: *mut LeanObject = *_args.add(17);
    let mut v___y_6988_: *mut LeanObject = *_args.add(18);
    let mut v_res_6989_: *mut LeanObject = core::ptr::null_mut();
    v_res_6989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(v_00_u03c3_6970_, v_00_u03c3_6971_, v_00_u03b1_6972_, v_00_u03b2_6973_, v_f_6974_, v_x_6975_, v_x_6976_, v___y_6977_, v___y_6978_, v___y_6979_, v___y_6980_, v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_);
    lean_dec(v___y_6987_);
    lean_dec_ref(v___y_6986_);
    lean_dec(v___y_6985_);
    lean_dec_ref(v___y_6984_);
    lean_dec(v___y_6983_);
    lean_dec_ref(v___y_6982_);
    lean_dec(v___y_6981_);
    lean_dec_ref(v___y_6980_);
    lean_dec(v___y_6979_);
    lean_dec(v___y_6978_);
    lean_dec(v___y_6977_);
    return v_res_6989_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_6990_: *mut LeanObject,
    mut v_00_u03b2_6991_: *mut LeanObject,
    mut v_00_u03c3_6992_: *mut LeanObject,
    mut v_00_u03c3_6993_: *mut LeanObject,
    mut v_f_6994_: *mut LeanObject,
    mut v_as_6995_: *mut LeanObject,
    mut v_i_6996_: usize,
    mut v_stop_6997_: usize,
    mut v_b_6998_: *mut LeanObject,
    mut v___y_6999_: *mut LeanObject,
    mut v___y_7000_: *mut LeanObject,
    mut v___y_7001_: *mut LeanObject,
    mut v___y_7002_: *mut LeanObject,
    mut v___y_7003_: *mut LeanObject,
    mut v___y_7004_: *mut LeanObject,
    mut v___y_7005_: *mut LeanObject,
    mut v___y_7006_: *mut LeanObject,
    mut v___y_7007_: *mut LeanObject,
    mut v___y_7008_: *mut LeanObject,
    mut v___y_7009_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7011_: *mut LeanObject = core::ptr::null_mut();
    v___x_7011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6994_, v_as_6995_, v_i_6996_, v_stop_6997_, v_b_6998_, v___y_6999_, v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_);
    return v___x_7011_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03b1_7012_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03b2_7013_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03c3_7014_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03c3_7015_: *mut LeanObject = *_args.add(3);
    let mut v_f_7016_: *mut LeanObject = *_args.add(4);
    let mut v_as_7017_: *mut LeanObject = *_args.add(5);
    let mut v_i_7018_: *mut LeanObject = *_args.add(6);
    let mut v_stop_7019_: *mut LeanObject = *_args.add(7);
    let mut v_b_7020_: *mut LeanObject = *_args.add(8);
    let mut v___y_7021_: *mut LeanObject = *_args.add(9);
    let mut v___y_7022_: *mut LeanObject = *_args.add(10);
    let mut v___y_7023_: *mut LeanObject = *_args.add(11);
    let mut v___y_7024_: *mut LeanObject = *_args.add(12);
    let mut v___y_7025_: *mut LeanObject = *_args.add(13);
    let mut v___y_7026_: *mut LeanObject = *_args.add(14);
    let mut v___y_7027_: *mut LeanObject = *_args.add(15);
    let mut v___y_7028_: *mut LeanObject = *_args.add(16);
    let mut v___y_7029_: *mut LeanObject = *_args.add(17);
    let mut v___y_7030_: *mut LeanObject = *_args.add(18);
    let mut v___y_7031_: *mut LeanObject = *_args.add(19);
    let mut v___y_7032_: *mut LeanObject = *_args.add(20);
    let mut v_i_boxed_7033_: usize = 0;
    let mut v_stop_boxed_7034_: usize = 0;
    let mut v_res_7035_: *mut LeanObject = core::ptr::null_mut();
    v_i_boxed_7033_ = lean_unbox_usize(v_i_7018_);
    lean_dec(v_i_7018_);
    v_stop_boxed_7034_ = lean_unbox_usize(v_stop_7019_);
    lean_dec(v_stop_7019_);
    v_res_7035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_7012_, v_00_u03b2_7013_, v_00_u03c3_7014_, v_00_u03c3_7015_, v_f_7016_, v_as_7017_, v_i_boxed_7033_, v_stop_boxed_7034_, v_b_7020_, v___y_7021_, v___y_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_);
    lean_dec(v___y_7031_);
    lean_dec_ref(v___y_7030_);
    lean_dec(v___y_7029_);
    lean_dec_ref(v___y_7028_);
    lean_dec(v___y_7027_);
    lean_dec_ref(v___y_7026_);
    lean_dec(v___y_7025_);
    lean_dec_ref(v___y_7024_);
    lean_dec(v___y_7023_);
    lean_dec(v___y_7022_);
    lean_dec(v___y_7021_);
    lean_dec_ref(v_as_7017_);
    return v_res_7035_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03c3_7036_: *mut LeanObject,
    mut v_00_u03c3_7037_: *mut LeanObject,
    mut v_00_u03b1_7038_: *mut LeanObject,
    mut v_00_u03b2_7039_: *mut LeanObject,
    mut v_f_7040_: *mut LeanObject,
    mut v_keys_7041_: *mut LeanObject,
    mut v_vals_7042_: *mut LeanObject,
    mut v_heq_7043_: *mut LeanObject,
    mut v_i_7044_: *mut LeanObject,
    mut v_acc_7045_: *mut LeanObject,
    mut v___y_7046_: *mut LeanObject,
    mut v___y_7047_: *mut LeanObject,
    mut v___y_7048_: *mut LeanObject,
    mut v___y_7049_: *mut LeanObject,
    mut v___y_7050_: *mut LeanObject,
    mut v___y_7051_: *mut LeanObject,
    mut v___y_7052_: *mut LeanObject,
    mut v___y_7053_: *mut LeanObject,
    mut v___y_7054_: *mut LeanObject,
    mut v___y_7055_: *mut LeanObject,
    mut v___y_7056_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7058_: *mut LeanObject = core::ptr::null_mut();
    v___x_7058_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_7040_, v_keys_7041_, v_vals_7042_, v_i_7044_, v_acc_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
    return v___x_7058_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_00_u03c3_7059_: *mut LeanObject = *_args.add(0);
    let mut v_00_u03c3_7060_: *mut LeanObject = *_args.add(1);
    let mut v_00_u03b1_7061_: *mut LeanObject = *_args.add(2);
    let mut v_00_u03b2_7062_: *mut LeanObject = *_args.add(3);
    let mut v_f_7063_: *mut LeanObject = *_args.add(4);
    let mut v_keys_7064_: *mut LeanObject = *_args.add(5);
    let mut v_vals_7065_: *mut LeanObject = *_args.add(6);
    let mut v_heq_7066_: *mut LeanObject = *_args.add(7);
    let mut v_i_7067_: *mut LeanObject = *_args.add(8);
    let mut v_acc_7068_: *mut LeanObject = *_args.add(9);
    let mut v___y_7069_: *mut LeanObject = *_args.add(10);
    let mut v___y_7070_: *mut LeanObject = *_args.add(11);
    let mut v___y_7071_: *mut LeanObject = *_args.add(12);
    let mut v___y_7072_: *mut LeanObject = *_args.add(13);
    let mut v___y_7073_: *mut LeanObject = *_args.add(14);
    let mut v___y_7074_: *mut LeanObject = *_args.add(15);
    let mut v___y_7075_: *mut LeanObject = *_args.add(16);
    let mut v___y_7076_: *mut LeanObject = *_args.add(17);
    let mut v___y_7077_: *mut LeanObject = *_args.add(18);
    let mut v___y_7078_: *mut LeanObject = *_args.add(19);
    let mut v___y_7079_: *mut LeanObject = *_args.add(20);
    let mut v___y_7080_: *mut LeanObject = *_args.add(21);
    let mut v_res_7081_: *mut LeanObject = core::ptr::null_mut();
    v_res_7081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_7059_, v_00_u03c3_7060_, v_00_u03b1_7061_, v_00_u03b2_7062_, v_f_7063_, v_keys_7064_, v_vals_7065_, v_heq_7066_, v_i_7067_, v_acc_7068_, v___y_7069_, v___y_7070_, v___y_7071_, v___y_7072_, v___y_7073_, v___y_7074_, v___y_7075_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_);
    lean_dec(v___y_7079_);
    lean_dec_ref(v___y_7078_);
    lean_dec(v___y_7077_);
    lean_dec_ref(v___y_7076_);
    lean_dec(v___y_7075_);
    lean_dec_ref(v___y_7074_);
    lean_dec(v___y_7073_);
    lean_dec_ref(v___y_7072_);
    lean_dec(v___y_7071_);
    lean_dec(v___y_7070_);
    lean_dec(v___y_7069_);
    lean_dec_ref(v_vals_7065_);
    lean_dec_ref(v_keys_7064_);
    return v_res_7081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(
    mut v_a_7082_: *mut LeanObject,
    mut v_a_7083_: *mut LeanObject,
    mut v_a_7084_: *mut LeanObject,
    mut v_a_7085_: *mut LeanObject,
    mut v_a_7086_: *mut LeanObject,
    mut v_a_7087_: *mut LeanObject,
    mut v_a_7088_: *mut LeanObject,
    mut v_a_7089_: *mut LeanObject,
    mut v_a_7090_: *mut LeanObject,
    mut v_a_7091_: *mut LeanObject,
    mut v_a_7092_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7094_: *mut LeanObject = core::ptr::null_mut();
    v___x_7094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
    if lean_obj_tag(v___x_7094_) == 0 {
        let mut v___x_7095_: *mut LeanObject = core::ptr::null_mut();
        lean_dec_ref_known(v___x_7094_, 1);
        v___x_7095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
        if lean_obj_tag(v___x_7095_) == 0 {
            let mut v___x_7096_: *mut LeanObject = core::ptr::null_mut();
            lean_dec_ref_known(v___x_7095_, 1);
            v___x_7096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
            if lean_obj_tag(v___x_7096_) == 0 {
                let mut v___x_7097_: *mut LeanObject = core::ptr::null_mut();
                lean_dec_ref_known(v___x_7096_, 1);
                v___x_7097_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
                return v___x_7097_;
            } else {
                return v___x_7096_;
            }
        } else {
            return v___x_7095_;
        }
    } else {
        return v___x_7094_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs___boxed(
    mut v_a_7098_: *mut LeanObject,
    mut v_a_7099_: *mut LeanObject,
    mut v_a_7100_: *mut LeanObject,
    mut v_a_7101_: *mut LeanObject,
    mut v_a_7102_: *mut LeanObject,
    mut v_a_7103_: *mut LeanObject,
    mut v_a_7104_: *mut LeanObject,
    mut v_a_7105_: *mut LeanObject,
    mut v_a_7106_: *mut LeanObject,
    mut v_a_7107_: *mut LeanObject,
    mut v_a_7108_: *mut LeanObject,
    mut v_a_7109_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7110_: *mut LeanObject = core::ptr::null_mut();
    v_res_7110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_, v_a_7106_, v_a_7107_, v_a_7108_);
    lean_dec(v_a_7108_);
    lean_dec_ref(v_a_7107_);
    lean_dec(v_a_7106_);
    lean_dec_ref(v_a_7105_);
    lean_dec(v_a_7104_);
    lean_dec_ref(v_a_7103_);
    lean_dec(v_a_7102_);
    lean_dec_ref(v_a_7101_);
    lean_dec(v_a_7100_);
    lean_dec(v_a_7099_);
    lean_dec(v_a_7098_);
    return v_res_7110_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2()
-> *mut LeanObject {
    let mut v___x_7113_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut LeanObject = core::ptr::null_mut();
    v___x_7113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1;
    v___x_7114_ = lean_unsigned_to_nat(6);
    v___x_7115_ = lean_unsigned_to_nat(103);
    v___x_7116_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0;
    v___x_7117_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0;
    v___x_7118_ = l_mkPanicMessageWithDecl(
        v___x_7117_,
        v___x_7116_,
        v___x_7115_,
        v___x_7114_,
        v___x_7113_,
    );
    return v___x_7118_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(
    mut v_upperBound_7119_: *mut LeanObject,
    mut v_a_7120_: *mut LeanObject,
    mut v_b_7121_: *mut LeanObject,
    mut v___y_7122_: *mut LeanObject,
    mut v___y_7123_: *mut LeanObject,
    mut v___y_7124_: *mut LeanObject,
    mut v___y_7125_: *mut LeanObject,
    mut v___y_7126_: *mut LeanObject,
    mut v___y_7127_: *mut LeanObject,
    mut v___y_7128_: *mut LeanObject,
    mut v___y_7129_: *mut LeanObject,
    mut v___y_7130_: *mut LeanObject,
    mut v___y_7131_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7133_: u8 = 0;
    let mut v___x_7134_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut LeanObject = core::ptr::null_mut();
    let mut v___y_7137_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: u8 = 0;
    let mut v___x_7142_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7133_ = lean_nat_dec_lt(v_a_7120_, v_upperBound_7119_);
                if v___x_7133_ == 0 {
                    lean_dec(v_a_7120_);
                    v___x_7134_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7134_, 0, v_b_7121_);
                    return v___x_7134_;
                } else {
                    v___x_7135_ = lean_box(0);
                    v___x_7141_ = lean_nat_dec_eq(v_a_7120_, v_a_7120_);
                    if v___x_7141_ == 0 {
                        v___x_7142_ = lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2);
                        v___x_7143_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_7142_, v_a_7120_, v___y_7122_, v___y_7123_, v___y_7124_, v___y_7125_, v___y_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_, v___y_7131_);
                        v___y_7137_ = v___x_7143_;
                        state = 1;
                        continue;
                    } else {
                        v___x_7144_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_7120_, v___y_7122_, v___y_7123_, v___y_7124_, v___y_7125_, v___y_7126_, v___y_7127_, v___y_7128_, v___y_7129_, v___y_7130_, v___y_7131_);
                        v___y_7137_ = v___x_7144_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                if lean_obj_tag(v___y_7137_) == 0 {
                    lean_dec_ref_known(v___y_7137_, 1);
                    v___x_7138_ = lean_unsigned_to_nat(1);
                    v___x_7139_ = lean_nat_add(v_a_7120_, v___x_7138_);
                    lean_dec(v_a_7120_);
                    v_a_7120_ = v___x_7139_;
                    v_b_7121_ = v___x_7135_;
                    state = 0;
                    continue;
                } else {
                    lean_dec(v_a_7120_);
                    return v___y_7137_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___boxed(
    mut v_upperBound_7145_: *mut LeanObject,
    mut v_a_7146_: *mut LeanObject,
    mut v_b_7147_: *mut LeanObject,
    mut v___y_7148_: *mut LeanObject,
    mut v___y_7149_: *mut LeanObject,
    mut v___y_7150_: *mut LeanObject,
    mut v___y_7151_: *mut LeanObject,
    mut v___y_7152_: *mut LeanObject,
    mut v___y_7153_: *mut LeanObject,
    mut v___y_7154_: *mut LeanObject,
    mut v___y_7155_: *mut LeanObject,
    mut v___y_7156_: *mut LeanObject,
    mut v___y_7157_: *mut LeanObject,
    mut v___y_7158_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7159_: *mut LeanObject = core::ptr::null_mut();
    v_res_7159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_7145_, v_a_7146_, v_b_7147_, v___y_7148_, v___y_7149_, v___y_7150_, v___y_7151_, v___y_7152_, v___y_7153_, v___y_7154_, v___y_7155_, v___y_7156_, v___y_7157_);
    lean_dec(v___y_7157_);
    lean_dec_ref(v___y_7156_);
    lean_dec(v___y_7155_);
    lean_dec_ref(v___y_7154_);
    lean_dec(v___y_7153_);
    lean_dec_ref(v___y_7152_);
    lean_dec(v___y_7151_);
    lean_dec_ref(v___y_7150_);
    lean_dec(v___y_7149_);
    lean_dec(v___y_7148_);
    lean_dec(v_upperBound_7145_);
    return v_res_7159_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_checkInvariants(
    mut v_a_7160_: *mut LeanObject,
    mut v_a_7161_: *mut LeanObject,
    mut v_a_7162_: *mut LeanObject,
    mut v_a_7163_: *mut LeanObject,
    mut v_a_7164_: *mut LeanObject,
    mut v_a_7165_: *mut LeanObject,
    mut v_a_7166_: *mut LeanObject,
    mut v_a_7167_: *mut LeanObject,
    mut v_a_7168_: *mut LeanObject,
    mut v_a_7169_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_debug_7171_: u8 = 0;
    let mut v___x_7172_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7175_: *mut LeanObject = core::ptr::null_mut();
    let mut v_structs_7176_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7183_: u8 = 0;
    let mut v___x_7185_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7186_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7187_: u8 = 0;
    let mut v_unused_7188_: *mut LeanObject = core::ptr::null_mut();
    let mut v_a_7189_: *mut LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isShared_7192_: u8 = 0;
    let mut v___x_7194_: *mut LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7195_: *mut LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_debug_7171_ = lean_ctor_get_uint8(
                    v_a_7162_,
                    (core::mem::size_of::<*mut LeanObject>() * 8 + 2) as u32,
                );
                if v_debug_7171_ == 0 {
                    v___x_7172_ = lean_box(0);
                    v___x_7173_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v___x_7173_, 0, v___x_7172_);
                    return v___x_7173_;
                } else {
                    v___x_7174_ =
                        l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_7160_, v_a_7168_);
                    if lean_obj_tag(v___x_7174_) == 0 {
                        v_a_7175_ = lean_ctor_get(v___x_7174_, 0);
                        lean_inc(v_a_7175_);
                        lean_dec_ref_known(v___x_7174_, 1);
                        v_structs_7176_ = lean_ctor_get(v_a_7175_, 0);
                        lean_inc_ref(v_structs_7176_);
                        lean_dec(v_a_7175_);
                        v___x_7177_ = lean_array_get_size(v_structs_7176_);
                        lean_dec_ref(v_structs_7176_);
                        v___x_7178_ = lean_unsigned_to_nat(0);
                        v___x_7179_ = lean_box(0);
                        v___x_7180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v___x_7177_, v___x_7178_, v___x_7179_, v_a_7160_, v_a_7161_, v_a_7162_, v_a_7163_, v_a_7164_, v_a_7165_, v_a_7166_, v_a_7167_, v_a_7168_, v_a_7169_);
                        if lean_obj_tag(v___x_7180_) == 0 {
                            v_isSharedCheck_7187_ = (!lean_is_exclusive(v___x_7180_)) as u8;
                            if v_isSharedCheck_7187_ == 0 {
                                v_unused_7188_ = lean_ctor_get(v___x_7180_, 0);
                                lean_dec(v_unused_7188_);
                                v___x_7182_ = v___x_7180_;
                                v_isShared_7183_ = v_isSharedCheck_7187_;
                                state = 1;
                                continue;
                            } else {
                                lean_dec(v___x_7180_);
                                v___x_7182_ = lean_box(0);
                                v_isShared_7183_ = v_isSharedCheck_7187_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_7180_;
                        }
                    } else {
                        v_a_7189_ = lean_ctor_get(v___x_7174_, 0);
                        v_isSharedCheck_7196_ = (!lean_is_exclusive(v___x_7174_)) as u8;
                        if v_isSharedCheck_7196_ == 0 {
                            v___x_7191_ = v___x_7174_;
                            v_isShared_7192_ = v_isSharedCheck_7196_;
                            state = 3;
                            continue;
                        } else {
                            lean_inc(v_a_7189_);
                            lean_dec(v___x_7174_);
                            v___x_7191_ = lean_box(0);
                            v_isShared_7192_ = v_isSharedCheck_7196_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7183_ == 0 {
                    lean_ctor_set(v___x_7182_, 0, v___x_7179_);
                    v___x_7185_ = v___x_7182_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7186_ = lean_alloc_ctor(0, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7186_, 0, v___x_7179_);
                    v___x_7185_ = v_reuseFailAlloc_7186_;
                    state = 2;
                    continue;
                }
            }
            2 => {
                return v___x_7185_;
            }
            3 => {
                if v_isShared_7192_ == 0 {
                    v___x_7194_ = v___x_7191_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_7195_ = lean_alloc_ctor(1, 1, (0) as u32);
                    lean_ctor_set(v_reuseFailAlloc_7195_, 0, v_a_7189_);
                    v___x_7194_ = v_reuseFailAlloc_7195_;
                    state = 4;
                    continue;
                }
            }
            4 => {
                return v___x_7194_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_checkInvariants___boxed(
    mut v_a_7197_: *mut LeanObject,
    mut v_a_7198_: *mut LeanObject,
    mut v_a_7199_: *mut LeanObject,
    mut v_a_7200_: *mut LeanObject,
    mut v_a_7201_: *mut LeanObject,
    mut v_a_7202_: *mut LeanObject,
    mut v_a_7203_: *mut LeanObject,
    mut v_a_7204_: *mut LeanObject,
    mut v_a_7205_: *mut LeanObject,
    mut v_a_7206_: *mut LeanObject,
    mut v_a_7207_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v_res_7208_: *mut LeanObject = core::ptr::null_mut();
    v_res_7208_ = l_Lean_Meta_Grind_Arith_Linear_checkInvariants(
        v_a_7197_, v_a_7198_, v_a_7199_, v_a_7200_, v_a_7201_, v_a_7202_, v_a_7203_, v_a_7204_,
        v_a_7205_, v_a_7206_,
    );
    lean_dec(v_a_7206_);
    lean_dec_ref(v_a_7205_);
    lean_dec(v_a_7204_);
    lean_dec_ref(v_a_7203_);
    lean_dec(v_a_7202_);
    lean_dec_ref(v_a_7201_);
    lean_dec(v_a_7200_);
    lean_dec_ref(v_a_7199_);
    lean_dec(v_a_7198_);
    lean_dec(v_a_7197_);
    return v_res_7208_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(
    mut v_upperBound_7209_: *mut LeanObject,
    mut v_inst_7210_: *mut LeanObject,
    mut v_R_7211_: *mut LeanObject,
    mut v_a_7212_: *mut LeanObject,
    mut v_b_7213_: *mut LeanObject,
    mut v_c_7214_: *mut LeanObject,
    mut v___y_7215_: *mut LeanObject,
    mut v___y_7216_: *mut LeanObject,
    mut v___y_7217_: *mut LeanObject,
    mut v___y_7218_: *mut LeanObject,
    mut v___y_7219_: *mut LeanObject,
    mut v___y_7220_: *mut LeanObject,
    mut v___y_7221_: *mut LeanObject,
    mut v___y_7222_: *mut LeanObject,
    mut v___y_7223_: *mut LeanObject,
    mut v___y_7224_: *mut LeanObject,
) -> *mut LeanObject {
    let mut v___x_7226_: *mut LeanObject = core::ptr::null_mut();
    v___x_7226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_7209_, v_a_7212_, v_b_7213_, v___y_7215_, v___y_7216_, v___y_7217_, v___y_7218_, v___y_7219_, v___y_7220_, v___y_7221_, v___y_7222_, v___y_7223_, v___y_7224_);
    return v___x_7226_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___boxed(
    _args: *mut *mut LeanObject,
) -> *mut LeanObject {
    let mut v_upperBound_7227_: *mut LeanObject = *_args.add(0);
    let mut v_inst_7228_: *mut LeanObject = *_args.add(1);
    let mut v_R_7229_: *mut LeanObject = *_args.add(2);
    let mut v_a_7230_: *mut LeanObject = *_args.add(3);
    let mut v_b_7231_: *mut LeanObject = *_args.add(4);
    let mut v_c_7232_: *mut LeanObject = *_args.add(5);
    let mut v___y_7233_: *mut LeanObject = *_args.add(6);
    let mut v___y_7234_: *mut LeanObject = *_args.add(7);
    let mut v___y_7235_: *mut LeanObject = *_args.add(8);
    let mut v___y_7236_: *mut LeanObject = *_args.add(9);
    let mut v___y_7237_: *mut LeanObject = *_args.add(10);
    let mut v___y_7238_: *mut LeanObject = *_args.add(11);
    let mut v___y_7239_: *mut LeanObject = *_args.add(12);
    let mut v___y_7240_: *mut LeanObject = *_args.add(13);
    let mut v___y_7241_: *mut LeanObject = *_args.add(14);
    let mut v___y_7242_: *mut LeanObject = *_args.add(15);
    let mut v___y_7243_: *mut LeanObject = *_args.add(16);
    let mut v_res_7244_: *mut LeanObject = core::ptr::null_mut();
    v_res_7244_ =
        l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(
            v_upperBound_7227_,
            v_inst_7228_,
            v_R_7229_,
            v_a_7230_,
            v_b_7231_,
            v_c_7232_,
            v___y_7233_,
            v___y_7234_,
            v___y_7235_,
            v___y_7236_,
            v___y_7237_,
            v___y_7238_,
            v___y_7239_,
            v___y_7240_,
            v___y_7241_,
            v___y_7242_,
        );
    lean_dec(v___y_7242_);
    lean_dec_ref(v___y_7241_);
    lean_dec(v___y_7240_);
    lean_dec_ref(v___y_7239_);
    lean_dec(v___y_7238_);
    lean_dec_ref(v___y_7237_);
    lean_dec(v___y_7236_);
    lean_dec_ref(v___y_7235_);
    lean_dec(v___y_7234_);
    lean_dec(v___y_7233_);
    lean_dec(v_upperBound_7227_);
    return v_res_7244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return lean_io_result_mk_ok(lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin: u8) -> *mut LeanObject {
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
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if lean_io_result_is_error(res) {
        return res;
    }
    lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
}
