// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.Inv
// Imports: Lean.Meta.Tactic.Grind.Arith.Linear.LinearM Lean.Meta.Tactic.Grind.Arith.Linear.Util
use crate::ffi::{
    lean_array_fget_borrowed, lean_array_get_size, lean_array_size, lean_array_uget_borrowed,
    lean_int_dec_eq, lean_int_dec_lt, lean_nat_add, lean_nat_dec_eq, lean_nat_dec_le,
    lean_nat_dec_lt, lean_nat_to_int, lean_panic_fn_borrowed, lean_usize_add, lean_usize_dec_eq,
    lean_usize_dec_lt, lean_usize_of_nat,
};
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
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value: leanh::LeanStringObject<40> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value: leanh::LeanStringObject<89> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 79, 99, 99, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value: leanh::LeanStringObject<123> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 123, m_capacity: 123, m_length: 122, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 50, 57, 56, 50, 52, 51, 48, 53, 52, 51, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 53, 46, 48, 32, 41, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 121, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value: leanh::LeanStringObject<92> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 78, 111, 69, 108, 105, 109, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value: leanh::LeanStringObject<110> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 110, m_capacity: 110, m_length: 109, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 51, 52, 49, 49, 54, 57, 48, 48, 51, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 51, 51, 46, 48, 32, 41, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value: leanh::LeanStringObject<89> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 67, 110, 115, 116, 114, 79, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value: leanh::LeanStringObject<30> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 32, 61, 61, 32, 121, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value: leanh::LeanStringObject<34> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value: leanh::LeanStringObject<35> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value: leanh::LeanStringObject<38> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 99, 104, 101, 99, 107, 67, 111, 101, 102, 102, 115, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value: leanh::LeanStringObject<94> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 76, 101, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value: leanh::LeanStringObject<45> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 76, 111, 119, 101, 114, 32, 61, 61, 32, 40, 97, 32, 60, 32, 48, 41, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value: leanh::LeanStringObject<92> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 76, 111, 119, 101, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value: leanh::LeanStringObject<53> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 108, 111, 119, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value: leanh::LeanStringObject<92> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 85, 112, 112, 101, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value: leanh::LeanStringObject<53> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 117, 112, 112, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value: leanh::LeanCtorObject<2> = leanh::LeanCtorObject { m_header: leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<leanh::LeanObject>() + core::mem::size_of::<*mut leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value: leanh::LeanStringObject<97> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 68, 105, 115, 101, 113, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value) as *mut leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value: leanh::LeanStringObject<53> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 100, 105, 115, 101, 113, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value: leanh::LeanStringObject<90> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 90, m_capacity: 90, m_length: 89, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value: leanh::LeanStringObject<48> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 120, 112, 114, 32, 101, 120, 112, 114, 39, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value: leanh::LeanStringObject<42> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110, 117, 109, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value) as *mut leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1: *mut leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value: leanh::LeanStringObject<45> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 73, 110, 118, 97, 114, 105, 97, 110, 116, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value) as *mut leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value: leanh::LeanStringObject<126> = leanh::LeanStringObject { m_header: leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 51, 49, 49, 57, 50, 50, 53, 55, 54, 52, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 48, 46, 48, 32, 41, 32, 61, 61, 32, 115, 116, 114, 117, 99, 116, 73, 100, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1: *mut leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value) as *mut leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once: leanh::LeanOnceCell = leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2: *mut leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
    mut v_a_3623_: *mut leanh::LeanObject,
    mut v_a_3624_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3625_: u8 = 0;
    let mut v_v_3626_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3627_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3631_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_a_3624_) == 0 {
                    leanh::lean_dec(v_a_3623_);
                    v___x_3625_ = 1;
                    return v___x_3625_;
                } else {
                    if leanh::lean_obj_tag(v_a_3623_) == 0 {
                        v_v_3626_ = leanh::lean_ctor_get(v_a_3624_, 1);
                        v_p_3627_ = leanh::lean_ctor_get(v_a_3624_, 2);
                        leanh::lean_inc(v_v_3626_);
                        v___x_3628_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3628_, 0, v_v_3626_);
                        v_a_3623_ = v___x_3628_;
                        v_a_3624_ = v_p_3627_;
                        state = 0;
                        continue;
                    } else {
                        v_v_3630_ = leanh::lean_ctor_get(v_a_3624_, 1);
                        v_p_3631_ = leanh::lean_ctor_get(v_a_3624_, 2);
                        v_val_3632_ = leanh::lean_ctor_get(v_a_3623_, 0);
                        v_isSharedCheck_3641_ = (!leanh::lean_is_exclusive(v_a_3623_)) as u8;
                        if v_isSharedCheck_3641_ == 0 {
                            v___x_3634_ = v_a_3623_;
                            v_isShared_3635_ = v_isSharedCheck_3641_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_val_3632_);
                            leanh::lean_dec(v_a_3623_);
                            v___x_3634_ = leanh::lean_box(0);
                            v_isShared_3635_ = v_isSharedCheck_3641_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3636_ = lean_nat_dec_lt(v_v_3630_, v_val_3632_);
                leanh::lean_dec(v_val_3632_);
                if v___x_3636_ == 0 {
                    leanh::lean_del_object(v___x_3634_);
                    return v___x_3636_;
                } else {
                    leanh::lean_inc(v_v_3630_);
                    if v_isShared_3635_ == 0 {
                        leanh::lean_ctor_set(v___x_3634_, 0, v_v_3630_);
                        v___x_3638_ = v___x_3634_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3640_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_v_3630_);
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
    mut v_a_3642_: *mut leanh::LeanObject,
    mut v_a_3643_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3644_: u8 = 0;
    let mut v_r_3645_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3644_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
            v_a_3642_, v_a_3643_,
        );
    leanh::lean_dec(v_a_3643_);
    v_r_3645_ = leanh::lean_box((v_res_3644_) as usize);
    return v_r_3645_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(
    mut v_p_3646_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3647_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    v___x_3647_ = leanh::lean_box(0);
    v___x_3648_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
            v___x_3647_,
            v_p_3646_,
        );
    return v___x_3648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted___boxed(
    mut v_p_3649_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3650_: u8 = 0;
    let mut v_r_3651_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(
            v_p_3649_,
        );
    leanh::lean_dec(v_p_3649_);
    v_r_3651_ = leanh::lean_box((v_res_3650_) as usize);
    return v_r_3651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3652_ = leanh::lean_unsigned_to_nat(0);
    v___x_3653_ = lean_nat_to_int(v___x_3652_);
    return v___x_3653_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(
    mut v_x_3654_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3655_: u8 = 0;
    let mut v_k_3656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_3654_) == 0 {
                    v___x_3655_ = 1;
                    return v___x_3655_;
                } else {
                    v_k_3656_ = leanh::lean_ctor_get(v_x_3654_, 0);
                    v_p_3657_ = leanh::lean_ctor_get(v_x_3654_, 2);
                    v___x_3658_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
    mut v_x_3662_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3663_: u8 = 0;
    let mut v_r_3664_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3663_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(
            v_x_3662_,
        );
    leanh::lean_dec(v_x_3662_);
    v_r_3664_ = leanh::lean_box((v_res_3663_) as usize);
    return v_r_3664_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3665_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Meta_Grind_instInhabitedGoalM(leanh::lean_box(0));
    return v___x_3665_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(
    mut v_msg_3666_: *mut leanh::LeanObject,
    mut v___y_3667_: *mut leanh::LeanObject,
    mut v___y_3668_: *mut leanh::LeanObject,
    mut v___y_3669_: *mut leanh::LeanObject,
    mut v___y_3670_: *mut leanh::LeanObject,
    mut v___y_3671_: *mut leanh::LeanObject,
    mut v___y_3672_: *mut leanh::LeanObject,
    mut v___y_3673_: *mut leanh::LeanObject,
    mut v___y_3674_: *mut leanh::LeanObject,
    mut v___y_3675_: *mut leanh::LeanObject,
    mut v___y_3676_: *mut leanh::LeanObject,
    mut v___y_3677_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201__overap_3681_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3679_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0);
    v___f_3680_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3680_, 0, v___x_3679_);
    v___x_2201__overap_3681_ = lean_panic_fn_borrowed(v___f_3680_, v_msg_3666_);
    leanh::lean_dec_ref(v___f_3680_);
    leanh::lean_inc(v___y_3677_);
    leanh::lean_inc_ref(v___y_3676_);
    leanh::lean_inc(v___y_3675_);
    leanh::lean_inc_ref(v___y_3674_);
    leanh::lean_inc(v___y_3673_);
    leanh::lean_inc_ref(v___y_3672_);
    leanh::lean_inc(v___y_3671_);
    leanh::lean_inc_ref(v___y_3670_);
    leanh::lean_inc(v___y_3669_);
    leanh::lean_inc(v___y_3668_);
    leanh::lean_inc(v___y_3667_);
    v___x_3682_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_3682_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___boxed(
    mut v_msg_3683_: *mut leanh::LeanObject,
    mut v___y_3684_: *mut leanh::LeanObject,
    mut v___y_3685_: *mut leanh::LeanObject,
    mut v___y_3686_: *mut leanh::LeanObject,
    mut v___y_3687_: *mut leanh::LeanObject,
    mut v___y_3688_: *mut leanh::LeanObject,
    mut v___y_3689_: *mut leanh::LeanObject,
    mut v___y_3690_: *mut leanh::LeanObject,
    mut v___y_3691_: *mut leanh::LeanObject,
    mut v___y_3692_: *mut leanh::LeanObject,
    mut v___y_3693_: *mut leanh::LeanObject,
    mut v___y_3694_: *mut leanh::LeanObject,
    mut v___y_3695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3696_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3696_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v_msg_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
    leanh::lean_dec(v___y_3694_);
    leanh::lean_dec_ref(v___y_3693_);
    leanh::lean_dec(v___y_3692_);
    leanh::lean_dec_ref(v___y_3691_);
    leanh::lean_dec(v___y_3690_);
    leanh::lean_dec_ref(v___y_3689_);
    leanh::lean_dec(v___y_3688_);
    leanh::lean_dec_ref(v___y_3687_);
    leanh::lean_dec(v___y_3686_);
    leanh::lean_dec(v___y_3685_);
    leanh::lean_dec(v___y_3684_);
    return v_res_3696_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(
    mut v_k_3697_: *mut leanh::LeanObject,
    mut v_t_3698_: *mut leanh::LeanObject,
) -> u8 {
    let mut v_k_3699_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3700_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3701_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: u8 = 0;
    let mut v___x_3706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_t_3698_) == 0 {
                    v_k_3699_ = leanh::lean_ctor_get(v_t_3698_, 1);
                    v_l_3700_ = leanh::lean_ctor_get(v_t_3698_, 3);
                    v_r_3701_ = leanh::lean_ctor_get(v_t_3698_, 4);
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
    mut v_k_3707_: *mut leanh::LeanObject,
    mut v_t_3708_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3709_: u8 = 0;
    let mut v_r_3710_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_3707_, v_t_3708_);
    leanh::lean_dec(v_t_3708_);
    leanh::lean_dec(v_k_3707_);
    v_r_3710_ = leanh::lean_box((v_res_3709_) as usize);
    return v_r_3710_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3()
-> *mut leanh::LeanObject {
    let mut v___x_3714_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2;
    v___x_3715_ = leanh::lean_unsigned_to_nat(4);
    v___x_3716_ = leanh::lean_unsigned_to_nat(32);
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
    mut v_y_3720_: *mut leanh::LeanObject,
    mut v_p_3721_: *mut leanh::LeanObject,
    mut v_a_3722_: *mut leanh::LeanObject,
    mut v_a_3723_: *mut leanh::LeanObject,
    mut v_a_3724_: *mut leanh::LeanObject,
    mut v_a_3725_: *mut leanh::LeanObject,
    mut v_a_3726_: *mut leanh::LeanObject,
    mut v_a_3727_: *mut leanh::LeanObject,
    mut v_a_3728_: *mut leanh::LeanObject,
    mut v_a_3729_: *mut leanh::LeanObject,
    mut v_a_3730_: *mut leanh::LeanObject,
    mut v_a_3731_: *mut leanh::LeanObject,
    mut v_a_3732_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_3734_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3748_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v___x_3750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_3721_) == 1 {
                    v_v_3734_ = leanh::lean_ctor_get(v_p_3721_, 1);
                    v_p_3735_ = leanh::lean_ctor_get(v_p_3721_, 2);
                    v___x_3736_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(
                        v_v_3734_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_,
                        v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_,
                    );
                    if leanh::lean_obj_tag(v___x_3736_) == 0 {
                        v_a_3737_ = leanh::lean_ctor_get(v___x_3736_, 0);
                        leanh::lean_inc(v_a_3737_);
                        leanh::lean_dec_ref_known(v___x_3736_, 1);
                        v___x_3738_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_y_3720_, v_a_3737_);
                        leanh::lean_dec(v_a_3737_);
                        if v___x_3738_ == 0 {
                            v___x_3739_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3);
                            v___x_3740_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3739_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
                            return v___x_3740_;
                        } else {
                            v_p_3721_ = v_p_3735_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_a_3742_ = leanh::lean_ctor_get(v___x_3736_, 0);
                        v_isSharedCheck_3749_ =
                            (!leanh::lean_is_exclusive(v___x_3736_)) as u8;
                        if v_isSharedCheck_3749_ == 0 {
                            v___x_3744_ = v___x_3736_;
                            v_isShared_3745_ = v_isSharedCheck_3749_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3742_);
                            leanh::lean_dec(v___x_3736_);
                            v___x_3744_ = leanh::lean_box(0);
                            v_isShared_3745_ = v_isSharedCheck_3749_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3750_ = leanh::lean_box(0);
                    v___x_3751_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3751_, 0, v___x_3750_);
                    return v___x_3751_;
                }
            }
            1 => {
                if v_isShared_3745_ == 0 {
                    v___x_3747_ = v___x_3744_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3748_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
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
    mut v_y_3752_: *mut leanh::LeanObject,
    mut v_p_3753_: *mut leanh::LeanObject,
    mut v_a_3754_: *mut leanh::LeanObject,
    mut v_a_3755_: *mut leanh::LeanObject,
    mut v_a_3756_: *mut leanh::LeanObject,
    mut v_a_3757_: *mut leanh::LeanObject,
    mut v_a_3758_: *mut leanh::LeanObject,
    mut v_a_3759_: *mut leanh::LeanObject,
    mut v_a_3760_: *mut leanh::LeanObject,
    mut v_a_3761_: *mut leanh::LeanObject,
    mut v_a_3762_: *mut leanh::LeanObject,
    mut v_a_3763_: *mut leanh::LeanObject,
    mut v_a_3764_: *mut leanh::LeanObject,
    mut v_a_3765_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3766_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_y_3752_, v_p_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
    leanh::lean_dec(v_a_3764_);
    leanh::lean_dec_ref(v_a_3763_);
    leanh::lean_dec(v_a_3762_);
    leanh::lean_dec_ref(v_a_3761_);
    leanh::lean_dec(v_a_3760_);
    leanh::lean_dec_ref(v_a_3759_);
    leanh::lean_dec(v_a_3758_);
    leanh::lean_dec_ref(v_a_3757_);
    leanh::lean_dec(v_a_3756_);
    leanh::lean_dec(v_a_3755_);
    leanh::lean_dec(v_a_3754_);
    leanh::lean_dec(v_p_3753_);
    leanh::lean_dec(v_y_3752_);
    return v_res_3766_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(
    mut v_00_u03b2_3767_: *mut leanh::LeanObject,
    mut v_k_3768_: *mut leanh::LeanObject,
    mut v_t_3769_: *mut leanh::LeanObject,
) -> u8 {
    let mut v___x_3770_: u8 = 0;
    v___x_3770_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_3768_, v_t_3769_);
    return v___x_3770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___boxed(
    mut v_00_u03b2_3771_: *mut leanh::LeanObject,
    mut v_k_3772_: *mut leanh::LeanObject,
    mut v_t_3773_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3774_: u8 = 0;
    let mut v_r_3775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3774_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(v_00_u03b2_3771_, v_k_3772_, v_t_3773_);
    leanh::lean_dec(v_t_3773_);
    leanh::lean_dec(v_k_3772_);
    v_r_3775_ = leanh::lean_box((v_res_3774_) as usize);
    return v_r_3775_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(
    mut v_p_3776_: *mut leanh::LeanObject,
    mut v_a_3777_: *mut leanh::LeanObject,
    mut v_a_3778_: *mut leanh::LeanObject,
    mut v_a_3779_: *mut leanh::LeanObject,
    mut v_a_3780_: *mut leanh::LeanObject,
    mut v_a_3781_: *mut leanh::LeanObject,
    mut v_a_3782_: *mut leanh::LeanObject,
    mut v_a_3783_: *mut leanh::LeanObject,
    mut v_a_3784_: *mut leanh::LeanObject,
    mut v_a_3785_: *mut leanh::LeanObject,
    mut v_a_3786_: *mut leanh::LeanObject,
    mut v_a_3787_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    if leanh::lean_obj_tag(v_p_3776_) == 1 {
        let mut v_v_3789_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_3790_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3791_: *mut leanh::LeanObject = core::ptr::null_mut();
        v_v_3789_ = leanh::lean_ctor_get(v_p_3776_, 1);
        v_p_3790_ = leanh::lean_ctor_get(v_p_3776_, 2);
        v___x_3791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_v_3789_, v_p_3790_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
        return v___x_3791_;
    } else {
        let mut v___x_3792_: *mut leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3793_: *mut leanh::LeanObject = core::ptr::null_mut();
        v___x_3792_ = leanh::lean_box(0);
        v___x_3793_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
        leanh::lean_ctor_set(v___x_3793_, 0, v___x_3792_);
        return v___x_3793_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs___boxed(
    mut v_p_3794_: *mut leanh::LeanObject,
    mut v_a_3795_: *mut leanh::LeanObject,
    mut v_a_3796_: *mut leanh::LeanObject,
    mut v_a_3797_: *mut leanh::LeanObject,
    mut v_a_3798_: *mut leanh::LeanObject,
    mut v_a_3799_: *mut leanh::LeanObject,
    mut v_a_3800_: *mut leanh::LeanObject,
    mut v_a_3801_: *mut leanh::LeanObject,
    mut v_a_3802_: *mut leanh::LeanObject,
    mut v_a_3803_: *mut leanh::LeanObject,
    mut v_a_3804_: *mut leanh::LeanObject,
    mut v_a_3805_: *mut leanh::LeanObject,
    mut v_a_3806_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3807_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(
            v_p_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_,
            v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_,
        );
    leanh::lean_dec(v_a_3805_);
    leanh::lean_dec_ref(v_a_3804_);
    leanh::lean_dec(v_a_3803_);
    leanh::lean_dec_ref(v_a_3802_);
    leanh::lean_dec(v_a_3801_);
    leanh::lean_dec_ref(v_a_3800_);
    leanh::lean_dec(v_a_3799_);
    leanh::lean_dec_ref(v_a_3798_);
    leanh::lean_dec(v_a_3797_);
    leanh::lean_dec(v_a_3796_);
    leanh::lean_dec(v_a_3795_);
    leanh::lean_dec(v_p_3794_);
    return v_res_3807_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1;
    v___x_3811_ = leanh::lean_unsigned_to_nat(2);
    v___x_3812_ = leanh::lean_unsigned_to_nat(38);
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
    mut v_p_3816_: *mut leanh::LeanObject,
    mut v_a_3817_: *mut leanh::LeanObject,
    mut v_a_3818_: *mut leanh::LeanObject,
    mut v_a_3819_: *mut leanh::LeanObject,
    mut v_a_3820_: *mut leanh::LeanObject,
    mut v_a_3821_: *mut leanh::LeanObject,
    mut v_a_3822_: *mut leanh::LeanObject,
    mut v_a_3823_: *mut leanh::LeanObject,
    mut v_a_3824_: *mut leanh::LeanObject,
    mut v_a_3825_: *mut leanh::LeanObject,
    mut v_a_3826_: *mut leanh::LeanObject,
    mut v_a_3827_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_v_3829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3830_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3835_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3837_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3842_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v___x_3845_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_p_3816_) == 1 {
                    v_v_3829_ = leanh::lean_ctor_get(v_p_3816_, 1);
                    v_p_3830_ = leanh::lean_ctor_get(v_p_3816_, 2);
                    v___x_3831_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(
                        v_v_3829_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_,
                        v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_,
                    );
                    if leanh::lean_obj_tag(v___x_3831_) == 0 {
                        v_a_3832_ = leanh::lean_ctor_get(v___x_3831_, 0);
                        leanh::lean_inc(v_a_3832_);
                        leanh::lean_dec_ref_known(v___x_3831_, 1);
                        v___x_3833_ = (leanh::lean_unbox(v_a_3832_) as u8);
                        leanh::lean_dec(v_a_3832_);
                        if v___x_3833_ == 0 {
                            v_p_3816_ = v_p_3830_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3835_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2);
                            v___x_3836_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3835_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
                            return v___x_3836_;
                        }
                    } else {
                        v_a_3837_ = leanh::lean_ctor_get(v___x_3831_, 0);
                        v_isSharedCheck_3844_ =
                            (!leanh::lean_is_exclusive(v___x_3831_)) as u8;
                        if v_isSharedCheck_3844_ == 0 {
                            v___x_3839_ = v___x_3831_;
                            v_isShared_3840_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_3837_);
                            leanh::lean_dec(v___x_3831_);
                            v___x_3839_ = leanh::lean_box(0);
                            v_isShared_3840_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3845_ = leanh::lean_box(0);
                    v___x_3846_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_3846_, 0, v___x_3845_);
                    return v___x_3846_;
                }
            }
            1 => {
                if v_isShared_3840_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
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
    mut v_p_3847_: *mut leanh::LeanObject,
    mut v_a_3848_: *mut leanh::LeanObject,
    mut v_a_3849_: *mut leanh::LeanObject,
    mut v_a_3850_: *mut leanh::LeanObject,
    mut v_a_3851_: *mut leanh::LeanObject,
    mut v_a_3852_: *mut leanh::LeanObject,
    mut v_a_3853_: *mut leanh::LeanObject,
    mut v_a_3854_: *mut leanh::LeanObject,
    mut v_a_3855_: *mut leanh::LeanObject,
    mut v_a_3856_: *mut leanh::LeanObject,
    mut v_a_3857_: *mut leanh::LeanObject,
    mut v_a_3858_: *mut leanh::LeanObject,
    mut v_a_3859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3860_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
    leanh::lean_dec(v_a_3858_);
    leanh::lean_dec_ref(v_a_3857_);
    leanh::lean_dec(v_a_3856_);
    leanh::lean_dec_ref(v_a_3855_);
    leanh::lean_dec(v_a_3854_);
    leanh::lean_dec_ref(v_a_3853_);
    leanh::lean_dec(v_a_3852_);
    leanh::lean_dec_ref(v_a_3851_);
    leanh::lean_dec(v_a_3850_);
    leanh::lean_dec(v_a_3849_);
    leanh::lean_dec(v_a_3848_);
    leanh::lean_dec(v_p_3847_);
    return v_res_3860_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3863_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3863_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1;
    v___x_3864_ = leanh::lean_unsigned_to_nat(2);
    v___x_3865_ = leanh::lean_unsigned_to_nat(49);
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
-> *mut leanh::LeanObject {
    let mut v___x_3870_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_3871_ = leanh::lean_unsigned_to_nat(24);
    v___x_3872_ = leanh::lean_unsigned_to_nat(48);
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
-> *mut leanh::LeanObject {
    let mut v___x_3877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5;
    v___x_3878_ = leanh::lean_unsigned_to_nat(2);
    v___x_3879_ = leanh::lean_unsigned_to_nat(42);
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
-> *mut leanh::LeanObject {
    let mut v___x_3884_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7;
    v___x_3885_ = leanh::lean_unsigned_to_nat(2);
    v___x_3886_ = leanh::lean_unsigned_to_nat(43);
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
    mut v_p_3890_: *mut leanh::LeanObject,
    mut v_x_3891_: *mut leanh::LeanObject,
    mut v_a_3892_: *mut leanh::LeanObject,
    mut v_a_3893_: *mut leanh::LeanObject,
    mut v_a_3894_: *mut leanh::LeanObject,
    mut v_a_3895_: *mut leanh::LeanObject,
    mut v_a_3896_: *mut leanh::LeanObject,
    mut v_a_3897_: *mut leanh::LeanObject,
    mut v_a_3898_: *mut leanh::LeanObject,
    mut v_a_3899_: *mut leanh::LeanObject,
    mut v_a_3900_: *mut leanh::LeanObject,
    mut v_a_3901_: *mut leanh::LeanObject,
    mut v_a_3902_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___y_3905_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3931_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(v_p_3890_);
                if v___x_3924_ == 0 {
                    v___x_3925_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6);
                    v___x_3926_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3925_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                    return v___x_3926_;
                } else {
                    v___x_3927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(v_p_3890_);
                    if v___x_3927_ == 0 {
                        v___x_3928_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8);
                        v___x_3929_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3928_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                        return v___x_3929_;
                    } else {
                        v___x_3930_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(
                            v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_,
                            v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_,
                        );
                        if leanh::lean_obj_tag(v___x_3930_) == 0 {
                            v_a_3931_ = leanh::lean_ctor_get(v___x_3930_, 0);
                            leanh::lean_inc(v_a_3931_);
                            leanh::lean_dec_ref_known(v___x_3930_, 1);
                            v___x_3932_ = (leanh::lean_unbox(v_a_3931_) as u8);
                            leanh::lean_dec(v_a_3931_);
                            if v___x_3932_ == 0 {
                                v___x_3933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_3890_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                                if leanh::lean_obj_tag(v___x_3933_) == 0 {
                                    leanh::lean_dec_ref_known(v___x_3933_, 1);
                                    v___x_3934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(v_p_3890_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                                    if leanh::lean_obj_tag(v___x_3934_) == 0 {
                                        leanh::lean_dec_ref_known(v___x_3934_, 1);
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
                            v_a_3935_ = leanh::lean_ctor_get(v___x_3930_, 0);
                            v_isSharedCheck_3942_ =
                                (!leanh::lean_is_exclusive(v___x_3930_)) as u8;
                            if v_isSharedCheck_3942_ == 0 {
                                v___x_3937_ = v___x_3930_;
                                v_isShared_3938_ = v_isSharedCheck_3942_;
                                state = 2;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_3935_);
                                leanh::lean_dec(v___x_3930_);
                                v___x_3937_ = leanh::lean_box(0);
                                v_isShared_3938_ = v_isSharedCheck_3942_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_p_3890_) == 1 {
                    v_v_3916_ = leanh::lean_ctor_get(v_p_3890_, 1);
                    v___x_3917_ = lean_nat_dec_eq(v_x_3891_, v_v_3916_);
                    if v___x_3917_ == 0 {
                        v___x_3918_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2);
                        v___x_3919_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3918_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
                        return v___x_3919_;
                    } else {
                        v___x_3920_ = leanh::lean_box(0);
                        v___x_3921_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v___x_3921_, 0, v___x_3920_);
                        return v___x_3921_;
                    }
                } else {
                    v___x_3922_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4);
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
                    v_reuseFailAlloc_3941_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
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
    mut v_p_3943_: *mut leanh::LeanObject,
    mut v_x_3944_: *mut leanh::LeanObject,
    mut v_a_3945_: *mut leanh::LeanObject,
    mut v_a_3946_: *mut leanh::LeanObject,
    mut v_a_3947_: *mut leanh::LeanObject,
    mut v_a_3948_: *mut leanh::LeanObject,
    mut v_a_3949_: *mut leanh::LeanObject,
    mut v_a_3950_: *mut leanh::LeanObject,
    mut v_a_3951_: *mut leanh::LeanObject,
    mut v_a_3952_: *mut leanh::LeanObject,
    mut v_a_3953_: *mut leanh::LeanObject,
    mut v_a_3954_: *mut leanh::LeanObject,
    mut v_a_3955_: *mut leanh::LeanObject,
    mut v_a_3956_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3957_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_3943_, v_x_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
    leanh::lean_dec(v_a_3955_);
    leanh::lean_dec_ref(v_a_3954_);
    leanh::lean_dec(v_a_3953_);
    leanh::lean_dec_ref(v_a_3952_);
    leanh::lean_dec(v_a_3951_);
    leanh::lean_dec_ref(v_a_3950_);
    leanh::lean_dec(v_a_3949_);
    leanh::lean_dec_ref(v_a_3948_);
    leanh::lean_dec(v_a_3947_);
    leanh::lean_dec(v_a_3946_);
    leanh::lean_dec(v_a_3945_);
    leanh::lean_dec(v_x_3944_);
    leanh::lean_dec(v_p_3943_);
    return v_res_3957_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_3958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3958_ = l_Lean_Meta_Grind_instInhabitedGoalM(leanh::lean_box(0));
    return v___x_3958_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(
    mut v_msg_3959_: *mut leanh::LeanObject,
    mut v___y_3960_: *mut leanh::LeanObject,
    mut v___y_3961_: *mut leanh::LeanObject,
    mut v___y_3962_: *mut leanh::LeanObject,
    mut v___y_3963_: *mut leanh::LeanObject,
    mut v___y_3964_: *mut leanh::LeanObject,
    mut v___y_3965_: *mut leanh::LeanObject,
    mut v___y_3966_: *mut leanh::LeanObject,
    mut v___y_3967_: *mut leanh::LeanObject,
    mut v___y_3968_: *mut leanh::LeanObject,
    mut v___y_3969_: *mut leanh::LeanObject,
    mut v___y_3970_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_3972_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3973_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606__overap_3974_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0);
    v___f_3973_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_3973_, 0, v___x_3972_);
    v___x_4606__overap_3974_ = lean_panic_fn_borrowed(v___f_3973_, v_msg_3959_);
    leanh::lean_dec_ref(v___f_3973_);
    leanh::lean_inc(v___y_3970_);
    leanh::lean_inc_ref(v___y_3969_);
    leanh::lean_inc(v___y_3968_);
    leanh::lean_inc_ref(v___y_3967_);
    leanh::lean_inc(v___y_3966_);
    leanh::lean_inc_ref(v___y_3965_);
    leanh::lean_inc(v___y_3964_);
    leanh::lean_inc_ref(v___y_3963_);
    leanh::lean_inc(v___y_3962_);
    leanh::lean_inc(v___y_3961_);
    leanh::lean_inc(v___y_3960_);
    v___x_3975_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_3975_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___boxed(
    mut v_msg_3976_: *mut leanh::LeanObject,
    mut v___y_3977_: *mut leanh::LeanObject,
    mut v___y_3978_: *mut leanh::LeanObject,
    mut v___y_3979_: *mut leanh::LeanObject,
    mut v___y_3980_: *mut leanh::LeanObject,
    mut v___y_3981_: *mut leanh::LeanObject,
    mut v___y_3982_: *mut leanh::LeanObject,
    mut v___y_3983_: *mut leanh::LeanObject,
    mut v___y_3984_: *mut leanh::LeanObject,
    mut v___y_3985_: *mut leanh::LeanObject,
    mut v___y_3986_: *mut leanh::LeanObject,
    mut v___y_3987_: *mut leanh::LeanObject,
    mut v___y_3988_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_3989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_3989_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v_msg_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
    leanh::lean_dec(v___y_3987_);
    leanh::lean_dec_ref(v___y_3986_);
    leanh::lean_dec(v___y_3985_);
    leanh::lean_dec_ref(v___y_3984_);
    leanh::lean_dec(v___y_3983_);
    leanh::lean_dec_ref(v___y_3982_);
    leanh::lean_dec(v___y_3981_);
    leanh::lean_dec_ref(v___y_3980_);
    leanh::lean_dec(v___y_3979_);
    leanh::lean_dec(v___y_3978_);
    leanh::lean_dec(v___y_3977_);
    return v_res_3989_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_3992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1;
    v___x_3993_ = leanh::lean_unsigned_to_nat(6);
    v___x_3994_ = leanh::lean_unsigned_to_nat(57);
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
-> *mut leanh::LeanObject {
    let mut v___x_3998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_3998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_3999_ = leanh::lean_unsigned_to_nat(30);
    v___x_4000_ = leanh::lean_unsigned_to_nat(56);
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
    mut v_____s_4004_: *mut leanh::LeanObject,
    mut v_isLower_4005_: u8,
    mut v_as_4006_: *mut leanh::LeanObject,
    mut v_sz_4007_: usize,
    mut v_i_4008_: usize,
    mut v_b_4009_: *mut leanh::LeanObject,
    mut v___y_4010_: *mut leanh::LeanObject,
    mut v___y_4011_: *mut leanh::LeanObject,
    mut v___y_4012_: *mut leanh::LeanObject,
    mut v___y_4013_: *mut leanh::LeanObject,
    mut v___y_4014_: *mut leanh::LeanObject,
    mut v___y_4015_: *mut leanh::LeanObject,
    mut v___y_4016_: *mut leanh::LeanObject,
    mut v___y_4017_: *mut leanh::LeanObject,
    mut v___y_4018_: *mut leanh::LeanObject,
    mut v___y_4019_: *mut leanh::LeanObject,
    mut v___y_4020_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v_a_4028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4029_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4033_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: usize = 0;
    let mut v___x_4037_: usize = 0;
    let mut v_reuseFailAlloc_4039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4053_: u8 = 0;
    let mut v_a_4054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v___x_4059_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut v___x_4062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4064_: u8 = 0;
    let mut v_k_4065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: u8 = 0;
    let mut v___x_4068_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4073_: u8 = 0;
    let mut v___x_4075_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_unused_4087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4022_ = lean_usize_dec_lt(v_i_4008_, v_sz_4007_);
                if v___x_4022_ == 0 {
                    v___x_4023_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4023_, 0, v_b_4009_);
                    return v___x_4023_;
                } else {
                    v_snd_4024_ = leanh::lean_ctor_get(v_b_4009_, 1);
                    v_isSharedCheck_4086_ = (!leanh::lean_is_exclusive(v_b_4009_)) as u8;
                    if v_isSharedCheck_4086_ == 0 {
                        v_unused_4087_ = leanh::lean_ctor_get(v_b_4009_, 0);
                        leanh::lean_dec(v_unused_4087_);
                        v___x_4026_ = v_b_4009_;
                        v_isShared_4027_ = v_isSharedCheck_4086_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4024_);
                        leanh::lean_dec(v_b_4009_);
                        v___x_4026_ = leanh::lean_box(0);
                        v_isShared_4027_ = v_isSharedCheck_4086_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4028_ = lean_array_uget_borrowed(v_as_4006_, v_i_4008_);
                v_p_4029_ = leanh::lean_ctor_get(v_a_4028_, 0);
                v___x_4030_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4029_, v_____s_4004_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                if leanh::lean_obj_tag(v___x_4030_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4030_, 1);
                    v___x_4031_ = leanh::lean_box(0);
                    v___x_4062_ = leanh::lean_box(0);
                    if leanh::lean_obj_tag(v_p_4029_) == 1 {
                        v_k_4065_ = leanh::lean_ctor_get(v_p_4029_, 0);
                        v___x_4066_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        leanh::lean_dec(v_snd_4024_);
                        v___x_4068_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4069_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4068_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                        if leanh::lean_obj_tag(v___x_4069_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4069_, 1);
                            v_a_4033_ = v___x_4062_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_4026_);
                            v_a_4070_ = leanh::lean_ctor_get(v___x_4069_, 0);
                            v_isSharedCheck_4077_ =
                                (!leanh::lean_is_exclusive(v___x_4069_)) as u8;
                            if v_isSharedCheck_4077_ == 0 {
                                v___x_4072_ = v___x_4069_;
                                v_isShared_4073_ = v_isSharedCheck_4077_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4070_);
                                leanh::lean_dec(v___x_4069_);
                                v___x_4072_ = leanh::lean_box(0);
                                v_isShared_4073_ = v_isSharedCheck_4077_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4026_);
                    leanh::lean_dec(v_snd_4024_);
                    v_a_4078_ = leanh::lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4085_ = (!leanh::lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4085_ == 0 {
                        v___x_4080_ = v___x_4030_;
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4078_);
                        leanh::lean_dec(v___x_4030_);
                        v___x_4080_ = leanh::lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4027_ == 0 {
                    leanh::lean_ctor_set(v___x_4026_, 1, v_a_4033_);
                    leanh::lean_ctor_set(v___x_4026_, 0, v___x_4031_);
                    v___x_4035_ = v___x_4026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4039_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4031_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_a_4033_);
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
                v___x_4041_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4042_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4041_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                if leanh::lean_obj_tag(v___x_4042_) == 0 {
                    v_a_4043_ = leanh::lean_ctor_get(v___x_4042_, 0);
                    v_isSharedCheck_4053_ = (!leanh::lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4053_ == 0 {
                        v___x_4045_ = v___x_4042_;
                        v_isShared_4046_ = v_isSharedCheck_4053_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4043_);
                        leanh::lean_dec(v___x_4042_);
                        v___x_4045_ = leanh::lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4053_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4026_);
                    leanh::lean_dec(v_snd_4024_);
                    v_a_4054_ = leanh::lean_ctor_get(v___x_4042_, 0);
                    v_isSharedCheck_4061_ = (!leanh::lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4061_ == 0 {
                        v___x_4056_ = v___x_4042_;
                        v_isShared_4057_ = v_isSharedCheck_4061_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4054_);
                        leanh::lean_dec(v___x_4042_);
                        v___x_4056_ = leanh::lean_box(0);
                        v_isShared_4057_ = v_isSharedCheck_4061_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_4043_) == 0 {
                    leanh::lean_del_object(v___x_4026_);
                    v___x_4047_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4047_, 0, v_a_4043_);
                    v___x_4048_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4048_, 0, v___x_4047_);
                    leanh::lean_ctor_set(v___x_4048_, 1, v_snd_4024_);
                    if v_isShared_4046_ == 0 {
                        leanh::lean_ctor_set(v___x_4045_, 0, v___x_4048_);
                        v___x_4050_ = v___x_4045_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4051_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
                        v___x_4050_ = v_reuseFailAlloc_4051_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4045_);
                    leanh::lean_dec(v_snd_4024_);
                    v_a_4052_ = leanh::lean_ctor_get(v_a_4043_, 0);
                    leanh::lean_inc(v_a_4052_);
                    leanh::lean_dec_ref_known(v_a_4043_, 1);
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
                    v_reuseFailAlloc_4060_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
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
                    leanh::lean_dec(v_snd_4024_);
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
                    v_reuseFailAlloc_4076_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
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
                    v_reuseFailAlloc_4084_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_4088_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4089_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_4090_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_4091_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_4092_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4093_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4094_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4095_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4096_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4097_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4098_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4099_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4100_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4101_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4102_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4103_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4104_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4105_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4106_: u8 = 0;
    let mut v_sz_boxed_4107_: usize = 0;
    let mut v_i_boxed_4108_: usize = 0;
    let mut v_res_4109_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4106_ = (leanh::lean_unbox(v_isLower_4089_) as u8);
    v_sz_boxed_4107_ = leanh::lean_unbox_usize(v_sz_4091_);
    leanh::lean_dec(v_sz_4091_);
    v_i_boxed_4108_ = leanh::lean_unbox_usize(v_i_4092_);
    leanh::lean_dec(v_i_4092_);
    v_res_4109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_4088_, v_isLower_boxed_4106_, v_as_4090_, v_sz_boxed_4107_, v_i_boxed_4108_, v_b_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
    leanh::lean_dec(v___y_4104_);
    leanh::lean_dec_ref(v___y_4103_);
    leanh::lean_dec(v___y_4102_);
    leanh::lean_dec_ref(v___y_4101_);
    leanh::lean_dec(v___y_4100_);
    leanh::lean_dec_ref(v___y_4099_);
    leanh::lean_dec(v___y_4098_);
    leanh::lean_dec_ref(v___y_4097_);
    leanh::lean_dec(v___y_4096_);
    leanh::lean_dec(v___y_4095_);
    leanh::lean_dec(v___y_4094_);
    leanh::lean_dec_ref(v_as_4090_);
    leanh::lean_dec(v_____s_4088_);
    return v_res_4109_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(
    mut v_____s_4110_: *mut leanh::LeanObject,
    mut v_isLower_4111_: u8,
    mut v_as_4112_: *mut leanh::LeanObject,
    mut v_sz_4113_: usize,
    mut v_i_4114_: usize,
    mut v_b_4115_: *mut leanh::LeanObject,
    mut v___y_4116_: *mut leanh::LeanObject,
    mut v___y_4117_: *mut leanh::LeanObject,
    mut v___y_4118_: *mut leanh::LeanObject,
    mut v___y_4119_: *mut leanh::LeanObject,
    mut v___y_4120_: *mut leanh::LeanObject,
    mut v___y_4121_: *mut leanh::LeanObject,
    mut v___y_4122_: *mut leanh::LeanObject,
    mut v___y_4123_: *mut leanh::LeanObject,
    mut v___y_4124_: *mut leanh::LeanObject,
    mut v___y_4125_: *mut leanh::LeanObject,
    mut v___y_4126_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4128_: u8 = 0;
    let mut v___x_4129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v_a_4134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: usize = 0;
    let mut v___x_4144_: usize = 0;
    let mut v___x_4145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v_a_4161_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v___y_4170_: u8 = 0;
    let mut v_k_4171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4179_: u8 = 0;
    let mut v___x_4181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4183_: u8 = 0;
    let mut v_a_4184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4187_: u8 = 0;
    let mut v___x_4189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4190_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4191_: u8 = 0;
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v_unused_4193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4128_ = lean_usize_dec_lt(v_i_4114_, v_sz_4113_);
                if v___x_4128_ == 0 {
                    v___x_4129_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4129_, 0, v_b_4115_);
                    return v___x_4129_;
                } else {
                    v_snd_4130_ = leanh::lean_ctor_get(v_b_4115_, 1);
                    v_isSharedCheck_4192_ = (!leanh::lean_is_exclusive(v_b_4115_)) as u8;
                    if v_isSharedCheck_4192_ == 0 {
                        v_unused_4193_ = leanh::lean_ctor_get(v_b_4115_, 0);
                        leanh::lean_dec(v_unused_4193_);
                        v___x_4132_ = v_b_4115_;
                        v_isShared_4133_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4130_);
                        leanh::lean_dec(v_b_4115_);
                        v___x_4132_ = leanh::lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4134_ = lean_array_uget_borrowed(v_as_4112_, v_i_4114_);
                v_p_4135_ = leanh::lean_ctor_get(v_a_4134_, 0);
                v___x_4136_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4135_, v_____s_4110_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                if leanh::lean_obj_tag(v___x_4136_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4136_, 1);
                    v___x_4137_ = leanh::lean_box(0);
                    v___x_4138_ = leanh::lean_box(0);
                    if leanh::lean_obj_tag(v_p_4135_) == 1 {
                        v_k_4171_ = leanh::lean_ctor_get(v_p_4135_, 0);
                        v___x_4172_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        leanh::lean_dec(v_snd_4130_);
                        v___x_4174_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4175_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4174_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        if leanh::lean_obj_tag(v___x_4175_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4175_, 1);
                            v_a_4140_ = v___x_4137_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_4132_);
                            v_a_4176_ = leanh::lean_ctor_get(v___x_4175_, 0);
                            v_isSharedCheck_4183_ =
                                (!leanh::lean_is_exclusive(v___x_4175_)) as u8;
                            if v_isSharedCheck_4183_ == 0 {
                                v___x_4178_ = v___x_4175_;
                                v_isShared_4179_ = v_isSharedCheck_4183_;
                                state = 10;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4176_);
                                leanh::lean_dec(v___x_4175_);
                                v___x_4178_ = leanh::lean_box(0);
                                v_isShared_4179_ = v_isSharedCheck_4183_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4132_);
                    leanh::lean_dec(v_snd_4130_);
                    v_a_4184_ = leanh::lean_ctor_get(v___x_4136_, 0);
                    v_isSharedCheck_4191_ = (!leanh::lean_is_exclusive(v___x_4136_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4186_ = v___x_4136_;
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 12;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4184_);
                        leanh::lean_dec(v___x_4136_);
                        v___x_4186_ = leanh::lean_box(0);
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4133_ == 0 {
                    leanh::lean_ctor_set(v___x_4132_, 1, v_a_4140_);
                    leanh::lean_ctor_set(v___x_4132_, 0, v___x_4138_);
                    v___x_4142_ = v___x_4132_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4138_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_a_4140_);
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
                v___x_4148_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4149_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4148_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                if leanh::lean_obj_tag(v___x_4149_) == 0 {
                    v_a_4150_ = leanh::lean_ctor_get(v___x_4149_, 0);
                    v_isSharedCheck_4160_ = (!leanh::lean_is_exclusive(v___x_4149_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4152_ = v___x_4149_;
                        v_isShared_4153_ = v_isSharedCheck_4160_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4150_);
                        leanh::lean_dec(v___x_4149_);
                        v___x_4152_ = leanh::lean_box(0);
                        v_isShared_4153_ = v_isSharedCheck_4160_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4132_);
                    leanh::lean_dec(v_snd_4130_);
                    v_a_4161_ = leanh::lean_ctor_get(v___x_4149_, 0);
                    v_isSharedCheck_4168_ = (!leanh::lean_is_exclusive(v___x_4149_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4163_ = v___x_4149_;
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 7;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4161_);
                        leanh::lean_dec(v___x_4149_);
                        v___x_4163_ = leanh::lean_box(0);
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_4150_) == 0 {
                    leanh::lean_del_object(v___x_4132_);
                    v___x_4154_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4154_, 0, v_a_4150_);
                    v___x_4155_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4155_, 0, v___x_4154_);
                    leanh::lean_ctor_set(v___x_4155_, 1, v_snd_4130_);
                    if v_isShared_4153_ == 0 {
                        leanh::lean_ctor_set(v___x_4152_, 0, v___x_4155_);
                        v___x_4157_ = v___x_4152_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4158_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
                        v___x_4157_ = v_reuseFailAlloc_4158_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4152_);
                    leanh::lean_dec(v_snd_4130_);
                    v_a_4159_ = leanh::lean_ctor_get(v_a_4150_, 0);
                    leanh::lean_inc(v_a_4159_);
                    leanh::lean_dec_ref_known(v_a_4150_, 1);
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
                    v_reuseFailAlloc_4167_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
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
                    leanh::lean_dec(v_snd_4130_);
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
                    v_reuseFailAlloc_4182_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
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
                    v_reuseFailAlloc_4190_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_4194_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4195_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_4196_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_4197_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_4198_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4199_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4200_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4201_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4202_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4203_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4204_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4205_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4206_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4207_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4208_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4209_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4210_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4211_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4212_: u8 = 0;
    let mut v_sz_boxed_4213_: usize = 0;
    let mut v_i_boxed_4214_: usize = 0;
    let mut v_res_4215_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4212_ = (leanh::lean_unbox(v_isLower_4195_) as u8);
    v_sz_boxed_4213_ = leanh::lean_unbox_usize(v_sz_4197_);
    leanh::lean_dec(v_sz_4197_);
    v_i_boxed_4214_ = leanh::lean_unbox_usize(v_i_4198_);
    leanh::lean_dec(v_i_4198_);
    v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_4194_, v_isLower_boxed_4212_, v_as_4196_, v_sz_boxed_4213_, v_i_boxed_4214_, v_b_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
    leanh::lean_dec(v___y_4210_);
    leanh::lean_dec_ref(v___y_4209_);
    leanh::lean_dec(v___y_4208_);
    leanh::lean_dec_ref(v___y_4207_);
    leanh::lean_dec(v___y_4206_);
    leanh::lean_dec_ref(v___y_4205_);
    leanh::lean_dec(v___y_4204_);
    leanh::lean_dec_ref(v___y_4203_);
    leanh::lean_dec(v___y_4202_);
    leanh::lean_dec(v___y_4201_);
    leanh::lean_dec(v___y_4200_);
    leanh::lean_dec_ref(v_as_4196_);
    leanh::lean_dec(v_____s_4194_);
    return v_res_4215_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(
    mut v_init_4216_: *mut leanh::LeanObject,
    mut v_____s_4217_: *mut leanh::LeanObject,
    mut v_isLower_4218_: u8,
    mut v_n_4219_: *mut leanh::LeanObject,
    mut v_b_4220_: *mut leanh::LeanObject,
    mut v___y_4221_: *mut leanh::LeanObject,
    mut v___y_4222_: *mut leanh::LeanObject,
    mut v___y_4223_: *mut leanh::LeanObject,
    mut v___y_4224_: *mut leanh::LeanObject,
    mut v___y_4225_: *mut leanh::LeanObject,
    mut v___y_4226_: *mut leanh::LeanObject,
    mut v___y_4227_: *mut leanh::LeanObject,
    mut v___y_4228_: *mut leanh::LeanObject,
    mut v___y_4229_: *mut leanh::LeanObject,
    mut v___y_4230_: *mut leanh::LeanObject,
    mut v___y_4231_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4236_: usize = 0;
    let mut v___x_4237_: usize = 0;
    let mut v___x_4238_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v_fst_4243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4244_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4248_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4249_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v_a_4254_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4257_: u8 = 0;
    let mut v___x_4259_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4260_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4261_: u8 = 0;
    let mut v_vs_4262_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4265_: usize = 0;
    let mut v___x_4266_: usize = 0;
    let mut v___x_4267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v_fst_4272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4278_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v_a_4283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v___x_4288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_4219_) == 0 {
                    v_cs_4233_ = leanh::lean_ctor_get(v_n_4219_, 0);
                    v___x_4234_ = leanh::lean_box(0);
                    v___x_4235_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4235_, 0, v___x_4234_);
                    leanh::lean_ctor_set(v___x_4235_, 1, v_b_4220_);
                    v_sz_4236_ = lean_array_size(v_cs_4233_);
                    v___x_4237_ = 0usize;
                    v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_4216_, v_____s_4217_, v_isLower_4218_, v_cs_4233_, v_sz_4236_, v___x_4237_, v___x_4235_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
                    if leanh::lean_obj_tag(v___x_4238_) == 0 {
                        v_a_4239_ = leanh::lean_ctor_get(v___x_4238_, 0);
                        v_isSharedCheck_4253_ =
                            (!leanh::lean_is_exclusive(v___x_4238_)) as u8;
                        if v_isSharedCheck_4253_ == 0 {
                            v___x_4241_ = v___x_4238_;
                            v_isShared_4242_ = v_isSharedCheck_4253_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4239_);
                            leanh::lean_dec(v___x_4238_);
                            v___x_4241_ = leanh::lean_box(0);
                            v_isShared_4242_ = v_isSharedCheck_4253_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4254_ = leanh::lean_ctor_get(v___x_4238_, 0);
                        v_isSharedCheck_4261_ =
                            (!leanh::lean_is_exclusive(v___x_4238_)) as u8;
                        if v_isSharedCheck_4261_ == 0 {
                            v___x_4256_ = v___x_4238_;
                            v_isShared_4257_ = v_isSharedCheck_4261_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4254_);
                            leanh::lean_dec(v___x_4238_);
                            v___x_4256_ = leanh::lean_box(0);
                            v_isShared_4257_ = v_isSharedCheck_4261_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4262_ = leanh::lean_ctor_get(v_n_4219_, 0);
                    v___x_4263_ = leanh::lean_box(0);
                    v___x_4264_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4264_, 0, v___x_4263_);
                    leanh::lean_ctor_set(v___x_4264_, 1, v_b_4220_);
                    v_sz_4265_ = lean_array_size(v_vs_4262_);
                    v___x_4266_ = 0usize;
                    v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_4217_, v_isLower_4218_, v_vs_4262_, v_sz_4265_, v___x_4266_, v___x_4264_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
                    if leanh::lean_obj_tag(v___x_4267_) == 0 {
                        v_a_4268_ = leanh::lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4282_ =
                            (!leanh::lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4282_ == 0 {
                            v___x_4270_ = v___x_4267_;
                            v_isShared_4271_ = v_isSharedCheck_4282_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4268_);
                            leanh::lean_dec(v___x_4267_);
                            v___x_4270_ = leanh::lean_box(0);
                            v_isShared_4271_ = v_isSharedCheck_4282_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4283_ = leanh::lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4290_ =
                            (!leanh::lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4290_ == 0 {
                            v___x_4285_ = v___x_4267_;
                            v_isShared_4286_ = v_isSharedCheck_4290_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4283_);
                            leanh::lean_dec(v___x_4267_);
                            v___x_4285_ = leanh::lean_box(0);
                            v_isShared_4286_ = v_isSharedCheck_4290_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4243_ = leanh::lean_ctor_get(v_a_4239_, 0);
                if leanh::lean_obj_tag(v_fst_4243_) == 0 {
                    v_snd_4244_ = leanh::lean_ctor_get(v_a_4239_, 1);
                    leanh::lean_inc(v_snd_4244_);
                    leanh::lean_dec(v_a_4239_);
                    v___x_4245_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4245_, 0, v_snd_4244_);
                    if v_isShared_4242_ == 0 {
                        leanh::lean_ctor_set(v___x_4241_, 0, v___x_4245_);
                        v___x_4247_ = v___x_4241_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4248_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
                        v___x_4247_ = v_reuseFailAlloc_4248_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4243_);
                    leanh::lean_dec(v_a_4239_);
                    v_val_4249_ = leanh::lean_ctor_get(v_fst_4243_, 0);
                    leanh::lean_inc(v_val_4249_);
                    leanh::lean_dec_ref_known(v_fst_4243_, 1);
                    if v_isShared_4242_ == 0 {
                        leanh::lean_ctor_set(v___x_4241_, 0, v_val_4249_);
                        v___x_4251_ = v___x_4241_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4252_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_val_4249_);
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
                    v_reuseFailAlloc_4260_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
                    v___x_4259_ = v_reuseFailAlloc_4260_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4259_;
            }
            6 => {
                v_fst_4272_ = leanh::lean_ctor_get(v_a_4268_, 0);
                if leanh::lean_obj_tag(v_fst_4272_) == 0 {
                    v_snd_4273_ = leanh::lean_ctor_get(v_a_4268_, 1);
                    leanh::lean_inc(v_snd_4273_);
                    leanh::lean_dec(v_a_4268_);
                    v___x_4274_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4274_, 0, v_snd_4273_);
                    if v_isShared_4271_ == 0 {
                        leanh::lean_ctor_set(v___x_4270_, 0, v___x_4274_);
                        v___x_4276_ = v___x_4270_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4277_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
                        v___x_4276_ = v_reuseFailAlloc_4277_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4272_);
                    leanh::lean_dec(v_a_4268_);
                    v_val_4278_ = leanh::lean_ctor_get(v_fst_4272_, 0);
                    leanh::lean_inc(v_val_4278_);
                    leanh::lean_dec_ref_known(v_fst_4272_, 1);
                    if v_isShared_4271_ == 0 {
                        leanh::lean_ctor_set(v___x_4270_, 0, v_val_4278_);
                        v___x_4280_ = v___x_4270_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4281_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_val_4278_);
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
                    v_reuseFailAlloc_4289_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
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
    mut v_init_4291_: *mut leanh::LeanObject,
    mut v_____s_4292_: *mut leanh::LeanObject,
    mut v_isLower_4293_: u8,
    mut v_as_4294_: *mut leanh::LeanObject,
    mut v_sz_4295_: usize,
    mut v_i_4296_: usize,
    mut v_b_4297_: *mut leanh::LeanObject,
    mut v___y_4298_: *mut leanh::LeanObject,
    mut v___y_4299_: *mut leanh::LeanObject,
    mut v___y_4300_: *mut leanh::LeanObject,
    mut v___y_4301_: *mut leanh::LeanObject,
    mut v___y_4302_: *mut leanh::LeanObject,
    mut v___y_4303_: *mut leanh::LeanObject,
    mut v___y_4304_: *mut leanh::LeanObject,
    mut v___y_4305_: *mut leanh::LeanObject,
    mut v___y_4306_: *mut leanh::LeanObject,
    mut v___y_4307_: *mut leanh::LeanObject,
    mut v___y_4308_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4312_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v_a_4316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4322_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: usize = 0;
    let mut v___x_4334_: usize = 0;
    let mut v_reuseFailAlloc_4336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v_a_4338_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4341_: u8 = 0;
    let mut v___x_4343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_unused_4347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4310_ = lean_usize_dec_lt(v_i_4296_, v_sz_4295_);
                if v___x_4310_ == 0 {
                    v___x_4311_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4311_, 0, v_b_4297_);
                    return v___x_4311_;
                } else {
                    v_snd_4312_ = leanh::lean_ctor_get(v_b_4297_, 1);
                    v_isSharedCheck_4346_ = (!leanh::lean_is_exclusive(v_b_4297_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v_unused_4347_ = leanh::lean_ctor_get(v_b_4297_, 0);
                        leanh::lean_dec(v_unused_4347_);
                        v___x_4314_ = v_b_4297_;
                        v_isShared_4315_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4312_);
                        leanh::lean_dec(v_b_4297_);
                        v___x_4314_ = leanh::lean_box(0);
                        v_isShared_4315_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4316_ = lean_array_uget_borrowed(v_as_4294_, v_i_4296_);
                leanh::lean_inc(v_snd_4312_);
                v___x_4317_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4291_, v_____s_4292_, v_isLower_4293_, v_a_4316_, v_snd_4312_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
                if leanh::lean_obj_tag(v___x_4317_) == 0 {
                    v_a_4318_ = leanh::lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4337_ = (!leanh::lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4320_ = v___x_4317_;
                        v_isShared_4321_ = v_isSharedCheck_4337_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4318_);
                        leanh::lean_dec(v___x_4317_);
                        v___x_4320_ = leanh::lean_box(0);
                        v_isShared_4321_ = v_isSharedCheck_4337_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4314_);
                    leanh::lean_dec(v_snd_4312_);
                    v_a_4338_ = leanh::lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4345_ = (!leanh::lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4345_ == 0 {
                        v___x_4340_ = v___x_4317_;
                        v_isShared_4341_ = v_isSharedCheck_4345_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4338_);
                        leanh::lean_dec(v___x_4317_);
                        v___x_4340_ = leanh::lean_box(0);
                        v_isShared_4341_ = v_isSharedCheck_4345_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4318_) == 0 {
                    v___x_4322_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4322_, 0, v_a_4318_);
                    if v_isShared_4315_ == 0 {
                        leanh::lean_ctor_set(v___x_4314_, 0, v___x_4322_);
                        v___x_4324_ = v___x_4314_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4328_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4322_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_snd_4312_);
                        v___x_4324_ = v_reuseFailAlloc_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4320_);
                    leanh::lean_dec(v_snd_4312_);
                    v_a_4329_ = leanh::lean_ctor_get(v_a_4318_, 0);
                    leanh::lean_inc(v_a_4329_);
                    leanh::lean_dec_ref_known(v_a_4318_, 1);
                    v___x_4330_ = leanh::lean_box(0);
                    if v_isShared_4315_ == 0 {
                        leanh::lean_ctor_set(v___x_4314_, 1, v_a_4329_);
                        leanh::lean_ctor_set(v___x_4314_, 0, v___x_4330_);
                        v___x_4332_ = v___x_4314_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4336_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4330_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_a_4329_);
                        v___x_4332_ = v_reuseFailAlloc_4336_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4321_ == 0 {
                    leanh::lean_ctor_set(v___x_4320_, 0, v___x_4324_);
                    v___x_4326_ = v___x_4320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
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
                    v_reuseFailAlloc_4344_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_init_4348_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_____s_4349_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_isLower_4350_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_as_4351_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_sz_4352_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_i_4353_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_b_4354_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4355_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4356_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4357_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4358_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4359_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4360_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4361_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4362_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4363_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4364_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4365_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_4366_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_isLower_boxed_4367_: u8 = 0;
    let mut v_sz_boxed_4368_: usize = 0;
    let mut v_i_boxed_4369_: usize = 0;
    let mut v_res_4370_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4367_ = (leanh::lean_unbox(v_isLower_4350_) as u8);
    v_sz_boxed_4368_ = leanh::lean_unbox_usize(v_sz_4352_);
    leanh::lean_dec(v_sz_4352_);
    v_i_boxed_4369_ = leanh::lean_unbox_usize(v_i_4353_);
    leanh::lean_dec(v_i_4353_);
    v_res_4370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_4348_, v_____s_4349_, v_isLower_boxed_4367_, v_as_4351_, v_sz_boxed_4368_, v_i_boxed_4369_, v_b_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
    leanh::lean_dec(v___y_4365_);
    leanh::lean_dec_ref(v___y_4364_);
    leanh::lean_dec(v___y_4363_);
    leanh::lean_dec_ref(v___y_4362_);
    leanh::lean_dec(v___y_4361_);
    leanh::lean_dec_ref(v___y_4360_);
    leanh::lean_dec(v___y_4359_);
    leanh::lean_dec_ref(v___y_4358_);
    leanh::lean_dec(v___y_4357_);
    leanh::lean_dec(v___y_4356_);
    leanh::lean_dec(v___y_4355_);
    leanh::lean_dec_ref(v_as_4351_);
    leanh::lean_dec(v_____s_4349_);
    return v_res_4370_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_init_4371_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_____s_4372_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_isLower_4373_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_n_4374_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_4375_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_4376_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4377_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4378_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4379_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4380_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4381_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4382_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4383_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4384_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4385_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4386_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4387_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4388_: u8 = 0;
    let mut v_res_4389_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4388_ = (leanh::lean_unbox(v_isLower_4373_) as u8);
    v_res_4389_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4371_, v_____s_4372_, v_isLower_boxed_4388_, v_n_4374_, v_b_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
    leanh::lean_dec(v___y_4386_);
    leanh::lean_dec_ref(v___y_4385_);
    leanh::lean_dec(v___y_4384_);
    leanh::lean_dec_ref(v___y_4383_);
    leanh::lean_dec(v___y_4382_);
    leanh::lean_dec_ref(v___y_4381_);
    leanh::lean_dec(v___y_4380_);
    leanh::lean_dec_ref(v___y_4379_);
    leanh::lean_dec(v___y_4378_);
    leanh::lean_dec(v___y_4377_);
    leanh::lean_dec(v___y_4376_);
    leanh::lean_dec_ref(v_n_4374_);
    leanh::lean_dec(v_____s_4372_);
    return v_res_4389_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(
    mut v_____s_4390_: *mut leanh::LeanObject,
    mut v_isLower_4391_: u8,
    mut v_as_4392_: *mut leanh::LeanObject,
    mut v_sz_4393_: usize,
    mut v_i_4394_: usize,
    mut v_b_4395_: *mut leanh::LeanObject,
    mut v___y_4396_: *mut leanh::LeanObject,
    mut v___y_4397_: *mut leanh::LeanObject,
    mut v___y_4398_: *mut leanh::LeanObject,
    mut v___y_4399_: *mut leanh::LeanObject,
    mut v___y_4400_: *mut leanh::LeanObject,
    mut v___y_4401_: *mut leanh::LeanObject,
    mut v___y_4402_: *mut leanh::LeanObject,
    mut v___y_4403_: *mut leanh::LeanObject,
    mut v___y_4404_: *mut leanh::LeanObject,
    mut v___y_4405_: *mut leanh::LeanObject,
    mut v___y_4406_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4413_: u8 = 0;
    let mut v_a_4414_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4415_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: usize = 0;
    let mut v___x_4423_: usize = 0;
    let mut v_reuseFailAlloc_4425_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v_a_4433_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4436_: u8 = 0;
    let mut v___x_4438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v_a_4445_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4446_: u8 = 0;
    let mut v_a_4447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4450_: u8 = 0;
    let mut v___x_4452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut v___x_4455_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4457_: u8 = 0;
    let mut v_k_4458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v___x_4468_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_a_4471_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_unused_4480_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4408_ = lean_usize_dec_lt(v_i_4394_, v_sz_4393_);
                if v___x_4408_ == 0 {
                    v___x_4409_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4409_, 0, v_b_4395_);
                    return v___x_4409_;
                } else {
                    v_snd_4410_ = leanh::lean_ctor_get(v_b_4395_, 1);
                    v_isSharedCheck_4479_ = (!leanh::lean_is_exclusive(v_b_4395_)) as u8;
                    if v_isSharedCheck_4479_ == 0 {
                        v_unused_4480_ = leanh::lean_ctor_get(v_b_4395_, 0);
                        leanh::lean_dec(v_unused_4480_);
                        v___x_4412_ = v_b_4395_;
                        v_isShared_4413_ = v_isSharedCheck_4479_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4410_);
                        leanh::lean_dec(v_b_4395_);
                        v___x_4412_ = leanh::lean_box(0);
                        v_isShared_4413_ = v_isSharedCheck_4479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4414_ = lean_array_uget_borrowed(v_as_4392_, v_i_4394_);
                v_p_4415_ = leanh::lean_ctor_get(v_a_4414_, 0);
                v___x_4416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4415_, v_____s_4390_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                if leanh::lean_obj_tag(v___x_4416_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4416_, 1);
                    v___x_4417_ = leanh::lean_box(0);
                    v___x_4455_ = leanh::lean_box(0);
                    if leanh::lean_obj_tag(v_p_4415_) == 1 {
                        v_k_4458_ = leanh::lean_ctor_get(v_p_4415_, 0);
                        v___x_4459_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        leanh::lean_dec(v_snd_4410_);
                        v___x_4461_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4462_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4461_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                        if leanh::lean_obj_tag(v___x_4462_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4462_, 1);
                            v_a_4419_ = v___x_4455_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_4412_);
                            v_a_4463_ = leanh::lean_ctor_get(v___x_4462_, 0);
                            v_isSharedCheck_4470_ =
                                (!leanh::lean_is_exclusive(v___x_4462_)) as u8;
                            if v_isSharedCheck_4470_ == 0 {
                                v___x_4465_ = v___x_4462_;
                                v_isShared_4466_ = v_isSharedCheck_4470_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4463_);
                                leanh::lean_dec(v___x_4462_);
                                v___x_4465_ = leanh::lean_box(0);
                                v_isShared_4466_ = v_isSharedCheck_4470_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4412_);
                    leanh::lean_dec(v_snd_4410_);
                    v_a_4471_ = leanh::lean_ctor_get(v___x_4416_, 0);
                    v_isSharedCheck_4478_ = (!leanh::lean_is_exclusive(v___x_4416_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4473_ = v___x_4416_;
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4471_);
                        leanh::lean_dec(v___x_4416_);
                        v___x_4473_ = leanh::lean_box(0);
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4413_ == 0 {
                    leanh::lean_ctor_set(v___x_4412_, 1, v_a_4419_);
                    leanh::lean_ctor_set(v___x_4412_, 0, v___x_4417_);
                    v___x_4421_ = v___x_4412_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4417_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_a_4419_);
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
                v___x_4427_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4428_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4427_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                if leanh::lean_obj_tag(v___x_4428_) == 0 {
                    v_a_4429_ = leanh::lean_ctor_get(v___x_4428_, 0);
                    v_isSharedCheck_4446_ = (!leanh::lean_is_exclusive(v___x_4428_)) as u8;
                    if v_isSharedCheck_4446_ == 0 {
                        v___x_4431_ = v___x_4428_;
                        v_isShared_4432_ = v_isSharedCheck_4446_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4429_);
                        leanh::lean_dec(v___x_4428_);
                        v___x_4431_ = leanh::lean_box(0);
                        v_isShared_4432_ = v_isSharedCheck_4446_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4412_);
                    leanh::lean_dec(v_snd_4410_);
                    v_a_4447_ = leanh::lean_ctor_get(v___x_4428_, 0);
                    v_isSharedCheck_4454_ = (!leanh::lean_is_exclusive(v___x_4428_)) as u8;
                    if v_isSharedCheck_4454_ == 0 {
                        v___x_4449_ = v___x_4428_;
                        v_isShared_4450_ = v_isSharedCheck_4454_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4447_);
                        leanh::lean_dec(v___x_4428_);
                        v___x_4449_ = leanh::lean_box(0);
                        v_isShared_4450_ = v_isSharedCheck_4454_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_4429_) == 0 {
                    leanh::lean_del_object(v___x_4412_);
                    v_a_4433_ = leanh::lean_ctor_get(v_a_4429_, 0);
                    v_isSharedCheck_4444_ = (!leanh::lean_is_exclusive(v_a_4429_)) as u8;
                    if v_isSharedCheck_4444_ == 0 {
                        v___x_4435_ = v_a_4429_;
                        v_isShared_4436_ = v_isSharedCheck_4444_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4433_);
                        leanh::lean_dec(v_a_4429_);
                        v___x_4435_ = leanh::lean_box(0);
                        v_isShared_4436_ = v_isSharedCheck_4444_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4431_);
                    leanh::lean_dec(v_snd_4410_);
                    v_a_4445_ = leanh::lean_ctor_get(v_a_4429_, 0);
                    leanh::lean_inc(v_a_4445_);
                    leanh::lean_dec_ref_known(v_a_4429_, 1);
                    v_a_4419_ = v_a_4445_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_4436_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4435_, 1);
                    v___x_4438_ = v___x_4435_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4443_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4433_);
                    v___x_4438_ = v_reuseFailAlloc_4443_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4439_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4439_, 0, v___x_4438_);
                leanh::lean_ctor_set(v___x_4439_, 1, v_snd_4410_);
                if v_isShared_4432_ == 0 {
                    leanh::lean_ctor_set(v___x_4431_, 0, v___x_4439_);
                    v___x_4441_ = v___x_4431_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
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
                    v_reuseFailAlloc_4453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
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
                    leanh::lean_dec(v_snd_4410_);
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
                    v_reuseFailAlloc_4469_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
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
                    v_reuseFailAlloc_4477_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_4481_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4482_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_4483_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_4484_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_4485_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4486_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4487_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4488_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4489_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4490_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4491_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4492_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4493_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4494_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4495_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4496_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4497_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4498_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4499_: u8 = 0;
    let mut v_sz_boxed_4500_: usize = 0;
    let mut v_i_boxed_4501_: usize = 0;
    let mut v_res_4502_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4499_ = (leanh::lean_unbox(v_isLower_4482_) as u8);
    v_sz_boxed_4500_ = leanh::lean_unbox_usize(v_sz_4484_);
    leanh::lean_dec(v_sz_4484_);
    v_i_boxed_4501_ = leanh::lean_unbox_usize(v_i_4485_);
    leanh::lean_dec(v_i_4485_);
    v_res_4502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_4481_, v_isLower_boxed_4499_, v_as_4483_, v_sz_boxed_4500_, v_i_boxed_4501_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
    leanh::lean_dec(v___y_4497_);
    leanh::lean_dec_ref(v___y_4496_);
    leanh::lean_dec(v___y_4495_);
    leanh::lean_dec_ref(v___y_4494_);
    leanh::lean_dec(v___y_4493_);
    leanh::lean_dec_ref(v___y_4492_);
    leanh::lean_dec(v___y_4491_);
    leanh::lean_dec_ref(v___y_4490_);
    leanh::lean_dec(v___y_4489_);
    leanh::lean_dec(v___y_4488_);
    leanh::lean_dec(v___y_4487_);
    leanh::lean_dec_ref(v_as_4483_);
    leanh::lean_dec(v_____s_4481_);
    return v_res_4502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(
    mut v_____s_4503_: *mut leanh::LeanObject,
    mut v_isLower_4504_: u8,
    mut v_as_4505_: *mut leanh::LeanObject,
    mut v_sz_4506_: usize,
    mut v_i_4507_: usize,
    mut v_b_4508_: *mut leanh::LeanObject,
    mut v___y_4509_: *mut leanh::LeanObject,
    mut v___y_4510_: *mut leanh::LeanObject,
    mut v___y_4511_: *mut leanh::LeanObject,
    mut v___y_4512_: *mut leanh::LeanObject,
    mut v___y_4513_: *mut leanh::LeanObject,
    mut v___y_4514_: *mut leanh::LeanObject,
    mut v___y_4515_: *mut leanh::LeanObject,
    mut v___y_4516_: *mut leanh::LeanObject,
    mut v___y_4517_: *mut leanh::LeanObject,
    mut v___y_4518_: *mut leanh::LeanObject,
    mut v___y_4519_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4521_: u8 = 0;
    let mut v___x_4522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v_a_4527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4533_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: usize = 0;
    let mut v___x_4537_: usize = 0;
    let mut v___x_4538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4546_: u8 = 0;
    let mut v_a_4547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v___x_4552_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_a_4559_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v_a_4561_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v___x_4566_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v___y_4570_: u8 = 0;
    let mut v_k_4571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4582_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4583_: u8 = 0;
    let mut v_a_4584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4591_: u8 = 0;
    let mut v_isSharedCheck_4592_: u8 = 0;
    let mut v_unused_4593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4521_ = lean_usize_dec_lt(v_i_4507_, v_sz_4506_);
                if v___x_4521_ == 0 {
                    v___x_4522_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4522_, 0, v_b_4508_);
                    return v___x_4522_;
                } else {
                    v_snd_4523_ = leanh::lean_ctor_get(v_b_4508_, 1);
                    v_isSharedCheck_4592_ = (!leanh::lean_is_exclusive(v_b_4508_)) as u8;
                    if v_isSharedCheck_4592_ == 0 {
                        v_unused_4593_ = leanh::lean_ctor_get(v_b_4508_, 0);
                        leanh::lean_dec(v_unused_4593_);
                        v___x_4525_ = v_b_4508_;
                        v_isShared_4526_ = v_isSharedCheck_4592_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4523_);
                        leanh::lean_dec(v_b_4508_);
                        v___x_4525_ = leanh::lean_box(0);
                        v_isShared_4526_ = v_isSharedCheck_4592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4527_ = lean_array_uget_borrowed(v_as_4505_, v_i_4507_);
                v_p_4528_ = leanh::lean_ctor_get(v_a_4527_, 0);
                v___x_4529_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4528_, v_____s_4503_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                if leanh::lean_obj_tag(v___x_4529_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4529_, 1);
                    v___x_4530_ = leanh::lean_box(0);
                    v___x_4531_ = leanh::lean_box(0);
                    if leanh::lean_obj_tag(v_p_4528_) == 1 {
                        v_k_4571_ = leanh::lean_ctor_get(v_p_4528_, 0);
                        v___x_4572_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        leanh::lean_dec(v_snd_4523_);
                        v___x_4574_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4575_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4574_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                        if leanh::lean_obj_tag(v___x_4575_) == 0 {
                            leanh::lean_dec_ref_known(v___x_4575_, 1);
                            v_a_4533_ = v___x_4530_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_del_object(v___x_4525_);
                            v_a_4576_ = leanh::lean_ctor_get(v___x_4575_, 0);
                            v_isSharedCheck_4583_ =
                                (!leanh::lean_is_exclusive(v___x_4575_)) as u8;
                            if v_isSharedCheck_4583_ == 0 {
                                v___x_4578_ = v___x_4575_;
                                v_isShared_4579_ = v_isSharedCheck_4583_;
                                state = 12;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_4576_);
                                leanh::lean_dec(v___x_4575_);
                                v___x_4578_ = leanh::lean_box(0);
                                v_isShared_4579_ = v_isSharedCheck_4583_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    leanh::lean_del_object(v___x_4525_);
                    leanh::lean_dec(v_snd_4523_);
                    v_a_4584_ = leanh::lean_ctor_get(v___x_4529_, 0);
                    v_isSharedCheck_4591_ = (!leanh::lean_is_exclusive(v___x_4529_)) as u8;
                    if v_isSharedCheck_4591_ == 0 {
                        v___x_4586_ = v___x_4529_;
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 14;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4584_);
                        leanh::lean_dec(v___x_4529_);
                        v___x_4586_ = leanh::lean_box(0);
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4526_ == 0 {
                    leanh::lean_ctor_set(v___x_4525_, 1, v_a_4533_);
                    leanh::lean_ctor_set(v___x_4525_, 0, v___x_4531_);
                    v___x_4535_ = v___x_4525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4531_);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_a_4533_);
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
                v___x_4541_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4542_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4541_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                if leanh::lean_obj_tag(v___x_4542_) == 0 {
                    v_a_4543_ = leanh::lean_ctor_get(v___x_4542_, 0);
                    v_isSharedCheck_4560_ = (!leanh::lean_is_exclusive(v___x_4542_)) as u8;
                    if v_isSharedCheck_4560_ == 0 {
                        v___x_4545_ = v___x_4542_;
                        v_isShared_4546_ = v_isSharedCheck_4560_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4543_);
                        leanh::lean_dec(v___x_4542_);
                        v___x_4545_ = leanh::lean_box(0);
                        v_isShared_4546_ = v_isSharedCheck_4560_;
                        state = 5;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4525_);
                    leanh::lean_dec(v_snd_4523_);
                    v_a_4561_ = leanh::lean_ctor_get(v___x_4542_, 0);
                    v_isSharedCheck_4568_ = (!leanh::lean_is_exclusive(v___x_4542_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4563_ = v___x_4542_;
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 9;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4561_);
                        leanh::lean_dec(v___x_4542_);
                        v___x_4563_ = leanh::lean_box(0);
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if leanh::lean_obj_tag(v_a_4543_) == 0 {
                    leanh::lean_del_object(v___x_4525_);
                    v_a_4547_ = leanh::lean_ctor_get(v_a_4543_, 0);
                    v_isSharedCheck_4558_ = (!leanh::lean_is_exclusive(v_a_4543_)) as u8;
                    if v_isSharedCheck_4558_ == 0 {
                        v___x_4549_ = v_a_4543_;
                        v_isShared_4550_ = v_isSharedCheck_4558_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4547_);
                        leanh::lean_dec(v_a_4543_);
                        v___x_4549_ = leanh::lean_box(0);
                        v_isShared_4550_ = v_isSharedCheck_4558_;
                        state = 6;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4545_);
                    leanh::lean_dec(v_snd_4523_);
                    v_a_4559_ = leanh::lean_ctor_get(v_a_4543_, 0);
                    leanh::lean_inc(v_a_4559_);
                    leanh::lean_dec_ref_known(v_a_4543_, 1);
                    v_a_4533_ = v_a_4559_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_4550_ == 0 {
                    leanh::lean_ctor_set_tag(v___x_4549_, 1);
                    v___x_4552_ = v___x_4549_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4547_);
                    v___x_4552_ = v_reuseFailAlloc_4557_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4553_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_4553_, 0, v___x_4552_);
                leanh::lean_ctor_set(v___x_4553_, 1, v_snd_4523_);
                if v_isShared_4546_ == 0 {
                    leanh::lean_ctor_set(v___x_4545_, 0, v___x_4553_);
                    v___x_4555_ = v___x_4545_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
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
                    v_reuseFailAlloc_4567_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
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
                    leanh::lean_dec(v_snd_4523_);
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
                    v_reuseFailAlloc_4582_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
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
                    v_reuseFailAlloc_4590_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_4594_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4595_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_4596_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_4597_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_4598_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4599_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4600_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4601_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4602_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4603_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4604_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4605_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4606_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4607_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4608_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4609_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4610_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4611_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4612_: u8 = 0;
    let mut v_sz_boxed_4613_: usize = 0;
    let mut v_i_boxed_4614_: usize = 0;
    let mut v_res_4615_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4612_ = (leanh::lean_unbox(v_isLower_4595_) as u8);
    v_sz_boxed_4613_ = leanh::lean_unbox_usize(v_sz_4597_);
    leanh::lean_dec(v_sz_4597_);
    v_i_boxed_4614_ = leanh::lean_unbox_usize(v_i_4598_);
    leanh::lean_dec(v_i_4598_);
    v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_4594_, v_isLower_boxed_4612_, v_as_4596_, v_sz_boxed_4613_, v_i_boxed_4614_, v_b_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
    leanh::lean_dec(v___y_4610_);
    leanh::lean_dec_ref(v___y_4609_);
    leanh::lean_dec(v___y_4608_);
    leanh::lean_dec_ref(v___y_4607_);
    leanh::lean_dec(v___y_4606_);
    leanh::lean_dec_ref(v___y_4605_);
    leanh::lean_dec(v___y_4604_);
    leanh::lean_dec_ref(v___y_4603_);
    leanh::lean_dec(v___y_4602_);
    leanh::lean_dec(v___y_4601_);
    leanh::lean_dec(v___y_4600_);
    leanh::lean_dec_ref(v_as_4596_);
    leanh::lean_dec(v_____s_4594_);
    return v_res_4615_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(
    mut v_____s_4616_: *mut leanh::LeanObject,
    mut v_isLower_4617_: u8,
    mut v_t_4618_: *mut leanh::LeanObject,
    mut v_init_4619_: *mut leanh::LeanObject,
    mut v___y_4620_: *mut leanh::LeanObject,
    mut v___y_4621_: *mut leanh::LeanObject,
    mut v___y_4622_: *mut leanh::LeanObject,
    mut v___y_4623_: *mut leanh::LeanObject,
    mut v___y_4624_: *mut leanh::LeanObject,
    mut v___y_4625_: *mut leanh::LeanObject,
    mut v___y_4626_: *mut leanh::LeanObject,
    mut v___y_4627_: *mut leanh::LeanObject,
    mut v___y_4628_: *mut leanh::LeanObject,
    mut v___y_4629_: *mut leanh::LeanObject,
    mut v___y_4630_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_4632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v_a_4639_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4646_: usize = 0;
    let mut v___x_4647_: usize = 0;
    let mut v___x_4648_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v_fst_4653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4657_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4658_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_a_4663_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v_isSharedCheck_4671_: u8 = 0;
    let mut v_a_4672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4632_ = leanh::lean_ctor_get(v_t_4618_, 0);
                v_tail_4633_ = leanh::lean_ctor_get(v_t_4618_, 1);
                v___x_4634_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4619_, v_____s_4616_, v_isLower_4617_, v_root_4632_, v_init_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                if leanh::lean_obj_tag(v___x_4634_) == 0 {
                    v_a_4635_ = leanh::lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4671_ = (!leanh::lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4671_ == 0 {
                        v___x_4637_ = v___x_4634_;
                        v_isShared_4638_ = v_isSharedCheck_4671_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4635_);
                        leanh::lean_dec(v___x_4634_);
                        v___x_4637_ = leanh::lean_box(0);
                        v_isShared_4638_ = v_isSharedCheck_4671_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4672_ = leanh::lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4679_ = (!leanh::lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4679_ == 0 {
                        v___x_4674_ = v___x_4634_;
                        v_isShared_4675_ = v_isSharedCheck_4679_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4672_);
                        leanh::lean_dec(v___x_4634_);
                        v___x_4674_ = leanh::lean_box(0);
                        v_isShared_4675_ = v_isSharedCheck_4679_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_4635_) == 0 {
                    v_a_4639_ = leanh::lean_ctor_get(v_a_4635_, 0);
                    leanh::lean_inc(v_a_4639_);
                    leanh::lean_dec_ref_known(v_a_4635_, 1);
                    if v_isShared_4638_ == 0 {
                        leanh::lean_ctor_set(v___x_4637_, 0, v_a_4639_);
                        v___x_4641_ = v___x_4637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4642_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4639_);
                        v___x_4641_ = v_reuseFailAlloc_4642_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4637_);
                    v_a_4643_ = leanh::lean_ctor_get(v_a_4635_, 0);
                    leanh::lean_inc(v_a_4643_);
                    leanh::lean_dec_ref_known(v_a_4635_, 1);
                    v___x_4644_ = leanh::lean_box(0);
                    v___x_4645_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4645_, 0, v___x_4644_);
                    leanh::lean_ctor_set(v___x_4645_, 1, v_a_4643_);
                    v_sz_4646_ = lean_array_size(v_tail_4633_);
                    v___x_4647_ = 0usize;
                    v___x_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_4616_, v_isLower_4617_, v_tail_4633_, v_sz_4646_, v___x_4647_, v___x_4645_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                    if leanh::lean_obj_tag(v___x_4648_) == 0 {
                        v_a_4649_ = leanh::lean_ctor_get(v___x_4648_, 0);
                        v_isSharedCheck_4662_ =
                            (!leanh::lean_is_exclusive(v___x_4648_)) as u8;
                        if v_isSharedCheck_4662_ == 0 {
                            v___x_4651_ = v___x_4648_;
                            v_isShared_4652_ = v_isSharedCheck_4662_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4649_);
                            leanh::lean_dec(v___x_4648_);
                            v___x_4651_ = leanh::lean_box(0);
                            v_isShared_4652_ = v_isSharedCheck_4662_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4663_ = leanh::lean_ctor_get(v___x_4648_, 0);
                        v_isSharedCheck_4670_ =
                            (!leanh::lean_is_exclusive(v___x_4648_)) as u8;
                        if v_isSharedCheck_4670_ == 0 {
                            v___x_4665_ = v___x_4648_;
                            v_isShared_4666_ = v_isSharedCheck_4670_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4663_);
                            leanh::lean_dec(v___x_4648_);
                            v___x_4665_ = leanh::lean_box(0);
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
                v_fst_4653_ = leanh::lean_ctor_get(v_a_4649_, 0);
                if leanh::lean_obj_tag(v_fst_4653_) == 0 {
                    v_snd_4654_ = leanh::lean_ctor_get(v_a_4649_, 1);
                    leanh::lean_inc(v_snd_4654_);
                    leanh::lean_dec(v_a_4649_);
                    if v_isShared_4652_ == 0 {
                        leanh::lean_ctor_set(v___x_4651_, 0, v_snd_4654_);
                        v___x_4656_ = v___x_4651_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4657_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_snd_4654_);
                        v___x_4656_ = v_reuseFailAlloc_4657_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4653_);
                    leanh::lean_dec(v_a_4649_);
                    v_val_4658_ = leanh::lean_ctor_get(v_fst_4653_, 0);
                    leanh::lean_inc(v_val_4658_);
                    leanh::lean_dec_ref_known(v_fst_4653_, 1);
                    if v_isShared_4652_ == 0 {
                        leanh::lean_ctor_set(v___x_4651_, 0, v_val_4658_);
                        v___x_4660_ = v___x_4651_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4661_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_val_4658_);
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
                    v_reuseFailAlloc_4669_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
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
                    v_reuseFailAlloc_4678_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
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
    mut v_____s_4680_: *mut leanh::LeanObject,
    mut v_isLower_4681_: *mut leanh::LeanObject,
    mut v_t_4682_: *mut leanh::LeanObject,
    mut v_init_4683_: *mut leanh::LeanObject,
    mut v___y_4684_: *mut leanh::LeanObject,
    mut v___y_4685_: *mut leanh::LeanObject,
    mut v___y_4686_: *mut leanh::LeanObject,
    mut v___y_4687_: *mut leanh::LeanObject,
    mut v___y_4688_: *mut leanh::LeanObject,
    mut v___y_4689_: *mut leanh::LeanObject,
    mut v___y_4690_: *mut leanh::LeanObject,
    mut v___y_4691_: *mut leanh::LeanObject,
    mut v___y_4692_: *mut leanh::LeanObject,
    mut v___y_4693_: *mut leanh::LeanObject,
    mut v___y_4694_: *mut leanh::LeanObject,
    mut v___y_4695_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_boxed_4696_: u8 = 0;
    let mut v_res_4697_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4696_ = (leanh::lean_unbox(v_isLower_4681_) as u8);
    v_res_4697_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_____s_4680_, v_isLower_boxed_4696_, v_t_4682_, v_init_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
    leanh::lean_dec(v___y_4694_);
    leanh::lean_dec_ref(v___y_4693_);
    leanh::lean_dec(v___y_4692_);
    leanh::lean_dec_ref(v___y_4691_);
    leanh::lean_dec(v___y_4690_);
    leanh::lean_dec_ref(v___y_4689_);
    leanh::lean_dec(v___y_4688_);
    leanh::lean_dec_ref(v___y_4687_);
    leanh::lean_dec(v___y_4686_);
    leanh::lean_dec(v___y_4685_);
    leanh::lean_dec(v___y_4684_);
    leanh::lean_dec_ref(v_t_4682_);
    leanh::lean_dec(v_____s_4680_);
    return v_res_4697_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(
    mut v_isLower_4698_: u8,
    mut v_as_4699_: *mut leanh::LeanObject,
    mut v_sz_4700_: usize,
    mut v_i_4701_: usize,
    mut v_b_4702_: *mut leanh::LeanObject,
    mut v___y_4703_: *mut leanh::LeanObject,
    mut v___y_4704_: *mut leanh::LeanObject,
    mut v___y_4705_: *mut leanh::LeanObject,
    mut v___y_4706_: *mut leanh::LeanObject,
    mut v___y_4707_: *mut leanh::LeanObject,
    mut v___y_4708_: *mut leanh::LeanObject,
    mut v___y_4709_: *mut leanh::LeanObject,
    mut v___y_4710_: *mut leanh::LeanObject,
    mut v___y_4711_: *mut leanh::LeanObject,
    mut v___y_4712_: *mut leanh::LeanObject,
    mut v___y_4713_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4715_: u8 = 0;
    let mut v___x_4716_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4717_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v_a_4721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: usize = 0;
    let mut v___x_4730_: usize = 0;
    let mut v_reuseFailAlloc_4732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4738_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_unused_4742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4715_ = lean_usize_dec_lt(v_i_4701_, v_sz_4700_);
                if v___x_4715_ == 0 {
                    v___x_4716_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4716_, 0, v_b_4702_);
                    return v___x_4716_;
                } else {
                    v_snd_4717_ = leanh::lean_ctor_get(v_b_4702_, 1);
                    v_isSharedCheck_4741_ = (!leanh::lean_is_exclusive(v_b_4702_)) as u8;
                    if v_isSharedCheck_4741_ == 0 {
                        v_unused_4742_ = leanh::lean_ctor_get(v_b_4702_, 0);
                        leanh::lean_dec(v_unused_4742_);
                        v___x_4719_ = v_b_4702_;
                        v_isShared_4720_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4717_);
                        leanh::lean_dec(v_b_4702_);
                        v___x_4719_ = leanh::lean_box(0);
                        v_isShared_4720_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4721_ = lean_array_uget_borrowed(v_as_4699_, v_i_4701_);
                v___x_4722_ = leanh::lean_box(0);
                v___x_4723_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_4717_, v_isLower_4698_, v_a_4721_, v___x_4722_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
                if leanh::lean_obj_tag(v___x_4723_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4723_, 1);
                    v___x_4724_ = leanh::lean_box(0);
                    v___x_4725_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4726_ = lean_nat_add(v_snd_4717_, v___x_4725_);
                    leanh::lean_dec(v_snd_4717_);
                    if v_isShared_4720_ == 0 {
                        leanh::lean_ctor_set(v___x_4719_, 1, v___x_4726_);
                        leanh::lean_ctor_set(v___x_4719_, 0, v___x_4724_);
                        v___x_4728_ = v___x_4719_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4732_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4724_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 1, v___x_4726_);
                        v___x_4728_ = v_reuseFailAlloc_4732_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4719_);
                    leanh::lean_dec(v_snd_4717_);
                    v_a_4733_ = leanh::lean_ctor_get(v___x_4723_, 0);
                    v_isSharedCheck_4740_ = (!leanh::lean_is_exclusive(v___x_4723_)) as u8;
                    if v_isSharedCheck_4740_ == 0 {
                        v___x_4735_ = v___x_4723_;
                        v_isShared_4736_ = v_isSharedCheck_4740_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4733_);
                        leanh::lean_dec(v___x_4723_);
                        v___x_4735_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4739_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_4743_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_4744_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_4745_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_4746_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_4747_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_4748_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4749_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4750_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4751_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4752_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4753_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4754_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4755_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4756_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4757_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4758_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4759_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4760_: u8 = 0;
    let mut v_sz_boxed_4761_: usize = 0;
    let mut v_i_boxed_4762_: usize = 0;
    let mut v_res_4763_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4760_ = (leanh::lean_unbox(v_isLower_4743_) as u8);
    v_sz_boxed_4761_ = leanh::lean_unbox_usize(v_sz_4745_);
    leanh::lean_dec(v_sz_4745_);
    v_i_boxed_4762_ = leanh::lean_unbox_usize(v_i_4746_);
    leanh::lean_dec(v_i_4746_);
    v_res_4763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_4760_, v_as_4744_, v_sz_boxed_4761_, v_i_boxed_4762_, v_b_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_);
    leanh::lean_dec(v___y_4758_);
    leanh::lean_dec_ref(v___y_4757_);
    leanh::lean_dec(v___y_4756_);
    leanh::lean_dec_ref(v___y_4755_);
    leanh::lean_dec(v___y_4754_);
    leanh::lean_dec_ref(v___y_4753_);
    leanh::lean_dec(v___y_4752_);
    leanh::lean_dec_ref(v___y_4751_);
    leanh::lean_dec(v___y_4750_);
    leanh::lean_dec(v___y_4749_);
    leanh::lean_dec(v___y_4748_);
    leanh::lean_dec_ref(v_as_4744_);
    return v_res_4763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(
    mut v_isLower_4764_: u8,
    mut v_as_4765_: *mut leanh::LeanObject,
    mut v_sz_4766_: usize,
    mut v_i_4767_: usize,
    mut v_b_4768_: *mut leanh::LeanObject,
    mut v___y_4769_: *mut leanh::LeanObject,
    mut v___y_4770_: *mut leanh::LeanObject,
    mut v___y_4771_: *mut leanh::LeanObject,
    mut v___y_4772_: *mut leanh::LeanObject,
    mut v___y_4773_: *mut leanh::LeanObject,
    mut v___y_4774_: *mut leanh::LeanObject,
    mut v___y_4775_: *mut leanh::LeanObject,
    mut v___y_4776_: *mut leanh::LeanObject,
    mut v___y_4777_: *mut leanh::LeanObject,
    mut v___y_4778_: *mut leanh::LeanObject,
    mut v___y_4779_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4783_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4786_: u8 = 0;
    let mut v_a_4787_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: usize = 0;
    let mut v___x_4796_: usize = 0;
    let mut v___x_4797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4802_: u8 = 0;
    let mut v___x_4804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v_unused_4808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4781_ = lean_usize_dec_lt(v_i_4767_, v_sz_4766_);
                if v___x_4781_ == 0 {
                    v___x_4782_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4782_, 0, v_b_4768_);
                    return v___x_4782_;
                } else {
                    v_snd_4783_ = leanh::lean_ctor_get(v_b_4768_, 1);
                    v_isSharedCheck_4807_ = (!leanh::lean_is_exclusive(v_b_4768_)) as u8;
                    if v_isSharedCheck_4807_ == 0 {
                        v_unused_4808_ = leanh::lean_ctor_get(v_b_4768_, 0);
                        leanh::lean_dec(v_unused_4808_);
                        v___x_4785_ = v_b_4768_;
                        v_isShared_4786_ = v_isSharedCheck_4807_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4783_);
                        leanh::lean_dec(v_b_4768_);
                        v___x_4785_ = leanh::lean_box(0);
                        v_isShared_4786_ = v_isSharedCheck_4807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4787_ = lean_array_uget_borrowed(v_as_4765_, v_i_4767_);
                v___x_4788_ = leanh::lean_box(0);
                v___x_4789_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_4783_, v_isLower_4764_, v_a_4787_, v___x_4788_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
                if leanh::lean_obj_tag(v___x_4789_) == 0 {
                    leanh::lean_dec_ref_known(v___x_4789_, 1);
                    v___x_4790_ = leanh::lean_box(0);
                    v___x_4791_ = leanh::lean_unsigned_to_nat(1);
                    v___x_4792_ = lean_nat_add(v_snd_4783_, v___x_4791_);
                    leanh::lean_dec(v_snd_4783_);
                    if v_isShared_4786_ == 0 {
                        leanh::lean_ctor_set(v___x_4785_, 1, v___x_4792_);
                        leanh::lean_ctor_set(v___x_4785_, 0, v___x_4790_);
                        v___x_4794_ = v___x_4785_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4798_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4790_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 1, v___x_4792_);
                        v___x_4794_ = v_reuseFailAlloc_4798_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4785_);
                    leanh::lean_dec(v_snd_4783_);
                    v_a_4799_ = leanh::lean_ctor_get(v___x_4789_, 0);
                    v_isSharedCheck_4806_ = (!leanh::lean_is_exclusive(v___x_4789_)) as u8;
                    if v_isSharedCheck_4806_ == 0 {
                        v___x_4801_ = v___x_4789_;
                        v_isShared_4802_ = v_isSharedCheck_4806_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4799_);
                        leanh::lean_dec(v___x_4789_);
                        v___x_4801_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_4805_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_4809_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_4810_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_4811_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_4812_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_4813_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_4814_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4815_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4816_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4817_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4818_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4819_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4820_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4821_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4822_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4823_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4824_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4825_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4826_: u8 = 0;
    let mut v_sz_boxed_4827_: usize = 0;
    let mut v_i_boxed_4828_: usize = 0;
    let mut v_res_4829_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4826_ = (leanh::lean_unbox(v_isLower_4809_) as u8);
    v_sz_boxed_4827_ = leanh::lean_unbox_usize(v_sz_4811_);
    leanh::lean_dec(v_sz_4811_);
    v_i_boxed_4828_ = leanh::lean_unbox_usize(v_i_4812_);
    leanh::lean_dec(v_i_4812_);
    v_res_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_4826_, v_as_4810_, v_sz_boxed_4827_, v_i_boxed_4828_, v_b_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
    leanh::lean_dec(v___y_4824_);
    leanh::lean_dec_ref(v___y_4823_);
    leanh::lean_dec(v___y_4822_);
    leanh::lean_dec_ref(v___y_4821_);
    leanh::lean_dec(v___y_4820_);
    leanh::lean_dec_ref(v___y_4819_);
    leanh::lean_dec(v___y_4818_);
    leanh::lean_dec_ref(v___y_4817_);
    leanh::lean_dec(v___y_4816_);
    leanh::lean_dec(v___y_4815_);
    leanh::lean_dec(v___y_4814_);
    leanh::lean_dec_ref(v_as_4810_);
    return v_res_4829_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(
    mut v_init_4830_: *mut leanh::LeanObject,
    mut v_isLower_4831_: u8,
    mut v_n_4832_: *mut leanh::LeanObject,
    mut v_b_4833_: *mut leanh::LeanObject,
    mut v___y_4834_: *mut leanh::LeanObject,
    mut v___y_4835_: *mut leanh::LeanObject,
    mut v___y_4836_: *mut leanh::LeanObject,
    mut v___y_4837_: *mut leanh::LeanObject,
    mut v___y_4838_: *mut leanh::LeanObject,
    mut v___y_4839_: *mut leanh::LeanObject,
    mut v___y_4840_: *mut leanh::LeanObject,
    mut v___y_4841_: *mut leanh::LeanObject,
    mut v___y_4842_: *mut leanh::LeanObject,
    mut v___y_4843_: *mut leanh::LeanObject,
    mut v___y_4844_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_4846_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4849_: usize = 0;
    let mut v___x_4850_: usize = 0;
    let mut v___x_4851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v_fst_4856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4865_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4866_: u8 = 0;
    let mut v_a_4867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v___x_4872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4874_: u8 = 0;
    let mut v_vs_4875_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4878_: usize = 0;
    let mut v___x_4879_: usize = 0;
    let mut v___x_4880_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v_fst_4885_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4886_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4891_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v_a_4896_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v___x_4901_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_4832_) == 0 {
                    v_cs_4846_ = leanh::lean_ctor_get(v_n_4832_, 0);
                    v___x_4847_ = leanh::lean_box(0);
                    v___x_4848_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4848_, 0, v___x_4847_);
                    leanh::lean_ctor_set(v___x_4848_, 1, v_b_4833_);
                    v_sz_4849_ = lean_array_size(v_cs_4846_);
                    v___x_4850_ = 0usize;
                    v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_4830_, v_isLower_4831_, v_cs_4846_, v_sz_4849_, v___x_4850_, v___x_4848_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
                    if leanh::lean_obj_tag(v___x_4851_) == 0 {
                        v_a_4852_ = leanh::lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4866_ =
                            (!leanh::lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4866_ == 0 {
                            v___x_4854_ = v___x_4851_;
                            v_isShared_4855_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4852_);
                            leanh::lean_dec(v___x_4851_);
                            v___x_4854_ = leanh::lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4867_ = leanh::lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4874_ =
                            (!leanh::lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4874_ == 0 {
                            v___x_4869_ = v___x_4851_;
                            v_isShared_4870_ = v_isSharedCheck_4874_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4867_);
                            leanh::lean_dec(v___x_4851_);
                            v___x_4869_ = leanh::lean_box(0);
                            v_isShared_4870_ = v_isSharedCheck_4874_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4875_ = leanh::lean_ctor_get(v_n_4832_, 0);
                    v___x_4876_ = leanh::lean_box(0);
                    v___x_4877_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_4877_, 0, v___x_4876_);
                    leanh::lean_ctor_set(v___x_4877_, 1, v_b_4833_);
                    v_sz_4878_ = lean_array_size(v_vs_4875_);
                    v___x_4879_ = 0usize;
                    v___x_4880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_4831_, v_vs_4875_, v_sz_4878_, v___x_4879_, v___x_4877_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
                    if leanh::lean_obj_tag(v___x_4880_) == 0 {
                        v_a_4881_ = leanh::lean_ctor_get(v___x_4880_, 0);
                        v_isSharedCheck_4895_ =
                            (!leanh::lean_is_exclusive(v___x_4880_)) as u8;
                        if v_isSharedCheck_4895_ == 0 {
                            v___x_4883_ = v___x_4880_;
                            v_isShared_4884_ = v_isSharedCheck_4895_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4881_);
                            leanh::lean_dec(v___x_4880_);
                            v___x_4883_ = leanh::lean_box(0);
                            v_isShared_4884_ = v_isSharedCheck_4895_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4896_ = leanh::lean_ctor_get(v___x_4880_, 0);
                        v_isSharedCheck_4903_ =
                            (!leanh::lean_is_exclusive(v___x_4880_)) as u8;
                        if v_isSharedCheck_4903_ == 0 {
                            v___x_4898_ = v___x_4880_;
                            v_isShared_4899_ = v_isSharedCheck_4903_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_4896_);
                            leanh::lean_dec(v___x_4880_);
                            v___x_4898_ = leanh::lean_box(0);
                            v_isShared_4899_ = v_isSharedCheck_4903_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4856_ = leanh::lean_ctor_get(v_a_4852_, 0);
                if leanh::lean_obj_tag(v_fst_4856_) == 0 {
                    v_snd_4857_ = leanh::lean_ctor_get(v_a_4852_, 1);
                    leanh::lean_inc(v_snd_4857_);
                    leanh::lean_dec(v_a_4852_);
                    v___x_4858_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4858_, 0, v_snd_4857_);
                    if v_isShared_4855_ == 0 {
                        leanh::lean_ctor_set(v___x_4854_, 0, v___x_4858_);
                        v___x_4860_ = v___x_4854_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4861_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
                        v___x_4860_ = v_reuseFailAlloc_4861_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4856_);
                    leanh::lean_dec(v_a_4852_);
                    v_val_4862_ = leanh::lean_ctor_get(v_fst_4856_, 0);
                    leanh::lean_inc(v_val_4862_);
                    leanh::lean_dec_ref_known(v_fst_4856_, 1);
                    if v_isShared_4855_ == 0 {
                        leanh::lean_ctor_set(v___x_4854_, 0, v_val_4862_);
                        v___x_4864_ = v___x_4854_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4865_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_val_4862_);
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
                    v_reuseFailAlloc_4873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
                    v___x_4872_ = v_reuseFailAlloc_4873_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4872_;
            }
            6 => {
                v_fst_4885_ = leanh::lean_ctor_get(v_a_4881_, 0);
                if leanh::lean_obj_tag(v_fst_4885_) == 0 {
                    v_snd_4886_ = leanh::lean_ctor_get(v_a_4881_, 1);
                    leanh::lean_inc(v_snd_4886_);
                    leanh::lean_dec(v_a_4881_);
                    v___x_4887_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4887_, 0, v_snd_4886_);
                    if v_isShared_4884_ == 0 {
                        leanh::lean_ctor_set(v___x_4883_, 0, v___x_4887_);
                        v___x_4889_ = v___x_4883_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4890_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
                        v___x_4889_ = v_reuseFailAlloc_4890_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_4885_);
                    leanh::lean_dec(v_a_4881_);
                    v_val_4891_ = leanh::lean_ctor_get(v_fst_4885_, 0);
                    leanh::lean_inc(v_val_4891_);
                    leanh::lean_dec_ref_known(v_fst_4885_, 1);
                    if v_isShared_4884_ == 0 {
                        leanh::lean_ctor_set(v___x_4883_, 0, v_val_4891_);
                        v___x_4893_ = v___x_4883_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4894_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_val_4891_);
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
                    v_reuseFailAlloc_4902_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
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
    mut v_init_4904_: *mut leanh::LeanObject,
    mut v_isLower_4905_: u8,
    mut v_as_4906_: *mut leanh::LeanObject,
    mut v_sz_4907_: usize,
    mut v_i_4908_: usize,
    mut v_b_4909_: *mut leanh::LeanObject,
    mut v___y_4910_: *mut leanh::LeanObject,
    mut v___y_4911_: *mut leanh::LeanObject,
    mut v___y_4912_: *mut leanh::LeanObject,
    mut v___y_4913_: *mut leanh::LeanObject,
    mut v___y_4914_: *mut leanh::LeanObject,
    mut v___y_4915_: *mut leanh::LeanObject,
    mut v___y_4916_: *mut leanh::LeanObject,
    mut v___y_4917_: *mut leanh::LeanObject,
    mut v___y_4918_: *mut leanh::LeanObject,
    mut v___y_4919_: *mut leanh::LeanObject,
    mut v___y_4920_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_4922_: u8 = 0;
    let mut v___x_4923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4924_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v_a_4928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v___x_4934_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4940_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: usize = 0;
    let mut v___x_4946_: usize = 0;
    let mut v_reuseFailAlloc_4948_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_a_4950_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut v_isSharedCheck_4958_: u8 = 0;
    let mut v_unused_4959_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4922_ = lean_usize_dec_lt(v_i_4908_, v_sz_4907_);
                if v___x_4922_ == 0 {
                    v___x_4923_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4923_, 0, v_b_4909_);
                    return v___x_4923_;
                } else {
                    v_snd_4924_ = leanh::lean_ctor_get(v_b_4909_, 1);
                    v_isSharedCheck_4958_ = (!leanh::lean_is_exclusive(v_b_4909_)) as u8;
                    if v_isSharedCheck_4958_ == 0 {
                        v_unused_4959_ = leanh::lean_ctor_get(v_b_4909_, 0);
                        leanh::lean_dec(v_unused_4959_);
                        v___x_4926_ = v_b_4909_;
                        v_isShared_4927_ = v_isSharedCheck_4958_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_4924_);
                        leanh::lean_dec(v_b_4909_);
                        v___x_4926_ = leanh::lean_box(0);
                        v_isShared_4927_ = v_isSharedCheck_4958_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4928_ = lean_array_uget_borrowed(v_as_4906_, v_i_4908_);
                leanh::lean_inc(v_snd_4924_);
                v___x_4929_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_4904_, v_isLower_4905_, v_a_4928_, v_snd_4924_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
                if leanh::lean_obj_tag(v___x_4929_) == 0 {
                    v_a_4930_ = leanh::lean_ctor_get(v___x_4929_, 0);
                    v_isSharedCheck_4949_ = (!leanh::lean_is_exclusive(v___x_4929_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4932_ = v___x_4929_;
                        v_isShared_4933_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4930_);
                        leanh::lean_dec(v___x_4929_);
                        v___x_4932_ = leanh::lean_box(0);
                        v_isShared_4933_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4926_);
                    leanh::lean_dec(v_snd_4924_);
                    v_a_4950_ = leanh::lean_ctor_get(v___x_4929_, 0);
                    v_isSharedCheck_4957_ = (!leanh::lean_is_exclusive(v___x_4929_)) as u8;
                    if v_isSharedCheck_4957_ == 0 {
                        v___x_4952_ = v___x_4929_;
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_4950_);
                        leanh::lean_dec(v___x_4929_);
                        v___x_4952_ = leanh::lean_box(0);
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_4930_) == 0 {
                    v___x_4934_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_4934_, 0, v_a_4930_);
                    if v_isShared_4927_ == 0 {
                        leanh::lean_ctor_set(v___x_4926_, 0, v___x_4934_);
                        v___x_4936_ = v___x_4926_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4940_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4934_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4940_, 1, v_snd_4924_);
                        v___x_4936_ = v_reuseFailAlloc_4940_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_4932_);
                    leanh::lean_dec(v_snd_4924_);
                    v_a_4941_ = leanh::lean_ctor_get(v_a_4930_, 0);
                    leanh::lean_inc(v_a_4941_);
                    leanh::lean_dec_ref_known(v_a_4930_, 1);
                    v___x_4942_ = leanh::lean_box(0);
                    if v_isShared_4927_ == 0 {
                        leanh::lean_ctor_set(v___x_4926_, 1, v_a_4941_);
                        leanh::lean_ctor_set(v___x_4926_, 0, v___x_4942_);
                        v___x_4944_ = v___x_4926_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4948_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4942_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 1, v_a_4941_);
                        v___x_4944_ = v_reuseFailAlloc_4948_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4933_ == 0 {
                    leanh::lean_ctor_set(v___x_4932_, 0, v___x_4936_);
                    v___x_4938_ = v___x_4932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4939_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4936_);
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
                    v_reuseFailAlloc_4956_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_init_4960_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4961_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_4962_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_4963_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_4964_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_4965_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_4966_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_4967_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_4968_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_4969_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_4970_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_4971_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_4972_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_4973_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_4974_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_4975_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_4976_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_4977_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4978_: u8 = 0;
    let mut v_sz_boxed_4979_: usize = 0;
    let mut v_i_boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4978_ = (leanh::lean_unbox(v_isLower_4961_) as u8);
    v_sz_boxed_4979_ = leanh::lean_unbox_usize(v_sz_4963_);
    leanh::lean_dec(v_sz_4963_);
    v_i_boxed_4980_ = leanh::lean_unbox_usize(v_i_4964_);
    leanh::lean_dec(v_i_4964_);
    v_res_4981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_4960_, v_isLower_boxed_4978_, v_as_4962_, v_sz_boxed_4979_, v_i_boxed_4980_, v_b_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
    leanh::lean_dec(v___y_4976_);
    leanh::lean_dec_ref(v___y_4975_);
    leanh::lean_dec(v___y_4974_);
    leanh::lean_dec_ref(v___y_4973_);
    leanh::lean_dec(v___y_4972_);
    leanh::lean_dec_ref(v___y_4971_);
    leanh::lean_dec(v___y_4970_);
    leanh::lean_dec_ref(v___y_4969_);
    leanh::lean_dec(v___y_4968_);
    leanh::lean_dec(v___y_4967_);
    leanh::lean_dec(v___y_4966_);
    leanh::lean_dec_ref(v_as_4962_);
    leanh::lean_dec(v_init_4960_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4___boxed(
    mut v_init_4982_: *mut leanh::LeanObject,
    mut v_isLower_4983_: *mut leanh::LeanObject,
    mut v_n_4984_: *mut leanh::LeanObject,
    mut v_b_4985_: *mut leanh::LeanObject,
    mut v___y_4986_: *mut leanh::LeanObject,
    mut v___y_4987_: *mut leanh::LeanObject,
    mut v___y_4988_: *mut leanh::LeanObject,
    mut v___y_4989_: *mut leanh::LeanObject,
    mut v___y_4990_: *mut leanh::LeanObject,
    mut v___y_4991_: *mut leanh::LeanObject,
    mut v___y_4992_: *mut leanh::LeanObject,
    mut v___y_4993_: *mut leanh::LeanObject,
    mut v___y_4994_: *mut leanh::LeanObject,
    mut v___y_4995_: *mut leanh::LeanObject,
    mut v___y_4996_: *mut leanh::LeanObject,
    mut v___y_4997_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_boxed_4998_: u8 = 0;
    let mut v_res_4999_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4998_ = (leanh::lean_unbox(v_isLower_4983_) as u8);
    v_res_4999_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_4982_, v_isLower_boxed_4998_, v_n_4984_, v_b_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
    leanh::lean_dec(v___y_4996_);
    leanh::lean_dec_ref(v___y_4995_);
    leanh::lean_dec(v___y_4994_);
    leanh::lean_dec_ref(v___y_4993_);
    leanh::lean_dec(v___y_4992_);
    leanh::lean_dec_ref(v___y_4991_);
    leanh::lean_dec(v___y_4990_);
    leanh::lean_dec_ref(v___y_4989_);
    leanh::lean_dec(v___y_4988_);
    leanh::lean_dec(v___y_4987_);
    leanh::lean_dec(v___y_4986_);
    leanh::lean_dec_ref(v_n_4984_);
    leanh::lean_dec(v_init_4982_);
    return v_res_4999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(
    mut v_isLower_5000_: u8,
    mut v_as_5001_: *mut leanh::LeanObject,
    mut v_sz_5002_: usize,
    mut v_i_5003_: usize,
    mut v_b_5004_: *mut leanh::LeanObject,
    mut v___y_5005_: *mut leanh::LeanObject,
    mut v___y_5006_: *mut leanh::LeanObject,
    mut v___y_5007_: *mut leanh::LeanObject,
    mut v___y_5008_: *mut leanh::LeanObject,
    mut v___y_5009_: *mut leanh::LeanObject,
    mut v___y_5010_: *mut leanh::LeanObject,
    mut v___y_5011_: *mut leanh::LeanObject,
    mut v___y_5012_: *mut leanh::LeanObject,
    mut v___y_5013_: *mut leanh::LeanObject,
    mut v___y_5014_: *mut leanh::LeanObject,
    mut v___y_5015_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5019_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5022_: u8 = 0;
    let mut v_a_5023_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: usize = 0;
    let mut v_reuseFailAlloc_5034_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5035_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___x_5040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5041_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5042_: u8 = 0;
    let mut v_isSharedCheck_5043_: u8 = 0;
    let mut v_unused_5044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5017_ = lean_usize_dec_lt(v_i_5003_, v_sz_5002_);
                if v___x_5017_ == 0 {
                    v___x_5018_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5018_, 0, v_b_5004_);
                    return v___x_5018_;
                } else {
                    v_snd_5019_ = leanh::lean_ctor_get(v_b_5004_, 1);
                    v_isSharedCheck_5043_ = (!leanh::lean_is_exclusive(v_b_5004_)) as u8;
                    if v_isSharedCheck_5043_ == 0 {
                        v_unused_5044_ = leanh::lean_ctor_get(v_b_5004_, 0);
                        leanh::lean_dec(v_unused_5044_);
                        v___x_5021_ = v_b_5004_;
                        v_isShared_5022_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5019_);
                        leanh::lean_dec(v_b_5004_);
                        v___x_5021_ = leanh::lean_box(0);
                        v_isShared_5022_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5023_ = lean_array_uget_borrowed(v_as_5001_, v_i_5003_);
                v___x_5024_ = leanh::lean_box(0);
                v___x_5025_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_5019_, v_isLower_5000_, v_a_5023_, v___x_5024_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
                if leanh::lean_obj_tag(v___x_5025_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5025_, 1);
                    v___x_5026_ = leanh::lean_box(0);
                    v___x_5027_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5028_ = lean_nat_add(v_snd_5019_, v___x_5027_);
                    leanh::lean_dec(v_snd_5019_);
                    if v_isShared_5022_ == 0 {
                        leanh::lean_ctor_set(v___x_5021_, 1, v___x_5028_);
                        leanh::lean_ctor_set(v___x_5021_, 0, v___x_5026_);
                        v___x_5030_ = v___x_5021_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5034_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5026_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5034_, 1, v___x_5028_);
                        v___x_5030_ = v_reuseFailAlloc_5034_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5021_);
                    leanh::lean_dec(v_snd_5019_);
                    v_a_5035_ = leanh::lean_ctor_get(v___x_5025_, 0);
                    v_isSharedCheck_5042_ = (!leanh::lean_is_exclusive(v___x_5025_)) as u8;
                    if v_isSharedCheck_5042_ == 0 {
                        v___x_5037_ = v___x_5025_;
                        v_isShared_5038_ = v_isSharedCheck_5042_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5035_);
                        leanh::lean_dec(v___x_5025_);
                        v___x_5037_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5041_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_5045_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_5046_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_5047_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_5048_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_5049_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5050_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5051_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5052_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5053_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5054_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5055_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5056_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5057_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5058_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5059_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5060_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5061_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5062_: u8 = 0;
    let mut v_sz_boxed_5063_: usize = 0;
    let mut v_i_boxed_5064_: usize = 0;
    let mut v_res_5065_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5062_ = (leanh::lean_unbox(v_isLower_5045_) as u8);
    v_sz_boxed_5063_ = leanh::lean_unbox_usize(v_sz_5047_);
    leanh::lean_dec(v_sz_5047_);
    v_i_boxed_5064_ = leanh::lean_unbox_usize(v_i_5048_);
    leanh::lean_dec(v_i_5048_);
    v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_5062_, v_as_5046_, v_sz_boxed_5063_, v_i_boxed_5064_, v_b_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
    leanh::lean_dec(v___y_5060_);
    leanh::lean_dec_ref(v___y_5059_);
    leanh::lean_dec(v___y_5058_);
    leanh::lean_dec_ref(v___y_5057_);
    leanh::lean_dec(v___y_5056_);
    leanh::lean_dec_ref(v___y_5055_);
    leanh::lean_dec(v___y_5054_);
    leanh::lean_dec_ref(v___y_5053_);
    leanh::lean_dec(v___y_5052_);
    leanh::lean_dec(v___y_5051_);
    leanh::lean_dec(v___y_5050_);
    leanh::lean_dec_ref(v_as_5046_);
    return v_res_5065_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(
    mut v_isLower_5066_: u8,
    mut v_as_5067_: *mut leanh::LeanObject,
    mut v_sz_5068_: usize,
    mut v_i_5069_: usize,
    mut v_b_5070_: *mut leanh::LeanObject,
    mut v___y_5071_: *mut leanh::LeanObject,
    mut v___y_5072_: *mut leanh::LeanObject,
    mut v___y_5073_: *mut leanh::LeanObject,
    mut v___y_5074_: *mut leanh::LeanObject,
    mut v___y_5075_: *mut leanh::LeanObject,
    mut v___y_5076_: *mut leanh::LeanObject,
    mut v___y_5077_: *mut leanh::LeanObject,
    mut v___y_5078_: *mut leanh::LeanObject,
    mut v___y_5079_: *mut leanh::LeanObject,
    mut v___y_5080_: *mut leanh::LeanObject,
    mut v___y_5081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5085_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v_a_5089_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: usize = 0;
    let mut v___x_5098_: usize = 0;
    let mut v___x_5099_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5104_: u8 = 0;
    let mut v___x_5106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5107_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut v_isSharedCheck_5109_: u8 = 0;
    let mut v_unused_5110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5083_ = lean_usize_dec_lt(v_i_5069_, v_sz_5068_);
                if v___x_5083_ == 0 {
                    v___x_5084_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5084_, 0, v_b_5070_);
                    return v___x_5084_;
                } else {
                    v_snd_5085_ = leanh::lean_ctor_get(v_b_5070_, 1);
                    v_isSharedCheck_5109_ = (!leanh::lean_is_exclusive(v_b_5070_)) as u8;
                    if v_isSharedCheck_5109_ == 0 {
                        v_unused_5110_ = leanh::lean_ctor_get(v_b_5070_, 0);
                        leanh::lean_dec(v_unused_5110_);
                        v___x_5087_ = v_b_5070_;
                        v_isShared_5088_ = v_isSharedCheck_5109_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5085_);
                        leanh::lean_dec(v_b_5070_);
                        v___x_5087_ = leanh::lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5109_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5089_ = lean_array_uget_borrowed(v_as_5067_, v_i_5069_);
                v___x_5090_ = leanh::lean_box(0);
                v___x_5091_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_5085_, v_isLower_5066_, v_a_5089_, v___x_5090_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
                if leanh::lean_obj_tag(v___x_5091_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5091_, 1);
                    v___x_5092_ = leanh::lean_box(0);
                    v___x_5093_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5094_ = lean_nat_add(v_snd_5085_, v___x_5093_);
                    leanh::lean_dec(v_snd_5085_);
                    if v_isShared_5088_ == 0 {
                        leanh::lean_ctor_set(v___x_5087_, 1, v___x_5094_);
                        leanh::lean_ctor_set(v___x_5087_, 0, v___x_5092_);
                        v___x_5096_ = v___x_5087_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5100_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5092_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5094_);
                        v___x_5096_ = v_reuseFailAlloc_5100_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5087_);
                    leanh::lean_dec(v_snd_5085_);
                    v_a_5101_ = leanh::lean_ctor_get(v___x_5091_, 0);
                    v_isSharedCheck_5108_ = (!leanh::lean_is_exclusive(v___x_5091_)) as u8;
                    if v_isSharedCheck_5108_ == 0 {
                        v___x_5103_ = v___x_5091_;
                        v_isShared_5104_ = v_isSharedCheck_5108_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5101_);
                        leanh::lean_dec(v___x_5091_);
                        v___x_5103_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5107_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_5111_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_5112_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_5113_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_5114_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_5115_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5116_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5117_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5118_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5119_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5120_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5121_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5122_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5123_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5124_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5125_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5126_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5127_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5128_: u8 = 0;
    let mut v_sz_boxed_5129_: usize = 0;
    let mut v_i_boxed_5130_: usize = 0;
    let mut v_res_5131_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5128_ = (leanh::lean_unbox(v_isLower_5111_) as u8);
    v_sz_boxed_5129_ = leanh::lean_unbox_usize(v_sz_5113_);
    leanh::lean_dec(v_sz_5113_);
    v_i_boxed_5130_ = leanh::lean_unbox_usize(v_i_5114_);
    leanh::lean_dec(v_i_5114_);
    v_res_5131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_5128_, v_as_5112_, v_sz_boxed_5129_, v_i_boxed_5130_, v_b_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
    leanh::lean_dec(v___y_5126_);
    leanh::lean_dec_ref(v___y_5125_);
    leanh::lean_dec(v___y_5124_);
    leanh::lean_dec_ref(v___y_5123_);
    leanh::lean_dec(v___y_5122_);
    leanh::lean_dec_ref(v___y_5121_);
    leanh::lean_dec(v___y_5120_);
    leanh::lean_dec_ref(v___y_5119_);
    leanh::lean_dec(v___y_5118_);
    leanh::lean_dec(v___y_5117_);
    leanh::lean_dec(v___y_5116_);
    leanh::lean_dec_ref(v_as_5112_);
    return v_res_5131_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(
    mut v_isLower_5132_: u8,
    mut v_t_5133_: *mut leanh::LeanObject,
    mut v_init_5134_: *mut leanh::LeanObject,
    mut v___y_5135_: *mut leanh::LeanObject,
    mut v___y_5136_: *mut leanh::LeanObject,
    mut v___y_5137_: *mut leanh::LeanObject,
    mut v___y_5138_: *mut leanh::LeanObject,
    mut v___y_5139_: *mut leanh::LeanObject,
    mut v___y_5140_: *mut leanh::LeanObject,
    mut v___y_5141_: *mut leanh::LeanObject,
    mut v___y_5142_: *mut leanh::LeanObject,
    mut v___y_5143_: *mut leanh::LeanObject,
    mut v___y_5144_: *mut leanh::LeanObject,
    mut v___y_5145_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5153_: u8 = 0;
    let mut v_a_5154_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5157_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5161_: usize = 0;
    let mut v___x_5162_: usize = 0;
    let mut v___x_5163_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5164_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v_fst_5168_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5169_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5177_: u8 = 0;
    let mut v_a_5178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5181_: u8 = 0;
    let mut v___x_5183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut v_a_5187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5147_ = leanh::lean_ctor_get(v_t_5133_, 0);
                v_tail_5148_ = leanh::lean_ctor_get(v_t_5133_, 1);
                leanh::lean_inc(v_init_5134_);
                v___x_5149_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_5134_, v_isLower_5132_, v_root_5147_, v_init_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
                leanh::lean_dec(v_init_5134_);
                if leanh::lean_obj_tag(v___x_5149_) == 0 {
                    v_a_5150_ = leanh::lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5186_ = (!leanh::lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5186_ == 0 {
                        v___x_5152_ = v___x_5149_;
                        v_isShared_5153_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5150_);
                        leanh::lean_dec(v___x_5149_);
                        v___x_5152_ = leanh::lean_box(0);
                        v_isShared_5153_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5187_ = leanh::lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5194_ = (!leanh::lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5194_ == 0 {
                        v___x_5189_ = v___x_5149_;
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5187_);
                        leanh::lean_dec(v___x_5149_);
                        v___x_5189_ = leanh::lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5150_) == 0 {
                    v_a_5154_ = leanh::lean_ctor_get(v_a_5150_, 0);
                    leanh::lean_inc(v_a_5154_);
                    leanh::lean_dec_ref_known(v_a_5150_, 1);
                    if v_isShared_5153_ == 0 {
                        leanh::lean_ctor_set(v___x_5152_, 0, v_a_5154_);
                        v___x_5156_ = v___x_5152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5157_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5154_);
                        v___x_5156_ = v_reuseFailAlloc_5157_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5152_);
                    v_a_5158_ = leanh::lean_ctor_get(v_a_5150_, 0);
                    leanh::lean_inc(v_a_5158_);
                    leanh::lean_dec_ref_known(v_a_5150_, 1);
                    v___x_5159_ = leanh::lean_box(0);
                    v___x_5160_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5160_, 0, v___x_5159_);
                    leanh::lean_ctor_set(v___x_5160_, 1, v_a_5158_);
                    v_sz_5161_ = lean_array_size(v_tail_5148_);
                    v___x_5162_ = 0usize;
                    v___x_5163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_5132_, v_tail_5148_, v_sz_5161_, v___x_5162_, v___x_5160_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
                    if leanh::lean_obj_tag(v___x_5163_) == 0 {
                        v_a_5164_ = leanh::lean_ctor_get(v___x_5163_, 0);
                        v_isSharedCheck_5177_ =
                            (!leanh::lean_is_exclusive(v___x_5163_)) as u8;
                        if v_isSharedCheck_5177_ == 0 {
                            v___x_5166_ = v___x_5163_;
                            v_isShared_5167_ = v_isSharedCheck_5177_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5164_);
                            leanh::lean_dec(v___x_5163_);
                            v___x_5166_ = leanh::lean_box(0);
                            v_isShared_5167_ = v_isSharedCheck_5177_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5178_ = leanh::lean_ctor_get(v___x_5163_, 0);
                        v_isSharedCheck_5185_ =
                            (!leanh::lean_is_exclusive(v___x_5163_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5180_ = v___x_5163_;
                            v_isShared_5181_ = v_isSharedCheck_5185_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5178_);
                            leanh::lean_dec(v___x_5163_);
                            v___x_5180_ = leanh::lean_box(0);
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
                v_fst_5168_ = leanh::lean_ctor_get(v_a_5164_, 0);
                if leanh::lean_obj_tag(v_fst_5168_) == 0 {
                    v_snd_5169_ = leanh::lean_ctor_get(v_a_5164_, 1);
                    leanh::lean_inc(v_snd_5169_);
                    leanh::lean_dec(v_a_5164_);
                    if v_isShared_5167_ == 0 {
                        leanh::lean_ctor_set(v___x_5166_, 0, v_snd_5169_);
                        v___x_5171_ = v___x_5166_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5172_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_snd_5169_);
                        v___x_5171_ = v_reuseFailAlloc_5172_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5168_);
                    leanh::lean_dec(v_a_5164_);
                    v_val_5173_ = leanh::lean_ctor_get(v_fst_5168_, 0);
                    leanh::lean_inc(v_val_5173_);
                    leanh::lean_dec_ref_known(v_fst_5168_, 1);
                    if v_isShared_5167_ == 0 {
                        leanh::lean_ctor_set(v___x_5166_, 0, v_val_5173_);
                        v___x_5175_ = v___x_5166_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5176_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_val_5173_);
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
                    v_reuseFailAlloc_5184_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
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
                    v_reuseFailAlloc_5193_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
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
    mut v_isLower_5195_: *mut leanh::LeanObject,
    mut v_t_5196_: *mut leanh::LeanObject,
    mut v_init_5197_: *mut leanh::LeanObject,
    mut v___y_5198_: *mut leanh::LeanObject,
    mut v___y_5199_: *mut leanh::LeanObject,
    mut v___y_5200_: *mut leanh::LeanObject,
    mut v___y_5201_: *mut leanh::LeanObject,
    mut v___y_5202_: *mut leanh::LeanObject,
    mut v___y_5203_: *mut leanh::LeanObject,
    mut v___y_5204_: *mut leanh::LeanObject,
    mut v___y_5205_: *mut leanh::LeanObject,
    mut v___y_5206_: *mut leanh::LeanObject,
    mut v___y_5207_: *mut leanh::LeanObject,
    mut v___y_5208_: *mut leanh::LeanObject,
    mut v___y_5209_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_boxed_5210_: u8 = 0;
    let mut v_res_5211_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5210_ = (leanh::lean_unbox(v_isLower_5195_) as u8);
    v_res_5211_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_boxed_5210_, v_t_5196_, v_init_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
    leanh::lean_dec(v___y_5208_);
    leanh::lean_dec_ref(v___y_5207_);
    leanh::lean_dec(v___y_5206_);
    leanh::lean_dec_ref(v___y_5205_);
    leanh::lean_dec(v___y_5204_);
    leanh::lean_dec_ref(v___y_5203_);
    leanh::lean_dec(v___y_5202_);
    leanh::lean_dec_ref(v___y_5201_);
    leanh::lean_dec(v___y_5200_);
    leanh::lean_dec(v___y_5199_);
    leanh::lean_dec(v___y_5198_);
    leanh::lean_dec_ref(v_t_5196_);
    return v_res_5211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(
    mut v_css_5212_: *mut leanh::LeanObject,
    mut v_isLower_5213_: u8,
    mut v_a_5214_: *mut leanh::LeanObject,
    mut v_a_5215_: *mut leanh::LeanObject,
    mut v_a_5216_: *mut leanh::LeanObject,
    mut v_a_5217_: *mut leanh::LeanObject,
    mut v_a_5218_: *mut leanh::LeanObject,
    mut v_a_5219_: *mut leanh::LeanObject,
    mut v_a_5220_: *mut leanh::LeanObject,
    mut v_a_5221_: *mut leanh::LeanObject,
    mut v_a_5222_: *mut leanh::LeanObject,
    mut v_a_5223_: *mut leanh::LeanObject,
    mut v_a_5224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_x_5226_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5231_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5235_: u8 = 0;
    let mut v_unused_5236_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5237_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v___x_5242_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5243_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_5226_ = leanh::lean_unsigned_to_nat(0);
                v___x_5227_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_5213_, v_css_5212_, v_x_5226_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
                if leanh::lean_obj_tag(v___x_5227_) == 0 {
                    v_isSharedCheck_5235_ = (!leanh::lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5235_ == 0 {
                        v_unused_5236_ = leanh::lean_ctor_get(v___x_5227_, 0);
                        leanh::lean_dec(v_unused_5236_);
                        v___x_5229_ = v___x_5227_;
                        v_isShared_5230_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_dec(v___x_5227_);
                        v___x_5229_ = leanh::lean_box(0);
                        v_isShared_5230_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5237_ = leanh::lean_ctor_get(v___x_5227_, 0);
                    v_isSharedCheck_5244_ = (!leanh::lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5244_ == 0 {
                        v___x_5239_ = v___x_5227_;
                        v_isShared_5240_ = v_isSharedCheck_5244_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5237_);
                        leanh::lean_dec(v___x_5227_);
                        v___x_5239_ = leanh::lean_box(0);
                        v_isShared_5240_ = v_isSharedCheck_5244_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5231_ = leanh::lean_box(0);
                if v_isShared_5230_ == 0 {
                    leanh::lean_ctor_set(v___x_5229_, 0, v___x_5231_);
                    v___x_5233_ = v___x_5229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5234_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
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
                    v_reuseFailAlloc_5243_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
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
    mut v_css_5245_: *mut leanh::LeanObject,
    mut v_isLower_5246_: *mut leanh::LeanObject,
    mut v_a_5247_: *mut leanh::LeanObject,
    mut v_a_5248_: *mut leanh::LeanObject,
    mut v_a_5249_: *mut leanh::LeanObject,
    mut v_a_5250_: *mut leanh::LeanObject,
    mut v_a_5251_: *mut leanh::LeanObject,
    mut v_a_5252_: *mut leanh::LeanObject,
    mut v_a_5253_: *mut leanh::LeanObject,
    mut v_a_5254_: *mut leanh::LeanObject,
    mut v_a_5255_: *mut leanh::LeanObject,
    mut v_a_5256_: *mut leanh::LeanObject,
    mut v_a_5257_: *mut leanh::LeanObject,
    mut v_a_5258_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_isLower_boxed_5259_: u8 = 0;
    let mut v_res_5260_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5259_ = (leanh::lean_unbox(v_isLower_5246_) as u8);
    v_res_5260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_css_5245_, v_isLower_boxed_5259_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
    leanh::lean_dec(v_a_5257_);
    leanh::lean_dec_ref(v_a_5256_);
    leanh::lean_dec(v_a_5255_);
    leanh::lean_dec_ref(v_a_5254_);
    leanh::lean_dec(v_a_5253_);
    leanh::lean_dec_ref(v_a_5252_);
    leanh::lean_dec(v_a_5251_);
    leanh::lean_dec_ref(v_a_5250_);
    leanh::lean_dec(v_a_5249_);
    leanh::lean_dec(v_a_5248_);
    leanh::lean_dec(v_a_5247_);
    leanh::lean_dec_ref(v_css_5245_);
    return v_res_5260_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5263_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1;
    v___x_5264_ = leanh::lean_unsigned_to_nat(2);
    v___x_5265_ = leanh::lean_unsigned_to_nat(63);
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
    mut v_a_5269_: *mut leanh::LeanObject,
    mut v_a_5270_: *mut leanh::LeanObject,
    mut v_a_5271_: *mut leanh::LeanObject,
    mut v_a_5272_: *mut leanh::LeanObject,
    mut v_a_5273_: *mut leanh::LeanObject,
    mut v_a_5274_: *mut leanh::LeanObject,
    mut v_a_5275_: *mut leanh::LeanObject,
    mut v_a_5276_: *mut leanh::LeanObject,
    mut v_a_5277_: *mut leanh::LeanObject,
    mut v_a_5278_: *mut leanh::LeanObject,
    mut v_a_5279_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5281_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_5283_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5286_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5297_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5281_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_,
                    v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_,
                );
                if leanh::lean_obj_tag(v___x_5281_) == 0 {
                    v_a_5282_ = leanh::lean_ctor_get(v___x_5281_, 0);
                    leanh::lean_inc(v_a_5282_);
                    leanh::lean_dec_ref_known(v___x_5281_, 1);
                    v_lowers_5283_ = leanh::lean_ctor_get(v_a_5282_, 32);
                    leanh::lean_inc_ref(v_lowers_5283_);
                    v_vars_5284_ = leanh::lean_ctor_get(v_a_5282_, 30);
                    leanh::lean_inc_ref(v_vars_5284_);
                    leanh::lean_dec(v_a_5282_);
                    v_size_5285_ = leanh::lean_ctor_get(v_lowers_5283_, 2);
                    v_size_5286_ = leanh::lean_ctor_get(v_vars_5284_, 2);
                    leanh::lean_inc(v_size_5286_);
                    leanh::lean_dec_ref(v_vars_5284_);
                    v___x_5287_ = lean_nat_dec_eq(v_size_5285_, v_size_5286_);
                    leanh::lean_dec(v_size_5286_);
                    if v___x_5287_ == 0 {
                        leanh::lean_dec_ref(v_lowers_5283_);
                        v___x_5288_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2);
                        v___x_5289_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_5288_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
                        return v___x_5289_;
                    } else {
                        v___x_5290_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_lowers_5283_, v___x_5287_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
                        leanh::lean_dec_ref(v_lowers_5283_);
                        return v___x_5290_;
                    }
                } else {
                    v_a_5291_ = leanh::lean_ctor_get(v___x_5281_, 0);
                    v_isSharedCheck_5298_ = (!leanh::lean_is_exclusive(v___x_5281_)) as u8;
                    if v_isSharedCheck_5298_ == 0 {
                        v___x_5293_ = v___x_5281_;
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5291_);
                        leanh::lean_dec(v___x_5281_);
                        v___x_5293_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5297_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
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
    mut v_a_5299_: *mut leanh::LeanObject,
    mut v_a_5300_: *mut leanh::LeanObject,
    mut v_a_5301_: *mut leanh::LeanObject,
    mut v_a_5302_: *mut leanh::LeanObject,
    mut v_a_5303_: *mut leanh::LeanObject,
    mut v_a_5304_: *mut leanh::LeanObject,
    mut v_a_5305_: *mut leanh::LeanObject,
    mut v_a_5306_: *mut leanh::LeanObject,
    mut v_a_5307_: *mut leanh::LeanObject,
    mut v_a_5308_: *mut leanh::LeanObject,
    mut v_a_5309_: *mut leanh::LeanObject,
    mut v_a_5310_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5311_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
    leanh::lean_dec(v_a_5309_);
    leanh::lean_dec_ref(v_a_5308_);
    leanh::lean_dec(v_a_5307_);
    leanh::lean_dec_ref(v_a_5306_);
    leanh::lean_dec(v_a_5305_);
    leanh::lean_dec_ref(v_a_5304_);
    leanh::lean_dec(v_a_5303_);
    leanh::lean_dec_ref(v_a_5302_);
    leanh::lean_dec(v_a_5301_);
    leanh::lean_dec(v_a_5300_);
    leanh::lean_dec(v_a_5299_);
    return v_res_5311_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_5314_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_5314_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1;
    v___x_5315_ = leanh::lean_unsigned_to_nat(2);
    v___x_5316_ = leanh::lean_unsigned_to_nat(68);
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
    mut v_a_5320_: *mut leanh::LeanObject,
    mut v_a_5321_: *mut leanh::LeanObject,
    mut v_a_5322_: *mut leanh::LeanObject,
    mut v_a_5323_: *mut leanh::LeanObject,
    mut v_a_5324_: *mut leanh::LeanObject,
    mut v_a_5325_: *mut leanh::LeanObject,
    mut v_a_5326_: *mut leanh::LeanObject,
    mut v_a_5327_: *mut leanh::LeanObject,
    mut v_a_5328_: *mut leanh::LeanObject,
    mut v_a_5329_: *mut leanh::LeanObject,
    mut v_a_5330_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5333_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_5334_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5335_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5336_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5337_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5343_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5332_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_,
                    v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_,
                );
                if leanh::lean_obj_tag(v___x_5332_) == 0 {
                    v_a_5333_ = leanh::lean_ctor_get(v___x_5332_, 0);
                    leanh::lean_inc(v_a_5333_);
                    leanh::lean_dec_ref_known(v___x_5332_, 1);
                    v_uppers_5334_ = leanh::lean_ctor_get(v_a_5333_, 33);
                    leanh::lean_inc_ref(v_uppers_5334_);
                    v_vars_5335_ = leanh::lean_ctor_get(v_a_5333_, 30);
                    leanh::lean_inc_ref(v_vars_5335_);
                    leanh::lean_dec(v_a_5333_);
                    v_size_5336_ = leanh::lean_ctor_get(v_uppers_5334_, 2);
                    v_size_5337_ = leanh::lean_ctor_get(v_vars_5335_, 2);
                    leanh::lean_inc(v_size_5337_);
                    leanh::lean_dec_ref(v_vars_5335_);
                    v___x_5338_ = lean_nat_dec_eq(v_size_5336_, v_size_5337_);
                    leanh::lean_dec(v_size_5337_);
                    if v___x_5338_ == 0 {
                        leanh::lean_dec_ref(v_uppers_5334_);
                        v___x_5339_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2);
                        v___x_5340_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_5339_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
                        return v___x_5340_;
                    } else {
                        v___x_5341_ = 0;
                        v___x_5342_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_uppers_5334_, v___x_5341_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
                        leanh::lean_dec_ref(v_uppers_5334_);
                        return v___x_5342_;
                    }
                } else {
                    v_a_5343_ = leanh::lean_ctor_get(v___x_5332_, 0);
                    v_isSharedCheck_5350_ = (!leanh::lean_is_exclusive(v___x_5332_)) as u8;
                    if v_isSharedCheck_5350_ == 0 {
                        v___x_5345_ = v___x_5332_;
                        v_isShared_5346_ = v_isSharedCheck_5350_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5343_);
                        leanh::lean_dec(v___x_5332_);
                        v___x_5345_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5349_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
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
    mut v_a_5351_: *mut leanh::LeanObject,
    mut v_a_5352_: *mut leanh::LeanObject,
    mut v_a_5353_: *mut leanh::LeanObject,
    mut v_a_5354_: *mut leanh::LeanObject,
    mut v_a_5355_: *mut leanh::LeanObject,
    mut v_a_5356_: *mut leanh::LeanObject,
    mut v_a_5357_: *mut leanh::LeanObject,
    mut v_a_5358_: *mut leanh::LeanObject,
    mut v_a_5359_: *mut leanh::LeanObject,
    mut v_a_5360_: *mut leanh::LeanObject,
    mut v_a_5361_: *mut leanh::LeanObject,
    mut v_a_5362_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5363_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_);
    leanh::lean_dec(v_a_5361_);
    leanh::lean_dec_ref(v_a_5360_);
    leanh::lean_dec(v_a_5359_);
    leanh::lean_dec_ref(v_a_5358_);
    leanh::lean_dec(v_a_5357_);
    leanh::lean_dec_ref(v_a_5356_);
    leanh::lean_dec(v_a_5355_);
    leanh::lean_dec_ref(v_a_5354_);
    leanh::lean_dec(v_a_5353_);
    leanh::lean_dec(v_a_5352_);
    leanh::lean_dec(v_a_5351_);
    return v_res_5363_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(
    mut v_____s_5367_: *mut leanh::LeanObject,
    mut v_as_5368_: *mut leanh::LeanObject,
    mut v_sz_5369_: usize,
    mut v_i_5370_: usize,
    mut v_b_5371_: *mut leanh::LeanObject,
    mut v___y_5372_: *mut leanh::LeanObject,
    mut v___y_5373_: *mut leanh::LeanObject,
    mut v___y_5374_: *mut leanh::LeanObject,
    mut v___y_5375_: *mut leanh::LeanObject,
    mut v___y_5376_: *mut leanh::LeanObject,
    mut v___y_5377_: *mut leanh::LeanObject,
    mut v___y_5378_: *mut leanh::LeanObject,
    mut v___y_5379_: *mut leanh::LeanObject,
    mut v___y_5380_: *mut leanh::LeanObject,
    mut v___y_5381_: *mut leanh::LeanObject,
    mut v___y_5382_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5384_: u8 = 0;
    let mut v___x_5385_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5386_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5387_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: usize = 0;
    let mut v___x_5391_: usize = 0;
    let mut v_a_5393_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5398_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5384_ = lean_usize_dec_lt(v_i_5370_, v_sz_5369_);
                if v___x_5384_ == 0 {
                    v___x_5385_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5385_, 0, v_b_5371_);
                    return v___x_5385_;
                } else {
                    leanh::lean_dec_ref(v_b_5371_);
                    v_a_5386_ = lean_array_uget_borrowed(v_as_5368_, v_i_5370_);
                    v_p_5387_ = leanh::lean_ctor_get(v_a_5386_, 0);
                    v___x_5388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5387_, v_____s_5367_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
                    if leanh::lean_obj_tag(v___x_5388_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5388_, 1);
                        v___x_5389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_5390_ = 1usize;
                        v___x_5391_ = lean_usize_add(v_i_5370_, v___x_5390_);
                        v_i_5370_ = v___x_5391_;
                        v_b_5371_ = v___x_5389_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5393_ = leanh::lean_ctor_get(v___x_5388_, 0);
                        v_isSharedCheck_5400_ =
                            (!leanh::lean_is_exclusive(v___x_5388_)) as u8;
                        if v_isSharedCheck_5400_ == 0 {
                            v___x_5395_ = v___x_5388_;
                            v_isShared_5396_ = v_isSharedCheck_5400_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5393_);
                            leanh::lean_dec(v___x_5388_);
                            v___x_5395_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5399_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_5401_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_5402_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_5403_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_5404_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_5405_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5406_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5407_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5408_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5409_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5410_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5411_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5412_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5413_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5414_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5415_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5416_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5417_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5418_: usize = 0;
    let mut v_i_boxed_5419_: usize = 0;
    let mut v_res_5420_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5418_ = leanh::lean_unbox_usize(v_sz_5403_);
    leanh::lean_dec(v_sz_5403_);
    v_i_boxed_5419_ = leanh::lean_unbox_usize(v_i_5404_);
    leanh::lean_dec(v_i_5404_);
    v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_5401_, v_as_5402_, v_sz_boxed_5418_, v_i_boxed_5419_, v_b_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
    leanh::lean_dec(v___y_5416_);
    leanh::lean_dec_ref(v___y_5415_);
    leanh::lean_dec(v___y_5414_);
    leanh::lean_dec_ref(v___y_5413_);
    leanh::lean_dec(v___y_5412_);
    leanh::lean_dec_ref(v___y_5411_);
    leanh::lean_dec(v___y_5410_);
    leanh::lean_dec_ref(v___y_5409_);
    leanh::lean_dec(v___y_5408_);
    leanh::lean_dec(v___y_5407_);
    leanh::lean_dec(v___y_5406_);
    leanh::lean_dec_ref(v_as_5402_);
    leanh::lean_dec(v_____s_5401_);
    return v_res_5420_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(
    mut v_____s_5421_: *mut leanh::LeanObject,
    mut v_as_5422_: *mut leanh::LeanObject,
    mut v_sz_5423_: usize,
    mut v_i_5424_: usize,
    mut v_b_5425_: *mut leanh::LeanObject,
    mut v___y_5426_: *mut leanh::LeanObject,
    mut v___y_5427_: *mut leanh::LeanObject,
    mut v___y_5428_: *mut leanh::LeanObject,
    mut v___y_5429_: *mut leanh::LeanObject,
    mut v___y_5430_: *mut leanh::LeanObject,
    mut v___y_5431_: *mut leanh::LeanObject,
    mut v___y_5432_: *mut leanh::LeanObject,
    mut v___y_5433_: *mut leanh::LeanObject,
    mut v___y_5434_: *mut leanh::LeanObject,
    mut v___y_5435_: *mut leanh::LeanObject,
    mut v___y_5436_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5438_: u8 = 0;
    let mut v___x_5439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5440_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5441_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: usize = 0;
    let mut v___x_5445_: usize = 0;
    let mut v___x_5446_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5452_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5438_ = lean_usize_dec_lt(v_i_5424_, v_sz_5423_);
                if v___x_5438_ == 0 {
                    v___x_5439_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5439_, 0, v_b_5425_);
                    return v___x_5439_;
                } else {
                    leanh::lean_dec_ref(v_b_5425_);
                    v_a_5440_ = lean_array_uget_borrowed(v_as_5422_, v_i_5424_);
                    v_p_5441_ = leanh::lean_ctor_get(v_a_5440_, 0);
                    v___x_5442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5441_, v_____s_5421_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
                    if leanh::lean_obj_tag(v___x_5442_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5442_, 1);
                        v___x_5443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_5444_ = 1usize;
                        v___x_5445_ = lean_usize_add(v_i_5424_, v___x_5444_);
                        v___x_5446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_5421_, v_as_5422_, v_sz_5423_, v___x_5445_, v___x_5443_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
                        return v___x_5446_;
                    } else {
                        v_a_5447_ = leanh::lean_ctor_get(v___x_5442_, 0);
                        v_isSharedCheck_5454_ =
                            (!leanh::lean_is_exclusive(v___x_5442_)) as u8;
                        if v_isSharedCheck_5454_ == 0 {
                            v___x_5449_ = v___x_5442_;
                            v_isShared_5450_ = v_isSharedCheck_5454_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5447_);
                            leanh::lean_dec(v___x_5442_);
                            v___x_5449_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5453_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_5455_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_5456_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_5457_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_5458_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_5459_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5460_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5461_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5462_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5463_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5464_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5465_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5466_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5467_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5468_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5469_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5470_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5471_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5472_: usize = 0;
    let mut v_i_boxed_5473_: usize = 0;
    let mut v_res_5474_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5472_ = leanh::lean_unbox_usize(v_sz_5457_);
    leanh::lean_dec(v_sz_5457_);
    v_i_boxed_5473_ = leanh::lean_unbox_usize(v_i_5458_);
    leanh::lean_dec(v_i_5458_);
    v_res_5474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_5455_, v_as_5456_, v_sz_boxed_5472_, v_i_boxed_5473_, v_b_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
    leanh::lean_dec(v___y_5470_);
    leanh::lean_dec_ref(v___y_5469_);
    leanh::lean_dec(v___y_5468_);
    leanh::lean_dec_ref(v___y_5467_);
    leanh::lean_dec(v___y_5466_);
    leanh::lean_dec_ref(v___y_5465_);
    leanh::lean_dec(v___y_5464_);
    leanh::lean_dec_ref(v___y_5463_);
    leanh::lean_dec(v___y_5462_);
    leanh::lean_dec(v___y_5461_);
    leanh::lean_dec(v___y_5460_);
    leanh::lean_dec_ref(v_as_5456_);
    leanh::lean_dec(v_____s_5455_);
    return v_res_5474_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(
    mut v_init_5475_: *mut leanh::LeanObject,
    mut v_____s_5476_: *mut leanh::LeanObject,
    mut v_n_5477_: *mut leanh::LeanObject,
    mut v_b_5478_: *mut leanh::LeanObject,
    mut v___y_5479_: *mut leanh::LeanObject,
    mut v___y_5480_: *mut leanh::LeanObject,
    mut v___y_5481_: *mut leanh::LeanObject,
    mut v___y_5482_: *mut leanh::LeanObject,
    mut v___y_5483_: *mut leanh::LeanObject,
    mut v___y_5484_: *mut leanh::LeanObject,
    mut v___y_5485_: *mut leanh::LeanObject,
    mut v___y_5486_: *mut leanh::LeanObject,
    mut v___y_5487_: *mut leanh::LeanObject,
    mut v___y_5488_: *mut leanh::LeanObject,
    mut v___y_5489_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_5491_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5494_: usize = 0;
    let mut v___x_5495_: usize = 0;
    let mut v___x_5496_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5497_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5500_: u8 = 0;
    let mut v_fst_5501_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5502_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5506_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5507_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5510_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v_a_5512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v___x_5517_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5519_: u8 = 0;
    let mut v_vs_5520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5523_: usize = 0;
    let mut v___x_5524_: usize = 0;
    let mut v___x_5525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5529_: u8 = 0;
    let mut v_fst_5530_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5540_: u8 = 0;
    let mut v_a_5541_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5546_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_5477_) == 0 {
                    v_cs_5491_ = leanh::lean_ctor_get(v_n_5477_, 0);
                    v___x_5492_ = leanh::lean_box(0);
                    v___x_5493_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5493_, 0, v___x_5492_);
                    leanh::lean_ctor_set(v___x_5493_, 1, v_b_5478_);
                    v_sz_5494_ = lean_array_size(v_cs_5491_);
                    v___x_5495_ = 0usize;
                    v___x_5496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_5475_, v_____s_5476_, v_cs_5491_, v_sz_5494_, v___x_5495_, v___x_5493_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
                    if leanh::lean_obj_tag(v___x_5496_) == 0 {
                        v_a_5497_ = leanh::lean_ctor_get(v___x_5496_, 0);
                        v_isSharedCheck_5511_ =
                            (!leanh::lean_is_exclusive(v___x_5496_)) as u8;
                        if v_isSharedCheck_5511_ == 0 {
                            v___x_5499_ = v___x_5496_;
                            v_isShared_5500_ = v_isSharedCheck_5511_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5497_);
                            leanh::lean_dec(v___x_5496_);
                            v___x_5499_ = leanh::lean_box(0);
                            v_isShared_5500_ = v_isSharedCheck_5511_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5512_ = leanh::lean_ctor_get(v___x_5496_, 0);
                        v_isSharedCheck_5519_ =
                            (!leanh::lean_is_exclusive(v___x_5496_)) as u8;
                        if v_isSharedCheck_5519_ == 0 {
                            v___x_5514_ = v___x_5496_;
                            v_isShared_5515_ = v_isSharedCheck_5519_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5512_);
                            leanh::lean_dec(v___x_5496_);
                            v___x_5514_ = leanh::lean_box(0);
                            v_isShared_5515_ = v_isSharedCheck_5519_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5520_ = leanh::lean_ctor_get(v_n_5477_, 0);
                    v___x_5521_ = leanh::lean_box(0);
                    v___x_5522_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5522_, 0, v___x_5521_);
                    leanh::lean_ctor_set(v___x_5522_, 1, v_b_5478_);
                    v_sz_5523_ = lean_array_size(v_vs_5520_);
                    v___x_5524_ = 0usize;
                    v___x_5525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_5476_, v_vs_5520_, v_sz_5523_, v___x_5524_, v___x_5522_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
                    if leanh::lean_obj_tag(v___x_5525_) == 0 {
                        v_a_5526_ = leanh::lean_ctor_get(v___x_5525_, 0);
                        v_isSharedCheck_5540_ =
                            (!leanh::lean_is_exclusive(v___x_5525_)) as u8;
                        if v_isSharedCheck_5540_ == 0 {
                            v___x_5528_ = v___x_5525_;
                            v_isShared_5529_ = v_isSharedCheck_5540_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5526_);
                            leanh::lean_dec(v___x_5525_);
                            v___x_5528_ = leanh::lean_box(0);
                            v_isShared_5529_ = v_isSharedCheck_5540_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5541_ = leanh::lean_ctor_get(v___x_5525_, 0);
                        v_isSharedCheck_5548_ =
                            (!leanh::lean_is_exclusive(v___x_5525_)) as u8;
                        if v_isSharedCheck_5548_ == 0 {
                            v___x_5543_ = v___x_5525_;
                            v_isShared_5544_ = v_isSharedCheck_5548_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5541_);
                            leanh::lean_dec(v___x_5525_);
                            v___x_5543_ = leanh::lean_box(0);
                            v_isShared_5544_ = v_isSharedCheck_5548_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5501_ = leanh::lean_ctor_get(v_a_5497_, 0);
                if leanh::lean_obj_tag(v_fst_5501_) == 0 {
                    v_snd_5502_ = leanh::lean_ctor_get(v_a_5497_, 1);
                    leanh::lean_inc(v_snd_5502_);
                    leanh::lean_dec(v_a_5497_);
                    v___x_5503_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5503_, 0, v_snd_5502_);
                    if v_isShared_5500_ == 0 {
                        leanh::lean_ctor_set(v___x_5499_, 0, v___x_5503_);
                        v___x_5505_ = v___x_5499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5506_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5503_);
                        v___x_5505_ = v_reuseFailAlloc_5506_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5501_);
                    leanh::lean_dec(v_a_5497_);
                    v_val_5507_ = leanh::lean_ctor_get(v_fst_5501_, 0);
                    leanh::lean_inc(v_val_5507_);
                    leanh::lean_dec_ref_known(v_fst_5501_, 1);
                    if v_isShared_5500_ == 0 {
                        leanh::lean_ctor_set(v___x_5499_, 0, v_val_5507_);
                        v___x_5509_ = v___x_5499_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5510_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_val_5507_);
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
                    v_reuseFailAlloc_5518_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
                    v___x_5517_ = v_reuseFailAlloc_5518_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5517_;
            }
            6 => {
                v_fst_5530_ = leanh::lean_ctor_get(v_a_5526_, 0);
                if leanh::lean_obj_tag(v_fst_5530_) == 0 {
                    v_snd_5531_ = leanh::lean_ctor_get(v_a_5526_, 1);
                    leanh::lean_inc(v_snd_5531_);
                    leanh::lean_dec(v_a_5526_);
                    v___x_5532_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5532_, 0, v_snd_5531_);
                    if v_isShared_5529_ == 0 {
                        leanh::lean_ctor_set(v___x_5528_, 0, v___x_5532_);
                        v___x_5534_ = v___x_5528_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5535_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v___x_5532_);
                        v___x_5534_ = v_reuseFailAlloc_5535_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5530_);
                    leanh::lean_dec(v_a_5526_);
                    v_val_5536_ = leanh::lean_ctor_get(v_fst_5530_, 0);
                    leanh::lean_inc(v_val_5536_);
                    leanh::lean_dec_ref_known(v_fst_5530_, 1);
                    if v_isShared_5529_ == 0 {
                        leanh::lean_ctor_set(v___x_5528_, 0, v_val_5536_);
                        v___x_5538_ = v___x_5528_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5539_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_val_5536_);
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
                    v_reuseFailAlloc_5547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
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
    mut v_init_5549_: *mut leanh::LeanObject,
    mut v_____s_5550_: *mut leanh::LeanObject,
    mut v_as_5551_: *mut leanh::LeanObject,
    mut v_sz_5552_: usize,
    mut v_i_5553_: usize,
    mut v_b_5554_: *mut leanh::LeanObject,
    mut v___y_5555_: *mut leanh::LeanObject,
    mut v___y_5556_: *mut leanh::LeanObject,
    mut v___y_5557_: *mut leanh::LeanObject,
    mut v___y_5558_: *mut leanh::LeanObject,
    mut v___y_5559_: *mut leanh::LeanObject,
    mut v___y_5560_: *mut leanh::LeanObject,
    mut v___y_5561_: *mut leanh::LeanObject,
    mut v___y_5562_: *mut leanh::LeanObject,
    mut v___y_5563_: *mut leanh::LeanObject,
    mut v___y_5564_: *mut leanh::LeanObject,
    mut v___y_5565_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5568_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5569_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5572_: u8 = 0;
    let mut v_a_5573_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5575_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5579_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5584_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: usize = 0;
    let mut v___x_5591_: usize = 0;
    let mut v_reuseFailAlloc_5593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut v_a_5595_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v___x_5600_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_isSharedCheck_5603_: u8 = 0;
    let mut v_unused_5604_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5567_ = lean_usize_dec_lt(v_i_5553_, v_sz_5552_);
                if v___x_5567_ == 0 {
                    v___x_5568_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5568_, 0, v_b_5554_);
                    return v___x_5568_;
                } else {
                    v_snd_5569_ = leanh::lean_ctor_get(v_b_5554_, 1);
                    v_isSharedCheck_5603_ = (!leanh::lean_is_exclusive(v_b_5554_)) as u8;
                    if v_isSharedCheck_5603_ == 0 {
                        v_unused_5604_ = leanh::lean_ctor_get(v_b_5554_, 0);
                        leanh::lean_dec(v_unused_5604_);
                        v___x_5571_ = v_b_5554_;
                        v_isShared_5572_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5569_);
                        leanh::lean_dec(v_b_5554_);
                        v___x_5571_ = leanh::lean_box(0);
                        v_isShared_5572_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5573_ = lean_array_uget_borrowed(v_as_5551_, v_i_5553_);
                leanh::lean_inc(v_snd_5569_);
                v___x_5574_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5549_, v_____s_5550_, v_a_5573_, v_snd_5569_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
                if leanh::lean_obj_tag(v___x_5574_) == 0 {
                    v_a_5575_ = leanh::lean_ctor_get(v___x_5574_, 0);
                    v_isSharedCheck_5594_ = (!leanh::lean_is_exclusive(v___x_5574_)) as u8;
                    if v_isSharedCheck_5594_ == 0 {
                        v___x_5577_ = v___x_5574_;
                        v_isShared_5578_ = v_isSharedCheck_5594_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5575_);
                        leanh::lean_dec(v___x_5574_);
                        v___x_5577_ = leanh::lean_box(0);
                        v_isShared_5578_ = v_isSharedCheck_5594_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5571_);
                    leanh::lean_dec(v_snd_5569_);
                    v_a_5595_ = leanh::lean_ctor_get(v___x_5574_, 0);
                    v_isSharedCheck_5602_ = (!leanh::lean_is_exclusive(v___x_5574_)) as u8;
                    if v_isSharedCheck_5602_ == 0 {
                        v___x_5597_ = v___x_5574_;
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5595_);
                        leanh::lean_dec(v___x_5574_);
                        v___x_5597_ = leanh::lean_box(0);
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_5575_) == 0 {
                    v___x_5579_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5579_, 0, v_a_5575_);
                    if v_isShared_5572_ == 0 {
                        leanh::lean_ctor_set(v___x_5571_, 0, v___x_5579_);
                        v___x_5581_ = v___x_5571_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5585_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5579_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_snd_5569_);
                        v___x_5581_ = v_reuseFailAlloc_5585_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5577_);
                    leanh::lean_dec(v_snd_5569_);
                    v_a_5586_ = leanh::lean_ctor_get(v_a_5575_, 0);
                    leanh::lean_inc(v_a_5586_);
                    leanh::lean_dec_ref_known(v_a_5575_, 1);
                    v___x_5587_ = leanh::lean_box(0);
                    if v_isShared_5572_ == 0 {
                        leanh::lean_ctor_set(v___x_5571_, 1, v_a_5586_);
                        leanh::lean_ctor_set(v___x_5571_, 0, v___x_5587_);
                        v___x_5589_ = v___x_5571_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5593_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5587_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_a_5586_);
                        v___x_5589_ = v_reuseFailAlloc_5593_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5578_ == 0 {
                    leanh::lean_ctor_set(v___x_5577_, 0, v___x_5581_);
                    v___x_5583_ = v___x_5577_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5584_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5581_);
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
                    v_reuseFailAlloc_5601_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_init_5605_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_____s_5606_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_as_5607_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_sz_5608_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_i_5609_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_b_5610_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5611_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5612_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5613_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5614_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5615_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5616_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5617_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5618_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5619_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5620_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5621_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_5622_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_sz_boxed_5623_: usize = 0;
    let mut v_i_boxed_5624_: usize = 0;
    let mut v_res_5625_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5623_ = leanh::lean_unbox_usize(v_sz_5608_);
    leanh::lean_dec(v_sz_5608_);
    v_i_boxed_5624_ = leanh::lean_unbox_usize(v_i_5609_);
    leanh::lean_dec(v_i_5609_);
    v_res_5625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_5605_, v_____s_5606_, v_as_5607_, v_sz_boxed_5623_, v_i_boxed_5624_, v_b_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    leanh::lean_dec(v___y_5621_);
    leanh::lean_dec_ref(v___y_5620_);
    leanh::lean_dec(v___y_5619_);
    leanh::lean_dec_ref(v___y_5618_);
    leanh::lean_dec(v___y_5617_);
    leanh::lean_dec_ref(v___y_5616_);
    leanh::lean_dec(v___y_5615_);
    leanh::lean_dec_ref(v___y_5614_);
    leanh::lean_dec(v___y_5613_);
    leanh::lean_dec(v___y_5612_);
    leanh::lean_dec(v___y_5611_);
    leanh::lean_dec_ref(v_as_5607_);
    leanh::lean_dec(v_____s_5606_);
    return v_res_5625_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0___boxed(
    mut v_init_5626_: *mut leanh::LeanObject,
    mut v_____s_5627_: *mut leanh::LeanObject,
    mut v_n_5628_: *mut leanh::LeanObject,
    mut v_b_5629_: *mut leanh::LeanObject,
    mut v___y_5630_: *mut leanh::LeanObject,
    mut v___y_5631_: *mut leanh::LeanObject,
    mut v___y_5632_: *mut leanh::LeanObject,
    mut v___y_5633_: *mut leanh::LeanObject,
    mut v___y_5634_: *mut leanh::LeanObject,
    mut v___y_5635_: *mut leanh::LeanObject,
    mut v___y_5636_: *mut leanh::LeanObject,
    mut v___y_5637_: *mut leanh::LeanObject,
    mut v___y_5638_: *mut leanh::LeanObject,
    mut v___y_5639_: *mut leanh::LeanObject,
    mut v___y_5640_: *mut leanh::LeanObject,
    mut v___y_5641_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5642_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5642_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5626_, v_____s_5627_, v_n_5628_, v_b_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
    leanh::lean_dec(v___y_5640_);
    leanh::lean_dec_ref(v___y_5639_);
    leanh::lean_dec(v___y_5638_);
    leanh::lean_dec_ref(v___y_5637_);
    leanh::lean_dec(v___y_5636_);
    leanh::lean_dec_ref(v___y_5635_);
    leanh::lean_dec(v___y_5634_);
    leanh::lean_dec_ref(v___y_5633_);
    leanh::lean_dec(v___y_5632_);
    leanh::lean_dec(v___y_5631_);
    leanh::lean_dec(v___y_5630_);
    leanh::lean_dec_ref(v_n_5628_);
    leanh::lean_dec(v_____s_5627_);
    return v_res_5642_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(
    mut v_____s_5646_: *mut leanh::LeanObject,
    mut v_as_5647_: *mut leanh::LeanObject,
    mut v_sz_5648_: usize,
    mut v_i_5649_: usize,
    mut v_b_5650_: *mut leanh::LeanObject,
    mut v___y_5651_: *mut leanh::LeanObject,
    mut v___y_5652_: *mut leanh::LeanObject,
    mut v___y_5653_: *mut leanh::LeanObject,
    mut v___y_5654_: *mut leanh::LeanObject,
    mut v___y_5655_: *mut leanh::LeanObject,
    mut v___y_5656_: *mut leanh::LeanObject,
    mut v___y_5657_: *mut leanh::LeanObject,
    mut v___y_5658_: *mut leanh::LeanObject,
    mut v___y_5659_: *mut leanh::LeanObject,
    mut v___y_5660_: *mut leanh::LeanObject,
    mut v___y_5661_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5663_: u8 = 0;
    let mut v___x_5664_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5665_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5666_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: usize = 0;
    let mut v___x_5670_: usize = 0;
    let mut v_a_5672_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5675_: u8 = 0;
    let mut v___x_5677_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5663_ = lean_usize_dec_lt(v_i_5649_, v_sz_5648_);
                if v___x_5663_ == 0 {
                    v___x_5664_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5664_, 0, v_b_5650_);
                    return v___x_5664_;
                } else {
                    leanh::lean_dec_ref(v_b_5650_);
                    v_a_5665_ = lean_array_uget_borrowed(v_as_5647_, v_i_5649_);
                    v_p_5666_ = leanh::lean_ctor_get(v_a_5665_, 0);
                    v___x_5667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5666_, v_____s_5646_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_);
                    if leanh::lean_obj_tag(v___x_5667_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5667_, 1);
                        v___x_5668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_5669_ = 1usize;
                        v___x_5670_ = lean_usize_add(v_i_5649_, v___x_5669_);
                        v_i_5649_ = v___x_5670_;
                        v_b_5650_ = v___x_5668_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5672_ = leanh::lean_ctor_get(v___x_5667_, 0);
                        v_isSharedCheck_5679_ =
                            (!leanh::lean_is_exclusive(v___x_5667_)) as u8;
                        if v_isSharedCheck_5679_ == 0 {
                            v___x_5674_ = v___x_5667_;
                            v_isShared_5675_ = v_isSharedCheck_5679_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5672_);
                            leanh::lean_dec(v___x_5667_);
                            v___x_5674_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5678_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5672_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_5680_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_5681_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_5682_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_5683_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_5684_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5685_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5686_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5687_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5688_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5689_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5690_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5691_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5692_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5693_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5694_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5695_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5696_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5697_: usize = 0;
    let mut v_i_boxed_5698_: usize = 0;
    let mut v_res_5699_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5697_ = leanh::lean_unbox_usize(v_sz_5682_);
    leanh::lean_dec(v_sz_5682_);
    v_i_boxed_5698_ = leanh::lean_unbox_usize(v_i_5683_);
    leanh::lean_dec(v_i_5683_);
    v_res_5699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_5680_, v_as_5681_, v_sz_boxed_5697_, v_i_boxed_5698_, v_b_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_);
    leanh::lean_dec(v___y_5695_);
    leanh::lean_dec_ref(v___y_5694_);
    leanh::lean_dec(v___y_5693_);
    leanh::lean_dec_ref(v___y_5692_);
    leanh::lean_dec(v___y_5691_);
    leanh::lean_dec_ref(v___y_5690_);
    leanh::lean_dec(v___y_5689_);
    leanh::lean_dec_ref(v___y_5688_);
    leanh::lean_dec(v___y_5687_);
    leanh::lean_dec(v___y_5686_);
    leanh::lean_dec(v___y_5685_);
    leanh::lean_dec_ref(v_as_5681_);
    leanh::lean_dec(v_____s_5680_);
    return v_res_5699_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(
    mut v_____s_5700_: *mut leanh::LeanObject,
    mut v_as_5701_: *mut leanh::LeanObject,
    mut v_sz_5702_: usize,
    mut v_i_5703_: usize,
    mut v_b_5704_: *mut leanh::LeanObject,
    mut v___y_5705_: *mut leanh::LeanObject,
    mut v___y_5706_: *mut leanh::LeanObject,
    mut v___y_5707_: *mut leanh::LeanObject,
    mut v___y_5708_: *mut leanh::LeanObject,
    mut v___y_5709_: *mut leanh::LeanObject,
    mut v___y_5710_: *mut leanh::LeanObject,
    mut v___y_5711_: *mut leanh::LeanObject,
    mut v___y_5712_: *mut leanh::LeanObject,
    mut v___y_5713_: *mut leanh::LeanObject,
    mut v___y_5714_: *mut leanh::LeanObject,
    mut v___y_5715_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5717_: u8 = 0;
    let mut v___x_5718_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5719_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5720_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: usize = 0;
    let mut v___x_5724_: usize = 0;
    let mut v___x_5725_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5729_: u8 = 0;
    let mut v___x_5731_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5717_ = lean_usize_dec_lt(v_i_5703_, v_sz_5702_);
                if v___x_5717_ == 0 {
                    v___x_5718_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5718_, 0, v_b_5704_);
                    return v___x_5718_;
                } else {
                    leanh::lean_dec_ref(v_b_5704_);
                    v_a_5719_ = lean_array_uget_borrowed(v_as_5701_, v_i_5703_);
                    v_p_5720_ = leanh::lean_ctor_get(v_a_5719_, 0);
                    v___x_5721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5720_, v_____s_5700_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
                    if leanh::lean_obj_tag(v___x_5721_) == 0 {
                        leanh::lean_dec_ref_known(v___x_5721_, 1);
                        v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_5723_ = 1usize;
                        v___x_5724_ = lean_usize_add(v_i_5703_, v___x_5723_);
                        v___x_5725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_5700_, v_as_5701_, v_sz_5702_, v___x_5724_, v___x_5722_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
                        return v___x_5725_;
                    } else {
                        v_a_5726_ = leanh::lean_ctor_get(v___x_5721_, 0);
                        v_isSharedCheck_5733_ =
                            (!leanh::lean_is_exclusive(v___x_5721_)) as u8;
                        if v_isSharedCheck_5733_ == 0 {
                            v___x_5728_ = v___x_5721_;
                            v_isShared_5729_ = v_isSharedCheck_5733_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5726_);
                            leanh::lean_dec(v___x_5721_);
                            v___x_5728_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5732_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_a_5726_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_____s_5734_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_5735_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_5736_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_5737_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_5738_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_5739_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_5740_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_5741_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_5742_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_5743_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_5744_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_5745_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_5746_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_5747_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_5748_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_5749_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_5750_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5751_: usize = 0;
    let mut v_i_boxed_5752_: usize = 0;
    let mut v_res_5753_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5751_ = leanh::lean_unbox_usize(v_sz_5736_);
    leanh::lean_dec(v_sz_5736_);
    v_i_boxed_5752_ = leanh::lean_unbox_usize(v_i_5737_);
    leanh::lean_dec(v_i_5737_);
    v_res_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_5734_, v_as_5735_, v_sz_boxed_5751_, v_i_boxed_5752_, v_b_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_);
    leanh::lean_dec(v___y_5749_);
    leanh::lean_dec_ref(v___y_5748_);
    leanh::lean_dec(v___y_5747_);
    leanh::lean_dec_ref(v___y_5746_);
    leanh::lean_dec(v___y_5745_);
    leanh::lean_dec_ref(v___y_5744_);
    leanh::lean_dec(v___y_5743_);
    leanh::lean_dec_ref(v___y_5742_);
    leanh::lean_dec(v___y_5741_);
    leanh::lean_dec(v___y_5740_);
    leanh::lean_dec(v___y_5739_);
    leanh::lean_dec_ref(v_as_5735_);
    leanh::lean_dec(v_____s_5734_);
    return v_res_5753_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(
    mut v_____s_5754_: *mut leanh::LeanObject,
    mut v_t_5755_: *mut leanh::LeanObject,
    mut v_init_5756_: *mut leanh::LeanObject,
    mut v___y_5757_: *mut leanh::LeanObject,
    mut v___y_5758_: *mut leanh::LeanObject,
    mut v___y_5759_: *mut leanh::LeanObject,
    mut v___y_5760_: *mut leanh::LeanObject,
    mut v___y_5761_: *mut leanh::LeanObject,
    mut v___y_5762_: *mut leanh::LeanObject,
    mut v___y_5763_: *mut leanh::LeanObject,
    mut v___y_5764_: *mut leanh::LeanObject,
    mut v___y_5765_: *mut leanh::LeanObject,
    mut v___y_5766_: *mut leanh::LeanObject,
    mut v___y_5767_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_5769_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5770_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5772_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v_a_5776_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5783_: usize = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5785_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5786_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5789_: u8 = 0;
    let mut v_fst_5790_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5791_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5799_: u8 = 0;
    let mut v_a_5800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v_a_5809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5812_: u8 = 0;
    let mut v___x_5814_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5769_ = leanh::lean_ctor_get(v_t_5755_, 0);
                v_tail_5770_ = leanh::lean_ctor_get(v_t_5755_, 1);
                v___x_5771_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5756_, v_____s_5754_, v_root_5769_, v_init_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                if leanh::lean_obj_tag(v___x_5771_) == 0 {
                    v_a_5772_ = leanh::lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5808_ = (!leanh::lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5808_ == 0 {
                        v___x_5774_ = v___x_5771_;
                        v_isShared_5775_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5772_);
                        leanh::lean_dec(v___x_5771_);
                        v___x_5774_ = leanh::lean_box(0);
                        v_isShared_5775_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5809_ = leanh::lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5816_ = (!leanh::lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5816_ == 0 {
                        v___x_5811_ = v___x_5771_;
                        v_isShared_5812_ = v_isSharedCheck_5816_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5809_);
                        leanh::lean_dec(v___x_5771_);
                        v___x_5811_ = leanh::lean_box(0);
                        v_isShared_5812_ = v_isSharedCheck_5816_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_5772_) == 0 {
                    v_a_5776_ = leanh::lean_ctor_get(v_a_5772_, 0);
                    leanh::lean_inc(v_a_5776_);
                    leanh::lean_dec_ref_known(v_a_5772_, 1);
                    if v_isShared_5775_ == 0 {
                        leanh::lean_ctor_set(v___x_5774_, 0, v_a_5776_);
                        v___x_5778_ = v___x_5774_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5779_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_a_5776_);
                        v___x_5778_ = v_reuseFailAlloc_5779_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5774_);
                    v_a_5780_ = leanh::lean_ctor_get(v_a_5772_, 0);
                    leanh::lean_inc(v_a_5780_);
                    leanh::lean_dec_ref_known(v_a_5772_, 1);
                    v___x_5781_ = leanh::lean_box(0);
                    v___x_5782_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_5782_, 0, v___x_5781_);
                    leanh::lean_ctor_set(v___x_5782_, 1, v_a_5780_);
                    v_sz_5783_ = lean_array_size(v_tail_5770_);
                    v___x_5784_ = 0usize;
                    v___x_5785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_5754_, v_tail_5770_, v_sz_5783_, v___x_5784_, v___x_5782_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                    if leanh::lean_obj_tag(v___x_5785_) == 0 {
                        v_a_5786_ = leanh::lean_ctor_get(v___x_5785_, 0);
                        v_isSharedCheck_5799_ =
                            (!leanh::lean_is_exclusive(v___x_5785_)) as u8;
                        if v_isSharedCheck_5799_ == 0 {
                            v___x_5788_ = v___x_5785_;
                            v_isShared_5789_ = v_isSharedCheck_5799_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5786_);
                            leanh::lean_dec(v___x_5785_);
                            v___x_5788_ = leanh::lean_box(0);
                            v_isShared_5789_ = v_isSharedCheck_5799_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5800_ = leanh::lean_ctor_get(v___x_5785_, 0);
                        v_isSharedCheck_5807_ =
                            (!leanh::lean_is_exclusive(v___x_5785_)) as u8;
                        if v_isSharedCheck_5807_ == 0 {
                            v___x_5802_ = v___x_5785_;
                            v_isShared_5803_ = v_isSharedCheck_5807_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_5800_);
                            leanh::lean_dec(v___x_5785_);
                            v___x_5802_ = leanh::lean_box(0);
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
                v_fst_5790_ = leanh::lean_ctor_get(v_a_5786_, 0);
                if leanh::lean_obj_tag(v_fst_5790_) == 0 {
                    v_snd_5791_ = leanh::lean_ctor_get(v_a_5786_, 1);
                    leanh::lean_inc(v_snd_5791_);
                    leanh::lean_dec(v_a_5786_);
                    if v_isShared_5789_ == 0 {
                        leanh::lean_ctor_set(v___x_5788_, 0, v_snd_5791_);
                        v___x_5793_ = v___x_5788_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5794_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_snd_5791_);
                        v___x_5793_ = v_reuseFailAlloc_5794_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_5790_);
                    leanh::lean_dec(v_a_5786_);
                    v_val_5795_ = leanh::lean_ctor_get(v_fst_5790_, 0);
                    leanh::lean_inc(v_val_5795_);
                    leanh::lean_dec_ref_known(v_fst_5790_, 1);
                    if v_isShared_5789_ == 0 {
                        leanh::lean_ctor_set(v___x_5788_, 0, v_val_5795_);
                        v___x_5797_ = v___x_5788_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5798_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_val_5795_);
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
                    v_reuseFailAlloc_5806_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
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
                    v_reuseFailAlloc_5815_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_a_5809_);
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
    mut v_____s_5817_: *mut leanh::LeanObject,
    mut v_t_5818_: *mut leanh::LeanObject,
    mut v_init_5819_: *mut leanh::LeanObject,
    mut v___y_5820_: *mut leanh::LeanObject,
    mut v___y_5821_: *mut leanh::LeanObject,
    mut v___y_5822_: *mut leanh::LeanObject,
    mut v___y_5823_: *mut leanh::LeanObject,
    mut v___y_5824_: *mut leanh::LeanObject,
    mut v___y_5825_: *mut leanh::LeanObject,
    mut v___y_5826_: *mut leanh::LeanObject,
    mut v___y_5827_: *mut leanh::LeanObject,
    mut v___y_5828_: *mut leanh::LeanObject,
    mut v___y_5829_: *mut leanh::LeanObject,
    mut v___y_5830_: *mut leanh::LeanObject,
    mut v___y_5831_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_5832_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_5832_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_____s_5817_, v_t_5818_, v_init_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
    leanh::lean_dec(v___y_5830_);
    leanh::lean_dec_ref(v___y_5829_);
    leanh::lean_dec(v___y_5828_);
    leanh::lean_dec_ref(v___y_5827_);
    leanh::lean_dec(v___y_5826_);
    leanh::lean_dec_ref(v___y_5825_);
    leanh::lean_dec(v___y_5824_);
    leanh::lean_dec_ref(v___y_5823_);
    leanh::lean_dec(v___y_5822_);
    leanh::lean_dec(v___y_5821_);
    leanh::lean_dec(v___y_5820_);
    leanh::lean_dec_ref(v_t_5818_);
    leanh::lean_dec(v_____s_5817_);
    return v_res_5832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(
    mut v_as_5833_: *mut leanh::LeanObject,
    mut v_sz_5834_: usize,
    mut v_i_5835_: usize,
    mut v_b_5836_: *mut leanh::LeanObject,
    mut v___y_5837_: *mut leanh::LeanObject,
    mut v___y_5838_: *mut leanh::LeanObject,
    mut v___y_5839_: *mut leanh::LeanObject,
    mut v___y_5840_: *mut leanh::LeanObject,
    mut v___y_5841_: *mut leanh::LeanObject,
    mut v___y_5842_: *mut leanh::LeanObject,
    mut v___y_5843_: *mut leanh::LeanObject,
    mut v___y_5844_: *mut leanh::LeanObject,
    mut v___y_5845_: *mut leanh::LeanObject,
    mut v___y_5846_: *mut leanh::LeanObject,
    mut v___y_5847_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5849_: u8 = 0;
    let mut v___x_5850_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5851_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5854_: u8 = 0;
    let mut v_a_5855_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: usize = 0;
    let mut v___x_5864_: usize = 0;
    let mut v_reuseFailAlloc_5866_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5867_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5872_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut v_isSharedCheck_5875_: u8 = 0;
    let mut v_unused_5876_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5849_ = lean_usize_dec_lt(v_i_5835_, v_sz_5834_);
                if v___x_5849_ == 0 {
                    v___x_5850_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5850_, 0, v_b_5836_);
                    return v___x_5850_;
                } else {
                    v_snd_5851_ = leanh::lean_ctor_get(v_b_5836_, 1);
                    v_isSharedCheck_5875_ = (!leanh::lean_is_exclusive(v_b_5836_)) as u8;
                    if v_isSharedCheck_5875_ == 0 {
                        v_unused_5876_ = leanh::lean_ctor_get(v_b_5836_, 0);
                        leanh::lean_dec(v_unused_5876_);
                        v___x_5853_ = v_b_5836_;
                        v_isShared_5854_ = v_isSharedCheck_5875_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5851_);
                        leanh::lean_dec(v_b_5836_);
                        v___x_5853_ = leanh::lean_box(0);
                        v_isShared_5854_ = v_isSharedCheck_5875_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5855_ = lean_array_uget_borrowed(v_as_5833_, v_i_5835_);
                v___x_5856_ = leanh::lean_box(0);
                v___x_5857_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5851_, v_a_5855_, v___x_5856_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
                if leanh::lean_obj_tag(v___x_5857_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5857_, 1);
                    v___x_5858_ = leanh::lean_box(0);
                    v___x_5859_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5860_ = lean_nat_add(v_snd_5851_, v___x_5859_);
                    leanh::lean_dec(v_snd_5851_);
                    if v_isShared_5854_ == 0 {
                        leanh::lean_ctor_set(v___x_5853_, 1, v___x_5860_);
                        leanh::lean_ctor_set(v___x_5853_, 0, v___x_5858_);
                        v___x_5862_ = v___x_5853_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5866_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___x_5858_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 1, v___x_5860_);
                        v___x_5862_ = v_reuseFailAlloc_5866_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5853_);
                    leanh::lean_dec(v_snd_5851_);
                    v_a_5867_ = leanh::lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5874_ = (!leanh::lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5874_ == 0 {
                        v___x_5869_ = v___x_5857_;
                        v_isShared_5870_ = v_isSharedCheck_5874_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5867_);
                        leanh::lean_dec(v___x_5857_);
                        v___x_5869_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5873_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
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
    mut v_as_5877_: *mut leanh::LeanObject,
    mut v_sz_5878_: *mut leanh::LeanObject,
    mut v_i_5879_: *mut leanh::LeanObject,
    mut v_b_5880_: *mut leanh::LeanObject,
    mut v___y_5881_: *mut leanh::LeanObject,
    mut v___y_5882_: *mut leanh::LeanObject,
    mut v___y_5883_: *mut leanh::LeanObject,
    mut v___y_5884_: *mut leanh::LeanObject,
    mut v___y_5885_: *mut leanh::LeanObject,
    mut v___y_5886_: *mut leanh::LeanObject,
    mut v___y_5887_: *mut leanh::LeanObject,
    mut v___y_5888_: *mut leanh::LeanObject,
    mut v___y_5889_: *mut leanh::LeanObject,
    mut v___y_5890_: *mut leanh::LeanObject,
    mut v___y_5891_: *mut leanh::LeanObject,
    mut v___y_5892_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5893_: usize = 0;
    let mut v_i_boxed_5894_: usize = 0;
    let mut v_res_5895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5893_ = leanh::lean_unbox_usize(v_sz_5878_);
    leanh::lean_dec(v_sz_5878_);
    v_i_boxed_5894_ = leanh::lean_unbox_usize(v_i_5879_);
    leanh::lean_dec(v_i_5879_);
    v_res_5895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_5877_, v_sz_boxed_5893_, v_i_boxed_5894_, v_b_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
    leanh::lean_dec(v___y_5891_);
    leanh::lean_dec_ref(v___y_5890_);
    leanh::lean_dec(v___y_5889_);
    leanh::lean_dec_ref(v___y_5888_);
    leanh::lean_dec(v___y_5887_);
    leanh::lean_dec_ref(v___y_5886_);
    leanh::lean_dec(v___y_5885_);
    leanh::lean_dec_ref(v___y_5884_);
    leanh::lean_dec(v___y_5883_);
    leanh::lean_dec(v___y_5882_);
    leanh::lean_dec(v___y_5881_);
    leanh::lean_dec_ref(v_as_5877_);
    return v_res_5895_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(
    mut v_as_5896_: *mut leanh::LeanObject,
    mut v_sz_5897_: usize,
    mut v_i_5898_: usize,
    mut v_b_5899_: *mut leanh::LeanObject,
    mut v___y_5900_: *mut leanh::LeanObject,
    mut v___y_5901_: *mut leanh::LeanObject,
    mut v___y_5902_: *mut leanh::LeanObject,
    mut v___y_5903_: *mut leanh::LeanObject,
    mut v___y_5904_: *mut leanh::LeanObject,
    mut v___y_5905_: *mut leanh::LeanObject,
    mut v___y_5906_: *mut leanh::LeanObject,
    mut v___y_5907_: *mut leanh::LeanObject,
    mut v___y_5908_: *mut leanh::LeanObject,
    mut v___y_5909_: *mut leanh::LeanObject,
    mut v___y_5910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5912_: u8 = 0;
    let mut v___x_5913_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5914_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v_a_5918_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: usize = 0;
    let mut v___x_5927_: usize = 0;
    let mut v___x_5928_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5929_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5930_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5933_: u8 = 0;
    let mut v___x_5935_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5936_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5937_: u8 = 0;
    let mut v_isSharedCheck_5938_: u8 = 0;
    let mut v_unused_5939_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5912_ = lean_usize_dec_lt(v_i_5898_, v_sz_5897_);
                if v___x_5912_ == 0 {
                    v___x_5913_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5913_, 0, v_b_5899_);
                    return v___x_5913_;
                } else {
                    v_snd_5914_ = leanh::lean_ctor_get(v_b_5899_, 1);
                    v_isSharedCheck_5938_ = (!leanh::lean_is_exclusive(v_b_5899_)) as u8;
                    if v_isSharedCheck_5938_ == 0 {
                        v_unused_5939_ = leanh::lean_ctor_get(v_b_5899_, 0);
                        leanh::lean_dec(v_unused_5939_);
                        v___x_5916_ = v_b_5899_;
                        v_isShared_5917_ = v_isSharedCheck_5938_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5914_);
                        leanh::lean_dec(v_b_5899_);
                        v___x_5916_ = leanh::lean_box(0);
                        v_isShared_5917_ = v_isSharedCheck_5938_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5918_ = lean_array_uget_borrowed(v_as_5896_, v_i_5898_);
                v___x_5919_ = leanh::lean_box(0);
                v___x_5920_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5914_, v_a_5918_, v___x_5919_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
                if leanh::lean_obj_tag(v___x_5920_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5920_, 1);
                    v___x_5921_ = leanh::lean_box(0);
                    v___x_5922_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5923_ = lean_nat_add(v_snd_5914_, v___x_5922_);
                    leanh::lean_dec(v_snd_5914_);
                    if v_isShared_5917_ == 0 {
                        leanh::lean_ctor_set(v___x_5916_, 1, v___x_5923_);
                        leanh::lean_ctor_set(v___x_5916_, 0, v___x_5921_);
                        v___x_5925_ = v___x_5916_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5929_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5921_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 1, v___x_5923_);
                        v___x_5925_ = v_reuseFailAlloc_5929_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5916_);
                    leanh::lean_dec(v_snd_5914_);
                    v_a_5930_ = leanh::lean_ctor_get(v___x_5920_, 0);
                    v_isSharedCheck_5937_ = (!leanh::lean_is_exclusive(v___x_5920_)) as u8;
                    if v_isSharedCheck_5937_ == 0 {
                        v___x_5932_ = v___x_5920_;
                        v_isShared_5933_ = v_isSharedCheck_5937_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5930_);
                        leanh::lean_dec(v___x_5920_);
                        v___x_5932_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5936_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_a_5930_);
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
    mut v_as_5940_: *mut leanh::LeanObject,
    mut v_sz_5941_: *mut leanh::LeanObject,
    mut v_i_5942_: *mut leanh::LeanObject,
    mut v_b_5943_: *mut leanh::LeanObject,
    mut v___y_5944_: *mut leanh::LeanObject,
    mut v___y_5945_: *mut leanh::LeanObject,
    mut v___y_5946_: *mut leanh::LeanObject,
    mut v___y_5947_: *mut leanh::LeanObject,
    mut v___y_5948_: *mut leanh::LeanObject,
    mut v___y_5949_: *mut leanh::LeanObject,
    mut v___y_5950_: *mut leanh::LeanObject,
    mut v___y_5951_: *mut leanh::LeanObject,
    mut v___y_5952_: *mut leanh::LeanObject,
    mut v___y_5953_: *mut leanh::LeanObject,
    mut v___y_5954_: *mut leanh::LeanObject,
    mut v___y_5955_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_5956_: usize = 0;
    let mut v_i_boxed_5957_: usize = 0;
    let mut v_res_5958_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5956_ = leanh::lean_unbox_usize(v_sz_5941_);
    leanh::lean_dec(v_sz_5941_);
    v_i_boxed_5957_ = leanh::lean_unbox_usize(v_i_5942_);
    leanh::lean_dec(v_i_5942_);
    v_res_5958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_as_5940_, v_sz_boxed_5956_, v_i_boxed_5957_, v_b_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
    leanh::lean_dec(v___y_5954_);
    leanh::lean_dec_ref(v___y_5953_);
    leanh::lean_dec(v___y_5952_);
    leanh::lean_dec_ref(v___y_5951_);
    leanh::lean_dec(v___y_5950_);
    leanh::lean_dec_ref(v___y_5949_);
    leanh::lean_dec(v___y_5948_);
    leanh::lean_dec_ref(v___y_5947_);
    leanh::lean_dec(v___y_5946_);
    leanh::lean_dec(v___y_5945_);
    leanh::lean_dec(v___y_5944_);
    leanh::lean_dec_ref(v_as_5940_);
    return v_res_5958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(
    mut v_as_5959_: *mut leanh::LeanObject,
    mut v_sz_5960_: usize,
    mut v_i_5961_: usize,
    mut v_b_5962_: *mut leanh::LeanObject,
    mut v___y_5963_: *mut leanh::LeanObject,
    mut v___y_5964_: *mut leanh::LeanObject,
    mut v___y_5965_: *mut leanh::LeanObject,
    mut v___y_5966_: *mut leanh::LeanObject,
    mut v___y_5967_: *mut leanh::LeanObject,
    mut v___y_5968_: *mut leanh::LeanObject,
    mut v___y_5969_: *mut leanh::LeanObject,
    mut v___y_5970_: *mut leanh::LeanObject,
    mut v___y_5971_: *mut leanh::LeanObject,
    mut v___y_5972_: *mut leanh::LeanObject,
    mut v___y_5973_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_5975_: u8 = 0;
    let mut v___x_5976_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5977_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5980_: u8 = 0;
    let mut v_a_5981_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: usize = 0;
    let mut v___x_5990_: usize = 0;
    let mut v_reuseFailAlloc_5992_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5993_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5996_: u8 = 0;
    let mut v___x_5998_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut v_isSharedCheck_6001_: u8 = 0;
    let mut v_unused_6002_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5975_ = lean_usize_dec_lt(v_i_5961_, v_sz_5960_);
                if v___x_5975_ == 0 {
                    v___x_5976_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_5976_, 0, v_b_5962_);
                    return v___x_5976_;
                } else {
                    v_snd_5977_ = leanh::lean_ctor_get(v_b_5962_, 1);
                    v_isSharedCheck_6001_ = (!leanh::lean_is_exclusive(v_b_5962_)) as u8;
                    if v_isSharedCheck_6001_ == 0 {
                        v_unused_6002_ = leanh::lean_ctor_get(v_b_5962_, 0);
                        leanh::lean_dec(v_unused_6002_);
                        v___x_5979_ = v_b_5962_;
                        v_isShared_5980_ = v_isSharedCheck_6001_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_5977_);
                        leanh::lean_dec(v_b_5962_);
                        v___x_5979_ = leanh::lean_box(0);
                        v_isShared_5980_ = v_isSharedCheck_6001_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5981_ = lean_array_uget_borrowed(v_as_5959_, v_i_5961_);
                v___x_5982_ = leanh::lean_box(0);
                v___x_5983_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5977_, v_a_5981_, v___x_5982_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_);
                if leanh::lean_obj_tag(v___x_5983_) == 0 {
                    leanh::lean_dec_ref_known(v___x_5983_, 1);
                    v___x_5984_ = leanh::lean_box(0);
                    v___x_5985_ = leanh::lean_unsigned_to_nat(1);
                    v___x_5986_ = lean_nat_add(v_snd_5977_, v___x_5985_);
                    leanh::lean_dec(v_snd_5977_);
                    if v_isShared_5980_ == 0 {
                        leanh::lean_ctor_set(v___x_5979_, 1, v___x_5986_);
                        leanh::lean_ctor_set(v___x_5979_, 0, v___x_5984_);
                        v___x_5988_ = v___x_5979_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5992_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5984_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 1, v___x_5986_);
                        v___x_5988_ = v_reuseFailAlloc_5992_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_5979_);
                    leanh::lean_dec(v_snd_5977_);
                    v_a_5993_ = leanh::lean_ctor_get(v___x_5983_, 0);
                    v_isSharedCheck_6000_ = (!leanh::lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6000_ == 0 {
                        v___x_5995_ = v___x_5983_;
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_5993_);
                        leanh::lean_dec(v___x_5983_);
                        v___x_5995_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_5999_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5993_);
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
    mut v_as_6003_: *mut leanh::LeanObject,
    mut v_sz_6004_: *mut leanh::LeanObject,
    mut v_i_6005_: *mut leanh::LeanObject,
    mut v_b_6006_: *mut leanh::LeanObject,
    mut v___y_6007_: *mut leanh::LeanObject,
    mut v___y_6008_: *mut leanh::LeanObject,
    mut v___y_6009_: *mut leanh::LeanObject,
    mut v___y_6010_: *mut leanh::LeanObject,
    mut v___y_6011_: *mut leanh::LeanObject,
    mut v___y_6012_: *mut leanh::LeanObject,
    mut v___y_6013_: *mut leanh::LeanObject,
    mut v___y_6014_: *mut leanh::LeanObject,
    mut v___y_6015_: *mut leanh::LeanObject,
    mut v___y_6016_: *mut leanh::LeanObject,
    mut v___y_6017_: *mut leanh::LeanObject,
    mut v___y_6018_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6019_: usize = 0;
    let mut v_i_boxed_6020_: usize = 0;
    let mut v_res_6021_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6019_ = leanh::lean_unbox_usize(v_sz_6004_);
    leanh::lean_dec(v_sz_6004_);
    v_i_boxed_6020_ = leanh::lean_unbox_usize(v_i_6005_);
    leanh::lean_dec(v_i_6005_);
    v_res_6021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_6003_, v_sz_boxed_6019_, v_i_boxed_6020_, v_b_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_);
    leanh::lean_dec(v___y_6017_);
    leanh::lean_dec_ref(v___y_6016_);
    leanh::lean_dec(v___y_6015_);
    leanh::lean_dec_ref(v___y_6014_);
    leanh::lean_dec(v___y_6013_);
    leanh::lean_dec_ref(v___y_6012_);
    leanh::lean_dec(v___y_6011_);
    leanh::lean_dec_ref(v___y_6010_);
    leanh::lean_dec(v___y_6009_);
    leanh::lean_dec(v___y_6008_);
    leanh::lean_dec(v___y_6007_);
    leanh::lean_dec_ref(v_as_6003_);
    return v_res_6021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(
    mut v_as_6022_: *mut leanh::LeanObject,
    mut v_sz_6023_: usize,
    mut v_i_6024_: usize,
    mut v_b_6025_: *mut leanh::LeanObject,
    mut v___y_6026_: *mut leanh::LeanObject,
    mut v___y_6027_: *mut leanh::LeanObject,
    mut v___y_6028_: *mut leanh::LeanObject,
    mut v___y_6029_: *mut leanh::LeanObject,
    mut v___y_6030_: *mut leanh::LeanObject,
    mut v___y_6031_: *mut leanh::LeanObject,
    mut v___y_6032_: *mut leanh::LeanObject,
    mut v___y_6033_: *mut leanh::LeanObject,
    mut v___y_6034_: *mut leanh::LeanObject,
    mut v___y_6035_: *mut leanh::LeanObject,
    mut v___y_6036_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6038_: u8 = 0;
    let mut v___x_6039_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6040_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v_a_6044_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: usize = 0;
    let mut v___x_6054_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v_isSharedCheck_6064_: u8 = 0;
    let mut v_unused_6065_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6038_ = lean_usize_dec_lt(v_i_6024_, v_sz_6023_);
                if v___x_6038_ == 0 {
                    v___x_6039_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6039_, 0, v_b_6025_);
                    return v___x_6039_;
                } else {
                    v_snd_6040_ = leanh::lean_ctor_get(v_b_6025_, 1);
                    v_isSharedCheck_6064_ = (!leanh::lean_is_exclusive(v_b_6025_)) as u8;
                    if v_isSharedCheck_6064_ == 0 {
                        v_unused_6065_ = leanh::lean_ctor_get(v_b_6025_, 0);
                        leanh::lean_dec(v_unused_6065_);
                        v___x_6042_ = v_b_6025_;
                        v_isShared_6043_ = v_isSharedCheck_6064_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6040_);
                        leanh::lean_dec(v_b_6025_);
                        v___x_6042_ = leanh::lean_box(0);
                        v_isShared_6043_ = v_isSharedCheck_6064_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6044_ = lean_array_uget_borrowed(v_as_6022_, v_i_6024_);
                v___x_6045_ = leanh::lean_box(0);
                v___x_6046_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_6040_, v_a_6044_, v___x_6045_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
                if leanh::lean_obj_tag(v___x_6046_) == 0 {
                    leanh::lean_dec_ref_known(v___x_6046_, 1);
                    v___x_6047_ = leanh::lean_box(0);
                    v___x_6048_ = leanh::lean_unsigned_to_nat(1);
                    v___x_6049_ = lean_nat_add(v_snd_6040_, v___x_6048_);
                    leanh::lean_dec(v_snd_6040_);
                    if v_isShared_6043_ == 0 {
                        leanh::lean_ctor_set(v___x_6042_, 1, v___x_6049_);
                        leanh::lean_ctor_set(v___x_6042_, 0, v___x_6047_);
                        v___x_6051_ = v___x_6042_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6055_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6047_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 1, v___x_6049_);
                        v___x_6051_ = v_reuseFailAlloc_6055_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6042_);
                    leanh::lean_dec(v_snd_6040_);
                    v_a_6056_ = leanh::lean_ctor_get(v___x_6046_, 0);
                    v_isSharedCheck_6063_ = (!leanh::lean_is_exclusive(v___x_6046_)) as u8;
                    if v_isSharedCheck_6063_ == 0 {
                        v___x_6058_ = v___x_6046_;
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6056_);
                        leanh::lean_dec(v___x_6046_);
                        v___x_6058_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6062_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
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
    mut v_as_6066_: *mut leanh::LeanObject,
    mut v_sz_6067_: *mut leanh::LeanObject,
    mut v_i_6068_: *mut leanh::LeanObject,
    mut v_b_6069_: *mut leanh::LeanObject,
    mut v___y_6070_: *mut leanh::LeanObject,
    mut v___y_6071_: *mut leanh::LeanObject,
    mut v___y_6072_: *mut leanh::LeanObject,
    mut v___y_6073_: *mut leanh::LeanObject,
    mut v___y_6074_: *mut leanh::LeanObject,
    mut v___y_6075_: *mut leanh::LeanObject,
    mut v___y_6076_: *mut leanh::LeanObject,
    mut v___y_6077_: *mut leanh::LeanObject,
    mut v___y_6078_: *mut leanh::LeanObject,
    mut v___y_6079_: *mut leanh::LeanObject,
    mut v___y_6080_: *mut leanh::LeanObject,
    mut v___y_6081_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_sz_boxed_6082_: usize = 0;
    let mut v_i_boxed_6083_: usize = 0;
    let mut v_res_6084_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6082_ = leanh::lean_unbox_usize(v_sz_6067_);
    leanh::lean_dec(v_sz_6067_);
    v_i_boxed_6083_ = leanh::lean_unbox_usize(v_i_6068_);
    leanh::lean_dec(v_i_6068_);
    v_res_6084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_6066_, v_sz_boxed_6082_, v_i_boxed_6083_, v_b_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
    leanh::lean_dec(v___y_6080_);
    leanh::lean_dec_ref(v___y_6079_);
    leanh::lean_dec(v___y_6078_);
    leanh::lean_dec_ref(v___y_6077_);
    leanh::lean_dec(v___y_6076_);
    leanh::lean_dec_ref(v___y_6075_);
    leanh::lean_dec(v___y_6074_);
    leanh::lean_dec_ref(v___y_6073_);
    leanh::lean_dec(v___y_6072_);
    leanh::lean_dec(v___y_6071_);
    leanh::lean_dec(v___y_6070_);
    leanh::lean_dec_ref(v_as_6066_);
    return v_res_6084_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(
    mut v_init_6085_: *mut leanh::LeanObject,
    mut v_n_6086_: *mut leanh::LeanObject,
    mut v_b_6087_: *mut leanh::LeanObject,
    mut v___y_6088_: *mut leanh::LeanObject,
    mut v___y_6089_: *mut leanh::LeanObject,
    mut v___y_6090_: *mut leanh::LeanObject,
    mut v___y_6091_: *mut leanh::LeanObject,
    mut v___y_6092_: *mut leanh::LeanObject,
    mut v___y_6093_: *mut leanh::LeanObject,
    mut v___y_6094_: *mut leanh::LeanObject,
    mut v___y_6095_: *mut leanh::LeanObject,
    mut v___y_6096_: *mut leanh::LeanObject,
    mut v___y_6097_: *mut leanh::LeanObject,
    mut v___y_6098_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_cs_6100_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6103_: usize = 0;
    let mut v___x_6104_: usize = 0;
    let mut v___x_6105_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6106_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6109_: u8 = 0;
    let mut v_fst_6110_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6111_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6119_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6120_: u8 = 0;
    let mut v_a_6121_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6124_: u8 = 0;
    let mut v___x_6126_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6127_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6128_: u8 = 0;
    let mut v_vs_6129_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6132_: usize = 0;
    let mut v___x_6133_: usize = 0;
    let mut v___x_6134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6138_: u8 = 0;
    let mut v_fst_6139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6140_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6145_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6148_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6149_: u8 = 0;
    let mut v_a_6150_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6153_: u8 = 0;
    let mut v___x_6155_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6156_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_n_6086_) == 0 {
                    v_cs_6100_ = leanh::lean_ctor_get(v_n_6086_, 0);
                    v___x_6101_ = leanh::lean_box(0);
                    v___x_6102_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6102_, 0, v___x_6101_);
                    leanh::lean_ctor_set(v___x_6102_, 1, v_b_6087_);
                    v_sz_6103_ = lean_array_size(v_cs_6100_);
                    v___x_6104_ = 0usize;
                    v___x_6105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_6085_, v_cs_6100_, v_sz_6103_, v___x_6104_, v___x_6102_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
                    if leanh::lean_obj_tag(v___x_6105_) == 0 {
                        v_a_6106_ = leanh::lean_ctor_get(v___x_6105_, 0);
                        v_isSharedCheck_6120_ =
                            (!leanh::lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6120_ == 0 {
                            v___x_6108_ = v___x_6105_;
                            v_isShared_6109_ = v_isSharedCheck_6120_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6106_);
                            leanh::lean_dec(v___x_6105_);
                            v___x_6108_ = leanh::lean_box(0);
                            v_isShared_6109_ = v_isSharedCheck_6120_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6121_ = leanh::lean_ctor_get(v___x_6105_, 0);
                        v_isSharedCheck_6128_ =
                            (!leanh::lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6128_ == 0 {
                            v___x_6123_ = v___x_6105_;
                            v_isShared_6124_ = v_isSharedCheck_6128_;
                            state = 4;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6121_);
                            leanh::lean_dec(v___x_6105_);
                            v___x_6123_ = leanh::lean_box(0);
                            v_isShared_6124_ = v_isSharedCheck_6128_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6129_ = leanh::lean_ctor_get(v_n_6086_, 0);
                    v___x_6130_ = leanh::lean_box(0);
                    v___x_6131_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6131_, 0, v___x_6130_);
                    leanh::lean_ctor_set(v___x_6131_, 1, v_b_6087_);
                    v_sz_6132_ = lean_array_size(v_vs_6129_);
                    v___x_6133_ = 0usize;
                    v___x_6134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_6129_, v_sz_6132_, v___x_6133_, v___x_6131_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
                    if leanh::lean_obj_tag(v___x_6134_) == 0 {
                        v_a_6135_ = leanh::lean_ctor_get(v___x_6134_, 0);
                        v_isSharedCheck_6149_ =
                            (!leanh::lean_is_exclusive(v___x_6134_)) as u8;
                        if v_isSharedCheck_6149_ == 0 {
                            v___x_6137_ = v___x_6134_;
                            v_isShared_6138_ = v_isSharedCheck_6149_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6135_);
                            leanh::lean_dec(v___x_6134_);
                            v___x_6137_ = leanh::lean_box(0);
                            v_isShared_6138_ = v_isSharedCheck_6149_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6150_ = leanh::lean_ctor_get(v___x_6134_, 0);
                        v_isSharedCheck_6157_ =
                            (!leanh::lean_is_exclusive(v___x_6134_)) as u8;
                        if v_isSharedCheck_6157_ == 0 {
                            v___x_6152_ = v___x_6134_;
                            v_isShared_6153_ = v_isSharedCheck_6157_;
                            state = 9;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6150_);
                            leanh::lean_dec(v___x_6134_);
                            v___x_6152_ = leanh::lean_box(0);
                            v_isShared_6153_ = v_isSharedCheck_6157_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6110_ = leanh::lean_ctor_get(v_a_6106_, 0);
                if leanh::lean_obj_tag(v_fst_6110_) == 0 {
                    v_snd_6111_ = leanh::lean_ctor_get(v_a_6106_, 1);
                    leanh::lean_inc(v_snd_6111_);
                    leanh::lean_dec(v_a_6106_);
                    v___x_6112_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6112_, 0, v_snd_6111_);
                    if v_isShared_6109_ == 0 {
                        leanh::lean_ctor_set(v___x_6108_, 0, v___x_6112_);
                        v___x_6114_ = v___x_6108_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6115_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6115_, 0, v___x_6112_);
                        v___x_6114_ = v_reuseFailAlloc_6115_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6110_);
                    leanh::lean_dec(v_a_6106_);
                    v_val_6116_ = leanh::lean_ctor_get(v_fst_6110_, 0);
                    leanh::lean_inc(v_val_6116_);
                    leanh::lean_dec_ref_known(v_fst_6110_, 1);
                    if v_isShared_6109_ == 0 {
                        leanh::lean_ctor_set(v___x_6108_, 0, v_val_6116_);
                        v___x_6118_ = v___x_6108_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6119_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_val_6116_);
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
                    v_reuseFailAlloc_6127_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
                    v___x_6126_ = v_reuseFailAlloc_6127_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6126_;
            }
            6 => {
                v_fst_6139_ = leanh::lean_ctor_get(v_a_6135_, 0);
                if leanh::lean_obj_tag(v_fst_6139_) == 0 {
                    v_snd_6140_ = leanh::lean_ctor_get(v_a_6135_, 1);
                    leanh::lean_inc(v_snd_6140_);
                    leanh::lean_dec(v_a_6135_);
                    v___x_6141_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6141_, 0, v_snd_6140_);
                    if v_isShared_6138_ == 0 {
                        leanh::lean_ctor_set(v___x_6137_, 0, v___x_6141_);
                        v___x_6143_ = v___x_6137_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6144_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6144_, 0, v___x_6141_);
                        v___x_6143_ = v_reuseFailAlloc_6144_;
                        state = 7;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6139_);
                    leanh::lean_dec(v_a_6135_);
                    v_val_6145_ = leanh::lean_ctor_get(v_fst_6139_, 0);
                    leanh::lean_inc(v_val_6145_);
                    leanh::lean_dec_ref_known(v_fst_6139_, 1);
                    if v_isShared_6138_ == 0 {
                        leanh::lean_ctor_set(v___x_6137_, 0, v_val_6145_);
                        v___x_6147_ = v___x_6137_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6148_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6148_, 0, v_val_6145_);
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
                    v_reuseFailAlloc_6156_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6150_);
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
    mut v_init_6158_: *mut leanh::LeanObject,
    mut v_as_6159_: *mut leanh::LeanObject,
    mut v_sz_6160_: usize,
    mut v_i_6161_: usize,
    mut v_b_6162_: *mut leanh::LeanObject,
    mut v___y_6163_: *mut leanh::LeanObject,
    mut v___y_6164_: *mut leanh::LeanObject,
    mut v___y_6165_: *mut leanh::LeanObject,
    mut v___y_6166_: *mut leanh::LeanObject,
    mut v___y_6167_: *mut leanh::LeanObject,
    mut v___y_6168_: *mut leanh::LeanObject,
    mut v___y_6169_: *mut leanh::LeanObject,
    mut v___y_6170_: *mut leanh::LeanObject,
    mut v___y_6171_: *mut leanh::LeanObject,
    mut v___y_6172_: *mut leanh::LeanObject,
    mut v___y_6173_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6175_: u8 = 0;
    let mut v___x_6176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v_a_6181_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6183_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6186_: u8 = 0;
    let mut v___x_6187_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6193_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: usize = 0;
    let mut v___x_6199_: usize = 0;
    let mut v_reuseFailAlloc_6201_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6202_: u8 = 0;
    let mut v_a_6203_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6206_: u8 = 0;
    let mut v___x_6208_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_isSharedCheck_6211_: u8 = 0;
    let mut v_unused_6212_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6175_ = lean_usize_dec_lt(v_i_6161_, v_sz_6160_);
                if v___x_6175_ == 0 {
                    v___x_6176_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6176_, 0, v_b_6162_);
                    return v___x_6176_;
                } else {
                    v_snd_6177_ = leanh::lean_ctor_get(v_b_6162_, 1);
                    v_isSharedCheck_6211_ = (!leanh::lean_is_exclusive(v_b_6162_)) as u8;
                    if v_isSharedCheck_6211_ == 0 {
                        v_unused_6212_ = leanh::lean_ctor_get(v_b_6162_, 0);
                        leanh::lean_dec(v_unused_6212_);
                        v___x_6179_ = v_b_6162_;
                        v_isShared_6180_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_snd_6177_);
                        leanh::lean_dec(v_b_6162_);
                        v___x_6179_ = leanh::lean_box(0);
                        v_isShared_6180_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6181_ = lean_array_uget_borrowed(v_as_6159_, v_i_6161_);
                leanh::lean_inc(v_snd_6177_);
                v___x_6182_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6158_, v_a_6181_, v_snd_6177_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                if leanh::lean_obj_tag(v___x_6182_) == 0 {
                    v_a_6183_ = leanh::lean_ctor_get(v___x_6182_, 0);
                    v_isSharedCheck_6202_ = (!leanh::lean_is_exclusive(v___x_6182_)) as u8;
                    if v_isSharedCheck_6202_ == 0 {
                        v___x_6185_ = v___x_6182_;
                        v_isShared_6186_ = v_isSharedCheck_6202_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6183_);
                        leanh::lean_dec(v___x_6182_);
                        v___x_6185_ = leanh::lean_box(0);
                        v_isShared_6186_ = v_isSharedCheck_6202_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6179_);
                    leanh::lean_dec(v_snd_6177_);
                    v_a_6203_ = leanh::lean_ctor_get(v___x_6182_, 0);
                    v_isSharedCheck_6210_ = (!leanh::lean_is_exclusive(v___x_6182_)) as u8;
                    if v_isSharedCheck_6210_ == 0 {
                        v___x_6205_ = v___x_6182_;
                        v_isShared_6206_ = v_isSharedCheck_6210_;
                        state = 6;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6203_);
                        leanh::lean_dec(v___x_6182_);
                        v___x_6205_ = leanh::lean_box(0);
                        v_isShared_6206_ = v_isSharedCheck_6210_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if leanh::lean_obj_tag(v_a_6183_) == 0 {
                    v___x_6187_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6187_, 0, v_a_6183_);
                    if v_isShared_6180_ == 0 {
                        leanh::lean_ctor_set(v___x_6179_, 0, v___x_6187_);
                        v___x_6189_ = v___x_6179_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6193_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6187_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 1, v_snd_6177_);
                        v___x_6189_ = v_reuseFailAlloc_6193_;
                        state = 3;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6185_);
                    leanh::lean_dec(v_snd_6177_);
                    v_a_6194_ = leanh::lean_ctor_get(v_a_6183_, 0);
                    leanh::lean_inc(v_a_6194_);
                    leanh::lean_dec_ref_known(v_a_6183_, 1);
                    v___x_6195_ = leanh::lean_box(0);
                    if v_isShared_6180_ == 0 {
                        leanh::lean_ctor_set(v___x_6179_, 1, v_a_6194_);
                        leanh::lean_ctor_set(v___x_6179_, 0, v___x_6195_);
                        v___x_6197_ = v___x_6179_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6201_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 0, v___x_6195_);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 1, v_a_6194_);
                        v___x_6197_ = v_reuseFailAlloc_6201_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6186_ == 0 {
                    leanh::lean_ctor_set(v___x_6185_, 0, v___x_6189_);
                    v___x_6191_ = v___x_6185_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6192_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6189_);
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
                    v_reuseFailAlloc_6209_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
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
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_init_6213_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_6214_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_sz_6215_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_6216_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_6217_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_6218_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_6219_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_6220_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_6221_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_6222_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_6223_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_6224_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6225_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6226_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_6227_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_6228_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6229_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_6230_: usize = 0;
    let mut v_i_boxed_6231_: usize = 0;
    let mut v_res_6232_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6230_ = leanh::lean_unbox_usize(v_sz_6215_);
    leanh::lean_dec(v_sz_6215_);
    v_i_boxed_6231_ = leanh::lean_unbox_usize(v_i_6216_);
    leanh::lean_dec(v_i_6216_);
    v_res_6232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_6213_, v_as_6214_, v_sz_boxed_6230_, v_i_boxed_6231_, v_b_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
    leanh::lean_dec(v___y_6228_);
    leanh::lean_dec_ref(v___y_6227_);
    leanh::lean_dec(v___y_6226_);
    leanh::lean_dec_ref(v___y_6225_);
    leanh::lean_dec(v___y_6224_);
    leanh::lean_dec_ref(v___y_6223_);
    leanh::lean_dec(v___y_6222_);
    leanh::lean_dec_ref(v___y_6221_);
    leanh::lean_dec(v___y_6220_);
    leanh::lean_dec(v___y_6219_);
    leanh::lean_dec(v___y_6218_);
    leanh::lean_dec_ref(v_as_6214_);
    leanh::lean_dec(v_init_6213_);
    return v_res_6232_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3___boxed(
    mut v_init_6233_: *mut leanh::LeanObject,
    mut v_n_6234_: *mut leanh::LeanObject,
    mut v_b_6235_: *mut leanh::LeanObject,
    mut v___y_6236_: *mut leanh::LeanObject,
    mut v___y_6237_: *mut leanh::LeanObject,
    mut v___y_6238_: *mut leanh::LeanObject,
    mut v___y_6239_: *mut leanh::LeanObject,
    mut v___y_6240_: *mut leanh::LeanObject,
    mut v___y_6241_: *mut leanh::LeanObject,
    mut v___y_6242_: *mut leanh::LeanObject,
    mut v___y_6243_: *mut leanh::LeanObject,
    mut v___y_6244_: *mut leanh::LeanObject,
    mut v___y_6245_: *mut leanh::LeanObject,
    mut v___y_6246_: *mut leanh::LeanObject,
    mut v___y_6247_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6248_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6248_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6233_, v_n_6234_, v_b_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
    leanh::lean_dec(v___y_6246_);
    leanh::lean_dec_ref(v___y_6245_);
    leanh::lean_dec(v___y_6244_);
    leanh::lean_dec_ref(v___y_6243_);
    leanh::lean_dec(v___y_6242_);
    leanh::lean_dec_ref(v___y_6241_);
    leanh::lean_dec(v___y_6240_);
    leanh::lean_dec_ref(v___y_6239_);
    leanh::lean_dec(v___y_6238_);
    leanh::lean_dec(v___y_6237_);
    leanh::lean_dec(v___y_6236_);
    leanh::lean_dec_ref(v_n_6234_);
    leanh::lean_dec(v_init_6233_);
    return v_res_6248_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(
    mut v_t_6249_: *mut leanh::LeanObject,
    mut v_init_6250_: *mut leanh::LeanObject,
    mut v___y_6251_: *mut leanh::LeanObject,
    mut v___y_6252_: *mut leanh::LeanObject,
    mut v___y_6253_: *mut leanh::LeanObject,
    mut v___y_6254_: *mut leanh::LeanObject,
    mut v___y_6255_: *mut leanh::LeanObject,
    mut v___y_6256_: *mut leanh::LeanObject,
    mut v___y_6257_: *mut leanh::LeanObject,
    mut v___y_6258_: *mut leanh::LeanObject,
    mut v___y_6259_: *mut leanh::LeanObject,
    mut v___y_6260_: *mut leanh::LeanObject,
    mut v___y_6261_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_root_6263_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6264_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6266_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6269_: u8 = 0;
    let mut v_a_6270_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6273_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6274_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6277_: usize = 0;
    let mut v___x_6278_: usize = 0;
    let mut v___x_6279_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6280_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v_fst_6284_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6285_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6288_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6289_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6292_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6293_: u8 = 0;
    let mut v_a_6294_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6297_: u8 = 0;
    let mut v___x_6299_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6301_: u8 = 0;
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v_a_6303_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6263_ = leanh::lean_ctor_get(v_t_6249_, 0);
                v_tail_6264_ = leanh::lean_ctor_get(v_t_6249_, 1);
                leanh::lean_inc(v_init_6250_);
                v___x_6265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6250_, v_root_6263_, v_init_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
                leanh::lean_dec(v_init_6250_);
                if leanh::lean_obj_tag(v___x_6265_) == 0 {
                    v_a_6266_ = leanh::lean_ctor_get(v___x_6265_, 0);
                    v_isSharedCheck_6302_ = (!leanh::lean_is_exclusive(v___x_6265_)) as u8;
                    if v_isSharedCheck_6302_ == 0 {
                        v___x_6268_ = v___x_6265_;
                        v_isShared_6269_ = v_isSharedCheck_6302_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6266_);
                        leanh::lean_dec(v___x_6265_);
                        v___x_6268_ = leanh::lean_box(0);
                        v_isShared_6269_ = v_isSharedCheck_6302_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6303_ = leanh::lean_ctor_get(v___x_6265_, 0);
                    v_isSharedCheck_6310_ = (!leanh::lean_is_exclusive(v___x_6265_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v___x_6305_ = v___x_6265_;
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6303_);
                        leanh::lean_dec(v___x_6265_);
                        v___x_6305_ = leanh::lean_box(0);
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6266_) == 0 {
                    v_a_6270_ = leanh::lean_ctor_get(v_a_6266_, 0);
                    leanh::lean_inc(v_a_6270_);
                    leanh::lean_dec_ref_known(v_a_6266_, 1);
                    if v_isShared_6269_ == 0 {
                        leanh::lean_ctor_set(v___x_6268_, 0, v_a_6270_);
                        v___x_6272_ = v___x_6268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6273_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6270_);
                        v___x_6272_ = v_reuseFailAlloc_6273_;
                        state = 2;
                        continue;
                    }
                } else {
                    leanh::lean_del_object(v___x_6268_);
                    v_a_6274_ = leanh::lean_ctor_get(v_a_6266_, 0);
                    leanh::lean_inc(v_a_6274_);
                    leanh::lean_dec_ref_known(v_a_6266_, 1);
                    v___x_6275_ = leanh::lean_box(0);
                    v___x_6276_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    leanh::lean_ctor_set(v___x_6276_, 0, v___x_6275_);
                    leanh::lean_ctor_set(v___x_6276_, 1, v_a_6274_);
                    v_sz_6277_ = lean_array_size(v_tail_6264_);
                    v___x_6278_ = 0usize;
                    v___x_6279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_tail_6264_, v_sz_6277_, v___x_6278_, v___x_6276_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
                    if leanh::lean_obj_tag(v___x_6279_) == 0 {
                        v_a_6280_ = leanh::lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6293_ =
                            (!leanh::lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6293_ == 0 {
                            v___x_6282_ = v___x_6279_;
                            v_isShared_6283_ = v_isSharedCheck_6293_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6280_);
                            leanh::lean_dec(v___x_6279_);
                            v___x_6282_ = leanh::lean_box(0);
                            v_isShared_6283_ = v_isSharedCheck_6293_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6294_ = leanh::lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6301_ =
                            (!leanh::lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6301_ == 0 {
                            v___x_6296_ = v___x_6279_;
                            v_isShared_6297_ = v_isSharedCheck_6301_;
                            state = 6;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6294_);
                            leanh::lean_dec(v___x_6279_);
                            v___x_6296_ = leanh::lean_box(0);
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
                v_fst_6284_ = leanh::lean_ctor_get(v_a_6280_, 0);
                if leanh::lean_obj_tag(v_fst_6284_) == 0 {
                    v_snd_6285_ = leanh::lean_ctor_get(v_a_6280_, 1);
                    leanh::lean_inc(v_snd_6285_);
                    leanh::lean_dec(v_a_6280_);
                    if v_isShared_6283_ == 0 {
                        leanh::lean_ctor_set(v___x_6282_, 0, v_snd_6285_);
                        v___x_6287_ = v___x_6282_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6288_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_snd_6285_);
                        v___x_6287_ = v_reuseFailAlloc_6288_;
                        state = 4;
                        continue;
                    }
                } else {
                    leanh::lean_inc_ref(v_fst_6284_);
                    leanh::lean_dec(v_a_6280_);
                    v_val_6289_ = leanh::lean_ctor_get(v_fst_6284_, 0);
                    leanh::lean_inc(v_val_6289_);
                    leanh::lean_dec_ref_known(v_fst_6284_, 1);
                    if v_isShared_6283_ == 0 {
                        leanh::lean_ctor_set(v___x_6282_, 0, v_val_6289_);
                        v___x_6291_ = v___x_6282_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6292_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6292_, 0, v_val_6289_);
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
                    v_reuseFailAlloc_6300_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6300_, 0, v_a_6294_);
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
                    v_reuseFailAlloc_6309_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6303_);
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
    mut v_t_6311_: *mut leanh::LeanObject,
    mut v_init_6312_: *mut leanh::LeanObject,
    mut v___y_6313_: *mut leanh::LeanObject,
    mut v___y_6314_: *mut leanh::LeanObject,
    mut v___y_6315_: *mut leanh::LeanObject,
    mut v___y_6316_: *mut leanh::LeanObject,
    mut v___y_6317_: *mut leanh::LeanObject,
    mut v___y_6318_: *mut leanh::LeanObject,
    mut v___y_6319_: *mut leanh::LeanObject,
    mut v___y_6320_: *mut leanh::LeanObject,
    mut v___y_6321_: *mut leanh::LeanObject,
    mut v___y_6322_: *mut leanh::LeanObject,
    mut v___y_6323_: *mut leanh::LeanObject,
    mut v___y_6324_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6325_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_t_6311_, v_init_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
    leanh::lean_dec(v___y_6323_);
    leanh::lean_dec_ref(v___y_6322_);
    leanh::lean_dec(v___y_6321_);
    leanh::lean_dec_ref(v___y_6320_);
    leanh::lean_dec(v___y_6319_);
    leanh::lean_dec_ref(v___y_6318_);
    leanh::lean_dec(v___y_6317_);
    leanh::lean_dec_ref(v___y_6316_);
    leanh::lean_dec(v___y_6315_);
    leanh::lean_dec(v___y_6314_);
    leanh::lean_dec(v___y_6313_);
    leanh::lean_dec_ref(v_t_6311_);
    return v_res_6325_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_6328_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1;
    v___x_6329_ = leanh::lean_unsigned_to_nat(2);
    v___x_6330_ = leanh::lean_unsigned_to_nat(73);
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
    mut v_a_6334_: *mut leanh::LeanObject,
    mut v_a_6335_: *mut leanh::LeanObject,
    mut v_a_6336_: *mut leanh::LeanObject,
    mut v_a_6337_: *mut leanh::LeanObject,
    mut v_a_6338_: *mut leanh::LeanObject,
    mut v_a_6339_: *mut leanh::LeanObject,
    mut v_a_6340_: *mut leanh::LeanObject,
    mut v_a_6341_: *mut leanh::LeanObject,
    mut v_a_6342_: *mut leanh::LeanObject,
    mut v_a_6343_: *mut leanh::LeanObject,
    mut v_a_6344_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6346_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6347_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6348_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_6349_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6350_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6351_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v___x_6360_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6363_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6364_: u8 = 0;
    let mut v_unused_6365_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6366_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6369_: u8 = 0;
    let mut v___x_6371_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6373_: u8 = 0;
    let mut v_a_6374_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6377_: u8 = 0;
    let mut v___x_6379_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6346_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_,
                    v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_,
                );
                if leanh::lean_obj_tag(v___x_6346_) == 0 {
                    v_a_6347_ = leanh::lean_ctor_get(v___x_6346_, 0);
                    leanh::lean_inc(v_a_6347_);
                    leanh::lean_dec_ref_known(v___x_6346_, 1);
                    v_vars_6348_ = leanh::lean_ctor_get(v_a_6347_, 30);
                    leanh::lean_inc_ref(v_vars_6348_);
                    v_diseqs_6349_ = leanh::lean_ctor_get(v_a_6347_, 34);
                    leanh::lean_inc_ref(v_diseqs_6349_);
                    leanh::lean_dec(v_a_6347_);
                    v_size_6350_ = leanh::lean_ctor_get(v_vars_6348_, 2);
                    leanh::lean_inc(v_size_6350_);
                    leanh::lean_dec_ref(v_vars_6348_);
                    v_size_6351_ = leanh::lean_ctor_get(v_diseqs_6349_, 2);
                    v___x_6352_ = lean_nat_dec_eq(v_size_6350_, v_size_6351_);
                    leanh::lean_dec(v_size_6350_);
                    if v___x_6352_ == 0 {
                        leanh::lean_dec_ref(v_diseqs_6349_);
                        v___x_6353_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2);
                        v___x_6354_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6353_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_);
                        return v___x_6354_;
                    } else {
                        v___x_6355_ = leanh::lean_unsigned_to_nat(0);
                        v___x_6356_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_diseqs_6349_, v___x_6355_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_);
                        leanh::lean_dec_ref(v_diseqs_6349_);
                        if leanh::lean_obj_tag(v___x_6356_) == 0 {
                            v_isSharedCheck_6364_ =
                                (!leanh::lean_is_exclusive(v___x_6356_)) as u8;
                            if v_isSharedCheck_6364_ == 0 {
                                v_unused_6365_ = leanh::lean_ctor_get(v___x_6356_, 0);
                                leanh::lean_dec(v_unused_6365_);
                                v___x_6358_ = v___x_6356_;
                                v_isShared_6359_ = v_isSharedCheck_6364_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_6356_);
                                v___x_6358_ = leanh::lean_box(0);
                                v_isShared_6359_ = v_isSharedCheck_6364_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_6366_ = leanh::lean_ctor_get(v___x_6356_, 0);
                            v_isSharedCheck_6373_ =
                                (!leanh::lean_is_exclusive(v___x_6356_)) as u8;
                            if v_isSharedCheck_6373_ == 0 {
                                v___x_6368_ = v___x_6356_;
                                v_isShared_6369_ = v_isSharedCheck_6373_;
                                state = 3;
                                continue;
                            } else {
                                leanh::lean_inc(v_a_6366_);
                                leanh::lean_dec(v___x_6356_);
                                v___x_6368_ = leanh::lean_box(0);
                                v_isShared_6369_ = v_isSharedCheck_6373_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_6374_ = leanh::lean_ctor_get(v___x_6346_, 0);
                    v_isSharedCheck_6381_ = (!leanh::lean_is_exclusive(v___x_6346_)) as u8;
                    if v_isSharedCheck_6381_ == 0 {
                        v___x_6376_ = v___x_6346_;
                        v_isShared_6377_ = v_isSharedCheck_6381_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6374_);
                        leanh::lean_dec(v___x_6346_);
                        v___x_6376_ = leanh::lean_box(0);
                        v_isShared_6377_ = v_isSharedCheck_6381_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6360_ = leanh::lean_box(0);
                if v_isShared_6359_ == 0 {
                    leanh::lean_ctor_set(v___x_6358_, 0, v___x_6360_);
                    v___x_6362_ = v___x_6358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6363_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6363_, 0, v___x_6360_);
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
                    v_reuseFailAlloc_6372_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_a_6366_);
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
                    v_reuseFailAlloc_6380_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_a_6374_);
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
    mut v_a_6382_: *mut leanh::LeanObject,
    mut v_a_6383_: *mut leanh::LeanObject,
    mut v_a_6384_: *mut leanh::LeanObject,
    mut v_a_6385_: *mut leanh::LeanObject,
    mut v_a_6386_: *mut leanh::LeanObject,
    mut v_a_6387_: *mut leanh::LeanObject,
    mut v_a_6388_: *mut leanh::LeanObject,
    mut v_a_6389_: *mut leanh::LeanObject,
    mut v_a_6390_: *mut leanh::LeanObject,
    mut v_a_6391_: *mut leanh::LeanObject,
    mut v_a_6392_: *mut leanh::LeanObject,
    mut v_a_6393_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6394_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_6382_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
    leanh::lean_dec(v_a_6392_);
    leanh::lean_dec_ref(v_a_6391_);
    leanh::lean_dec(v_a_6390_);
    leanh::lean_dec_ref(v_a_6389_);
    leanh::lean_dec(v_a_6388_);
    leanh::lean_dec_ref(v_a_6387_);
    leanh::lean_dec(v_a_6386_);
    leanh::lean_dec_ref(v_a_6385_);
    leanh::lean_dec(v_a_6384_);
    leanh::lean_dec(v_a_6383_);
    leanh::lean_dec(v_a_6382_);
    return v_res_6394_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0()
-> *mut leanh::LeanObject {
    let mut v___x_6395_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6395_ = l_Lean_Meta_Grind_instInhabitedGoalM(leanh::lean_box(0));
    return v___x_6395_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(
    mut v_msg_6396_: *mut leanh::LeanObject,
    mut v___y_6397_: *mut leanh::LeanObject,
    mut v___y_6398_: *mut leanh::LeanObject,
    mut v___y_6399_: *mut leanh::LeanObject,
    mut v___y_6400_: *mut leanh::LeanObject,
    mut v___y_6401_: *mut leanh::LeanObject,
    mut v___y_6402_: *mut leanh::LeanObject,
    mut v___y_6403_: *mut leanh::LeanObject,
    mut v___y_6404_: *mut leanh::LeanObject,
    mut v___y_6405_: *mut leanh::LeanObject,
    mut v___y_6406_: *mut leanh::LeanObject,
    mut v___y_6407_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6409_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6410_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472__overap_6411_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6409_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0);
    v___f_6410_ = leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    leanh::lean_closure_set(v___f_6410_, 0, v___x_6409_);
    v___x_5472__overap_6411_ = lean_panic_fn_borrowed(v___f_6410_, v_msg_6396_);
    leanh::lean_dec_ref(v___f_6410_);
    leanh::lean_inc(v___y_6407_);
    leanh::lean_inc_ref(v___y_6406_);
    leanh::lean_inc(v___y_6405_);
    leanh::lean_inc_ref(v___y_6404_);
    leanh::lean_inc(v___y_6403_);
    leanh::lean_inc_ref(v___y_6402_);
    leanh::lean_inc(v___y_6401_);
    leanh::lean_inc_ref(v___y_6400_);
    leanh::lean_inc(v___y_6399_);
    leanh::lean_inc(v___y_6398_);
    leanh::lean_inc(v___y_6397_);
    v___x_6412_ = leanh::lean_apply_12(
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
        leanh::lean_box(0),
    );
    return v___x_6412_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___boxed(
    mut v_msg_6413_: *mut leanh::LeanObject,
    mut v___y_6414_: *mut leanh::LeanObject,
    mut v___y_6415_: *mut leanh::LeanObject,
    mut v___y_6416_: *mut leanh::LeanObject,
    mut v___y_6417_: *mut leanh::LeanObject,
    mut v___y_6418_: *mut leanh::LeanObject,
    mut v___y_6419_: *mut leanh::LeanObject,
    mut v___y_6420_: *mut leanh::LeanObject,
    mut v___y_6421_: *mut leanh::LeanObject,
    mut v___y_6422_: *mut leanh::LeanObject,
    mut v___y_6423_: *mut leanh::LeanObject,
    mut v___y_6424_: *mut leanh::LeanObject,
    mut v___y_6425_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6426_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6426_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v_msg_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_);
    leanh::lean_dec(v___y_6424_);
    leanh::lean_dec_ref(v___y_6423_);
    leanh::lean_dec(v___y_6422_);
    leanh::lean_dec_ref(v___y_6421_);
    leanh::lean_dec(v___y_6420_);
    leanh::lean_dec_ref(v___y_6419_);
    leanh::lean_dec(v___y_6418_);
    leanh::lean_dec_ref(v___y_6417_);
    leanh::lean_dec(v___y_6416_);
    leanh::lean_dec(v___y_6415_);
    leanh::lean_dec(v___y_6414_);
    return v_res_6426_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6428_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6428_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_6429_ = leanh::lean_unsigned_to_nat(6);
    v___x_6430_ = leanh::lean_unsigned_to_nat(89);
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
-> *mut leanh::LeanObject {
    let mut v___x_6435_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2;
    v___x_6436_ = leanh::lean_unsigned_to_nat(6);
    v___x_6437_ = leanh::lean_unsigned_to_nat(87);
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
    mut v_vars_6441_: *mut leanh::LeanObject,
    mut v_x_6442_: *mut leanh::LeanObject,
    mut v_____s_6443_: *mut leanh::LeanObject,
    mut v___y_6444_: *mut leanh::LeanObject,
    mut v___y_6445_: *mut leanh::LeanObject,
    mut v___y_6446_: *mut leanh::LeanObject,
    mut v___y_6447_: *mut leanh::LeanObject,
    mut v___y_6448_: *mut leanh::LeanObject,
    mut v___y_6449_: *mut leanh::LeanObject,
    mut v___y_6450_: *mut leanh::LeanObject,
    mut v___y_6451_: *mut leanh::LeanObject,
    mut v___y_6452_: *mut leanh::LeanObject,
    mut v___y_6453_: *mut leanh::LeanObject,
    mut v___y_6454_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6457_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6461_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6462_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6463_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: u8 = 0;
    let mut v___x_6465_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6467_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6470_: u8 = 0;
    let mut v___x_6472_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6473_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6474_: u8 = 0;
    let mut v___x_6475_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6461_ = leanh::lean_ctor_get(v_x_6442_, 0);
                v_snd_6462_ = leanh::lean_ctor_get(v_x_6442_, 1);
                v_size_6463_ = leanh::lean_ctor_get(v_vars_6441_, 2);
                v___x_6464_ = lean_nat_dec_lt(v_snd_6462_, v_size_6463_);
                if v___x_6464_ == 0 {
                    v___x_6465_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1);
                    v___x_6466_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6465_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
                    if leanh::lean_obj_tag(v___x_6466_) == 0 {
                        leanh::lean_dec_ref_known(v___x_6466_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_6467_ = leanh::lean_ctor_get(v___x_6466_, 0);
                        v_isSharedCheck_6474_ =
                            (!leanh::lean_is_exclusive(v___x_6466_)) as u8;
                        if v_isSharedCheck_6474_ == 0 {
                            v___x_6469_ = v___x_6466_;
                            v_isShared_6470_ = v_isSharedCheck_6474_;
                            state = 2;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6467_);
                            leanh::lean_dec(v___x_6466_);
                            v___x_6469_ = leanh::lean_box(0);
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
                    leanh::lean_dec(v___x_6476_);
                    if v___x_6477_ == 0 {
                        v___x_6478_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3);
                        v___x_6479_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v___x_6478_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
                        return v___x_6479_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6457_ = leanh::lean_unsigned_to_nat(1);
                v___x_6458_ = lean_nat_add(v_____s_6443_, v___x_6457_);
                v___x_6459_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6459_, 0, v___x_6458_);
                v___x_6460_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6460_, 0, v___x_6459_);
                return v___x_6460_;
            }
            2 => {
                if v_isShared_6470_ == 0 {
                    v___x_6472_ = v___x_6469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6473_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6467_);
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
    mut v_vars_6480_: *mut leanh::LeanObject,
    mut v_x_6481_: *mut leanh::LeanObject,
    mut v_____s_6482_: *mut leanh::LeanObject,
    mut v___y_6483_: *mut leanh::LeanObject,
    mut v___y_6484_: *mut leanh::LeanObject,
    mut v___y_6485_: *mut leanh::LeanObject,
    mut v___y_6486_: *mut leanh::LeanObject,
    mut v___y_6487_: *mut leanh::LeanObject,
    mut v___y_6488_: *mut leanh::LeanObject,
    mut v___y_6489_: *mut leanh::LeanObject,
    mut v___y_6490_: *mut leanh::LeanObject,
    mut v___y_6491_: *mut leanh::LeanObject,
    mut v___y_6492_: *mut leanh::LeanObject,
    mut v___y_6493_: *mut leanh::LeanObject,
    mut v___y_6494_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6495_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6495_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(v_vars_6480_, v_x_6481_, v_____s_6482_, v___y_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_);
    leanh::lean_dec(v___y_6493_);
    leanh::lean_dec_ref(v___y_6492_);
    leanh::lean_dec(v___y_6491_);
    leanh::lean_dec_ref(v___y_6490_);
    leanh::lean_dec(v___y_6489_);
    leanh::lean_dec_ref(v___y_6488_);
    leanh::lean_dec(v___y_6487_);
    leanh::lean_dec_ref(v___y_6486_);
    leanh::lean_dec(v___y_6485_);
    leanh::lean_dec(v___y_6484_);
    leanh::lean_dec(v___y_6483_);
    leanh::lean_dec(v_____s_6482_);
    leanh::lean_dec_ref(v_x_6481_);
    leanh::lean_dec_ref(v_vars_6480_);
    return v_res_6495_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(
    mut v_f_6496_: *mut leanh::LeanObject,
    mut v_s_6497_: *mut leanh::LeanObject,
    mut v_a_6498_: *mut leanh::LeanObject,
    mut v_b_6499_: *mut leanh::LeanObject,
    mut v___y_6500_: *mut leanh::LeanObject,
    mut v___y_6501_: *mut leanh::LeanObject,
    mut v___y_6502_: *mut leanh::LeanObject,
    mut v___y_6503_: *mut leanh::LeanObject,
    mut v___y_6504_: *mut leanh::LeanObject,
    mut v___y_6505_: *mut leanh::LeanObject,
    mut v___y_6506_: *mut leanh::LeanObject,
    mut v___y_6507_: *mut leanh::LeanObject,
    mut v___y_6508_: *mut leanh::LeanObject,
    mut v___y_6509_: *mut leanh::LeanObject,
    mut v___y_6510_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6512_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6514_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6517_: u8 = 0;
    let mut v_a_6518_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6521_: u8 = 0;
    let mut v___x_6523_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_a_6529_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___x_6534_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6537_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
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
                v___x_6512_ = leanh::lean_alloc_ctor(0, 2, (0) as u32);
                leanh::lean_ctor_set(v___x_6512_, 0, v_a_6498_);
                leanh::lean_ctor_set(v___x_6512_, 1, v_b_6499_);
                leanh::lean_inc(v___y_6510_);
                leanh::lean_inc_ref(v___y_6509_);
                leanh::lean_inc(v___y_6508_);
                leanh::lean_inc_ref(v___y_6507_);
                leanh::lean_inc(v___y_6506_);
                leanh::lean_inc_ref(v___y_6505_);
                leanh::lean_inc(v___y_6504_);
                leanh::lean_inc_ref(v___y_6503_);
                leanh::lean_inc(v___y_6502_);
                leanh::lean_inc(v___y_6501_);
                leanh::lean_inc(v___y_6500_);
                v___x_6513_ = leanh::lean_apply_14(
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
                    leanh::lean_box(0),
                );
                if leanh::lean_obj_tag(v___x_6513_) == 0 {
                    v_a_6514_ = leanh::lean_ctor_get(v___x_6513_, 0);
                    v_isSharedCheck_6540_ = (!leanh::lean_is_exclusive(v___x_6513_)) as u8;
                    if v_isSharedCheck_6540_ == 0 {
                        v___x_6516_ = v___x_6513_;
                        v_isShared_6517_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6514_);
                        leanh::lean_dec(v___x_6513_);
                        v___x_6516_ = leanh::lean_box(0);
                        v_isShared_6517_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6541_ = leanh::lean_ctor_get(v___x_6513_, 0);
                    v_isSharedCheck_6548_ = (!leanh::lean_is_exclusive(v___x_6513_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v___x_6543_ = v___x_6513_;
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 8;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6541_);
                        leanh::lean_dec(v___x_6513_);
                        v___x_6543_ = leanh::lean_box(0);
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if leanh::lean_obj_tag(v_a_6514_) == 0 {
                    v_a_6518_ = leanh::lean_ctor_get(v_a_6514_, 0);
                    v_isSharedCheck_6528_ = (!leanh::lean_is_exclusive(v_a_6514_)) as u8;
                    if v_isSharedCheck_6528_ == 0 {
                        v___x_6520_ = v_a_6514_;
                        v_isShared_6521_ = v_isSharedCheck_6528_;
                        state = 2;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6518_);
                        leanh::lean_dec(v_a_6514_);
                        v___x_6520_ = leanh::lean_box(0);
                        v_isShared_6521_ = v_isSharedCheck_6528_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6529_ = leanh::lean_ctor_get(v_a_6514_, 0);
                    v_isSharedCheck_6539_ = (!leanh::lean_is_exclusive(v_a_6514_)) as u8;
                    if v_isSharedCheck_6539_ == 0 {
                        v___x_6531_ = v_a_6514_;
                        v_isShared_6532_ = v_isSharedCheck_6539_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6529_);
                        leanh::lean_dec(v_a_6514_);
                        v___x_6531_ = leanh::lean_box(0);
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
                    v_reuseFailAlloc_6527_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6518_);
                    v___x_6523_ = v_reuseFailAlloc_6527_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6517_ == 0 {
                    leanh::lean_ctor_set(v___x_6516_, 0, v___x_6523_);
                    v___x_6525_ = v___x_6516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6526_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 0, v___x_6523_);
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
                    v_reuseFailAlloc_6538_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6529_);
                    v___x_6534_ = v_reuseFailAlloc_6538_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6517_ == 0 {
                    leanh::lean_ctor_set(v___x_6516_, 0, v___x_6534_);
                    v___x_6536_ = v___x_6516_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6537_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6537_, 0, v___x_6534_);
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
                    v_reuseFailAlloc_6547_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
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
    mut v_f_6549_: *mut leanh::LeanObject,
    mut v_s_6550_: *mut leanh::LeanObject,
    mut v_a_6551_: *mut leanh::LeanObject,
    mut v_b_6552_: *mut leanh::LeanObject,
    mut v___y_6553_: *mut leanh::LeanObject,
    mut v___y_6554_: *mut leanh::LeanObject,
    mut v___y_6555_: *mut leanh::LeanObject,
    mut v___y_6556_: *mut leanh::LeanObject,
    mut v___y_6557_: *mut leanh::LeanObject,
    mut v___y_6558_: *mut leanh::LeanObject,
    mut v___y_6559_: *mut leanh::LeanObject,
    mut v___y_6560_: *mut leanh::LeanObject,
    mut v___y_6561_: *mut leanh::LeanObject,
    mut v___y_6562_: *mut leanh::LeanObject,
    mut v___y_6563_: *mut leanh::LeanObject,
    mut v___y_6564_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6565_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6565_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(v_f_6549_, v_s_6550_, v_a_6551_, v_b_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_);
    leanh::lean_dec(v___y_6563_);
    leanh::lean_dec_ref(v___y_6562_);
    leanh::lean_dec(v___y_6561_);
    leanh::lean_dec_ref(v___y_6560_);
    leanh::lean_dec(v___y_6559_);
    leanh::lean_dec_ref(v___y_6558_);
    leanh::lean_dec(v___y_6557_);
    leanh::lean_dec_ref(v___y_6556_);
    leanh::lean_dec(v___y_6555_);
    leanh::lean_dec(v___y_6554_);
    leanh::lean_dec(v___y_6553_);
    return v_res_6565_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_f_6566_: *mut leanh::LeanObject,
    mut v_keys_6567_: *mut leanh::LeanObject,
    mut v_vals_6568_: *mut leanh::LeanObject,
    mut v_i_6569_: *mut leanh::LeanObject,
    mut v_acc_6570_: *mut leanh::LeanObject,
    mut v___y_6571_: *mut leanh::LeanObject,
    mut v___y_6572_: *mut leanh::LeanObject,
    mut v___y_6573_: *mut leanh::LeanObject,
    mut v___y_6574_: *mut leanh::LeanObject,
    mut v___y_6575_: *mut leanh::LeanObject,
    mut v___y_6576_: *mut leanh::LeanObject,
    mut v___y_6577_: *mut leanh::LeanObject,
    mut v___y_6578_: *mut leanh::LeanObject,
    mut v___y_6579_: *mut leanh::LeanObject,
    mut v___y_6580_: *mut leanh::LeanObject,
    mut v___y_6581_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6583_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6587_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6588_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6590_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6591_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6583_ = lean_array_get_size(v_keys_6567_);
                v___x_6584_ = lean_nat_dec_lt(v_i_6569_, v___x_6583_);
                if v___x_6584_ == 0 {
                    leanh::lean_dec(v_i_6569_);
                    leanh::lean_dec_ref(v_f_6566_);
                    v___x_6585_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6585_, 0, v_acc_6570_);
                    v___x_6586_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6586_, 0, v___x_6585_);
                    return v___x_6586_;
                } else {
                    v_k_6587_ = lean_array_fget_borrowed(v_keys_6567_, v_i_6569_);
                    v_v_6588_ = lean_array_fget_borrowed(v_vals_6568_, v_i_6569_);
                    leanh::lean_inc_ref(v_f_6566_);
                    leanh::lean_inc(v___y_6581_);
                    leanh::lean_inc_ref(v___y_6580_);
                    leanh::lean_inc(v___y_6579_);
                    leanh::lean_inc_ref(v___y_6578_);
                    leanh::lean_inc(v___y_6577_);
                    leanh::lean_inc_ref(v___y_6576_);
                    leanh::lean_inc(v___y_6575_);
                    leanh::lean_inc_ref(v___y_6574_);
                    leanh::lean_inc(v___y_6573_);
                    leanh::lean_inc(v___y_6572_);
                    leanh::lean_inc(v___y_6571_);
                    leanh::lean_inc(v_v_6588_);
                    leanh::lean_inc(v_k_6587_);
                    v___x_6589_ = leanh::lean_apply_15(
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
                        leanh::lean_box(0),
                    );
                    if leanh::lean_obj_tag(v___x_6589_) == 0 {
                        v_a_6590_ = leanh::lean_ctor_get(v___x_6589_, 0);
                        leanh::lean_inc(v_a_6590_);
                        if leanh::lean_obj_tag(v_a_6590_) == 0 {
                            leanh::lean_dec_ref_known(v_a_6590_, 1);
                            leanh::lean_dec(v_i_6569_);
                            leanh::lean_dec_ref(v_f_6566_);
                            return v___x_6589_;
                        } else {
                            leanh::lean_dec_ref_known(v___x_6589_, 1);
                            v_a_6591_ = leanh::lean_ctor_get(v_a_6590_, 0);
                            leanh::lean_inc(v_a_6591_);
                            leanh::lean_dec_ref_known(v_a_6590_, 1);
                            v___x_6592_ = leanh::lean_unsigned_to_nat(1);
                            v___x_6593_ = lean_nat_add(v_i_6569_, v___x_6592_);
                            leanh::lean_dec(v_i_6569_);
                            v_i_6569_ = v___x_6593_;
                            v_acc_6570_ = v_a_6591_;
                            state = 0;
                            continue;
                        }
                    } else {
                        leanh::lean_dec(v_i_6569_);
                        leanh::lean_dec_ref(v_f_6566_);
                        return v___x_6589_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_6595_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_keys_6596_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_vals_6597_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_i_6598_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_acc_6599_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_6600_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_6601_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_6602_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_6603_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_6604_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_6605_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_6606_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6607_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6608_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_6609_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_6610_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6611_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_6612_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_6595_, v_keys_6596_, v_vals_6597_, v_i_6598_, v_acc_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
    leanh::lean_dec(v___y_6610_);
    leanh::lean_dec_ref(v___y_6609_);
    leanh::lean_dec(v___y_6608_);
    leanh::lean_dec_ref(v___y_6607_);
    leanh::lean_dec(v___y_6606_);
    leanh::lean_dec_ref(v___y_6605_);
    leanh::lean_dec(v___y_6604_);
    leanh::lean_dec_ref(v___y_6603_);
    leanh::lean_dec(v___y_6602_);
    leanh::lean_dec(v___y_6601_);
    leanh::lean_dec(v___y_6600_);
    leanh::lean_dec_ref(v_vals_6597_);
    leanh::lean_dec_ref(v_keys_6596_);
    return v_res_6612_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(
    mut v_f_6613_: *mut leanh::LeanObject,
    mut v_x_6614_: *mut leanh::LeanObject,
    mut v_x_6615_: *mut leanh::LeanObject,
    mut v___y_6616_: *mut leanh::LeanObject,
    mut v___y_6617_: *mut leanh::LeanObject,
    mut v___y_6618_: *mut leanh::LeanObject,
    mut v___y_6619_: *mut leanh::LeanObject,
    mut v___y_6620_: *mut leanh::LeanObject,
    mut v___y_6621_: *mut leanh::LeanObject,
    mut v___y_6622_: *mut leanh::LeanObject,
    mut v___y_6623_: *mut leanh::LeanObject,
    mut v___y_6624_: *mut leanh::LeanObject,
    mut v___y_6625_: *mut leanh::LeanObject,
    mut v___y_6626_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_es_6628_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6631_: u8 = 0;
    let mut v___x_6632_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: u8 = 0;
    let mut v___x_6636_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: u8 = 0;
    let mut v___x_6641_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6643_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: usize = 0;
    let mut v___x_6645_: usize = 0;
    let mut v___x_6646_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: usize = 0;
    let mut v___x_6648_: usize = 0;
    let mut v___x_6649_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6650_: u8 = 0;
    let mut v_ks_6651_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6652_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if leanh::lean_obj_tag(v_x_6614_) == 0 {
                    v_es_6628_ = leanh::lean_ctor_get(v_x_6614_, 0);
                    v_isSharedCheck_6650_ = (!leanh::lean_is_exclusive(v_x_6614_)) as u8;
                    if v_isSharedCheck_6650_ == 0 {
                        v___x_6630_ = v_x_6614_;
                        v_isShared_6631_ = v_isSharedCheck_6650_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_es_6628_);
                        leanh::lean_dec(v_x_6614_);
                        v___x_6630_ = leanh::lean_box(0);
                        v_isShared_6631_ = v_isSharedCheck_6650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_6651_ = leanh::lean_ctor_get(v_x_6614_, 0);
                    leanh::lean_inc_ref(v_ks_6651_);
                    v_vs_6652_ = leanh::lean_ctor_get(v_x_6614_, 1);
                    leanh::lean_inc_ref(v_vs_6652_);
                    leanh::lean_dec_ref_known(v_x_6614_, 2);
                    v___x_6653_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_6613_, v_ks_6651_, v_vs_6652_, v___x_6653_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                    leanh::lean_dec_ref(v_vs_6652_);
                    leanh::lean_dec_ref(v_ks_6651_);
                    return v___x_6654_;
                }
            }
            1 => {
                v___x_6632_ = leanh::lean_unsigned_to_nat(0);
                v___x_6633_ = lean_array_get_size(v_es_6628_);
                v___x_6634_ = lean_nat_dec_lt(v___x_6632_, v___x_6633_);
                if v___x_6634_ == 0 {
                    leanh::lean_dec_ref(v_es_6628_);
                    leanh::lean_dec_ref(v_f_6613_);
                    if v_isShared_6631_ == 0 {
                        leanh::lean_ctor_set_tag(v___x_6630_, 1);
                        leanh::lean_ctor_set(v___x_6630_, 0, v_x_6615_);
                        v___x_6636_ = v___x_6630_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6638_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_x_6615_);
                        v___x_6636_ = v_reuseFailAlloc_6638_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6639_ = lean_nat_dec_le(v___x_6633_, v___x_6633_);
                    if v___x_6639_ == 0 {
                        if v___x_6634_ == 0 {
                            leanh::lean_dec_ref(v_es_6628_);
                            leanh::lean_dec_ref(v_f_6613_);
                            if v_isShared_6631_ == 0 {
                                leanh::lean_ctor_set_tag(v___x_6630_, 1);
                                leanh::lean_ctor_set(v___x_6630_, 0, v_x_6615_);
                                v___x_6641_ = v___x_6630_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6643_ =
                                    leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                leanh::lean_ctor_set(v_reuseFailAlloc_6643_, 0, v_x_6615_);
                                v___x_6641_ = v_reuseFailAlloc_6643_;
                                state = 3;
                                continue;
                            }
                        } else {
                            leanh::lean_del_object(v___x_6630_);
                            v___x_6644_ = 0usize;
                            v___x_6645_ = lean_usize_of_nat(v___x_6633_);
                            v___x_6646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6613_, v_es_6628_, v___x_6644_, v___x_6645_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                            leanh::lean_dec_ref(v_es_6628_);
                            return v___x_6646_;
                        }
                    } else {
                        leanh::lean_del_object(v___x_6630_);
                        v___x_6647_ = 0usize;
                        v___x_6648_ = lean_usize_of_nat(v___x_6633_);
                        v___x_6649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6613_, v_es_6628_, v___x_6647_, v___x_6648_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                        leanh::lean_dec_ref(v_es_6628_);
                        return v___x_6649_;
                    }
                }
            }
            2 => {
                v___x_6637_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6637_, 0, v___x_6636_);
                return v___x_6637_;
            }
            3 => {
                v___x_6642_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                leanh::lean_ctor_set(v___x_6642_, 0, v___x_6641_);
                return v___x_6642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_f_6655_: *mut leanh::LeanObject,
    mut v_as_6656_: *mut leanh::LeanObject,
    mut v_i_6657_: usize,
    mut v_stop_6658_: usize,
    mut v_b_6659_: *mut leanh::LeanObject,
    mut v___y_6660_: *mut leanh::LeanObject,
    mut v___y_6661_: *mut leanh::LeanObject,
    mut v___y_6662_: *mut leanh::LeanObject,
    mut v___y_6663_: *mut leanh::LeanObject,
    mut v___y_6664_: *mut leanh::LeanObject,
    mut v___y_6665_: *mut leanh::LeanObject,
    mut v___y_6666_: *mut leanh::LeanObject,
    mut v___y_6667_: *mut leanh::LeanObject,
    mut v___y_6668_: *mut leanh::LeanObject,
    mut v___y_6669_: *mut leanh::LeanObject,
    mut v___y_6670_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_a_6673_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: usize = 0;
    let mut v___x_6675_: usize = 0;
    let mut v___y_6678_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6679_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6680_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: u8 = 0;
    let mut v___x_6682_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6683_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6684_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_6686_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6681_ = lean_usize_dec_eq(v_i_6657_, v_stop_6658_);
                if v___x_6681_ == 0 {
                    v___x_6682_ = lean_array_uget_borrowed(v_as_6656_, v_i_6657_);
                    match leanh::lean_obj_tag(v___x_6682_) {
                        0 => {
                            v_key_6683_ = leanh::lean_ctor_get(v___x_6682_, 0);
                            v_val_6684_ = leanh::lean_ctor_get(v___x_6682_, 1);
                            leanh::lean_inc_ref(v_f_6655_);
                            leanh::lean_inc(v___y_6670_);
                            leanh::lean_inc_ref(v___y_6669_);
                            leanh::lean_inc(v___y_6668_);
                            leanh::lean_inc_ref(v___y_6667_);
                            leanh::lean_inc(v___y_6666_);
                            leanh::lean_inc_ref(v___y_6665_);
                            leanh::lean_inc(v___y_6664_);
                            leanh::lean_inc_ref(v___y_6663_);
                            leanh::lean_inc(v___y_6662_);
                            leanh::lean_inc(v___y_6661_);
                            leanh::lean_inc(v___y_6660_);
                            leanh::lean_inc(v_val_6684_);
                            leanh::lean_inc(v_key_6683_);
                            v___x_6685_ = leanh::lean_apply_15(
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
                                leanh::lean_box(0),
                            );
                            v___y_6678_ = v___x_6685_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_6686_ = leanh::lean_ctor_get(v___x_6682_, 0);
                            leanh::lean_inc(v_node_6686_);
                            leanh::lean_inc_ref(v_f_6655_);
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
                    leanh::lean_dec_ref(v_f_6655_);
                    v___x_6688_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6688_, 0, v_b_6659_);
                    v___x_6689_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_6689_, 0, v___x_6688_);
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
                if leanh::lean_obj_tag(v___y_6678_) == 0 {
                    v_a_6679_ = leanh::lean_ctor_get(v___y_6678_, 0);
                    if leanh::lean_obj_tag(v_a_6679_) == 0 {
                        leanh::lean_dec_ref(v_f_6655_);
                        return v___y_6678_;
                    } else {
                        leanh::lean_inc_ref(v_a_6679_);
                        leanh::lean_dec_ref_known(v___y_6678_, 1);
                        v_a_6680_ = leanh::lean_ctor_get(v_a_6679_, 0);
                        leanh::lean_inc(v_a_6680_);
                        leanh::lean_dec_ref_known(v_a_6679_, 1);
                        v_a_6673_ = v_a_6680_;
                        state = 1;
                        continue;
                    }
                } else {
                    leanh::lean_dec_ref(v_f_6655_);
                    return v___y_6678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_f_6690_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_as_6691_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_i_6692_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_stop_6693_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_6694_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_6695_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_6696_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_6697_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_6698_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_6699_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_6700_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_6701_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6702_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6703_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_6704_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_6705_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6706_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_i_boxed_6707_: usize = 0;
    let mut v_stop_boxed_6708_: usize = 0;
    let mut v_res_6709_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6707_ = leanh::lean_unbox_usize(v_i_6692_);
    leanh::lean_dec(v_i_6692_);
    v_stop_boxed_6708_ = leanh::lean_unbox_usize(v_stop_6693_);
    leanh::lean_dec(v_stop_6693_);
    v_res_6709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6690_, v_as_6691_, v_i_boxed_6707_, v_stop_boxed_6708_, v_b_6694_, v___y_6695_, v___y_6696_, v___y_6697_, v___y_6698_, v___y_6699_, v___y_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
    leanh::lean_dec(v___y_6705_);
    leanh::lean_dec_ref(v___y_6704_);
    leanh::lean_dec(v___y_6703_);
    leanh::lean_dec_ref(v___y_6702_);
    leanh::lean_dec(v___y_6701_);
    leanh::lean_dec_ref(v___y_6700_);
    leanh::lean_dec(v___y_6699_);
    leanh::lean_dec_ref(v___y_6698_);
    leanh::lean_dec(v___y_6697_);
    leanh::lean_dec(v___y_6696_);
    leanh::lean_dec(v___y_6695_);
    leanh::lean_dec_ref(v_as_6691_);
    return v_res_6709_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_6710_: *mut leanh::LeanObject,
    mut v_x_6711_: *mut leanh::LeanObject,
    mut v_x_6712_: *mut leanh::LeanObject,
    mut v___y_6713_: *mut leanh::LeanObject,
    mut v___y_6714_: *mut leanh::LeanObject,
    mut v___y_6715_: *mut leanh::LeanObject,
    mut v___y_6716_: *mut leanh::LeanObject,
    mut v___y_6717_: *mut leanh::LeanObject,
    mut v___y_6718_: *mut leanh::LeanObject,
    mut v___y_6719_: *mut leanh::LeanObject,
    mut v___y_6720_: *mut leanh::LeanObject,
    mut v___y_6721_: *mut leanh::LeanObject,
    mut v___y_6722_: *mut leanh::LeanObject,
    mut v___y_6723_: *mut leanh::LeanObject,
    mut v___y_6724_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6725_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6725_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6710_, v_x_6711_, v_x_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
    leanh::lean_dec(v___y_6723_);
    leanh::lean_dec_ref(v___y_6722_);
    leanh::lean_dec(v___y_6721_);
    leanh::lean_dec_ref(v___y_6720_);
    leanh::lean_dec(v___y_6719_);
    leanh::lean_dec_ref(v___y_6718_);
    leanh::lean_dec(v___y_6717_);
    leanh::lean_dec_ref(v___y_6716_);
    leanh::lean_dec(v___y_6715_);
    leanh::lean_dec(v___y_6714_);
    leanh::lean_dec(v___y_6713_);
    return v_res_6725_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(
    mut v_map_6726_: *mut leanh::LeanObject,
    mut v_init_6727_: *mut leanh::LeanObject,
    mut v_f_6728_: *mut leanh::LeanObject,
    mut v___y_6729_: *mut leanh::LeanObject,
    mut v___y_6730_: *mut leanh::LeanObject,
    mut v___y_6731_: *mut leanh::LeanObject,
    mut v___y_6732_: *mut leanh::LeanObject,
    mut v___y_6733_: *mut leanh::LeanObject,
    mut v___y_6734_: *mut leanh::LeanObject,
    mut v___y_6735_: *mut leanh::LeanObject,
    mut v___y_6736_: *mut leanh::LeanObject,
    mut v___y_6737_: *mut leanh::LeanObject,
    mut v___y_6738_: *mut leanh::LeanObject,
    mut v___y_6739_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___f_6741_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6743_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6746_: u8 = 0;
    let mut v_a_6747_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6751_: u8 = 0;
    let mut v_a_6752_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6755_: u8 = 0;
    let mut v___x_6757_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6758_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6741_ = leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 1);
                leanh::lean_closure_set(v___f_6741_, 0, v_f_6728_);
                leanh::lean_inc_ref(v_map_6726_);
                v___x_6742_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v___f_6741_, v_map_6726_, v_init_6727_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_, v___y_6734_, v___y_6735_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_);
                if leanh::lean_obj_tag(v___x_6742_) == 0 {
                    v_a_6743_ = leanh::lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6751_ = (!leanh::lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6751_ == 0 {
                        v___x_6745_ = v___x_6742_;
                        v_isShared_6746_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6743_);
                        leanh::lean_dec(v___x_6742_);
                        v___x_6745_ = leanh::lean_box(0);
                        v_isShared_6746_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6752_ = leanh::lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6759_ = (!leanh::lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6759_ == 0 {
                        v___x_6754_ = v___x_6742_;
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 3;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6752_);
                        leanh::lean_dec(v___x_6742_);
                        v___x_6754_ = leanh::lean_box(0);
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6747_ = leanh::lean_ctor_get(v_a_6743_, 0);
                leanh::lean_inc(v_a_6747_);
                leanh::lean_dec(v_a_6743_);
                if v_isShared_6746_ == 0 {
                    leanh::lean_ctor_set(v___x_6745_, 0, v_a_6747_);
                    v___x_6749_ = v___x_6745_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6750_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_a_6747_);
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
                    v_reuseFailAlloc_6758_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6752_);
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
    mut v_map_6760_: *mut leanh::LeanObject,
    mut v_init_6761_: *mut leanh::LeanObject,
    mut v_f_6762_: *mut leanh::LeanObject,
    mut v___y_6763_: *mut leanh::LeanObject,
    mut v___y_6764_: *mut leanh::LeanObject,
    mut v___y_6765_: *mut leanh::LeanObject,
    mut v___y_6766_: *mut leanh::LeanObject,
    mut v___y_6767_: *mut leanh::LeanObject,
    mut v___y_6768_: *mut leanh::LeanObject,
    mut v___y_6769_: *mut leanh::LeanObject,
    mut v___y_6770_: *mut leanh::LeanObject,
    mut v___y_6771_: *mut leanh::LeanObject,
    mut v___y_6772_: *mut leanh::LeanObject,
    mut v___y_6773_: *mut leanh::LeanObject,
    mut v___y_6774_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6775_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6775_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_6760_, v_init_6761_, v_f_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_, v___y_6773_);
    leanh::lean_dec(v___y_6773_);
    leanh::lean_dec_ref(v___y_6772_);
    leanh::lean_dec(v___y_6771_);
    leanh::lean_dec_ref(v___y_6770_);
    leanh::lean_dec(v___y_6769_);
    leanh::lean_dec_ref(v___y_6768_);
    leanh::lean_dec(v___y_6767_);
    leanh::lean_dec_ref(v___y_6766_);
    leanh::lean_dec(v___y_6765_);
    leanh::lean_dec(v___y_6764_);
    leanh::lean_dec(v___y_6763_);
    leanh::lean_dec_ref(v_map_6760_);
    return v_res_6775_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1()
-> *mut leanh::LeanObject {
    let mut v___x_6777_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0;
    v___x_6778_ = leanh::lean_unsigned_to_nat(2);
    v___x_6779_ = leanh::lean_unsigned_to_nat(91);
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
    mut v_a_6783_: *mut leanh::LeanObject,
    mut v_a_6784_: *mut leanh::LeanObject,
    mut v_a_6785_: *mut leanh::LeanObject,
    mut v_a_6786_: *mut leanh::LeanObject,
    mut v_a_6787_: *mut leanh::LeanObject,
    mut v_a_6788_: *mut leanh::LeanObject,
    mut v_a_6789_: *mut leanh::LeanObject,
    mut v_a_6790_: *mut leanh::LeanObject,
    mut v_a_6791_: *mut leanh::LeanObject,
    mut v_a_6792_: *mut leanh::LeanObject,
    mut v_a_6793_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6795_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6796_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6797_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_6798_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6799_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6802_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6805_: u8 = 0;
    let mut v_size_6806_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    let mut v___x_6808_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6813_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6814_: u8 = 0;
    let mut v_a_6815_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6818_: u8 = 0;
    let mut v___x_6820_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6821_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6822_: u8 = 0;
    let mut v_a_6823_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6826_: u8 = 0;
    let mut v___x_6828_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6829_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6795_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_,
                    v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_,
                );
                if leanh::lean_obj_tag(v___x_6795_) == 0 {
                    v_a_6796_ = leanh::lean_ctor_get(v___x_6795_, 0);
                    leanh::lean_inc(v_a_6796_);
                    leanh::lean_dec_ref_known(v___x_6795_, 1);
                    v_vars_6797_ = leanh::lean_ctor_get(v_a_6796_, 30);
                    leanh::lean_inc_ref_n(v_vars_6797_, 2);
                    v_varMap_6798_ = leanh::lean_ctor_get(v_a_6796_, 31);
                    leanh::lean_inc_ref(v_varMap_6798_);
                    leanh::lean_dec(v_a_6796_);
                    v___f_6799_ = leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed as *mut core::ffi::c_void, 15, 1);
                    leanh::lean_closure_set(v___f_6799_, 0, v_vars_6797_);
                    v___x_6800_ = leanh::lean_unsigned_to_nat(0);
                    v___x_6801_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_varMap_6798_, v___x_6800_, v___f_6799_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
                    leanh::lean_dec_ref(v_varMap_6798_);
                    if leanh::lean_obj_tag(v___x_6801_) == 0 {
                        v_a_6802_ = leanh::lean_ctor_get(v___x_6801_, 0);
                        v_isSharedCheck_6814_ =
                            (!leanh::lean_is_exclusive(v___x_6801_)) as u8;
                        if v_isSharedCheck_6814_ == 0 {
                            v___x_6804_ = v___x_6801_;
                            v_isShared_6805_ = v_isSharedCheck_6814_;
                            state = 1;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6802_);
                            leanh::lean_dec(v___x_6801_);
                            v___x_6804_ = leanh::lean_box(0);
                            v_isShared_6805_ = v_isSharedCheck_6814_;
                            state = 1;
                            continue;
                        }
                    } else {
                        leanh::lean_dec_ref(v_vars_6797_);
                        v_a_6815_ = leanh::lean_ctor_get(v___x_6801_, 0);
                        v_isSharedCheck_6822_ =
                            (!leanh::lean_is_exclusive(v___x_6801_)) as u8;
                        if v_isSharedCheck_6822_ == 0 {
                            v___x_6817_ = v___x_6801_;
                            v_isShared_6818_ = v_isSharedCheck_6822_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_6815_);
                            leanh::lean_dec(v___x_6801_);
                            v___x_6817_ = leanh::lean_box(0);
                            v_isShared_6818_ = v_isSharedCheck_6822_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_6823_ = leanh::lean_ctor_get(v___x_6795_, 0);
                    v_isSharedCheck_6830_ = (!leanh::lean_is_exclusive(v___x_6795_)) as u8;
                    if v_isSharedCheck_6830_ == 0 {
                        v___x_6825_ = v___x_6795_;
                        v_isShared_6826_ = v_isSharedCheck_6830_;
                        state = 5;
                        continue;
                    } else {
                        leanh::lean_inc(v_a_6823_);
                        leanh::lean_dec(v___x_6795_);
                        v___x_6825_ = leanh::lean_box(0);
                        v_isShared_6826_ = v_isSharedCheck_6830_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_size_6806_ = leanh::lean_ctor_get(v_vars_6797_, 2);
                leanh::lean_inc(v_size_6806_);
                leanh::lean_dec_ref(v_vars_6797_);
                v___x_6807_ = lean_nat_dec_eq(v_size_6806_, v_a_6802_);
                leanh::lean_dec(v_a_6802_);
                leanh::lean_dec(v_size_6806_);
                if v___x_6807_ == 0 {
                    leanh::lean_del_object(v___x_6804_);
                    v___x_6808_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1);
                    v___x_6809_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6808_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
                    return v___x_6809_;
                } else {
                    v___x_6810_ = leanh::lean_box(0);
                    if v_isShared_6805_ == 0 {
                        leanh::lean_ctor_set(v___x_6804_, 0, v___x_6810_);
                        v___x_6812_ = v___x_6804_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6813_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        leanh::lean_ctor_set(v_reuseFailAlloc_6813_, 0, v___x_6810_);
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
                    v_reuseFailAlloc_6821_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_a_6815_);
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
                    v_reuseFailAlloc_6829_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_6829_, 0, v_a_6823_);
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
    mut v_a_6831_: *mut leanh::LeanObject,
    mut v_a_6832_: *mut leanh::LeanObject,
    mut v_a_6833_: *mut leanh::LeanObject,
    mut v_a_6834_: *mut leanh::LeanObject,
    mut v_a_6835_: *mut leanh::LeanObject,
    mut v_a_6836_: *mut leanh::LeanObject,
    mut v_a_6837_: *mut leanh::LeanObject,
    mut v_a_6838_: *mut leanh::LeanObject,
    mut v_a_6839_: *mut leanh::LeanObject,
    mut v_a_6840_: *mut leanh::LeanObject,
    mut v_a_6841_: *mut leanh::LeanObject,
    mut v_a_6842_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6843_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6843_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_6831_, v_a_6832_, v_a_6833_, v_a_6834_, v_a_6835_, v_a_6836_, v_a_6837_, v_a_6838_, v_a_6839_, v_a_6840_, v_a_6841_);
    leanh::lean_dec(v_a_6841_);
    leanh::lean_dec_ref(v_a_6840_);
    leanh::lean_dec(v_a_6839_);
    leanh::lean_dec_ref(v_a_6838_);
    leanh::lean_dec(v_a_6837_);
    leanh::lean_dec_ref(v_a_6836_);
    leanh::lean_dec(v_a_6835_);
    leanh::lean_dec_ref(v_a_6834_);
    leanh::lean_dec(v_a_6833_);
    leanh::lean_dec(v_a_6832_);
    leanh::lean_dec(v_a_6831_);
    return v_res_6843_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(
    mut v_00_u03c3_6844_: *mut leanh::LeanObject,
    mut v_00_u03b2_6845_: *mut leanh::LeanObject,
    mut v_map_6846_: *mut leanh::LeanObject,
    mut v_init_6847_: *mut leanh::LeanObject,
    mut v_f_6848_: *mut leanh::LeanObject,
    mut v___y_6849_: *mut leanh::LeanObject,
    mut v___y_6850_: *mut leanh::LeanObject,
    mut v___y_6851_: *mut leanh::LeanObject,
    mut v___y_6852_: *mut leanh::LeanObject,
    mut v___y_6853_: *mut leanh::LeanObject,
    mut v___y_6854_: *mut leanh::LeanObject,
    mut v___y_6855_: *mut leanh::LeanObject,
    mut v___y_6856_: *mut leanh::LeanObject,
    mut v___y_6857_: *mut leanh::LeanObject,
    mut v___y_6858_: *mut leanh::LeanObject,
    mut v___y_6859_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6861_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6861_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_6846_, v_init_6847_, v_f_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_);
    return v___x_6861_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_00_u03c3_6862_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b2_6863_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_map_6864_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_init_6865_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_f_6866_: *mut leanh::LeanObject = *_args.add(4);
    let mut v___y_6867_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_6868_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_6869_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_6870_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_6871_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_6872_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_6873_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6874_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6875_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_6876_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_6877_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6878_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_6879_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6879_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(v_00_u03c3_6862_, v_00_u03b2_6863_, v_map_6864_, v_init_6865_, v_f_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_);
    leanh::lean_dec(v___y_6877_);
    leanh::lean_dec_ref(v___y_6876_);
    leanh::lean_dec(v___y_6875_);
    leanh::lean_dec_ref(v___y_6874_);
    leanh::lean_dec(v___y_6873_);
    leanh::lean_dec_ref(v___y_6872_);
    leanh::lean_dec(v___y_6871_);
    leanh::lean_dec_ref(v___y_6870_);
    leanh::lean_dec(v___y_6869_);
    leanh::lean_dec(v___y_6868_);
    leanh::lean_dec(v___y_6867_);
    leanh::lean_dec_ref(v_map_6864_);
    return v_res_6879_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(
    mut v_map_6880_: *mut leanh::LeanObject,
    mut v_f_6881_: *mut leanh::LeanObject,
    mut v_init_6882_: *mut leanh::LeanObject,
    mut v___y_6883_: *mut leanh::LeanObject,
    mut v___y_6884_: *mut leanh::LeanObject,
    mut v___y_6885_: *mut leanh::LeanObject,
    mut v___y_6886_: *mut leanh::LeanObject,
    mut v___y_6887_: *mut leanh::LeanObject,
    mut v___y_6888_: *mut leanh::LeanObject,
    mut v___y_6889_: *mut leanh::LeanObject,
    mut v___y_6890_: *mut leanh::LeanObject,
    mut v___y_6891_: *mut leanh::LeanObject,
    mut v___y_6892_: *mut leanh::LeanObject,
    mut v___y_6893_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6895_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6895_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6881_, v_map_6880_, v_init_6882_, v___y_6883_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_);
    return v___x_6895_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg___boxed(
    mut v_map_6896_: *mut leanh::LeanObject,
    mut v_f_6897_: *mut leanh::LeanObject,
    mut v_init_6898_: *mut leanh::LeanObject,
    mut v___y_6899_: *mut leanh::LeanObject,
    mut v___y_6900_: *mut leanh::LeanObject,
    mut v___y_6901_: *mut leanh::LeanObject,
    mut v___y_6902_: *mut leanh::LeanObject,
    mut v___y_6903_: *mut leanh::LeanObject,
    mut v___y_6904_: *mut leanh::LeanObject,
    mut v___y_6905_: *mut leanh::LeanObject,
    mut v___y_6906_: *mut leanh::LeanObject,
    mut v___y_6907_: *mut leanh::LeanObject,
    mut v___y_6908_: *mut leanh::LeanObject,
    mut v___y_6909_: *mut leanh::LeanObject,
    mut v___y_6910_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_6911_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6911_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(v_map_6896_, v_f_6897_, v_init_6898_, v___y_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_);
    leanh::lean_dec(v___y_6909_);
    leanh::lean_dec_ref(v___y_6908_);
    leanh::lean_dec(v___y_6907_);
    leanh::lean_dec_ref(v___y_6906_);
    leanh::lean_dec(v___y_6905_);
    leanh::lean_dec_ref(v___y_6904_);
    leanh::lean_dec(v___y_6903_);
    leanh::lean_dec_ref(v___y_6902_);
    leanh::lean_dec(v___y_6901_);
    leanh::lean_dec(v___y_6900_);
    leanh::lean_dec(v___y_6899_);
    return v_res_6911_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(
    mut v_00_u03c3_6912_: *mut leanh::LeanObject,
    mut v_00_u03c3_6913_: *mut leanh::LeanObject,
    mut v_00_u03b2_6914_: *mut leanh::LeanObject,
    mut v_map_6915_: *mut leanh::LeanObject,
    mut v_f_6916_: *mut leanh::LeanObject,
    mut v_init_6917_: *mut leanh::LeanObject,
    mut v___y_6918_: *mut leanh::LeanObject,
    mut v___y_6919_: *mut leanh::LeanObject,
    mut v___y_6920_: *mut leanh::LeanObject,
    mut v___y_6921_: *mut leanh::LeanObject,
    mut v___y_6922_: *mut leanh::LeanObject,
    mut v___y_6923_: *mut leanh::LeanObject,
    mut v___y_6924_: *mut leanh::LeanObject,
    mut v___y_6925_: *mut leanh::LeanObject,
    mut v___y_6926_: *mut leanh::LeanObject,
    mut v___y_6927_: *mut leanh::LeanObject,
    mut v___y_6928_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6930_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6930_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6916_, v_map_6915_, v_init_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_, v___y_6922_, v___y_6923_, v___y_6924_, v___y_6925_, v___y_6926_, v___y_6927_, v___y_6928_);
    return v___x_6930_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_00_u03c3_6931_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_6932_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b2_6933_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_map_6934_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_f_6935_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_init_6936_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_6937_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_6938_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_6939_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_6940_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_6941_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_6942_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6943_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6944_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_6945_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_6946_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6947_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_6948_: *mut leanh::LeanObject = *_args.add(17);
    let mut v_res_6949_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6949_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(v_00_u03c3_6931_, v_00_u03c3_6932_, v_00_u03b2_6933_, v_map_6934_, v_f_6935_, v_init_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
    leanh::lean_dec(v___y_6947_);
    leanh::lean_dec_ref(v___y_6946_);
    leanh::lean_dec(v___y_6945_);
    leanh::lean_dec_ref(v___y_6944_);
    leanh::lean_dec(v___y_6943_);
    leanh::lean_dec_ref(v___y_6942_);
    leanh::lean_dec(v___y_6941_);
    leanh::lean_dec_ref(v___y_6940_);
    leanh::lean_dec(v___y_6939_);
    leanh::lean_dec(v___y_6938_);
    leanh::lean_dec(v___y_6937_);
    return v_res_6949_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(
    mut v_00_u03c3_6950_: *mut leanh::LeanObject,
    mut v_00_u03c3_6951_: *mut leanh::LeanObject,
    mut v_00_u03b1_6952_: *mut leanh::LeanObject,
    mut v_00_u03b2_6953_: *mut leanh::LeanObject,
    mut v_f_6954_: *mut leanh::LeanObject,
    mut v_x_6955_: *mut leanh::LeanObject,
    mut v_x_6956_: *mut leanh::LeanObject,
    mut v___y_6957_: *mut leanh::LeanObject,
    mut v___y_6958_: *mut leanh::LeanObject,
    mut v___y_6959_: *mut leanh::LeanObject,
    mut v___y_6960_: *mut leanh::LeanObject,
    mut v___y_6961_: *mut leanh::LeanObject,
    mut v___y_6962_: *mut leanh::LeanObject,
    mut v___y_6963_: *mut leanh::LeanObject,
    mut v___y_6964_: *mut leanh::LeanObject,
    mut v___y_6965_: *mut leanh::LeanObject,
    mut v___y_6966_: *mut leanh::LeanObject,
    mut v___y_6967_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_6969_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_6969_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6954_, v_x_6955_, v_x_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_);
    return v___x_6969_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_00_u03c3_6970_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_6971_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b1_6972_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b2_6973_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_f_6974_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_x_6975_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_x_6976_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_6977_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_6978_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_6979_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_6980_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_6981_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_6982_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_6983_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_6984_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_6985_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_6986_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_6987_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_6988_: *mut leanh::LeanObject = *_args.add(18);
    let mut v_res_6989_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_6989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(v_00_u03c3_6970_, v_00_u03c3_6971_, v_00_u03b1_6972_, v_00_u03b2_6973_, v_f_6974_, v_x_6975_, v_x_6976_, v___y_6977_, v___y_6978_, v___y_6979_, v___y_6980_, v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_);
    leanh::lean_dec(v___y_6987_);
    leanh::lean_dec_ref(v___y_6986_);
    leanh::lean_dec(v___y_6985_);
    leanh::lean_dec_ref(v___y_6984_);
    leanh::lean_dec(v___y_6983_);
    leanh::lean_dec_ref(v___y_6982_);
    leanh::lean_dec(v___y_6981_);
    leanh::lean_dec_ref(v___y_6980_);
    leanh::lean_dec(v___y_6979_);
    leanh::lean_dec(v___y_6978_);
    leanh::lean_dec(v___y_6977_);
    return v_res_6989_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_6990_: *mut leanh::LeanObject,
    mut v_00_u03b2_6991_: *mut leanh::LeanObject,
    mut v_00_u03c3_6992_: *mut leanh::LeanObject,
    mut v_00_u03c3_6993_: *mut leanh::LeanObject,
    mut v_f_6994_: *mut leanh::LeanObject,
    mut v_as_6995_: *mut leanh::LeanObject,
    mut v_i_6996_: usize,
    mut v_stop_6997_: usize,
    mut v_b_6998_: *mut leanh::LeanObject,
    mut v___y_6999_: *mut leanh::LeanObject,
    mut v___y_7000_: *mut leanh::LeanObject,
    mut v___y_7001_: *mut leanh::LeanObject,
    mut v___y_7002_: *mut leanh::LeanObject,
    mut v___y_7003_: *mut leanh::LeanObject,
    mut v___y_7004_: *mut leanh::LeanObject,
    mut v___y_7005_: *mut leanh::LeanObject,
    mut v___y_7006_: *mut leanh::LeanObject,
    mut v___y_7007_: *mut leanh::LeanObject,
    mut v___y_7008_: *mut leanh::LeanObject,
    mut v___y_7009_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7011_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6994_, v_as_6995_, v_i_6996_, v_stop_6997_, v_b_6998_, v___y_6999_, v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_);
    return v___x_7011_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_00_u03b1_7012_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b2_7013_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3_7014_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3_7015_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_f_7016_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_as_7017_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_i_7018_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_stop_7019_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_b_7020_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_7021_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_7022_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_7023_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_7024_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7025_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7026_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7027_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7028_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_7029_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_7030_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_7031_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_7032_: *mut leanh::LeanObject = *_args.add(20);
    let mut v_i_boxed_7033_: usize = 0;
    let mut v_stop_boxed_7034_: usize = 0;
    let mut v_res_7035_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7033_ = leanh::lean_unbox_usize(v_i_7018_);
    leanh::lean_dec(v_i_7018_);
    v_stop_boxed_7034_ = leanh::lean_unbox_usize(v_stop_7019_);
    leanh::lean_dec(v_stop_7019_);
    v_res_7035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_7012_, v_00_u03b2_7013_, v_00_u03c3_7014_, v_00_u03c3_7015_, v_f_7016_, v_as_7017_, v_i_boxed_7033_, v_stop_boxed_7034_, v_b_7020_, v___y_7021_, v___y_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_);
    leanh::lean_dec(v___y_7031_);
    leanh::lean_dec_ref(v___y_7030_);
    leanh::lean_dec(v___y_7029_);
    leanh::lean_dec_ref(v___y_7028_);
    leanh::lean_dec(v___y_7027_);
    leanh::lean_dec_ref(v___y_7026_);
    leanh::lean_dec(v___y_7025_);
    leanh::lean_dec_ref(v___y_7024_);
    leanh::lean_dec(v___y_7023_);
    leanh::lean_dec(v___y_7022_);
    leanh::lean_dec(v___y_7021_);
    leanh::lean_dec_ref(v_as_7017_);
    return v_res_7035_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03c3_7036_: *mut leanh::LeanObject,
    mut v_00_u03c3_7037_: *mut leanh::LeanObject,
    mut v_00_u03b1_7038_: *mut leanh::LeanObject,
    mut v_00_u03b2_7039_: *mut leanh::LeanObject,
    mut v_f_7040_: *mut leanh::LeanObject,
    mut v_keys_7041_: *mut leanh::LeanObject,
    mut v_vals_7042_: *mut leanh::LeanObject,
    mut v_heq_7043_: *mut leanh::LeanObject,
    mut v_i_7044_: *mut leanh::LeanObject,
    mut v_acc_7045_: *mut leanh::LeanObject,
    mut v___y_7046_: *mut leanh::LeanObject,
    mut v___y_7047_: *mut leanh::LeanObject,
    mut v___y_7048_: *mut leanh::LeanObject,
    mut v___y_7049_: *mut leanh::LeanObject,
    mut v___y_7050_: *mut leanh::LeanObject,
    mut v___y_7051_: *mut leanh::LeanObject,
    mut v___y_7052_: *mut leanh::LeanObject,
    mut v___y_7053_: *mut leanh::LeanObject,
    mut v___y_7054_: *mut leanh::LeanObject,
    mut v___y_7055_: *mut leanh::LeanObject,
    mut v___y_7056_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7058_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7058_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_7040_, v_keys_7041_, v_vals_7042_, v_i_7044_, v_acc_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
    return v___x_7058_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_00_u03c3_7059_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_7060_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b1_7061_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b2_7062_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_f_7063_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_keys_7064_: *mut leanh::LeanObject = *_args.add(5);
    let mut v_vals_7065_: *mut leanh::LeanObject = *_args.add(6);
    let mut v_heq_7066_: *mut leanh::LeanObject = *_args.add(7);
    let mut v_i_7067_: *mut leanh::LeanObject = *_args.add(8);
    let mut v_acc_7068_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_7069_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_7070_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_7071_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7072_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7073_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7074_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7075_: *mut leanh::LeanObject = *_args.add(16);
    let mut v___y_7076_: *mut leanh::LeanObject = *_args.add(17);
    let mut v___y_7077_: *mut leanh::LeanObject = *_args.add(18);
    let mut v___y_7078_: *mut leanh::LeanObject = *_args.add(19);
    let mut v___y_7079_: *mut leanh::LeanObject = *_args.add(20);
    let mut v___y_7080_: *mut leanh::LeanObject = *_args.add(21);
    let mut v_res_7081_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_7059_, v_00_u03c3_7060_, v_00_u03b1_7061_, v_00_u03b2_7062_, v_f_7063_, v_keys_7064_, v_vals_7065_, v_heq_7066_, v_i_7067_, v_acc_7068_, v___y_7069_, v___y_7070_, v___y_7071_, v___y_7072_, v___y_7073_, v___y_7074_, v___y_7075_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_);
    leanh::lean_dec(v___y_7079_);
    leanh::lean_dec_ref(v___y_7078_);
    leanh::lean_dec(v___y_7077_);
    leanh::lean_dec_ref(v___y_7076_);
    leanh::lean_dec(v___y_7075_);
    leanh::lean_dec_ref(v___y_7074_);
    leanh::lean_dec(v___y_7073_);
    leanh::lean_dec_ref(v___y_7072_);
    leanh::lean_dec(v___y_7071_);
    leanh::lean_dec(v___y_7070_);
    leanh::lean_dec(v___y_7069_);
    leanh::lean_dec_ref(v_vals_7065_);
    leanh::lean_dec_ref(v_keys_7064_);
    return v_res_7081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(
    mut v_a_7082_: *mut leanh::LeanObject,
    mut v_a_7083_: *mut leanh::LeanObject,
    mut v_a_7084_: *mut leanh::LeanObject,
    mut v_a_7085_: *mut leanh::LeanObject,
    mut v_a_7086_: *mut leanh::LeanObject,
    mut v_a_7087_: *mut leanh::LeanObject,
    mut v_a_7088_: *mut leanh::LeanObject,
    mut v_a_7089_: *mut leanh::LeanObject,
    mut v_a_7090_: *mut leanh::LeanObject,
    mut v_a_7091_: *mut leanh::LeanObject,
    mut v_a_7092_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7094_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
    if leanh::lean_obj_tag(v___x_7094_) == 0 {
        let mut v___x_7095_: *mut leanh::LeanObject = core::ptr::null_mut();
        leanh::lean_dec_ref_known(v___x_7094_, 1);
        v___x_7095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
        if leanh::lean_obj_tag(v___x_7095_) == 0 {
            let mut v___x_7096_: *mut leanh::LeanObject = core::ptr::null_mut();
            leanh::lean_dec_ref_known(v___x_7095_, 1);
            v___x_7096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
            if leanh::lean_obj_tag(v___x_7096_) == 0 {
                let mut v___x_7097_: *mut leanh::LeanObject = core::ptr::null_mut();
                leanh::lean_dec_ref_known(v___x_7096_, 1);
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
    mut v_a_7098_: *mut leanh::LeanObject,
    mut v_a_7099_: *mut leanh::LeanObject,
    mut v_a_7100_: *mut leanh::LeanObject,
    mut v_a_7101_: *mut leanh::LeanObject,
    mut v_a_7102_: *mut leanh::LeanObject,
    mut v_a_7103_: *mut leanh::LeanObject,
    mut v_a_7104_: *mut leanh::LeanObject,
    mut v_a_7105_: *mut leanh::LeanObject,
    mut v_a_7106_: *mut leanh::LeanObject,
    mut v_a_7107_: *mut leanh::LeanObject,
    mut v_a_7108_: *mut leanh::LeanObject,
    mut v_a_7109_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7110_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_, v_a_7106_, v_a_7107_, v_a_7108_);
    leanh::lean_dec(v_a_7108_);
    leanh::lean_dec_ref(v_a_7107_);
    leanh::lean_dec(v_a_7106_);
    leanh::lean_dec_ref(v_a_7105_);
    leanh::lean_dec(v_a_7104_);
    leanh::lean_dec_ref(v_a_7103_);
    leanh::lean_dec(v_a_7102_);
    leanh::lean_dec_ref(v_a_7101_);
    leanh::lean_dec(v_a_7100_);
    leanh::lean_dec(v_a_7099_);
    leanh::lean_dec(v_a_7098_);
    return v_res_7110_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2()
-> *mut leanh::LeanObject {
    let mut v___x_7113_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1;
    v___x_7114_ = leanh::lean_unsigned_to_nat(6);
    v___x_7115_ = leanh::lean_unsigned_to_nat(103);
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
    mut v_upperBound_7119_: *mut leanh::LeanObject,
    mut v_a_7120_: *mut leanh::LeanObject,
    mut v_b_7121_: *mut leanh::LeanObject,
    mut v___y_7122_: *mut leanh::LeanObject,
    mut v___y_7123_: *mut leanh::LeanObject,
    mut v___y_7124_: *mut leanh::LeanObject,
    mut v___y_7125_: *mut leanh::LeanObject,
    mut v___y_7126_: *mut leanh::LeanObject,
    mut v___y_7127_: *mut leanh::LeanObject,
    mut v___y_7128_: *mut leanh::LeanObject,
    mut v___y_7129_: *mut leanh::LeanObject,
    mut v___y_7130_: *mut leanh::LeanObject,
    mut v___y_7131_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7133_: u8 = 0;
    let mut v___x_7134_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7137_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: u8 = 0;
    let mut v___x_7142_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7133_ = lean_nat_dec_lt(v_a_7120_, v_upperBound_7119_);
                if v___x_7133_ == 0 {
                    leanh::lean_dec(v_a_7120_);
                    v___x_7134_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7134_, 0, v_b_7121_);
                    return v___x_7134_;
                } else {
                    v___x_7135_ = leanh::lean_box(0);
                    v___x_7141_ = lean_nat_dec_eq(v_a_7120_, v_a_7120_);
                    if v___x_7141_ == 0 {
                        v___x_7142_ = leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2);
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
                if leanh::lean_obj_tag(v___y_7137_) == 0 {
                    leanh::lean_dec_ref_known(v___y_7137_, 1);
                    v___x_7138_ = leanh::lean_unsigned_to_nat(1);
                    v___x_7139_ = lean_nat_add(v_a_7120_, v___x_7138_);
                    leanh::lean_dec(v_a_7120_);
                    v_a_7120_ = v___x_7139_;
                    v_b_7121_ = v___x_7135_;
                    state = 0;
                    continue;
                } else {
                    leanh::lean_dec(v_a_7120_);
                    return v___y_7137_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___boxed(
    mut v_upperBound_7145_: *mut leanh::LeanObject,
    mut v_a_7146_: *mut leanh::LeanObject,
    mut v_b_7147_: *mut leanh::LeanObject,
    mut v___y_7148_: *mut leanh::LeanObject,
    mut v___y_7149_: *mut leanh::LeanObject,
    mut v___y_7150_: *mut leanh::LeanObject,
    mut v___y_7151_: *mut leanh::LeanObject,
    mut v___y_7152_: *mut leanh::LeanObject,
    mut v___y_7153_: *mut leanh::LeanObject,
    mut v___y_7154_: *mut leanh::LeanObject,
    mut v___y_7155_: *mut leanh::LeanObject,
    mut v___y_7156_: *mut leanh::LeanObject,
    mut v___y_7157_: *mut leanh::LeanObject,
    mut v___y_7158_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7159_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_7145_, v_a_7146_, v_b_7147_, v___y_7148_, v___y_7149_, v___y_7150_, v___y_7151_, v___y_7152_, v___y_7153_, v___y_7154_, v___y_7155_, v___y_7156_, v___y_7157_);
    leanh::lean_dec(v___y_7157_);
    leanh::lean_dec_ref(v___y_7156_);
    leanh::lean_dec(v___y_7155_);
    leanh::lean_dec_ref(v___y_7154_);
    leanh::lean_dec(v___y_7153_);
    leanh::lean_dec_ref(v___y_7152_);
    leanh::lean_dec(v___y_7151_);
    leanh::lean_dec_ref(v___y_7150_);
    leanh::lean_dec(v___y_7149_);
    leanh::lean_dec(v___y_7148_);
    leanh::lean_dec(v_upperBound_7145_);
    return v_res_7159_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_checkInvariants(
    mut v_a_7160_: *mut leanh::LeanObject,
    mut v_a_7161_: *mut leanh::LeanObject,
    mut v_a_7162_: *mut leanh::LeanObject,
    mut v_a_7163_: *mut leanh::LeanObject,
    mut v_a_7164_: *mut leanh::LeanObject,
    mut v_a_7165_: *mut leanh::LeanObject,
    mut v_a_7166_: *mut leanh::LeanObject,
    mut v_a_7167_: *mut leanh::LeanObject,
    mut v_a_7168_: *mut leanh::LeanObject,
    mut v_a_7169_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_debug_7171_: u8 = 0;
    let mut v___x_7172_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7175_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_7176_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7183_: u8 = 0;
    let mut v___x_7185_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7186_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7187_: u8 = 0;
    let mut v_unused_7188_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7189_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7192_: u8 = 0;
    let mut v___x_7194_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7195_: *mut leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_debug_7171_ = leanh::lean_ctor_get_uint8(
                    v_a_7162_,
                    (core::mem::size_of::<*mut leanh::LeanObject>() * 8 + 2) as u32,
                );
                if v_debug_7171_ == 0 {
                    v___x_7172_ = leanh::lean_box(0);
                    v___x_7173_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v___x_7173_, 0, v___x_7172_);
                    return v___x_7173_;
                } else {
                    v___x_7174_ =
                        l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_7160_, v_a_7168_);
                    if leanh::lean_obj_tag(v___x_7174_) == 0 {
                        v_a_7175_ = leanh::lean_ctor_get(v___x_7174_, 0);
                        leanh::lean_inc(v_a_7175_);
                        leanh::lean_dec_ref_known(v___x_7174_, 1);
                        v_structs_7176_ = leanh::lean_ctor_get(v_a_7175_, 0);
                        leanh::lean_inc_ref(v_structs_7176_);
                        leanh::lean_dec(v_a_7175_);
                        v___x_7177_ = lean_array_get_size(v_structs_7176_);
                        leanh::lean_dec_ref(v_structs_7176_);
                        v___x_7178_ = leanh::lean_unsigned_to_nat(0);
                        v___x_7179_ = leanh::lean_box(0);
                        v___x_7180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v___x_7177_, v___x_7178_, v___x_7179_, v_a_7160_, v_a_7161_, v_a_7162_, v_a_7163_, v_a_7164_, v_a_7165_, v_a_7166_, v_a_7167_, v_a_7168_, v_a_7169_);
                        if leanh::lean_obj_tag(v___x_7180_) == 0 {
                            v_isSharedCheck_7187_ =
                                (!leanh::lean_is_exclusive(v___x_7180_)) as u8;
                            if v_isSharedCheck_7187_ == 0 {
                                v_unused_7188_ = leanh::lean_ctor_get(v___x_7180_, 0);
                                leanh::lean_dec(v_unused_7188_);
                                v___x_7182_ = v___x_7180_;
                                v_isShared_7183_ = v_isSharedCheck_7187_;
                                state = 1;
                                continue;
                            } else {
                                leanh::lean_dec(v___x_7180_);
                                v___x_7182_ = leanh::lean_box(0);
                                v_isShared_7183_ = v_isSharedCheck_7187_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_7180_;
                        }
                    } else {
                        v_a_7189_ = leanh::lean_ctor_get(v___x_7174_, 0);
                        v_isSharedCheck_7196_ =
                            (!leanh::lean_is_exclusive(v___x_7174_)) as u8;
                        if v_isSharedCheck_7196_ == 0 {
                            v___x_7191_ = v___x_7174_;
                            v_isShared_7192_ = v_isSharedCheck_7196_;
                            state = 3;
                            continue;
                        } else {
                            leanh::lean_inc(v_a_7189_);
                            leanh::lean_dec(v___x_7174_);
                            v___x_7191_ = leanh::lean_box(0);
                            v_isShared_7192_ = v_isSharedCheck_7196_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7183_ == 0 {
                    leanh::lean_ctor_set(v___x_7182_, 0, v___x_7179_);
                    v___x_7185_ = v___x_7182_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7186_ = leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7186_, 0, v___x_7179_);
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
                    v_reuseFailAlloc_7195_ = leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    leanh::lean_ctor_set(v_reuseFailAlloc_7195_, 0, v_a_7189_);
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
    mut v_a_7197_: *mut leanh::LeanObject,
    mut v_a_7198_: *mut leanh::LeanObject,
    mut v_a_7199_: *mut leanh::LeanObject,
    mut v_a_7200_: *mut leanh::LeanObject,
    mut v_a_7201_: *mut leanh::LeanObject,
    mut v_a_7202_: *mut leanh::LeanObject,
    mut v_a_7203_: *mut leanh::LeanObject,
    mut v_a_7204_: *mut leanh::LeanObject,
    mut v_a_7205_: *mut leanh::LeanObject,
    mut v_a_7206_: *mut leanh::LeanObject,
    mut v_a_7207_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_res_7208_: *mut leanh::LeanObject = core::ptr::null_mut();
    v_res_7208_ = l_Lean_Meta_Grind_Arith_Linear_checkInvariants(
        v_a_7197_, v_a_7198_, v_a_7199_, v_a_7200_, v_a_7201_, v_a_7202_, v_a_7203_, v_a_7204_,
        v_a_7205_, v_a_7206_,
    );
    leanh::lean_dec(v_a_7206_);
    leanh::lean_dec_ref(v_a_7205_);
    leanh::lean_dec(v_a_7204_);
    leanh::lean_dec_ref(v_a_7203_);
    leanh::lean_dec(v_a_7202_);
    leanh::lean_dec_ref(v_a_7201_);
    leanh::lean_dec(v_a_7200_);
    leanh::lean_dec_ref(v_a_7199_);
    leanh::lean_dec(v_a_7198_);
    leanh::lean_dec(v_a_7197_);
    return v_res_7208_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(
    mut v_upperBound_7209_: *mut leanh::LeanObject,
    mut v_inst_7210_: *mut leanh::LeanObject,
    mut v_R_7211_: *mut leanh::LeanObject,
    mut v_a_7212_: *mut leanh::LeanObject,
    mut v_b_7213_: *mut leanh::LeanObject,
    mut v_c_7214_: *mut leanh::LeanObject,
    mut v___y_7215_: *mut leanh::LeanObject,
    mut v___y_7216_: *mut leanh::LeanObject,
    mut v___y_7217_: *mut leanh::LeanObject,
    mut v___y_7218_: *mut leanh::LeanObject,
    mut v___y_7219_: *mut leanh::LeanObject,
    mut v___y_7220_: *mut leanh::LeanObject,
    mut v___y_7221_: *mut leanh::LeanObject,
    mut v___y_7222_: *mut leanh::LeanObject,
    mut v___y_7223_: *mut leanh::LeanObject,
    mut v___y_7224_: *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v___x_7226_: *mut leanh::LeanObject = core::ptr::null_mut();
    v___x_7226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_7209_, v_a_7212_, v_b_7213_, v___y_7215_, v___y_7216_, v___y_7217_, v___y_7218_, v___y_7219_, v___y_7220_, v___y_7221_, v___y_7222_, v___y_7223_, v___y_7224_);
    return v___x_7226_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___boxed(
    _args: *mut *mut leanh::LeanObject,
) -> *mut leanh::LeanObject {
    let mut v_upperBound_7227_: *mut leanh::LeanObject = *_args.add(0);
    let mut v_inst_7228_: *mut leanh::LeanObject = *_args.add(1);
    let mut v_R_7229_: *mut leanh::LeanObject = *_args.add(2);
    let mut v_a_7230_: *mut leanh::LeanObject = *_args.add(3);
    let mut v_b_7231_: *mut leanh::LeanObject = *_args.add(4);
    let mut v_c_7232_: *mut leanh::LeanObject = *_args.add(5);
    let mut v___y_7233_: *mut leanh::LeanObject = *_args.add(6);
    let mut v___y_7234_: *mut leanh::LeanObject = *_args.add(7);
    let mut v___y_7235_: *mut leanh::LeanObject = *_args.add(8);
    let mut v___y_7236_: *mut leanh::LeanObject = *_args.add(9);
    let mut v___y_7237_: *mut leanh::LeanObject = *_args.add(10);
    let mut v___y_7238_: *mut leanh::LeanObject = *_args.add(11);
    let mut v___y_7239_: *mut leanh::LeanObject = *_args.add(12);
    let mut v___y_7240_: *mut leanh::LeanObject = *_args.add(13);
    let mut v___y_7241_: *mut leanh::LeanObject = *_args.add(14);
    let mut v___y_7242_: *mut leanh::LeanObject = *_args.add(15);
    let mut v___y_7243_: *mut leanh::LeanObject = *_args.add(16);
    let mut v_res_7244_: *mut leanh::LeanObject = core::ptr::null_mut();
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
    leanh::lean_dec(v___y_7242_);
    leanh::lean_dec_ref(v___y_7241_);
    leanh::lean_dec(v___y_7240_);
    leanh::lean_dec_ref(v___y_7239_);
    leanh::lean_dec(v___y_7238_);
    leanh::lean_dec_ref(v___y_7237_);
    leanh::lean_dec(v___y_7236_);
    leanh::lean_dec_ref(v___y_7235_);
    leanh::lean_dec(v___y_7234_);
    leanh::lean_dec(v___y_7233_);
    leanh::lean_dec(v_upperBound_7227_);
    return v_res_7244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_runtime_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_runtime_initialized = true;
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
    builtin: u8,
) -> *mut leanh::LeanObject {
    let mut res: *mut leanh::LeanObject = core::ptr::null_mut();
    if _G_initialized {
        return leanh::lean_io_result_mk_ok(leanh::lean_box(0));
    }
    _G_initialized = true;
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_LinearM(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if leanh::lean_io_result_is_error(res) {
        return res;
    }
    leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
}