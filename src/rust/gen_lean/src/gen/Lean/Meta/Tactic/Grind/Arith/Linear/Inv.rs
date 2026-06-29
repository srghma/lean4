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
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value: crate::leanh::LeanStringObject<40> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 40, m_capacity: 40, m_length: 39, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value: crate::leanh::LeanStringObject<89> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 79, 99, 99, 115, 46, 103, 111, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__1_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value: crate::leanh::LeanStringObject<123> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 123, m_capacity: 123, m_length: 122, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 50, 57, 56, 50, 52, 51, 48, 53, 52, 51, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 53, 46, 48, 32, 41, 46, 99, 111, 110, 116, 97, 105, 110, 115, 32, 121, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value: crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 78, 111, 69, 108, 105, 109, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value: crate::leanh::LeanStringObject<110> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 110, m_capacity: 110, m_length: 109, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 33, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 51, 52, 49, 49, 54, 57, 48, 48, 51, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 51, 51, 46, 48, 32, 41, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value: crate::leanh::LeanStringObject<89> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 89, m_capacity: 89, m_length: 88, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 71, 114, 105, 110, 100, 46, 76, 105, 110, 97, 114, 105, 116, 104, 46, 80, 111, 108, 121, 46, 99, 104, 101, 99, 107, 67, 110, 115, 116, 114, 79, 102, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value: crate::leanh::LeanStringObject<30> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 30, m_capacity: 30, m_length: 29, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 120, 32, 61, 61, 32, 121, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value: crate::leanh::LeanStringObject<34> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 34, m_capacity: 34, m_length: 33, m_data: [117, 110, 114, 101, 97, 99, 104, 97, 98, 108, 101, 32, 99, 111, 100, 101, 32, 104, 97, 115, 32, 98, 101, 101, 110, 32, 114, 101, 97, 99, 104, 101, 100, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value: crate::leanh::LeanStringObject<35> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 35, m_capacity: 35, m_length: 34, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 105, 115, 83, 111, 114, 116, 101, 100, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value: crate::leanh::LeanStringObject<38> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 38, m_capacity: 38, m_length: 37, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 112, 46, 99, 104, 101, 99, 107, 67, 111, 101, 102, 102, 115, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value: crate::leanh::LeanStringObject<94> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 94, m_capacity: 94, m_length: 93, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 76, 101, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 76, 111, 119, 101, 114, 32, 61, 61, 32, 40, 97, 32, 60, 32, 48, 41, 10, 32, 32, 32, 32, 0]};
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value: crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 76, 111, 119, 101, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 108, 111, 119, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value: crate::leanh::LeanStringObject<92> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 92, m_capacity: 92, m_length: 91, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 85, 112, 112, 101, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 117, 112, 112, 101, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value: crate::leanh::LeanCtorObject<2> = crate::leanh::LeanCtorObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (core::mem::size_of::<crate::leanh::LeanObject>() + core::mem::size_of::<*mut crate::leanh::LeanObject>()*2 + 0) as u16, other: 2, tag: 0 }, m_objs: [((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject,((( 0 as usize) << 1) | 1) as *mut crate::leanh::LeanObject] };
static mut l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value: crate::leanh::LeanStringObject<97> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 97, m_capacity: 97, m_length: 96, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 68, 105, 115, 101, 113, 67, 110, 115, 116, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value: crate::leanh::LeanStringObject<53> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 53, m_capacity: 53, m_length: 52, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 115, 46, 100, 105, 115, 101, 113, 115, 46, 115, 105, 122, 101, 10, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value: crate::leanh::LeanStringObject<90> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 90, m_capacity: 90, m_length: 89, m_data: [95, 112, 114, 105, 118, 97, 116, 101, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 48, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 86, 97, 114, 115, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value: crate::leanh::LeanStringObject<48> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 48, m_capacity: 48, m_length: 47, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 105, 115, 83, 97, 109, 101, 69, 120, 112, 114, 32, 101, 120, 112, 114, 32, 101, 120, 112, 114, 39, 10, 32, 32, 32, 32, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value: crate::leanh::LeanStringObject<42> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 42, m_capacity: 42, m_length: 41, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 115, 46, 118, 97, 114, 115, 46, 115, 105, 122, 101, 32, 61, 61, 32, 110, 117, 109, 10, 10, 0]};
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0_value) as *mut crate::leanh::LeanObject;
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value: crate::leanh::LeanStringObject<45> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 45, m_capacity: 45, m_length: 44, m_data: [76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 99, 104, 101, 99, 107, 73, 110, 118, 97, 114, 105, 97, 110, 116, 115, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__0_value) as *mut crate::leanh::LeanObject;
pub static l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value: crate::leanh::LeanStringObject<126> = crate::leanh::LeanStringObject { m_header: crate::leanh::LeanObject { rc: 0, cs_size: (0) as u16, other: 0, tag: 249 }, m_size: 126, m_capacity: 126, m_length: 125, m_data: [97, 115, 115, 101, 114, 116, 105, 111, 110, 32, 118, 105, 111, 108, 97, 116, 105, 111, 110, 58, 32, 40, 32, 95, 95, 100, 111, 95, 108, 105, 102, 116, 46, 95, 64, 46, 76, 101, 97, 110, 46, 77, 101, 116, 97, 46, 84, 97, 99, 116, 105, 99, 46, 71, 114, 105, 110, 100, 46, 65, 114, 105, 116, 104, 46, 76, 105, 110, 101, 97, 114, 46, 73, 110, 118, 46, 51, 49, 49, 57, 50, 50, 53, 55, 54, 52, 46, 95, 104, 121, 103, 67, 116, 120, 46, 95, 104, 121, 103, 46, 54, 48, 46, 48, 32, 41, 32, 61, 61, 32, 115, 116, 114, 117, 99, 116, 73, 100, 10, 32, 32, 32, 32, 32, 32, 0]};
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1: *mut crate::leanh::LeanObject = core::ptr::addr_of!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1_value) as *mut crate::leanh::LeanObject;
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once: crate::leanh::LeanOnceCell = crate::leanh::LeanOnceCell { state: core::sync::atomic::AtomicI32::new(0), lock: core::sync::atomic::AtomicI32::new(0) };
static mut l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2: *mut crate::leanh::LeanObject = core::ptr::null_mut();
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
    mut v_a_3623_: *mut crate::leanh::LeanObject,
    mut v_a_3624_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3625_: u8 = 0;
    let mut v_v_3626_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3627_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3631_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_3632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3635_: u8 = 0;
    let mut v___x_3636_: u8 = 0;
    let mut v___x_3638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3640_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3641_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_a_3624_) == 0 {
                    crate::leanh::lean_dec(v_a_3623_);
                    v___x_3625_ = 1;
                    return v___x_3625_;
                } else {
                    if crate::leanh::lean_obj_tag(v_a_3623_) == 0 {
                        v_v_3626_ = crate::leanh::lean_ctor_get(v_a_3624_, 1);
                        v_p_3627_ = crate::leanh::lean_ctor_get(v_a_3624_, 2);
                        crate::leanh::lean_inc(v_v_3626_);
                        v___x_3628_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3628_, 0, v_v_3626_);
                        v_a_3623_ = v___x_3628_;
                        v_a_3624_ = v_p_3627_;
                        state = 0;
                        continue;
                    } else {
                        v_v_3630_ = crate::leanh::lean_ctor_get(v_a_3624_, 1);
                        v_p_3631_ = crate::leanh::lean_ctor_get(v_a_3624_, 2);
                        v_val_3632_ = crate::leanh::lean_ctor_get(v_a_3623_, 0);
                        v_isSharedCheck_3641_ = (!crate::leanh::lean_is_exclusive(v_a_3623_)) as u8;
                        if v_isSharedCheck_3641_ == 0 {
                            v___x_3634_ = v_a_3623_;
                            v_isShared_3635_ = v_isSharedCheck_3641_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_val_3632_);
                            crate::leanh::lean_dec(v_a_3623_);
                            v___x_3634_ = crate::leanh::lean_box(0);
                            v_isShared_3635_ = v_isSharedCheck_3641_;
                            state = 1;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v___x_3636_ = lean_nat_dec_lt(v_v_3630_, v_val_3632_);
                crate::leanh::lean_dec(v_val_3632_);
                if v___x_3636_ == 0 {
                    crate::leanh::lean_del_object(v___x_3634_);
                    return v___x_3636_;
                } else {
                    crate::leanh::lean_inc(v_v_3630_);
                    if v_isShared_3635_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_3634_, 0, v_v_3630_);
                        v___x_3638_ = v___x_3634_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_3640_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_3640_, 0, v_v_3630_);
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
    mut v_a_3642_: *mut crate::leanh::LeanObject,
    mut v_a_3643_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3644_: u8 = 0;
    let mut v_r_3645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3644_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
            v_a_3642_, v_a_3643_,
        );
    crate::leanh::lean_dec(v_a_3643_);
    v_r_3645_ = crate::leanh::lean_box((v_res_3644_) as usize);
    return v_r_3645_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(
    mut v_p_3646_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3647_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3648_: u8 = 0;
    v___x_3647_ = crate::leanh::lean_box(0);
    v___x_3648_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted_go(
            v___x_3647_,
            v_p_3646_,
        );
    return v___x_3648_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted___boxed(
    mut v_p_3649_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3650_: u8 = 0;
    let mut v_r_3651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3650_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(
            v_p_3649_,
        );
    crate::leanh::lean_dec(v_p_3649_);
    v_r_3651_ = crate::leanh::lean_box((v_res_3650_) as usize);
    return v_r_3651_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3652_ = crate::leanh::lean_unsigned_to_nat(0);
    v___x_3653_ = lean_nat_to_int(v___x_3652_);
    return v___x_3653_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(
    mut v_x_3654_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3655_: u8 = 0;
    let mut v_k_3656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3659_: u8 = 0;
    let mut v___x_3661_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_3654_) == 0 {
                    v___x_3655_ = 1;
                    return v___x_3655_;
                } else {
                    v_k_3656_ = crate::leanh::lean_ctor_get(v_x_3654_, 0);
                    v_p_3657_ = crate::leanh::lean_ctor_get(v_x_3654_, 2);
                    v___x_3658_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
    mut v_x_3662_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3663_: u8 = 0;
    let mut v_r_3664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3663_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(
            v_x_3662_,
        );
    crate::leanh::lean_dec(v_x_3662_);
    v_r_3664_ = crate::leanh::lean_box((v_res_3663_) as usize);
    return v_r_3664_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3665_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_3665_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(
    mut v_msg_3666_: *mut crate::leanh::LeanObject,
    mut v___y_3667_: *mut crate::leanh::LeanObject,
    mut v___y_3668_: *mut crate::leanh::LeanObject,
    mut v___y_3669_: *mut crate::leanh::LeanObject,
    mut v___y_3670_: *mut crate::leanh::LeanObject,
    mut v___y_3671_: *mut crate::leanh::LeanObject,
    mut v___y_3672_: *mut crate::leanh::LeanObject,
    mut v___y_3673_: *mut crate::leanh::LeanObject,
    mut v___y_3674_: *mut crate::leanh::LeanObject,
    mut v___y_3675_: *mut crate::leanh::LeanObject,
    mut v___y_3676_: *mut crate::leanh::LeanObject,
    mut v___y_3677_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_2201__overap_3681_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3679_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___closed__0);
    v___f_3680_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3680_, 0, v___x_3679_);
    v___x_2201__overap_3681_ = lean_panic_fn_borrowed(v___f_3680_, v_msg_3666_);
    crate::leanh::lean_dec_ref(v___f_3680_);
    crate::leanh::lean_inc(v___y_3677_);
    crate::leanh::lean_inc_ref(v___y_3676_);
    crate::leanh::lean_inc(v___y_3675_);
    crate::leanh::lean_inc_ref(v___y_3674_);
    crate::leanh::lean_inc(v___y_3673_);
    crate::leanh::lean_inc_ref(v___y_3672_);
    crate::leanh::lean_inc(v___y_3671_);
    crate::leanh::lean_inc_ref(v___y_3670_);
    crate::leanh::lean_inc(v___y_3669_);
    crate::leanh::lean_inc(v___y_3668_);
    crate::leanh::lean_inc(v___y_3667_);
    v___x_3682_ = crate::leanh::lean_apply_12(
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
        crate::leanh::lean_box(0),
    );
    return v___x_3682_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1___boxed(
    mut v_msg_3683_: *mut crate::leanh::LeanObject,
    mut v___y_3684_: *mut crate::leanh::LeanObject,
    mut v___y_3685_: *mut crate::leanh::LeanObject,
    mut v___y_3686_: *mut crate::leanh::LeanObject,
    mut v___y_3687_: *mut crate::leanh::LeanObject,
    mut v___y_3688_: *mut crate::leanh::LeanObject,
    mut v___y_3689_: *mut crate::leanh::LeanObject,
    mut v___y_3690_: *mut crate::leanh::LeanObject,
    mut v___y_3691_: *mut crate::leanh::LeanObject,
    mut v___y_3692_: *mut crate::leanh::LeanObject,
    mut v___y_3693_: *mut crate::leanh::LeanObject,
    mut v___y_3694_: *mut crate::leanh::LeanObject,
    mut v___y_3695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3696_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3696_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v_msg_3683_, v___y_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
    crate::leanh::lean_dec(v___y_3694_);
    crate::leanh::lean_dec_ref(v___y_3693_);
    crate::leanh::lean_dec(v___y_3692_);
    crate::leanh::lean_dec_ref(v___y_3691_);
    crate::leanh::lean_dec(v___y_3690_);
    crate::leanh::lean_dec_ref(v___y_3689_);
    crate::leanh::lean_dec(v___y_3688_);
    crate::leanh::lean_dec_ref(v___y_3687_);
    crate::leanh::lean_dec(v___y_3686_);
    crate::leanh::lean_dec(v___y_3685_);
    crate::leanh::lean_dec(v___y_3684_);
    return v_res_3696_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(
    mut v_k_3697_: *mut crate::leanh::LeanObject,
    mut v_t_3698_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v_k_3699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_l_3700_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_r_3701_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3702_: u8 = 0;
    let mut v___x_3703_: u8 = 0;
    let mut v___x_3706_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_t_3698_) == 0 {
                    v_k_3699_ = crate::leanh::lean_ctor_get(v_t_3698_, 1);
                    v_l_3700_ = crate::leanh::lean_ctor_get(v_t_3698_, 3);
                    v_r_3701_ = crate::leanh::lean_ctor_get(v_t_3698_, 4);
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
    mut v_k_3707_: *mut crate::leanh::LeanObject,
    mut v_t_3708_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3709_: u8 = 0;
    let mut v_r_3710_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3709_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_3707_, v_t_3708_);
    crate::leanh::lean_dec(v_t_3708_);
    crate::leanh::lean_dec(v_k_3707_);
    v_r_3710_ = crate::leanh::lean_box((v_res_3709_) as usize);
    return v_r_3710_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3714_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3715_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3714_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__2;
    v___x_3715_ = crate::leanh::lean_unsigned_to_nat(4);
    v___x_3716_ = crate::leanh::lean_unsigned_to_nat(32);
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
    mut v_y_3720_: *mut crate::leanh::LeanObject,
    mut v_p_3721_: *mut crate::leanh::LeanObject,
    mut v_a_3722_: *mut crate::leanh::LeanObject,
    mut v_a_3723_: *mut crate::leanh::LeanObject,
    mut v_a_3724_: *mut crate::leanh::LeanObject,
    mut v_a_3725_: *mut crate::leanh::LeanObject,
    mut v_a_3726_: *mut crate::leanh::LeanObject,
    mut v_a_3727_: *mut crate::leanh::LeanObject,
    mut v_a_3728_: *mut crate::leanh::LeanObject,
    mut v_a_3729_: *mut crate::leanh::LeanObject,
    mut v_a_3730_: *mut crate::leanh::LeanObject,
    mut v_a_3731_: *mut crate::leanh::LeanObject,
    mut v_a_3732_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_3734_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3736_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3737_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3738_: u8 = 0;
    let mut v___x_3739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3740_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3744_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3745_: u8 = 0;
    let mut v___x_3747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3748_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3749_: u8 = 0;
    let mut v___x_3750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3751_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_3721_) == 1 {
                    v_v_3734_ = crate::leanh::lean_ctor_get(v_p_3721_, 1);
                    v_p_3735_ = crate::leanh::lean_ctor_get(v_p_3721_, 2);
                    v___x_3736_ = l_Lean_Meta_Grind_Arith_Linear_getOccursOf(
                        v_v_3734_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_,
                        v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3736_) == 0 {
                        v_a_3737_ = crate::leanh::lean_ctor_get(v___x_3736_, 0);
                        crate::leanh::lean_inc(v_a_3737_);
                        crate::leanh::lean_dec_ref_known(v___x_3736_, 1);
                        v___x_3738_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_y_3720_, v_a_3737_);
                        crate::leanh::lean_dec(v_a_3737_);
                        if v___x_3738_ == 0 {
                            v___x_3739_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go___closed__3);
                            v___x_3740_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3739_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_, v_a_3728_, v_a_3729_, v_a_3730_, v_a_3731_, v_a_3732_);
                            return v___x_3740_;
                        } else {
                            v_p_3721_ = v_p_3735_;
                            state = 0;
                            continue;
                        }
                    } else {
                        v_a_3742_ = crate::leanh::lean_ctor_get(v___x_3736_, 0);
                        v_isSharedCheck_3749_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3736_)) as u8;
                        if v_isSharedCheck_3749_ == 0 {
                            v___x_3744_ = v___x_3736_;
                            v_isShared_3745_ = v_isSharedCheck_3749_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3742_);
                            crate::leanh::lean_dec(v___x_3736_);
                            v___x_3744_ = crate::leanh::lean_box(0);
                            v_isShared_3745_ = v_isSharedCheck_3749_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3750_ = crate::leanh::lean_box(0);
                    v___x_3751_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3751_, 0, v___x_3750_);
                    return v___x_3751_;
                }
            }
            1 => {
                if v_isShared_3745_ == 0 {
                    v___x_3747_ = v___x_3744_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3748_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3748_, 0, v_a_3742_);
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
    mut v_y_3752_: *mut crate::leanh::LeanObject,
    mut v_p_3753_: *mut crate::leanh::LeanObject,
    mut v_a_3754_: *mut crate::leanh::LeanObject,
    mut v_a_3755_: *mut crate::leanh::LeanObject,
    mut v_a_3756_: *mut crate::leanh::LeanObject,
    mut v_a_3757_: *mut crate::leanh::LeanObject,
    mut v_a_3758_: *mut crate::leanh::LeanObject,
    mut v_a_3759_: *mut crate::leanh::LeanObject,
    mut v_a_3760_: *mut crate::leanh::LeanObject,
    mut v_a_3761_: *mut crate::leanh::LeanObject,
    mut v_a_3762_: *mut crate::leanh::LeanObject,
    mut v_a_3763_: *mut crate::leanh::LeanObject,
    mut v_a_3764_: *mut crate::leanh::LeanObject,
    mut v_a_3765_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3766_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3766_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_y_3752_, v_p_3753_, v_a_3754_, v_a_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_, v_a_3760_, v_a_3761_, v_a_3762_, v_a_3763_, v_a_3764_);
    crate::leanh::lean_dec(v_a_3764_);
    crate::leanh::lean_dec_ref(v_a_3763_);
    crate::leanh::lean_dec(v_a_3762_);
    crate::leanh::lean_dec_ref(v_a_3761_);
    crate::leanh::lean_dec(v_a_3760_);
    crate::leanh::lean_dec_ref(v_a_3759_);
    crate::leanh::lean_dec(v_a_3758_);
    crate::leanh::lean_dec_ref(v_a_3757_);
    crate::leanh::lean_dec(v_a_3756_);
    crate::leanh::lean_dec(v_a_3755_);
    crate::leanh::lean_dec(v_a_3754_);
    crate::leanh::lean_dec(v_p_3753_);
    crate::leanh::lean_dec(v_y_3752_);
    return v_res_3766_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(
    mut v_00_u03b2_3767_: *mut crate::leanh::LeanObject,
    mut v_k_3768_: *mut crate::leanh::LeanObject,
    mut v_t_3769_: *mut crate::leanh::LeanObject,
) -> u8 {
    let mut v___x_3770_: u8 = 0;
    v___x_3770_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___redArg(v_k_3768_, v_t_3769_);
    return v___x_3770_;
}
pub unsafe fn l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0___boxed(
    mut v_00_u03b2_3771_: *mut crate::leanh::LeanObject,
    mut v_k_3772_: *mut crate::leanh::LeanObject,
    mut v_t_3773_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3774_: u8 = 0;
    let mut v_r_3775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3774_ = l_Std_DTreeMap_Internal_Impl_contains___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__0(v_00_u03b2_3771_, v_k_3772_, v_t_3773_);
    crate::leanh::lean_dec(v_t_3773_);
    crate::leanh::lean_dec(v_k_3772_);
    v_r_3775_ = crate::leanh::lean_box((v_res_3774_) as usize);
    return v_r_3775_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(
    mut v_p_3776_: *mut crate::leanh::LeanObject,
    mut v_a_3777_: *mut crate::leanh::LeanObject,
    mut v_a_3778_: *mut crate::leanh::LeanObject,
    mut v_a_3779_: *mut crate::leanh::LeanObject,
    mut v_a_3780_: *mut crate::leanh::LeanObject,
    mut v_a_3781_: *mut crate::leanh::LeanObject,
    mut v_a_3782_: *mut crate::leanh::LeanObject,
    mut v_a_3783_: *mut crate::leanh::LeanObject,
    mut v_a_3784_: *mut crate::leanh::LeanObject,
    mut v_a_3785_: *mut crate::leanh::LeanObject,
    mut v_a_3786_: *mut crate::leanh::LeanObject,
    mut v_a_3787_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    if crate::leanh::lean_obj_tag(v_p_3776_) == 1 {
        let mut v_v_3789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v_p_3790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v_v_3789_ = crate::leanh::lean_ctor_get(v_p_3776_, 1);
        v_p_3790_ = crate::leanh::lean_ctor_get(v_p_3776_, 2);
        v___x_3791_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go(v_v_3789_, v_p_3790_, v_a_3777_, v_a_3778_, v_a_3779_, v_a_3780_, v_a_3781_, v_a_3782_, v_a_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
        return v___x_3791_;
    } else {
        let mut v___x_3792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        let mut v___x_3793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        v___x_3792_ = crate::leanh::lean_box(0);
        v___x_3793_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
        crate::leanh::lean_ctor_set(v___x_3793_, 0, v___x_3792_);
        return v___x_3793_;
    }
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs___boxed(
    mut v_p_3794_: *mut crate::leanh::LeanObject,
    mut v_a_3795_: *mut crate::leanh::LeanObject,
    mut v_a_3796_: *mut crate::leanh::LeanObject,
    mut v_a_3797_: *mut crate::leanh::LeanObject,
    mut v_a_3798_: *mut crate::leanh::LeanObject,
    mut v_a_3799_: *mut crate::leanh::LeanObject,
    mut v_a_3800_: *mut crate::leanh::LeanObject,
    mut v_a_3801_: *mut crate::leanh::LeanObject,
    mut v_a_3802_: *mut crate::leanh::LeanObject,
    mut v_a_3803_: *mut crate::leanh::LeanObject,
    mut v_a_3804_: *mut crate::leanh::LeanObject,
    mut v_a_3805_: *mut crate::leanh::LeanObject,
    mut v_a_3806_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3807_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3807_ =
        l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(
            v_p_3794_, v_a_3795_, v_a_3796_, v_a_3797_, v_a_3798_, v_a_3799_, v_a_3800_, v_a_3801_,
            v_a_3802_, v_a_3803_, v_a_3804_, v_a_3805_,
        );
    crate::leanh::lean_dec(v_a_3805_);
    crate::leanh::lean_dec_ref(v_a_3804_);
    crate::leanh::lean_dec(v_a_3803_);
    crate::leanh::lean_dec_ref(v_a_3802_);
    crate::leanh::lean_dec(v_a_3801_);
    crate::leanh::lean_dec_ref(v_a_3800_);
    crate::leanh::lean_dec(v_a_3799_);
    crate::leanh::lean_dec_ref(v_a_3798_);
    crate::leanh::lean_dec(v_a_3797_);
    crate::leanh::lean_dec(v_a_3796_);
    crate::leanh::lean_dec(v_a_3795_);
    crate::leanh::lean_dec(v_p_3794_);
    return v_res_3807_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3810_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__1;
    v___x_3811_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3812_ = crate::leanh::lean_unsigned_to_nat(38);
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
    mut v_p_3816_: *mut crate::leanh::LeanObject,
    mut v_a_3817_: *mut crate::leanh::LeanObject,
    mut v_a_3818_: *mut crate::leanh::LeanObject,
    mut v_a_3819_: *mut crate::leanh::LeanObject,
    mut v_a_3820_: *mut crate::leanh::LeanObject,
    mut v_a_3821_: *mut crate::leanh::LeanObject,
    mut v_a_3822_: *mut crate::leanh::LeanObject,
    mut v_a_3823_: *mut crate::leanh::LeanObject,
    mut v_a_3824_: *mut crate::leanh::LeanObject,
    mut v_a_3825_: *mut crate::leanh::LeanObject,
    mut v_a_3826_: *mut crate::leanh::LeanObject,
    mut v_a_3827_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_v_3829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_3830_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3831_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3833_: u8 = 0;
    let mut v___x_3835_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3836_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3837_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3839_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3840_: u8 = 0;
    let mut v___x_3842_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3844_: u8 = 0;
    let mut v___x_3845_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_p_3816_) == 1 {
                    v_v_3829_ = crate::leanh::lean_ctor_get(v_p_3816_, 1);
                    v_p_3830_ = crate::leanh::lean_ctor_get(v_p_3816_, 2);
                    v___x_3831_ = l_Lean_Meta_Grind_Arith_Linear_eliminated(
                        v_v_3829_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_,
                        v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_,
                    );
                    if crate::leanh::lean_obj_tag(v___x_3831_) == 0 {
                        v_a_3832_ = crate::leanh::lean_ctor_get(v___x_3831_, 0);
                        crate::leanh::lean_inc(v_a_3832_);
                        crate::leanh::lean_dec_ref_known(v___x_3831_, 1);
                        v___x_3833_ = (crate::leanh::lean_unbox(v_a_3832_) as u8);
                        crate::leanh::lean_dec(v_a_3832_);
                        if v___x_3833_ == 0 {
                            v_p_3816_ = v_p_3830_;
                            state = 0;
                            continue;
                        } else {
                            v___x_3835_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars___closed__2);
                            v___x_3836_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3835_, v_a_3817_, v_a_3818_, v_a_3819_, v_a_3820_, v_a_3821_, v_a_3822_, v_a_3823_, v_a_3824_, v_a_3825_, v_a_3826_, v_a_3827_);
                            return v___x_3836_;
                        }
                    } else {
                        v_a_3837_ = crate::leanh::lean_ctor_get(v___x_3831_, 0);
                        v_isSharedCheck_3844_ =
                            (!crate::leanh::lean_is_exclusive(v___x_3831_)) as u8;
                        if v_isSharedCheck_3844_ == 0 {
                            v___x_3839_ = v___x_3831_;
                            v_isShared_3840_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_3837_);
                            crate::leanh::lean_dec(v___x_3831_);
                            v___x_3839_ = crate::leanh::lean_box(0);
                            v_isShared_3840_ = v_isSharedCheck_3844_;
                            state = 1;
                            continue;
                        }
                    }
                } else {
                    v___x_3845_ = crate::leanh::lean_box(0);
                    v___x_3846_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_3846_, 0, v___x_3845_);
                    return v___x_3846_;
                }
            }
            1 => {
                if v_isShared_3840_ == 0 {
                    v___x_3842_ = v___x_3839_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_3843_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3843_, 0, v_a_3837_);
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
    mut v_p_3847_: *mut crate::leanh::LeanObject,
    mut v_a_3848_: *mut crate::leanh::LeanObject,
    mut v_a_3849_: *mut crate::leanh::LeanObject,
    mut v_a_3850_: *mut crate::leanh::LeanObject,
    mut v_a_3851_: *mut crate::leanh::LeanObject,
    mut v_a_3852_: *mut crate::leanh::LeanObject,
    mut v_a_3853_: *mut crate::leanh::LeanObject,
    mut v_a_3854_: *mut crate::leanh::LeanObject,
    mut v_a_3855_: *mut crate::leanh::LeanObject,
    mut v_a_3856_: *mut crate::leanh::LeanObject,
    mut v_a_3857_: *mut crate::leanh::LeanObject,
    mut v_a_3858_: *mut crate::leanh::LeanObject,
    mut v_a_3859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3860_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_3847_, v_a_3848_, v_a_3849_, v_a_3850_, v_a_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_, v_a_3856_, v_a_3857_, v_a_3858_);
    crate::leanh::lean_dec(v_a_3858_);
    crate::leanh::lean_dec_ref(v_a_3857_);
    crate::leanh::lean_dec(v_a_3856_);
    crate::leanh::lean_dec_ref(v_a_3855_);
    crate::leanh::lean_dec(v_a_3854_);
    crate::leanh::lean_dec_ref(v_a_3853_);
    crate::leanh::lean_dec(v_a_3852_);
    crate::leanh::lean_dec_ref(v_a_3851_);
    crate::leanh::lean_dec(v_a_3850_);
    crate::leanh::lean_dec(v_a_3849_);
    crate::leanh::lean_dec(v_a_3848_);
    crate::leanh::lean_dec(v_p_3847_);
    return v_res_3860_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3863_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3868_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3863_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__1;
    v___x_3864_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3865_ = crate::leanh::lean_unsigned_to_nat(49);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3870_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3871_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3874_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3870_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_3871_ = crate::leanh::lean_unsigned_to_nat(24);
    v___x_3872_ = crate::leanh::lean_unsigned_to_nat(48);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3878_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3882_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3877_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__5;
    v___x_3878_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3879_ = crate::leanh::lean_unsigned_to_nat(42);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3884_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3888_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3884_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__7;
    v___x_3885_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_3886_ = crate::leanh::lean_unsigned_to_nat(43);
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
    mut v_p_3890_: *mut crate::leanh::LeanObject,
    mut v_x_3891_: *mut crate::leanh::LeanObject,
    mut v_a_3892_: *mut crate::leanh::LeanObject,
    mut v_a_3893_: *mut crate::leanh::LeanObject,
    mut v_a_3894_: *mut crate::leanh::LeanObject,
    mut v_a_3895_: *mut crate::leanh::LeanObject,
    mut v_a_3896_: *mut crate::leanh::LeanObject,
    mut v_a_3897_: *mut crate::leanh::LeanObject,
    mut v_a_3898_: *mut crate::leanh::LeanObject,
    mut v_a_3899_: *mut crate::leanh::LeanObject,
    mut v_a_3900_: *mut crate::leanh::LeanObject,
    mut v_a_3901_: *mut crate::leanh::LeanObject,
    mut v_a_3902_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___y_3905_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3906_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3907_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3908_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3909_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3910_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3912_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_3915_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_3916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3917_: u8 = 0;
    let mut v___x_3918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3924_: u8 = 0;
    let mut v___x_3925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3927_: u8 = 0;
    let mut v___x_3928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3931_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3932_: u8 = 0;
    let mut v___x_3933_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_3935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3937_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_3938_: u8 = 0;
    let mut v___x_3940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_3941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_3942_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_3924_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_isSorted(v_p_3890_);
                if v___x_3924_ == 0 {
                    v___x_3925_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__6);
                    v___x_3926_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3925_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                    return v___x_3926_;
                } else {
                    v___x_3927_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs(v_p_3890_);
                    if v___x_3927_ == 0 {
                        v___x_3928_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__8);
                        v___x_3929_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3928_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                        return v___x_3929_;
                    } else {
                        v___x_3930_ = l_Lean_Meta_Grind_Arith_Linear_inconsistent(
                            v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_,
                            v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_,
                        );
                        if crate::leanh::lean_obj_tag(v___x_3930_) == 0 {
                            v_a_3931_ = crate::leanh::lean_ctor_get(v___x_3930_, 0);
                            crate::leanh::lean_inc(v_a_3931_);
                            crate::leanh::lean_dec_ref_known(v___x_3930_, 1);
                            v___x_3932_ = (crate::leanh::lean_unbox(v_a_3931_) as u8);
                            crate::leanh::lean_dec(v_a_3931_);
                            if v___x_3932_ == 0 {
                                v___x_3933_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkNoElimVars(v_p_3890_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                                if crate::leanh::lean_obj_tag(v___x_3933_) == 0 {
                                    crate::leanh::lean_dec_ref_known(v___x_3933_, 1);
                                    v___x_3934_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs(v_p_3890_, v_a_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_, v_a_3897_, v_a_3898_, v_a_3899_, v_a_3900_, v_a_3901_, v_a_3902_);
                                    if crate::leanh::lean_obj_tag(v___x_3934_) == 0 {
                                        crate::leanh::lean_dec_ref_known(v___x_3934_, 1);
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
                            v_a_3935_ = crate::leanh::lean_ctor_get(v___x_3930_, 0);
                            v_isSharedCheck_3942_ =
                                (!crate::leanh::lean_is_exclusive(v___x_3930_)) as u8;
                            if v_isSharedCheck_3942_ == 0 {
                                v___x_3937_ = v___x_3930_;
                                v_isShared_3938_ = v_isSharedCheck_3942_;
                                state = 2;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_3935_);
                                crate::leanh::lean_dec(v___x_3930_);
                                v___x_3937_ = crate::leanh::lean_box(0);
                                v_isShared_3938_ = v_isSharedCheck_3942_;
                                state = 2;
                                continue;
                            }
                        }
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_p_3890_) == 1 {
                    v_v_3916_ = crate::leanh::lean_ctor_get(v_p_3890_, 1);
                    v___x_3917_ = lean_nat_dec_eq(v_x_3891_, v_v_3916_);
                    if v___x_3917_ == 0 {
                        v___x_3918_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__2);
                        v___x_3919_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_3918_, v___y_3905_, v___y_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_, v___y_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_);
                        return v___x_3919_;
                    } else {
                        v___x_3920_ = crate::leanh::lean_box(0);
                        v___x_3921_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v___x_3921_, 0, v___x_3920_);
                        return v___x_3921_;
                    }
                } else {
                    v___x_3922_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__4);
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
                    v_reuseFailAlloc_3941_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_3941_, 0, v_a_3935_);
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
    mut v_p_3943_: *mut crate::leanh::LeanObject,
    mut v_x_3944_: *mut crate::leanh::LeanObject,
    mut v_a_3945_: *mut crate::leanh::LeanObject,
    mut v_a_3946_: *mut crate::leanh::LeanObject,
    mut v_a_3947_: *mut crate::leanh::LeanObject,
    mut v_a_3948_: *mut crate::leanh::LeanObject,
    mut v_a_3949_: *mut crate::leanh::LeanObject,
    mut v_a_3950_: *mut crate::leanh::LeanObject,
    mut v_a_3951_: *mut crate::leanh::LeanObject,
    mut v_a_3952_: *mut crate::leanh::LeanObject,
    mut v_a_3953_: *mut crate::leanh::LeanObject,
    mut v_a_3954_: *mut crate::leanh::LeanObject,
    mut v_a_3955_: *mut crate::leanh::LeanObject,
    mut v_a_3956_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3957_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3957_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_3943_, v_x_3944_, v_a_3945_, v_a_3946_, v_a_3947_, v_a_3948_, v_a_3949_, v_a_3950_, v_a_3951_, v_a_3952_, v_a_3953_, v_a_3954_, v_a_3955_);
    crate::leanh::lean_dec(v_a_3955_);
    crate::leanh::lean_dec_ref(v_a_3954_);
    crate::leanh::lean_dec(v_a_3953_);
    crate::leanh::lean_dec_ref(v_a_3952_);
    crate::leanh::lean_dec(v_a_3951_);
    crate::leanh::lean_dec_ref(v_a_3950_);
    crate::leanh::lean_dec(v_a_3949_);
    crate::leanh::lean_dec_ref(v_a_3948_);
    crate::leanh::lean_dec(v_a_3947_);
    crate::leanh::lean_dec(v_a_3946_);
    crate::leanh::lean_dec(v_a_3945_);
    crate::leanh::lean_dec(v_x_3944_);
    crate::leanh::lean_dec(v_p_3943_);
    return v_res_3957_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3958_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_3958_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(
    mut v_msg_3959_: *mut crate::leanh::LeanObject,
    mut v___y_3960_: *mut crate::leanh::LeanObject,
    mut v___y_3961_: *mut crate::leanh::LeanObject,
    mut v___y_3962_: *mut crate::leanh::LeanObject,
    mut v___y_3963_: *mut crate::leanh::LeanObject,
    mut v___y_3964_: *mut crate::leanh::LeanObject,
    mut v___y_3965_: *mut crate::leanh::LeanObject,
    mut v___y_3966_: *mut crate::leanh::LeanObject,
    mut v___y_3967_: *mut crate::leanh::LeanObject,
    mut v___y_3968_: *mut crate::leanh::LeanObject,
    mut v___y_3969_: *mut crate::leanh::LeanObject,
    mut v___y_3970_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_3972_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_3973_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4606__overap_3974_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3975_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3972_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___closed__0);
    v___f_3973_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_3973_, 0, v___x_3972_);
    v___x_4606__overap_3974_ = lean_panic_fn_borrowed(v___f_3973_, v_msg_3959_);
    crate::leanh::lean_dec_ref(v___f_3973_);
    crate::leanh::lean_inc(v___y_3970_);
    crate::leanh::lean_inc_ref(v___y_3969_);
    crate::leanh::lean_inc(v___y_3968_);
    crate::leanh::lean_inc_ref(v___y_3967_);
    crate::leanh::lean_inc(v___y_3966_);
    crate::leanh::lean_inc_ref(v___y_3965_);
    crate::leanh::lean_inc(v___y_3964_);
    crate::leanh::lean_inc_ref(v___y_3963_);
    crate::leanh::lean_inc(v___y_3962_);
    crate::leanh::lean_inc(v___y_3961_);
    crate::leanh::lean_inc(v___y_3960_);
    v___x_3975_ = crate::leanh::lean_apply_12(
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
        crate::leanh::lean_box(0),
    );
    return v___x_3975_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0___boxed(
    mut v_msg_3976_: *mut crate::leanh::LeanObject,
    mut v___y_3977_: *mut crate::leanh::LeanObject,
    mut v___y_3978_: *mut crate::leanh::LeanObject,
    mut v___y_3979_: *mut crate::leanh::LeanObject,
    mut v___y_3980_: *mut crate::leanh::LeanObject,
    mut v___y_3981_: *mut crate::leanh::LeanObject,
    mut v___y_3982_: *mut crate::leanh::LeanObject,
    mut v___y_3983_: *mut crate::leanh::LeanObject,
    mut v___y_3984_: *mut crate::leanh::LeanObject,
    mut v___y_3985_: *mut crate::leanh::LeanObject,
    mut v___y_3986_: *mut crate::leanh::LeanObject,
    mut v___y_3987_: *mut crate::leanh::LeanObject,
    mut v___y_3988_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_3989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_3989_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v_msg_3976_, v___y_3977_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_, v___y_3985_, v___y_3986_, v___y_3987_);
    crate::leanh::lean_dec(v___y_3987_);
    crate::leanh::lean_dec_ref(v___y_3986_);
    crate::leanh::lean_dec(v___y_3985_);
    crate::leanh::lean_dec_ref(v___y_3984_);
    crate::leanh::lean_dec(v___y_3983_);
    crate::leanh::lean_dec_ref(v___y_3982_);
    crate::leanh::lean_dec(v___y_3981_);
    crate::leanh::lean_dec_ref(v___y_3980_);
    crate::leanh::lean_dec(v___y_3979_);
    crate::leanh::lean_dec(v___y_3978_);
    crate::leanh::lean_dec(v___y_3977_);
    return v_res_3989_;
}
pub unsafe fn _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_3992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3994_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3996_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3997_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3992_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__1;
    v___x_3993_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_3994_ = crate::leanh::lean_unsigned_to_nat(57);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_3998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_3999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4000_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4001_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4003_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_3998_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_3999_ = crate::leanh::lean_unsigned_to_nat(30);
    v___x_4000_ = crate::leanh::lean_unsigned_to_nat(56);
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
    mut v_____s_4004_: *mut crate::leanh::LeanObject,
    mut v_isLower_4005_: u8,
    mut v_as_4006_: *mut crate::leanh::LeanObject,
    mut v_sz_4007_: usize,
    mut v_i_4008_: usize,
    mut v_b_4009_: *mut crate::leanh::LeanObject,
    mut v___y_4010_: *mut crate::leanh::LeanObject,
    mut v___y_4011_: *mut crate::leanh::LeanObject,
    mut v___y_4012_: *mut crate::leanh::LeanObject,
    mut v___y_4013_: *mut crate::leanh::LeanObject,
    mut v___y_4014_: *mut crate::leanh::LeanObject,
    mut v___y_4015_: *mut crate::leanh::LeanObject,
    mut v___y_4016_: *mut crate::leanh::LeanObject,
    mut v___y_4017_: *mut crate::leanh::LeanObject,
    mut v___y_4018_: *mut crate::leanh::LeanObject,
    mut v___y_4019_: *mut crate::leanh::LeanObject,
    mut v___y_4020_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4022_: u8 = 0;
    let mut v___x_4023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4027_: u8 = 0;
    let mut v_a_4028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4029_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4031_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4033_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4036_: usize = 0;
    let mut v___x_4037_: usize = 0;
    let mut v_reuseFailAlloc_4039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4043_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4046_: u8 = 0;
    let mut v___x_4047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4050_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4052_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4053_: u8 = 0;
    let mut v_a_4054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4057_: u8 = 0;
    let mut v___x_4059_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4060_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4061_: u8 = 0;
    let mut v___x_4062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4064_: u8 = 0;
    let mut v_k_4065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4066_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4067_: u8 = 0;
    let mut v___x_4068_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4069_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4070_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4072_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4073_: u8 = 0;
    let mut v___x_4075_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4076_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4077_: u8 = 0;
    let mut v_a_4078_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4080_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4081_: u8 = 0;
    let mut v___x_4083_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4085_: u8 = 0;
    let mut v_isSharedCheck_4086_: u8 = 0;
    let mut v_unused_4087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4022_ = lean_usize_dec_lt(v_i_4008_, v_sz_4007_);
                if v___x_4022_ == 0 {
                    v___x_4023_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4023_, 0, v_b_4009_);
                    return v___x_4023_;
                } else {
                    v_snd_4024_ = crate::leanh::lean_ctor_get(v_b_4009_, 1);
                    v_isSharedCheck_4086_ = (!crate::leanh::lean_is_exclusive(v_b_4009_)) as u8;
                    if v_isSharedCheck_4086_ == 0 {
                        v_unused_4087_ = crate::leanh::lean_ctor_get(v_b_4009_, 0);
                        crate::leanh::lean_dec(v_unused_4087_);
                        v___x_4026_ = v_b_4009_;
                        v_isShared_4027_ = v_isSharedCheck_4086_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4024_);
                        crate::leanh::lean_dec(v_b_4009_);
                        v___x_4026_ = crate::leanh::lean_box(0);
                        v_isShared_4027_ = v_isSharedCheck_4086_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4028_ = lean_array_uget_borrowed(v_as_4006_, v_i_4008_);
                v_p_4029_ = crate::leanh::lean_ctor_get(v_a_4028_, 0);
                v___x_4030_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4029_, v_____s_4004_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                if crate::leanh::lean_obj_tag(v___x_4030_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4030_, 1);
                    v___x_4031_ = crate::leanh::lean_box(0);
                    v___x_4062_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_p_4029_) == 1 {
                        v_k_4065_ = crate::leanh::lean_ctor_get(v_p_4029_, 0);
                        v___x_4066_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        crate::leanh::lean_dec(v_snd_4024_);
                        v___x_4068_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4069_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4068_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                        if crate::leanh::lean_obj_tag(v___x_4069_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4069_, 1);
                            v_a_4033_ = v___x_4062_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_4026_);
                            v_a_4070_ = crate::leanh::lean_ctor_get(v___x_4069_, 0);
                            v_isSharedCheck_4077_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4069_)) as u8;
                            if v_isSharedCheck_4077_ == 0 {
                                v___x_4072_ = v___x_4069_;
                                v_isShared_4073_ = v_isSharedCheck_4077_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4070_);
                                crate::leanh::lean_dec(v___x_4069_);
                                v___x_4072_ = crate::leanh::lean_box(0);
                                v_isShared_4073_ = v_isSharedCheck_4077_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4026_);
                    crate::leanh::lean_dec(v_snd_4024_);
                    v_a_4078_ = crate::leanh::lean_ctor_get(v___x_4030_, 0);
                    v_isSharedCheck_4085_ = (!crate::leanh::lean_is_exclusive(v___x_4030_)) as u8;
                    if v_isSharedCheck_4085_ == 0 {
                        v___x_4080_ = v___x_4030_;
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4078_);
                        crate::leanh::lean_dec(v___x_4030_);
                        v___x_4080_ = crate::leanh::lean_box(0);
                        v_isShared_4081_ = v_isSharedCheck_4085_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4027_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4026_, 1, v_a_4033_);
                    crate::leanh::lean_ctor_set(v___x_4026_, 0, v___x_4031_);
                    v___x_4035_ = v___x_4026_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4039_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 0, v___x_4031_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4039_, 1, v_a_4033_);
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
                v___x_4041_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4042_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4041_, v___y_4010_, v___y_4011_, v___y_4012_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
                if crate::leanh::lean_obj_tag(v___x_4042_) == 0 {
                    v_a_4043_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
                    v_isSharedCheck_4053_ = (!crate::leanh::lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4053_ == 0 {
                        v___x_4045_ = v___x_4042_;
                        v_isShared_4046_ = v_isSharedCheck_4053_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4043_);
                        crate::leanh::lean_dec(v___x_4042_);
                        v___x_4045_ = crate::leanh::lean_box(0);
                        v_isShared_4046_ = v_isSharedCheck_4053_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4026_);
                    crate::leanh::lean_dec(v_snd_4024_);
                    v_a_4054_ = crate::leanh::lean_ctor_get(v___x_4042_, 0);
                    v_isSharedCheck_4061_ = (!crate::leanh::lean_is_exclusive(v___x_4042_)) as u8;
                    if v_isSharedCheck_4061_ == 0 {
                        v___x_4056_ = v___x_4042_;
                        v_isShared_4057_ = v_isSharedCheck_4061_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4054_);
                        crate::leanh::lean_dec(v___x_4042_);
                        v___x_4056_ = crate::leanh::lean_box(0);
                        v_isShared_4057_ = v_isSharedCheck_4061_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4043_) == 0 {
                    crate::leanh::lean_del_object(v___x_4026_);
                    v___x_4047_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4047_, 0, v_a_4043_);
                    v___x_4048_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4048_, 0, v___x_4047_);
                    crate::leanh::lean_ctor_set(v___x_4048_, 1, v_snd_4024_);
                    if v_isShared_4046_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4045_, 0, v___x_4048_);
                        v___x_4050_ = v___x_4045_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4051_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4051_, 0, v___x_4048_);
                        v___x_4050_ = v_reuseFailAlloc_4051_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4045_);
                    crate::leanh::lean_dec(v_snd_4024_);
                    v_a_4052_ = crate::leanh::lean_ctor_get(v_a_4043_, 0);
                    crate::leanh::lean_inc(v_a_4052_);
                    crate::leanh::lean_dec_ref_known(v_a_4043_, 1);
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
                    v_reuseFailAlloc_4060_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4060_, 0, v_a_4054_);
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
                    crate::leanh::lean_dec(v_snd_4024_);
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
                    v_reuseFailAlloc_4076_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4076_, 0, v_a_4070_);
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
                    v_reuseFailAlloc_4084_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4084_, 0, v_a_4078_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_4088_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4089_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_4090_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_4091_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_4092_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_4093_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4094_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4095_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4096_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4097_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4098_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4099_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4100_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4101_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4102_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4103_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4104_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4105_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4106_: u8 = 0;
    let mut v_sz_boxed_4107_: usize = 0;
    let mut v_i_boxed_4108_: usize = 0;
    let mut v_res_4109_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4106_ = (crate::leanh::lean_unbox(v_isLower_4089_) as u8);
    v_sz_boxed_4107_ = crate::leanh::lean_unbox_usize(v_sz_4091_);
    crate::leanh::lean_dec(v_sz_4091_);
    v_i_boxed_4108_ = crate::leanh::lean_unbox_usize(v_i_4092_);
    crate::leanh::lean_dec(v_i_4092_);
    v_res_4109_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5(v_____s_4088_, v_isLower_boxed_4106_, v_as_4090_, v_sz_boxed_4107_, v_i_boxed_4108_, v_b_4093_, v___y_4094_, v___y_4095_, v___y_4096_, v___y_4097_, v___y_4098_, v___y_4099_, v___y_4100_, v___y_4101_, v___y_4102_, v___y_4103_, v___y_4104_);
    crate::leanh::lean_dec(v___y_4104_);
    crate::leanh::lean_dec_ref(v___y_4103_);
    crate::leanh::lean_dec(v___y_4102_);
    crate::leanh::lean_dec_ref(v___y_4101_);
    crate::leanh::lean_dec(v___y_4100_);
    crate::leanh::lean_dec_ref(v___y_4099_);
    crate::leanh::lean_dec(v___y_4098_);
    crate::leanh::lean_dec_ref(v___y_4097_);
    crate::leanh::lean_dec(v___y_4096_);
    crate::leanh::lean_dec(v___y_4095_);
    crate::leanh::lean_dec(v___y_4094_);
    crate::leanh::lean_dec_ref(v_as_4090_);
    crate::leanh::lean_dec(v_____s_4088_);
    return v_res_4109_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(
    mut v_____s_4110_: *mut crate::leanh::LeanObject,
    mut v_isLower_4111_: u8,
    mut v_as_4112_: *mut crate::leanh::LeanObject,
    mut v_sz_4113_: usize,
    mut v_i_4114_: usize,
    mut v_b_4115_: *mut crate::leanh::LeanObject,
    mut v___y_4116_: *mut crate::leanh::LeanObject,
    mut v___y_4117_: *mut crate::leanh::LeanObject,
    mut v___y_4118_: *mut crate::leanh::LeanObject,
    mut v___y_4119_: *mut crate::leanh::LeanObject,
    mut v___y_4120_: *mut crate::leanh::LeanObject,
    mut v___y_4121_: *mut crate::leanh::LeanObject,
    mut v___y_4122_: *mut crate::leanh::LeanObject,
    mut v___y_4123_: *mut crate::leanh::LeanObject,
    mut v___y_4124_: *mut crate::leanh::LeanObject,
    mut v___y_4125_: *mut crate::leanh::LeanObject,
    mut v___y_4126_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4128_: u8 = 0;
    let mut v___x_4129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4132_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4133_: u8 = 0;
    let mut v_a_4134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4136_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4143_: usize = 0;
    let mut v___x_4144_: usize = 0;
    let mut v___x_4145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4146_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4153_: u8 = 0;
    let mut v___x_4154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4160_: u8 = 0;
    let mut v_a_4161_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4164_: u8 = 0;
    let mut v___x_4166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4167_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4168_: u8 = 0;
    let mut v___y_4170_: u8 = 0;
    let mut v_k_4171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4173_: u8 = 0;
    let mut v___x_4174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    let mut v_isSharedCheck_4192_: u8 = 0;
    let mut v_unused_4193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4128_ = lean_usize_dec_lt(v_i_4114_, v_sz_4113_);
                if v___x_4128_ == 0 {
                    v___x_4129_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4129_, 0, v_b_4115_);
                    return v___x_4129_;
                } else {
                    v_snd_4130_ = crate::leanh::lean_ctor_get(v_b_4115_, 1);
                    v_isSharedCheck_4192_ = (!crate::leanh::lean_is_exclusive(v_b_4115_)) as u8;
                    if v_isSharedCheck_4192_ == 0 {
                        v_unused_4193_ = crate::leanh::lean_ctor_get(v_b_4115_, 0);
                        crate::leanh::lean_dec(v_unused_4193_);
                        v___x_4132_ = v_b_4115_;
                        v_isShared_4133_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4130_);
                        crate::leanh::lean_dec(v_b_4115_);
                        v___x_4132_ = crate::leanh::lean_box(0);
                        v_isShared_4133_ = v_isSharedCheck_4192_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4134_ = lean_array_uget_borrowed(v_as_4112_, v_i_4114_);
                v_p_4135_ = crate::leanh::lean_ctor_get(v_a_4134_, 0);
                v___x_4136_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4135_, v_____s_4110_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                if crate::leanh::lean_obj_tag(v___x_4136_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4136_, 1);
                    v___x_4137_ = crate::leanh::lean_box(0);
                    v___x_4138_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_p_4135_) == 1 {
                        v_k_4171_ = crate::leanh::lean_ctor_get(v_p_4135_, 0);
                        v___x_4172_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        crate::leanh::lean_dec(v_snd_4130_);
                        v___x_4174_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4175_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4174_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                        if crate::leanh::lean_obj_tag(v___x_4175_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4175_, 1);
                            v_a_4140_ = v___x_4137_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_4132_);
                            v_a_4176_ = crate::leanh::lean_ctor_get(v___x_4175_, 0);
                            v_isSharedCheck_4183_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4175_)) as u8;
                            if v_isSharedCheck_4183_ == 0 {
                                v___x_4178_ = v___x_4175_;
                                v_isShared_4179_ = v_isSharedCheck_4183_;
                                state = 10;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4176_);
                                crate::leanh::lean_dec(v___x_4175_);
                                v___x_4178_ = crate::leanh::lean_box(0);
                                v_isShared_4179_ = v_isSharedCheck_4183_;
                                state = 10;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4132_);
                    crate::leanh::lean_dec(v_snd_4130_);
                    v_a_4184_ = crate::leanh::lean_ctor_get(v___x_4136_, 0);
                    v_isSharedCheck_4191_ = (!crate::leanh::lean_is_exclusive(v___x_4136_)) as u8;
                    if v_isSharedCheck_4191_ == 0 {
                        v___x_4186_ = v___x_4136_;
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 12;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4184_);
                        crate::leanh::lean_dec(v___x_4136_);
                        v___x_4186_ = crate::leanh::lean_box(0);
                        v_isShared_4187_ = v_isSharedCheck_4191_;
                        state = 12;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4133_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4132_, 1, v_a_4140_);
                    crate::leanh::lean_ctor_set(v___x_4132_, 0, v___x_4138_);
                    v___x_4142_ = v___x_4132_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4146_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4138_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4146_, 1, v_a_4140_);
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
                v___x_4148_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4149_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4148_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_, v___y_4120_, v___y_4121_, v___y_4122_, v___y_4123_, v___y_4124_, v___y_4125_, v___y_4126_);
                if crate::leanh::lean_obj_tag(v___x_4149_) == 0 {
                    v_a_4150_ = crate::leanh::lean_ctor_get(v___x_4149_, 0);
                    v_isSharedCheck_4160_ = (!crate::leanh::lean_is_exclusive(v___x_4149_)) as u8;
                    if v_isSharedCheck_4160_ == 0 {
                        v___x_4152_ = v___x_4149_;
                        v_isShared_4153_ = v_isSharedCheck_4160_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4150_);
                        crate::leanh::lean_dec(v___x_4149_);
                        v___x_4152_ = crate::leanh::lean_box(0);
                        v_isShared_4153_ = v_isSharedCheck_4160_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4132_);
                    crate::leanh::lean_dec(v_snd_4130_);
                    v_a_4161_ = crate::leanh::lean_ctor_get(v___x_4149_, 0);
                    v_isSharedCheck_4168_ = (!crate::leanh::lean_is_exclusive(v___x_4149_)) as u8;
                    if v_isSharedCheck_4168_ == 0 {
                        v___x_4163_ = v___x_4149_;
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 7;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4161_);
                        crate::leanh::lean_dec(v___x_4149_);
                        v___x_4163_ = crate::leanh::lean_box(0);
                        v_isShared_4164_ = v_isSharedCheck_4168_;
                        state = 7;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4150_) == 0 {
                    crate::leanh::lean_del_object(v___x_4132_);
                    v___x_4154_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4154_, 0, v_a_4150_);
                    v___x_4155_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4155_, 0, v___x_4154_);
                    crate::leanh::lean_ctor_set(v___x_4155_, 1, v_snd_4130_);
                    if v_isShared_4153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4152_, 0, v___x_4155_);
                        v___x_4157_ = v___x_4152_;
                        state = 6;
                        continue;
                    } else {
                        v_reuseFailAlloc_4158_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4158_, 0, v___x_4155_);
                        v___x_4157_ = v_reuseFailAlloc_4158_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4152_);
                    crate::leanh::lean_dec(v_snd_4130_);
                    v_a_4159_ = crate::leanh::lean_ctor_get(v_a_4150_, 0);
                    crate::leanh::lean_inc(v_a_4159_);
                    crate::leanh::lean_dec_ref_known(v_a_4150_, 1);
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
                    v_reuseFailAlloc_4167_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4167_, 0, v_a_4161_);
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
                    crate::leanh::lean_dec(v_snd_4130_);
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
                    v_reuseFailAlloc_4182_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4182_, 0, v_a_4176_);
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
                    v_reuseFailAlloc_4190_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4190_, 0, v_a_4184_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_4194_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4195_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_4196_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_4197_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_4198_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_4199_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4200_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4201_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4202_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4203_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4204_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4205_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4206_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4207_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4208_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4209_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4210_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4211_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4212_: u8 = 0;
    let mut v_sz_boxed_4213_: usize = 0;
    let mut v_i_boxed_4214_: usize = 0;
    let mut v_res_4215_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4212_ = (crate::leanh::lean_unbox(v_isLower_4195_) as u8);
    v_sz_boxed_4213_ = crate::leanh::lean_unbox_usize(v_sz_4197_);
    crate::leanh::lean_dec(v_sz_4197_);
    v_i_boxed_4214_ = crate::leanh::lean_unbox_usize(v_i_4198_);
    crate::leanh::lean_dec(v_i_4198_);
    v_res_4215_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_4194_, v_isLower_boxed_4212_, v_as_4196_, v_sz_boxed_4213_, v_i_boxed_4214_, v_b_4199_, v___y_4200_, v___y_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
    crate::leanh::lean_dec(v___y_4210_);
    crate::leanh::lean_dec_ref(v___y_4209_);
    crate::leanh::lean_dec(v___y_4208_);
    crate::leanh::lean_dec_ref(v___y_4207_);
    crate::leanh::lean_dec(v___y_4206_);
    crate::leanh::lean_dec_ref(v___y_4205_);
    crate::leanh::lean_dec(v___y_4204_);
    crate::leanh::lean_dec_ref(v___y_4203_);
    crate::leanh::lean_dec(v___y_4202_);
    crate::leanh::lean_dec(v___y_4201_);
    crate::leanh::lean_dec(v___y_4200_);
    crate::leanh::lean_dec_ref(v_as_4196_);
    crate::leanh::lean_dec(v_____s_4194_);
    return v_res_4215_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(
    mut v_init_4216_: *mut crate::leanh::LeanObject,
    mut v_____s_4217_: *mut crate::leanh::LeanObject,
    mut v_isLower_4218_: u8,
    mut v_n_4219_: *mut crate::leanh::LeanObject,
    mut v_b_4220_: *mut crate::leanh::LeanObject,
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
    let mut v_cs_4233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4235_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4236_: usize = 0;
    let mut v___x_4237_: usize = 0;
    let mut v___x_4238_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4241_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4242_: u8 = 0;
    let mut v_fst_4243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4245_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4247_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4249_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4251_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4252_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4253_: u8 = 0;
    let mut v_a_4254_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4256_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4257_: u8 = 0;
    let mut v___x_4259_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4261_: u8 = 0;
    let mut v_vs_4262_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4265_: usize = 0;
    let mut v___x_4266_: usize = 0;
    let mut v___x_4267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4271_: u8 = 0;
    let mut v_fst_4272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4277_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4278_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4282_: u8 = 0;
    let mut v_a_4283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4286_: u8 = 0;
    let mut v___x_4288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4290_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_4219_) == 0 {
                    v_cs_4233_ = crate::leanh::lean_ctor_get(v_n_4219_, 0);
                    v___x_4234_ = crate::leanh::lean_box(0);
                    v___x_4235_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4235_, 0, v___x_4234_);
                    crate::leanh::lean_ctor_set(v___x_4235_, 1, v_b_4220_);
                    v_sz_4236_ = lean_array_size(v_cs_4233_);
                    v___x_4237_ = 0usize;
                    v___x_4238_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_4216_, v_____s_4217_, v_isLower_4218_, v_cs_4233_, v_sz_4236_, v___x_4237_, v___x_4235_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
                    if crate::leanh::lean_obj_tag(v___x_4238_) == 0 {
                        v_a_4239_ = crate::leanh::lean_ctor_get(v___x_4238_, 0);
                        v_isSharedCheck_4253_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4238_)) as u8;
                        if v_isSharedCheck_4253_ == 0 {
                            v___x_4241_ = v___x_4238_;
                            v_isShared_4242_ = v_isSharedCheck_4253_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4239_);
                            crate::leanh::lean_dec(v___x_4238_);
                            v___x_4241_ = crate::leanh::lean_box(0);
                            v_isShared_4242_ = v_isSharedCheck_4253_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4254_ = crate::leanh::lean_ctor_get(v___x_4238_, 0);
                        v_isSharedCheck_4261_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4238_)) as u8;
                        if v_isSharedCheck_4261_ == 0 {
                            v___x_4256_ = v___x_4238_;
                            v_isShared_4257_ = v_isSharedCheck_4261_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4254_);
                            crate::leanh::lean_dec(v___x_4238_);
                            v___x_4256_ = crate::leanh::lean_box(0);
                            v_isShared_4257_ = v_isSharedCheck_4261_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4262_ = crate::leanh::lean_ctor_get(v_n_4219_, 0);
                    v___x_4263_ = crate::leanh::lean_box(0);
                    v___x_4264_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4264_, 0, v___x_4263_);
                    crate::leanh::lean_ctor_set(v___x_4264_, 1, v_b_4220_);
                    v_sz_4265_ = lean_array_size(v_vs_4262_);
                    v___x_4266_ = 0usize;
                    v___x_4267_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3(v_____s_4217_, v_isLower_4218_, v_vs_4262_, v_sz_4265_, v___x_4266_, v___x_4264_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
                    if crate::leanh::lean_obj_tag(v___x_4267_) == 0 {
                        v_a_4268_ = crate::leanh::lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4282_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4282_ == 0 {
                            v___x_4270_ = v___x_4267_;
                            v_isShared_4271_ = v_isSharedCheck_4282_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4268_);
                            crate::leanh::lean_dec(v___x_4267_);
                            v___x_4270_ = crate::leanh::lean_box(0);
                            v_isShared_4271_ = v_isSharedCheck_4282_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4283_ = crate::leanh::lean_ctor_get(v___x_4267_, 0);
                        v_isSharedCheck_4290_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4267_)) as u8;
                        if v_isSharedCheck_4290_ == 0 {
                            v___x_4285_ = v___x_4267_;
                            v_isShared_4286_ = v_isSharedCheck_4290_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4283_);
                            crate::leanh::lean_dec(v___x_4267_);
                            v___x_4285_ = crate::leanh::lean_box(0);
                            v_isShared_4286_ = v_isSharedCheck_4290_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4243_ = crate::leanh::lean_ctor_get(v_a_4239_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4243_) == 0 {
                    v_snd_4244_ = crate::leanh::lean_ctor_get(v_a_4239_, 1);
                    crate::leanh::lean_inc(v_snd_4244_);
                    crate::leanh::lean_dec(v_a_4239_);
                    v___x_4245_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4245_, 0, v_snd_4244_);
                    if v_isShared_4242_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4241_, 0, v___x_4245_);
                        v___x_4247_ = v___x_4241_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4248_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4248_, 0, v___x_4245_);
                        v___x_4247_ = v_reuseFailAlloc_4248_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4243_);
                    crate::leanh::lean_dec(v_a_4239_);
                    v_val_4249_ = crate::leanh::lean_ctor_get(v_fst_4243_, 0);
                    crate::leanh::lean_inc(v_val_4249_);
                    crate::leanh::lean_dec_ref_known(v_fst_4243_, 1);
                    if v_isShared_4242_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4241_, 0, v_val_4249_);
                        v___x_4251_ = v___x_4241_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4252_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4252_, 0, v_val_4249_);
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
                    v_reuseFailAlloc_4260_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4260_, 0, v_a_4254_);
                    v___x_4259_ = v_reuseFailAlloc_4260_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4259_;
            }
            6 => {
                v_fst_4272_ = crate::leanh::lean_ctor_get(v_a_4268_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4272_) == 0 {
                    v_snd_4273_ = crate::leanh::lean_ctor_get(v_a_4268_, 1);
                    crate::leanh::lean_inc(v_snd_4273_);
                    crate::leanh::lean_dec(v_a_4268_);
                    v___x_4274_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4274_, 0, v_snd_4273_);
                    if v_isShared_4271_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4270_, 0, v___x_4274_);
                        v___x_4276_ = v___x_4270_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4277_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4277_, 0, v___x_4274_);
                        v___x_4276_ = v_reuseFailAlloc_4277_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4272_);
                    crate::leanh::lean_dec(v_a_4268_);
                    v_val_4278_ = crate::leanh::lean_ctor_get(v_fst_4272_, 0);
                    crate::leanh::lean_inc(v_val_4278_);
                    crate::leanh::lean_dec_ref_known(v_fst_4272_, 1);
                    if v_isShared_4271_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4270_, 0, v_val_4278_);
                        v___x_4280_ = v___x_4270_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4281_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4281_, 0, v_val_4278_);
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
                    v_reuseFailAlloc_4289_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4289_, 0, v_a_4283_);
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
    mut v_init_4291_: *mut crate::leanh::LeanObject,
    mut v_____s_4292_: *mut crate::leanh::LeanObject,
    mut v_isLower_4293_: u8,
    mut v_as_4294_: *mut crate::leanh::LeanObject,
    mut v_sz_4295_: usize,
    mut v_i_4296_: usize,
    mut v_b_4297_: *mut crate::leanh::LeanObject,
    mut v___y_4298_: *mut crate::leanh::LeanObject,
    mut v___y_4299_: *mut crate::leanh::LeanObject,
    mut v___y_4300_: *mut crate::leanh::LeanObject,
    mut v___y_4301_: *mut crate::leanh::LeanObject,
    mut v___y_4302_: *mut crate::leanh::LeanObject,
    mut v___y_4303_: *mut crate::leanh::LeanObject,
    mut v___y_4304_: *mut crate::leanh::LeanObject,
    mut v___y_4305_: *mut crate::leanh::LeanObject,
    mut v___y_4306_: *mut crate::leanh::LeanObject,
    mut v___y_4307_: *mut crate::leanh::LeanObject,
    mut v___y_4308_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4310_: u8 = 0;
    let mut v___x_4311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4312_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4315_: u8 = 0;
    let mut v_a_4316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4320_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4321_: u8 = 0;
    let mut v___x_4322_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4324_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4326_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4327_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4333_: usize = 0;
    let mut v___x_4334_: usize = 0;
    let mut v_reuseFailAlloc_4336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4337_: u8 = 0;
    let mut v_a_4338_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4341_: u8 = 0;
    let mut v___x_4343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4344_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4345_: u8 = 0;
    let mut v_isSharedCheck_4346_: u8 = 0;
    let mut v_unused_4347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4310_ = lean_usize_dec_lt(v_i_4296_, v_sz_4295_);
                if v___x_4310_ == 0 {
                    v___x_4311_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4311_, 0, v_b_4297_);
                    return v___x_4311_;
                } else {
                    v_snd_4312_ = crate::leanh::lean_ctor_get(v_b_4297_, 1);
                    v_isSharedCheck_4346_ = (!crate::leanh::lean_is_exclusive(v_b_4297_)) as u8;
                    if v_isSharedCheck_4346_ == 0 {
                        v_unused_4347_ = crate::leanh::lean_ctor_get(v_b_4297_, 0);
                        crate::leanh::lean_dec(v_unused_4347_);
                        v___x_4314_ = v_b_4297_;
                        v_isShared_4315_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4312_);
                        crate::leanh::lean_dec(v_b_4297_);
                        v___x_4314_ = crate::leanh::lean_box(0);
                        v_isShared_4315_ = v_isSharedCheck_4346_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4316_ = lean_array_uget_borrowed(v_as_4294_, v_i_4296_);
                crate::leanh::lean_inc(v_snd_4312_);
                v___x_4317_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4291_, v_____s_4292_, v_isLower_4293_, v_a_4316_, v_snd_4312_, v___y_4298_, v___y_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_, v___y_4308_);
                if crate::leanh::lean_obj_tag(v___x_4317_) == 0 {
                    v_a_4318_ = crate::leanh::lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4337_ = (!crate::leanh::lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4337_ == 0 {
                        v___x_4320_ = v___x_4317_;
                        v_isShared_4321_ = v_isSharedCheck_4337_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4318_);
                        crate::leanh::lean_dec(v___x_4317_);
                        v___x_4320_ = crate::leanh::lean_box(0);
                        v_isShared_4321_ = v_isSharedCheck_4337_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4314_);
                    crate::leanh::lean_dec(v_snd_4312_);
                    v_a_4338_ = crate::leanh::lean_ctor_get(v___x_4317_, 0);
                    v_isSharedCheck_4345_ = (!crate::leanh::lean_is_exclusive(v___x_4317_)) as u8;
                    if v_isSharedCheck_4345_ == 0 {
                        v___x_4340_ = v___x_4317_;
                        v_isShared_4341_ = v_isSharedCheck_4345_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4338_);
                        crate::leanh::lean_dec(v___x_4317_);
                        v___x_4340_ = crate::leanh::lean_box(0);
                        v_isShared_4341_ = v_isSharedCheck_4345_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4318_) == 0 {
                    v___x_4322_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4322_, 0, v_a_4318_);
                    if v_isShared_4315_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4314_, 0, v___x_4322_);
                        v___x_4324_ = v___x_4314_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4328_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 0, v___x_4322_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4328_, 1, v_snd_4312_);
                        v___x_4324_ = v_reuseFailAlloc_4328_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4320_);
                    crate::leanh::lean_dec(v_snd_4312_);
                    v_a_4329_ = crate::leanh::lean_ctor_get(v_a_4318_, 0);
                    crate::leanh::lean_inc(v_a_4329_);
                    crate::leanh::lean_dec_ref_known(v_a_4318_, 1);
                    v___x_4330_ = crate::leanh::lean_box(0);
                    if v_isShared_4315_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4314_, 1, v_a_4329_);
                        crate::leanh::lean_ctor_set(v___x_4314_, 0, v___x_4330_);
                        v___x_4332_ = v___x_4314_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4336_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 0, v___x_4330_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4336_, 1, v_a_4329_);
                        v___x_4332_ = v_reuseFailAlloc_4336_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4321_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4320_, 0, v___x_4324_);
                    v___x_4326_ = v___x_4320_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4327_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4327_, 0, v___x_4324_);
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
                    v_reuseFailAlloc_4344_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4344_, 0, v_a_4338_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_4348_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_____s_4349_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_isLower_4350_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_as_4351_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_sz_4352_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_i_4353_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_b_4354_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4355_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4356_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4357_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4358_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4359_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4360_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4361_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4362_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4363_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4364_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4365_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_4366_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_isLower_boxed_4367_: u8 = 0;
    let mut v_sz_boxed_4368_: usize = 0;
    let mut v_i_boxed_4369_: usize = 0;
    let mut v_res_4370_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4367_ = (crate::leanh::lean_unbox(v_isLower_4350_) as u8);
    v_sz_boxed_4368_ = crate::leanh::lean_unbox_usize(v_sz_4352_);
    crate::leanh::lean_dec(v_sz_4352_);
    v_i_boxed_4369_ = crate::leanh::lean_unbox_usize(v_i_4353_);
    crate::leanh::lean_dec(v_i_4353_);
    v_res_4370_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__2(v_init_4348_, v_____s_4349_, v_isLower_boxed_4367_, v_as_4351_, v_sz_boxed_4368_, v_i_boxed_4369_, v_b_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_, v___y_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
    crate::leanh::lean_dec(v___y_4365_);
    crate::leanh::lean_dec_ref(v___y_4364_);
    crate::leanh::lean_dec(v___y_4363_);
    crate::leanh::lean_dec_ref(v___y_4362_);
    crate::leanh::lean_dec(v___y_4361_);
    crate::leanh::lean_dec_ref(v___y_4360_);
    crate::leanh::lean_dec(v___y_4359_);
    crate::leanh::lean_dec_ref(v___y_4358_);
    crate::leanh::lean_dec(v___y_4357_);
    crate::leanh::lean_dec(v___y_4356_);
    crate::leanh::lean_dec(v___y_4355_);
    crate::leanh::lean_dec_ref(v_as_4351_);
    crate::leanh::lean_dec(v_____s_4349_);
    return v_res_4370_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_4371_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_____s_4372_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_isLower_4373_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_n_4374_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_4375_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_4376_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4377_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4378_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4379_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4380_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4381_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4382_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4383_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4384_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4385_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4386_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4387_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4388_: u8 = 0;
    let mut v_res_4389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4388_ = (crate::leanh::lean_unbox(v_isLower_4373_) as u8);
    v_res_4389_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4371_, v_____s_4372_, v_isLower_boxed_4388_, v_n_4374_, v_b_4375_, v___y_4376_, v___y_4377_, v___y_4378_, v___y_4379_, v___y_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_, v___y_4386_);
    crate::leanh::lean_dec(v___y_4386_);
    crate::leanh::lean_dec_ref(v___y_4385_);
    crate::leanh::lean_dec(v___y_4384_);
    crate::leanh::lean_dec_ref(v___y_4383_);
    crate::leanh::lean_dec(v___y_4382_);
    crate::leanh::lean_dec_ref(v___y_4381_);
    crate::leanh::lean_dec(v___y_4380_);
    crate::leanh::lean_dec_ref(v___y_4379_);
    crate::leanh::lean_dec(v___y_4378_);
    crate::leanh::lean_dec(v___y_4377_);
    crate::leanh::lean_dec(v___y_4376_);
    crate::leanh::lean_dec_ref(v_n_4374_);
    crate::leanh::lean_dec(v_____s_4372_);
    return v_res_4389_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(
    mut v_____s_4390_: *mut crate::leanh::LeanObject,
    mut v_isLower_4391_: u8,
    mut v_as_4392_: *mut crate::leanh::LeanObject,
    mut v_sz_4393_: usize,
    mut v_i_4394_: usize,
    mut v_b_4395_: *mut crate::leanh::LeanObject,
    mut v___y_4396_: *mut crate::leanh::LeanObject,
    mut v___y_4397_: *mut crate::leanh::LeanObject,
    mut v___y_4398_: *mut crate::leanh::LeanObject,
    mut v___y_4399_: *mut crate::leanh::LeanObject,
    mut v___y_4400_: *mut crate::leanh::LeanObject,
    mut v___y_4401_: *mut crate::leanh::LeanObject,
    mut v___y_4402_: *mut crate::leanh::LeanObject,
    mut v___y_4403_: *mut crate::leanh::LeanObject,
    mut v___y_4404_: *mut crate::leanh::LeanObject,
    mut v___y_4405_: *mut crate::leanh::LeanObject,
    mut v___y_4406_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4408_: u8 = 0;
    let mut v___x_4409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4413_: u8 = 0;
    let mut v_a_4414_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4415_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4416_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4417_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4419_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4421_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4422_: usize = 0;
    let mut v___x_4423_: usize = 0;
    let mut v_reuseFailAlloc_4425_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4427_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4432_: u8 = 0;
    let mut v_a_4433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4436_: u8 = 0;
    let mut v___x_4438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4444_: u8 = 0;
    let mut v_a_4445_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4446_: u8 = 0;
    let mut v_a_4447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4450_: u8 = 0;
    let mut v___x_4452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4454_: u8 = 0;
    let mut v___x_4455_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_4457_: u8 = 0;
    let mut v_k_4458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4460_: u8 = 0;
    let mut v___x_4461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4466_: u8 = 0;
    let mut v___x_4468_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4470_: u8 = 0;
    let mut v_a_4471_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4474_: u8 = 0;
    let mut v___x_4476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4477_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4478_: u8 = 0;
    let mut v_isSharedCheck_4479_: u8 = 0;
    let mut v_unused_4480_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4408_ = lean_usize_dec_lt(v_i_4394_, v_sz_4393_);
                if v___x_4408_ == 0 {
                    v___x_4409_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4409_, 0, v_b_4395_);
                    return v___x_4409_;
                } else {
                    v_snd_4410_ = crate::leanh::lean_ctor_get(v_b_4395_, 1);
                    v_isSharedCheck_4479_ = (!crate::leanh::lean_is_exclusive(v_b_4395_)) as u8;
                    if v_isSharedCheck_4479_ == 0 {
                        v_unused_4480_ = crate::leanh::lean_ctor_get(v_b_4395_, 0);
                        crate::leanh::lean_dec(v_unused_4480_);
                        v___x_4412_ = v_b_4395_;
                        v_isShared_4413_ = v_isSharedCheck_4479_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4410_);
                        crate::leanh::lean_dec(v_b_4395_);
                        v___x_4412_ = crate::leanh::lean_box(0);
                        v_isShared_4413_ = v_isSharedCheck_4479_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4414_ = lean_array_uget_borrowed(v_as_4392_, v_i_4394_);
                v_p_4415_ = crate::leanh::lean_ctor_get(v_a_4414_, 0);
                v___x_4416_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4415_, v_____s_4390_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                if crate::leanh::lean_obj_tag(v___x_4416_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4416_, 1);
                    v___x_4417_ = crate::leanh::lean_box(0);
                    v___x_4455_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_p_4415_) == 1 {
                        v_k_4458_ = crate::leanh::lean_ctor_get(v_p_4415_, 0);
                        v___x_4459_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        crate::leanh::lean_dec(v_snd_4410_);
                        v___x_4461_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4462_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4461_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                        if crate::leanh::lean_obj_tag(v___x_4462_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4462_, 1);
                            v_a_4419_ = v___x_4455_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_4412_);
                            v_a_4463_ = crate::leanh::lean_ctor_get(v___x_4462_, 0);
                            v_isSharedCheck_4470_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4462_)) as u8;
                            if v_isSharedCheck_4470_ == 0 {
                                v___x_4465_ = v___x_4462_;
                                v_isShared_4466_ = v_isSharedCheck_4470_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4463_);
                                crate::leanh::lean_dec(v___x_4462_);
                                v___x_4465_ = crate::leanh::lean_box(0);
                                v_isShared_4466_ = v_isSharedCheck_4470_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4412_);
                    crate::leanh::lean_dec(v_snd_4410_);
                    v_a_4471_ = crate::leanh::lean_ctor_get(v___x_4416_, 0);
                    v_isSharedCheck_4478_ = (!crate::leanh::lean_is_exclusive(v___x_4416_)) as u8;
                    if v_isSharedCheck_4478_ == 0 {
                        v___x_4473_ = v___x_4416_;
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4471_);
                        crate::leanh::lean_dec(v___x_4416_);
                        v___x_4473_ = crate::leanh::lean_box(0);
                        v_isShared_4474_ = v_isSharedCheck_4478_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4413_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4412_, 1, v_a_4419_);
                    crate::leanh::lean_ctor_set(v___x_4412_, 0, v___x_4417_);
                    v___x_4421_ = v___x_4412_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4425_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4417_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_a_4419_);
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
                v___x_4427_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4428_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4427_, v___y_4396_, v___y_4397_, v___y_4398_, v___y_4399_, v___y_4400_, v___y_4401_, v___y_4402_, v___y_4403_, v___y_4404_, v___y_4405_, v___y_4406_);
                if crate::leanh::lean_obj_tag(v___x_4428_) == 0 {
                    v_a_4429_ = crate::leanh::lean_ctor_get(v___x_4428_, 0);
                    v_isSharedCheck_4446_ = (!crate::leanh::lean_is_exclusive(v___x_4428_)) as u8;
                    if v_isSharedCheck_4446_ == 0 {
                        v___x_4431_ = v___x_4428_;
                        v_isShared_4432_ = v_isSharedCheck_4446_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4429_);
                        crate::leanh::lean_dec(v___x_4428_);
                        v___x_4431_ = crate::leanh::lean_box(0);
                        v_isShared_4432_ = v_isSharedCheck_4446_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4412_);
                    crate::leanh::lean_dec(v_snd_4410_);
                    v_a_4447_ = crate::leanh::lean_ctor_get(v___x_4428_, 0);
                    v_isSharedCheck_4454_ = (!crate::leanh::lean_is_exclusive(v___x_4428_)) as u8;
                    if v_isSharedCheck_4454_ == 0 {
                        v___x_4449_ = v___x_4428_;
                        v_isShared_4450_ = v_isSharedCheck_4454_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4447_);
                        crate::leanh::lean_dec(v___x_4428_);
                        v___x_4449_ = crate::leanh::lean_box(0);
                        v_isShared_4450_ = v_isSharedCheck_4454_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4429_) == 0 {
                    crate::leanh::lean_del_object(v___x_4412_);
                    v_a_4433_ = crate::leanh::lean_ctor_get(v_a_4429_, 0);
                    v_isSharedCheck_4444_ = (!crate::leanh::lean_is_exclusive(v_a_4429_)) as u8;
                    if v_isSharedCheck_4444_ == 0 {
                        v___x_4435_ = v_a_4429_;
                        v_isShared_4436_ = v_isSharedCheck_4444_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4433_);
                        crate::leanh::lean_dec(v_a_4429_);
                        v___x_4435_ = crate::leanh::lean_box(0);
                        v_isShared_4436_ = v_isSharedCheck_4444_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4431_);
                    crate::leanh::lean_dec(v_snd_4410_);
                    v_a_4445_ = crate::leanh::lean_ctor_get(v_a_4429_, 0);
                    crate::leanh::lean_inc(v_a_4445_);
                    crate::leanh::lean_dec_ref_known(v_a_4429_, 1);
                    v_a_4419_ = v_a_4445_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_4436_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4435_, 1);
                    v___x_4438_ = v___x_4435_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4443_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4443_, 0, v_a_4433_);
                    v___x_4438_ = v_reuseFailAlloc_4443_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4439_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4439_, 0, v___x_4438_);
                crate::leanh::lean_ctor_set(v___x_4439_, 1, v_snd_4410_);
                if v_isShared_4432_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4431_, 0, v___x_4439_);
                    v___x_4441_ = v___x_4431_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4442_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4442_, 0, v___x_4439_);
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
                    v_reuseFailAlloc_4453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
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
                    crate::leanh::lean_dec(v_snd_4410_);
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
                    v_reuseFailAlloc_4469_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4469_, 0, v_a_4463_);
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
                    v_reuseFailAlloc_4477_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4477_, 0, v_a_4471_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_4481_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4482_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_4483_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_4484_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_4485_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_4486_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4487_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4488_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4489_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4490_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4491_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4492_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4493_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4494_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4495_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4496_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4497_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4498_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4499_: u8 = 0;
    let mut v_sz_boxed_4500_: usize = 0;
    let mut v_i_boxed_4501_: usize = 0;
    let mut v_res_4502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4499_ = (crate::leanh::lean_unbox(v_isLower_4482_) as u8);
    v_sz_boxed_4500_ = crate::leanh::lean_unbox_usize(v_sz_4484_);
    crate::leanh::lean_dec(v_sz_4484_);
    v_i_boxed_4501_ = crate::leanh::lean_unbox_usize(v_i_4485_);
    crate::leanh::lean_dec(v_i_4485_);
    v_res_4502_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2_spec__5(v_____s_4481_, v_isLower_boxed_4499_, v_as_4483_, v_sz_boxed_4500_, v_i_boxed_4501_, v_b_4486_, v___y_4487_, v___y_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_, v___y_4496_, v___y_4497_);
    crate::leanh::lean_dec(v___y_4497_);
    crate::leanh::lean_dec_ref(v___y_4496_);
    crate::leanh::lean_dec(v___y_4495_);
    crate::leanh::lean_dec_ref(v___y_4494_);
    crate::leanh::lean_dec(v___y_4493_);
    crate::leanh::lean_dec_ref(v___y_4492_);
    crate::leanh::lean_dec(v___y_4491_);
    crate::leanh::lean_dec_ref(v___y_4490_);
    crate::leanh::lean_dec(v___y_4489_);
    crate::leanh::lean_dec(v___y_4488_);
    crate::leanh::lean_dec(v___y_4487_);
    crate::leanh::lean_dec_ref(v_as_4483_);
    crate::leanh::lean_dec(v_____s_4481_);
    return v_res_4502_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(
    mut v_____s_4503_: *mut crate::leanh::LeanObject,
    mut v_isLower_4504_: u8,
    mut v_as_4505_: *mut crate::leanh::LeanObject,
    mut v_sz_4506_: usize,
    mut v_i_4507_: usize,
    mut v_b_4508_: *mut crate::leanh::LeanObject,
    mut v___y_4509_: *mut crate::leanh::LeanObject,
    mut v___y_4510_: *mut crate::leanh::LeanObject,
    mut v___y_4511_: *mut crate::leanh::LeanObject,
    mut v___y_4512_: *mut crate::leanh::LeanObject,
    mut v___y_4513_: *mut crate::leanh::LeanObject,
    mut v___y_4514_: *mut crate::leanh::LeanObject,
    mut v___y_4515_: *mut crate::leanh::LeanObject,
    mut v___y_4516_: *mut crate::leanh::LeanObject,
    mut v___y_4517_: *mut crate::leanh::LeanObject,
    mut v___y_4518_: *mut crate::leanh::LeanObject,
    mut v___y_4519_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4521_: u8 = 0;
    let mut v___x_4522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4526_: u8 = 0;
    let mut v_a_4527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_4528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4533_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4536_: usize = 0;
    let mut v___x_4537_: usize = 0;
    let mut v___x_4538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4542_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4545_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4546_: u8 = 0;
    let mut v_a_4547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4549_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4550_: u8 = 0;
    let mut v___x_4552_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4553_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4555_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4556_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4557_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4558_: u8 = 0;
    let mut v_a_4559_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4560_: u8 = 0;
    let mut v_a_4561_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4563_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4564_: u8 = 0;
    let mut v___x_4566_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4567_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4568_: u8 = 0;
    let mut v___y_4570_: u8 = 0;
    let mut v_k_4571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4572_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4573_: u8 = 0;
    let mut v___x_4574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4576_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4578_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4579_: u8 = 0;
    let mut v___x_4581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4582_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4583_: u8 = 0;
    let mut v_a_4584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4587_: u8 = 0;
    let mut v___x_4589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4591_: u8 = 0;
    let mut v_isSharedCheck_4592_: u8 = 0;
    let mut v_unused_4593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4521_ = lean_usize_dec_lt(v_i_4507_, v_sz_4506_);
                if v___x_4521_ == 0 {
                    v___x_4522_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4522_, 0, v_b_4508_);
                    return v___x_4522_;
                } else {
                    v_snd_4523_ = crate::leanh::lean_ctor_get(v_b_4508_, 1);
                    v_isSharedCheck_4592_ = (!crate::leanh::lean_is_exclusive(v_b_4508_)) as u8;
                    if v_isSharedCheck_4592_ == 0 {
                        v_unused_4593_ = crate::leanh::lean_ctor_get(v_b_4508_, 0);
                        crate::leanh::lean_dec(v_unused_4593_);
                        v___x_4525_ = v_b_4508_;
                        v_isShared_4526_ = v_isSharedCheck_4592_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4523_);
                        crate::leanh::lean_dec(v_b_4508_);
                        v___x_4525_ = crate::leanh::lean_box(0);
                        v_isShared_4526_ = v_isSharedCheck_4592_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4527_ = lean_array_uget_borrowed(v_as_4505_, v_i_4507_);
                v_p_4528_ = crate::leanh::lean_ctor_get(v_a_4527_, 0);
                v___x_4529_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_4528_, v_____s_4503_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                if crate::leanh::lean_obj_tag(v___x_4529_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4529_, 1);
                    v___x_4530_ = crate::leanh::lean_box(0);
                    v___x_4531_ = crate::leanh::lean_box(0);
                    if crate::leanh::lean_obj_tag(v_p_4528_) == 1 {
                        v_k_4571_ = crate::leanh::lean_ctor_get(v_p_4528_, 0);
                        v___x_4572_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCoeffs___closed__0);
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
                        crate::leanh::lean_dec(v_snd_4523_);
                        v___x_4574_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__3);
                        v___x_4575_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_4574_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                        if crate::leanh::lean_obj_tag(v___x_4575_) == 0 {
                            crate::leanh::lean_dec_ref_known(v___x_4575_, 1);
                            v_a_4533_ = v___x_4530_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_del_object(v___x_4525_);
                            v_a_4576_ = crate::leanh::lean_ctor_get(v___x_4575_, 0);
                            v_isSharedCheck_4583_ =
                                (!crate::leanh::lean_is_exclusive(v___x_4575_)) as u8;
                            if v_isSharedCheck_4583_ == 0 {
                                v___x_4578_ = v___x_4575_;
                                v_isShared_4579_ = v_isSharedCheck_4583_;
                                state = 12;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_4576_);
                                crate::leanh::lean_dec(v___x_4575_);
                                v___x_4578_ = crate::leanh::lean_box(0);
                                v_isShared_4579_ = v_isSharedCheck_4583_;
                                state = 12;
                                continue;
                            }
                        }
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4525_);
                    crate::leanh::lean_dec(v_snd_4523_);
                    v_a_4584_ = crate::leanh::lean_ctor_get(v___x_4529_, 0);
                    v_isSharedCheck_4591_ = (!crate::leanh::lean_is_exclusive(v___x_4529_)) as u8;
                    if v_isSharedCheck_4591_ == 0 {
                        v___x_4586_ = v___x_4529_;
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 14;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4584_);
                        crate::leanh::lean_dec(v___x_4529_);
                        v___x_4586_ = crate::leanh::lean_box(0);
                        v_isShared_4587_ = v_isSharedCheck_4591_;
                        state = 14;
                        continue;
                    }
                }
            }
            2 => {
                if v_isShared_4526_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4525_, 1, v_a_4533_);
                    crate::leanh::lean_ctor_set(v___x_4525_, 0, v___x_4531_);
                    v___x_4535_ = v___x_4525_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_4539_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 0, v___x_4531_);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4539_, 1, v_a_4533_);
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
                v___x_4541_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2), core::ptr::addr_of_mut!(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2_once), _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1_spec__3_spec__5___closed__2);
                v___x_4542_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__0(v___x_4541_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_, v___y_4516_, v___y_4517_, v___y_4518_, v___y_4519_);
                if crate::leanh::lean_obj_tag(v___x_4542_) == 0 {
                    v_a_4543_ = crate::leanh::lean_ctor_get(v___x_4542_, 0);
                    v_isSharedCheck_4560_ = (!crate::leanh::lean_is_exclusive(v___x_4542_)) as u8;
                    if v_isSharedCheck_4560_ == 0 {
                        v___x_4545_ = v___x_4542_;
                        v_isShared_4546_ = v_isSharedCheck_4560_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4543_);
                        crate::leanh::lean_dec(v___x_4542_);
                        v___x_4545_ = crate::leanh::lean_box(0);
                        v_isShared_4546_ = v_isSharedCheck_4560_;
                        state = 5;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4525_);
                    crate::leanh::lean_dec(v_snd_4523_);
                    v_a_4561_ = crate::leanh::lean_ctor_get(v___x_4542_, 0);
                    v_isSharedCheck_4568_ = (!crate::leanh::lean_is_exclusive(v___x_4542_)) as u8;
                    if v_isSharedCheck_4568_ == 0 {
                        v___x_4563_ = v___x_4542_;
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 9;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4561_);
                        crate::leanh::lean_dec(v___x_4542_);
                        v___x_4563_ = crate::leanh::lean_box(0);
                        v_isShared_4564_ = v_isSharedCheck_4568_;
                        state = 9;
                        continue;
                    }
                }
            }
            5 => {
                if crate::leanh::lean_obj_tag(v_a_4543_) == 0 {
                    crate::leanh::lean_del_object(v___x_4525_);
                    v_a_4547_ = crate::leanh::lean_ctor_get(v_a_4543_, 0);
                    v_isSharedCheck_4558_ = (!crate::leanh::lean_is_exclusive(v_a_4543_)) as u8;
                    if v_isSharedCheck_4558_ == 0 {
                        v___x_4549_ = v_a_4543_;
                        v_isShared_4550_ = v_isSharedCheck_4558_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4547_);
                        crate::leanh::lean_dec(v_a_4543_);
                        v___x_4549_ = crate::leanh::lean_box(0);
                        v_isShared_4550_ = v_isSharedCheck_4558_;
                        state = 6;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4545_);
                    crate::leanh::lean_dec(v_snd_4523_);
                    v_a_4559_ = crate::leanh::lean_ctor_get(v_a_4543_, 0);
                    crate::leanh::lean_inc(v_a_4559_);
                    crate::leanh::lean_dec_ref_known(v_a_4543_, 1);
                    v_a_4533_ = v_a_4559_;
                    state = 2;
                    continue;
                }
            }
            6 => {
                if v_isShared_4550_ == 0 {
                    crate::leanh::lean_ctor_set_tag(v___x_4549_, 1);
                    v___x_4552_ = v___x_4549_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_4557_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4547_);
                    v___x_4552_ = v_reuseFailAlloc_4557_;
                    state = 7;
                    continue;
                }
            }
            7 => {
                v___x_4553_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_4553_, 0, v___x_4552_);
                crate::leanh::lean_ctor_set(v___x_4553_, 1, v_snd_4523_);
                if v_isShared_4546_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4545_, 0, v___x_4553_);
                    v___x_4555_ = v___x_4545_;
                    state = 8;
                    continue;
                } else {
                    v_reuseFailAlloc_4556_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4556_, 0, v___x_4553_);
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
                    v_reuseFailAlloc_4567_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4567_, 0, v_a_4561_);
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
                    crate::leanh::lean_dec(v_snd_4523_);
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
                    v_reuseFailAlloc_4582_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4582_, 0, v_a_4576_);
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
                    v_reuseFailAlloc_4590_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4590_, 0, v_a_4584_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_4594_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4595_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_4596_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_4597_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_4598_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_4599_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4600_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4601_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4602_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4603_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4604_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4605_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4606_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4607_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4608_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4609_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4610_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4611_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4612_: u8 = 0;
    let mut v_sz_boxed_4613_: usize = 0;
    let mut v_i_boxed_4614_: usize = 0;
    let mut v_res_4615_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4612_ = (crate::leanh::lean_unbox(v_isLower_4595_) as u8);
    v_sz_boxed_4613_ = crate::leanh::lean_unbox_usize(v_sz_4597_);
    crate::leanh::lean_dec(v_sz_4597_);
    v_i_boxed_4614_ = crate::leanh::lean_unbox_usize(v_i_4598_);
    crate::leanh::lean_dec(v_i_4598_);
    v_res_4615_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_4594_, v_isLower_boxed_4612_, v_as_4596_, v_sz_boxed_4613_, v_i_boxed_4614_, v_b_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
    crate::leanh::lean_dec(v___y_4610_);
    crate::leanh::lean_dec_ref(v___y_4609_);
    crate::leanh::lean_dec(v___y_4608_);
    crate::leanh::lean_dec_ref(v___y_4607_);
    crate::leanh::lean_dec(v___y_4606_);
    crate::leanh::lean_dec_ref(v___y_4605_);
    crate::leanh::lean_dec(v___y_4604_);
    crate::leanh::lean_dec_ref(v___y_4603_);
    crate::leanh::lean_dec(v___y_4602_);
    crate::leanh::lean_dec(v___y_4601_);
    crate::leanh::lean_dec(v___y_4600_);
    crate::leanh::lean_dec_ref(v_as_4596_);
    crate::leanh::lean_dec(v_____s_4594_);
    return v_res_4615_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(
    mut v_____s_4616_: *mut crate::leanh::LeanObject,
    mut v_isLower_4617_: u8,
    mut v_t_4618_: *mut crate::leanh::LeanObject,
    mut v_init_4619_: *mut crate::leanh::LeanObject,
    mut v___y_4620_: *mut crate::leanh::LeanObject,
    mut v___y_4621_: *mut crate::leanh::LeanObject,
    mut v___y_4622_: *mut crate::leanh::LeanObject,
    mut v___y_4623_: *mut crate::leanh::LeanObject,
    mut v___y_4624_: *mut crate::leanh::LeanObject,
    mut v___y_4625_: *mut crate::leanh::LeanObject,
    mut v___y_4626_: *mut crate::leanh::LeanObject,
    mut v___y_4627_: *mut crate::leanh::LeanObject,
    mut v___y_4628_: *mut crate::leanh::LeanObject,
    mut v___y_4629_: *mut crate::leanh::LeanObject,
    mut v___y_4630_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_4632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_4633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4634_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4635_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4638_: u8 = 0;
    let mut v_a_4639_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4644_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4645_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4646_: usize = 0;
    let mut v___x_4647_: usize = 0;
    let mut v___x_4648_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4652_: u8 = 0;
    let mut v_fst_4653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4656_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4657_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4658_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4660_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4661_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4662_: u8 = 0;
    let mut v_a_4663_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4666_: u8 = 0;
    let mut v___x_4668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4669_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4670_: u8 = 0;
    let mut v_isSharedCheck_4671_: u8 = 0;
    let mut v_a_4672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4675_: u8 = 0;
    let mut v___x_4677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_4632_ = crate::leanh::lean_ctor_get(v_t_4618_, 0);
                v_tail_4633_ = crate::leanh::lean_ctor_get(v_t_4618_, 1);
                v___x_4634_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__1(v_init_4619_, v_____s_4616_, v_isLower_4617_, v_root_4632_, v_init_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                if crate::leanh::lean_obj_tag(v___x_4634_) == 0 {
                    v_a_4635_ = crate::leanh::lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4671_ = (!crate::leanh::lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4671_ == 0 {
                        v___x_4637_ = v___x_4634_;
                        v_isShared_4638_ = v_isSharedCheck_4671_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4635_);
                        crate::leanh::lean_dec(v___x_4634_);
                        v___x_4637_ = crate::leanh::lean_box(0);
                        v_isShared_4638_ = v_isSharedCheck_4671_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_4672_ = crate::leanh::lean_ctor_get(v___x_4634_, 0);
                    v_isSharedCheck_4679_ = (!crate::leanh::lean_is_exclusive(v___x_4634_)) as u8;
                    if v_isSharedCheck_4679_ == 0 {
                        v___x_4674_ = v___x_4634_;
                        v_isShared_4675_ = v_isSharedCheck_4679_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4672_);
                        crate::leanh::lean_dec(v___x_4634_);
                        v___x_4674_ = crate::leanh::lean_box(0);
                        v_isShared_4675_ = v_isSharedCheck_4679_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_4635_) == 0 {
                    v_a_4639_ = crate::leanh::lean_ctor_get(v_a_4635_, 0);
                    crate::leanh::lean_inc(v_a_4639_);
                    crate::leanh::lean_dec_ref_known(v_a_4635_, 1);
                    if v_isShared_4638_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4637_, 0, v_a_4639_);
                        v___x_4641_ = v___x_4637_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4642_, 0, v_a_4639_);
                        v___x_4641_ = v_reuseFailAlloc_4642_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4637_);
                    v_a_4643_ = crate::leanh::lean_ctor_get(v_a_4635_, 0);
                    crate::leanh::lean_inc(v_a_4643_);
                    crate::leanh::lean_dec_ref_known(v_a_4635_, 1);
                    v___x_4644_ = crate::leanh::lean_box(0);
                    v___x_4645_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4645_, 0, v___x_4644_);
                    crate::leanh::lean_ctor_set(v___x_4645_, 1, v_a_4643_);
                    v_sz_4646_ = lean_array_size(v_tail_4633_);
                    v___x_4647_ = 0usize;
                    v___x_4648_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1_spec__2(v_____s_4616_, v_isLower_4617_, v_tail_4633_, v_sz_4646_, v___x_4647_, v___x_4645_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_, v___y_4629_, v___y_4630_);
                    if crate::leanh::lean_obj_tag(v___x_4648_) == 0 {
                        v_a_4649_ = crate::leanh::lean_ctor_get(v___x_4648_, 0);
                        v_isSharedCheck_4662_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4648_)) as u8;
                        if v_isSharedCheck_4662_ == 0 {
                            v___x_4651_ = v___x_4648_;
                            v_isShared_4652_ = v_isSharedCheck_4662_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4649_);
                            crate::leanh::lean_dec(v___x_4648_);
                            v___x_4651_ = crate::leanh::lean_box(0);
                            v_isShared_4652_ = v_isSharedCheck_4662_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_4663_ = crate::leanh::lean_ctor_get(v___x_4648_, 0);
                        v_isSharedCheck_4670_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4648_)) as u8;
                        if v_isSharedCheck_4670_ == 0 {
                            v___x_4665_ = v___x_4648_;
                            v_isShared_4666_ = v_isSharedCheck_4670_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4663_);
                            crate::leanh::lean_dec(v___x_4648_);
                            v___x_4665_ = crate::leanh::lean_box(0);
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
                v_fst_4653_ = crate::leanh::lean_ctor_get(v_a_4649_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4653_) == 0 {
                    v_snd_4654_ = crate::leanh::lean_ctor_get(v_a_4649_, 1);
                    crate::leanh::lean_inc(v_snd_4654_);
                    crate::leanh::lean_dec(v_a_4649_);
                    if v_isShared_4652_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4651_, 0, v_snd_4654_);
                        v___x_4656_ = v___x_4651_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_4657_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4657_, 0, v_snd_4654_);
                        v___x_4656_ = v_reuseFailAlloc_4657_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4653_);
                    crate::leanh::lean_dec(v_a_4649_);
                    v_val_4658_ = crate::leanh::lean_ctor_get(v_fst_4653_, 0);
                    crate::leanh::lean_inc(v_val_4658_);
                    crate::leanh::lean_dec_ref_known(v_fst_4653_, 1);
                    if v_isShared_4652_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4651_, 0, v_val_4658_);
                        v___x_4660_ = v___x_4651_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4661_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4661_, 0, v_val_4658_);
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
                    v_reuseFailAlloc_4669_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4669_, 0, v_a_4663_);
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
                    v_reuseFailAlloc_4678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4678_, 0, v_a_4672_);
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
    mut v_____s_4680_: *mut crate::leanh::LeanObject,
    mut v_isLower_4681_: *mut crate::leanh::LeanObject,
    mut v_t_4682_: *mut crate::leanh::LeanObject,
    mut v_init_4683_: *mut crate::leanh::LeanObject,
    mut v___y_4684_: *mut crate::leanh::LeanObject,
    mut v___y_4685_: *mut crate::leanh::LeanObject,
    mut v___y_4686_: *mut crate::leanh::LeanObject,
    mut v___y_4687_: *mut crate::leanh::LeanObject,
    mut v___y_4688_: *mut crate::leanh::LeanObject,
    mut v___y_4689_: *mut crate::leanh::LeanObject,
    mut v___y_4690_: *mut crate::leanh::LeanObject,
    mut v___y_4691_: *mut crate::leanh::LeanObject,
    mut v___y_4692_: *mut crate::leanh::LeanObject,
    mut v___y_4693_: *mut crate::leanh::LeanObject,
    mut v___y_4694_: *mut crate::leanh::LeanObject,
    mut v___y_4695_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_boxed_4696_: u8 = 0;
    let mut v_res_4697_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4696_ = (crate::leanh::lean_unbox(v_isLower_4681_) as u8);
    v_res_4697_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_____s_4680_, v_isLower_boxed_4696_, v_t_4682_, v_init_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_, v___y_4688_, v___y_4689_, v___y_4690_, v___y_4691_, v___y_4692_, v___y_4693_, v___y_4694_);
    crate::leanh::lean_dec(v___y_4694_);
    crate::leanh::lean_dec_ref(v___y_4693_);
    crate::leanh::lean_dec(v___y_4692_);
    crate::leanh::lean_dec_ref(v___y_4691_);
    crate::leanh::lean_dec(v___y_4690_);
    crate::leanh::lean_dec_ref(v___y_4689_);
    crate::leanh::lean_dec(v___y_4688_);
    crate::leanh::lean_dec_ref(v___y_4687_);
    crate::leanh::lean_dec(v___y_4686_);
    crate::leanh::lean_dec(v___y_4685_);
    crate::leanh::lean_dec(v___y_4684_);
    crate::leanh::lean_dec_ref(v_t_4682_);
    crate::leanh::lean_dec(v_____s_4680_);
    return v_res_4697_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(
    mut v_isLower_4698_: u8,
    mut v_as_4699_: *mut crate::leanh::LeanObject,
    mut v_sz_4700_: usize,
    mut v_i_4701_: usize,
    mut v_b_4702_: *mut crate::leanh::LeanObject,
    mut v___y_4703_: *mut crate::leanh::LeanObject,
    mut v___y_4704_: *mut crate::leanh::LeanObject,
    mut v___y_4705_: *mut crate::leanh::LeanObject,
    mut v___y_4706_: *mut crate::leanh::LeanObject,
    mut v___y_4707_: *mut crate::leanh::LeanObject,
    mut v___y_4708_: *mut crate::leanh::LeanObject,
    mut v___y_4709_: *mut crate::leanh::LeanObject,
    mut v___y_4710_: *mut crate::leanh::LeanObject,
    mut v___y_4711_: *mut crate::leanh::LeanObject,
    mut v___y_4712_: *mut crate::leanh::LeanObject,
    mut v___y_4713_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4715_: u8 = 0;
    let mut v___x_4716_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4717_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4720_: u8 = 0;
    let mut v_a_4721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4723_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4724_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4729_: usize = 0;
    let mut v___x_4730_: usize = 0;
    let mut v_reuseFailAlloc_4732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4733_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4735_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4736_: u8 = 0;
    let mut v___x_4738_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4739_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4740_: u8 = 0;
    let mut v_isSharedCheck_4741_: u8 = 0;
    let mut v_unused_4742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4715_ = lean_usize_dec_lt(v_i_4701_, v_sz_4700_);
                if v___x_4715_ == 0 {
                    v___x_4716_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4716_, 0, v_b_4702_);
                    return v___x_4716_;
                } else {
                    v_snd_4717_ = crate::leanh::lean_ctor_get(v_b_4702_, 1);
                    v_isSharedCheck_4741_ = (!crate::leanh::lean_is_exclusive(v_b_4702_)) as u8;
                    if v_isSharedCheck_4741_ == 0 {
                        v_unused_4742_ = crate::leanh::lean_ctor_get(v_b_4702_, 0);
                        crate::leanh::lean_dec(v_unused_4742_);
                        v___x_4719_ = v_b_4702_;
                        v_isShared_4720_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4717_);
                        crate::leanh::lean_dec(v_b_4702_);
                        v___x_4719_ = crate::leanh::lean_box(0);
                        v_isShared_4720_ = v_isSharedCheck_4741_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4721_ = lean_array_uget_borrowed(v_as_4699_, v_i_4701_);
                v___x_4722_ = crate::leanh::lean_box(0);
                v___x_4723_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_4717_, v_isLower_4698_, v_a_4721_, v___x_4722_, v___y_4703_, v___y_4704_, v___y_4705_, v___y_4706_, v___y_4707_, v___y_4708_, v___y_4709_, v___y_4710_, v___y_4711_, v___y_4712_, v___y_4713_);
                if crate::leanh::lean_obj_tag(v___x_4723_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4723_, 1);
                    v___x_4724_ = crate::leanh::lean_box(0);
                    v___x_4725_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4726_ = lean_nat_add(v_snd_4717_, v___x_4725_);
                    crate::leanh::lean_dec(v_snd_4717_);
                    if v_isShared_4720_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4719_, 1, v___x_4726_);
                        crate::leanh::lean_ctor_set(v___x_4719_, 0, v___x_4724_);
                        v___x_4728_ = v___x_4719_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4732_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4724_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4732_, 1, v___x_4726_);
                        v___x_4728_ = v_reuseFailAlloc_4732_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4719_);
                    crate::leanh::lean_dec(v_snd_4717_);
                    v_a_4733_ = crate::leanh::lean_ctor_get(v___x_4723_, 0);
                    v_isSharedCheck_4740_ = (!crate::leanh::lean_is_exclusive(v___x_4723_)) as u8;
                    if v_isSharedCheck_4740_ == 0 {
                        v___x_4735_ = v___x_4723_;
                        v_isShared_4736_ = v_isSharedCheck_4740_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4733_);
                        crate::leanh::lean_dec(v___x_4723_);
                        v___x_4735_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4739_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4739_, 0, v_a_4733_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_4743_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_4744_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_4745_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_4746_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_4747_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_4748_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4749_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4750_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4751_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4752_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4753_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4754_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4755_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4756_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4757_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4758_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4759_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4760_: u8 = 0;
    let mut v_sz_boxed_4761_: usize = 0;
    let mut v_i_boxed_4762_: usize = 0;
    let mut v_res_4763_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4760_ = (crate::leanh::lean_unbox(v_isLower_4743_) as u8);
    v_sz_boxed_4761_ = crate::leanh::lean_unbox_usize(v_sz_4745_);
    crate::leanh::lean_dec(v_sz_4745_);
    v_i_boxed_4762_ = crate::leanh::lean_unbox_usize(v_i_4746_);
    crate::leanh::lean_dec(v_i_4746_);
    v_res_4763_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9_spec__11(v_isLower_boxed_4760_, v_as_4744_, v_sz_boxed_4761_, v_i_boxed_4762_, v_b_4747_, v___y_4748_, v___y_4749_, v___y_4750_, v___y_4751_, v___y_4752_, v___y_4753_, v___y_4754_, v___y_4755_, v___y_4756_, v___y_4757_, v___y_4758_);
    crate::leanh::lean_dec(v___y_4758_);
    crate::leanh::lean_dec_ref(v___y_4757_);
    crate::leanh::lean_dec(v___y_4756_);
    crate::leanh::lean_dec_ref(v___y_4755_);
    crate::leanh::lean_dec(v___y_4754_);
    crate::leanh::lean_dec_ref(v___y_4753_);
    crate::leanh::lean_dec(v___y_4752_);
    crate::leanh::lean_dec_ref(v___y_4751_);
    crate::leanh::lean_dec(v___y_4750_);
    crate::leanh::lean_dec(v___y_4749_);
    crate::leanh::lean_dec(v___y_4748_);
    crate::leanh::lean_dec_ref(v_as_4744_);
    return v_res_4763_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(
    mut v_isLower_4764_: u8,
    mut v_as_4765_: *mut crate::leanh::LeanObject,
    mut v_sz_4766_: usize,
    mut v_i_4767_: usize,
    mut v_b_4768_: *mut crate::leanh::LeanObject,
    mut v___y_4769_: *mut crate::leanh::LeanObject,
    mut v___y_4770_: *mut crate::leanh::LeanObject,
    mut v___y_4771_: *mut crate::leanh::LeanObject,
    mut v___y_4772_: *mut crate::leanh::LeanObject,
    mut v___y_4773_: *mut crate::leanh::LeanObject,
    mut v___y_4774_: *mut crate::leanh::LeanObject,
    mut v___y_4775_: *mut crate::leanh::LeanObject,
    mut v___y_4776_: *mut crate::leanh::LeanObject,
    mut v___y_4777_: *mut crate::leanh::LeanObject,
    mut v___y_4778_: *mut crate::leanh::LeanObject,
    mut v___y_4779_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4781_: u8 = 0;
    let mut v___x_4782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4783_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4786_: u8 = 0;
    let mut v_a_4787_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4789_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4792_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4795_: usize = 0;
    let mut v___x_4796_: usize = 0;
    let mut v___x_4797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4802_: u8 = 0;
    let mut v___x_4804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4806_: u8 = 0;
    let mut v_isSharedCheck_4807_: u8 = 0;
    let mut v_unused_4808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4781_ = lean_usize_dec_lt(v_i_4767_, v_sz_4766_);
                if v___x_4781_ == 0 {
                    v___x_4782_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4782_, 0, v_b_4768_);
                    return v___x_4782_;
                } else {
                    v_snd_4783_ = crate::leanh::lean_ctor_get(v_b_4768_, 1);
                    v_isSharedCheck_4807_ = (!crate::leanh::lean_is_exclusive(v_b_4768_)) as u8;
                    if v_isSharedCheck_4807_ == 0 {
                        v_unused_4808_ = crate::leanh::lean_ctor_get(v_b_4768_, 0);
                        crate::leanh::lean_dec(v_unused_4808_);
                        v___x_4785_ = v_b_4768_;
                        v_isShared_4786_ = v_isSharedCheck_4807_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4783_);
                        crate::leanh::lean_dec(v_b_4768_);
                        v___x_4785_ = crate::leanh::lean_box(0);
                        v_isShared_4786_ = v_isSharedCheck_4807_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4787_ = lean_array_uget_borrowed(v_as_4765_, v_i_4767_);
                v___x_4788_ = crate::leanh::lean_box(0);
                v___x_4789_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_4783_, v_isLower_4764_, v_a_4787_, v___x_4788_, v___y_4769_, v___y_4770_, v___y_4771_, v___y_4772_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_, v___y_4777_, v___y_4778_, v___y_4779_);
                if crate::leanh::lean_obj_tag(v___x_4789_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_4789_, 1);
                    v___x_4790_ = crate::leanh::lean_box(0);
                    v___x_4791_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_4792_ = lean_nat_add(v_snd_4783_, v___x_4791_);
                    crate::leanh::lean_dec(v_snd_4783_);
                    if v_isShared_4786_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4785_, 1, v___x_4792_);
                        crate::leanh::lean_ctor_set(v___x_4785_, 0, v___x_4790_);
                        v___x_4794_ = v___x_4785_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4798_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 0, v___x_4790_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4798_, 1, v___x_4792_);
                        v___x_4794_ = v_reuseFailAlloc_4798_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4785_);
                    crate::leanh::lean_dec(v_snd_4783_);
                    v_a_4799_ = crate::leanh::lean_ctor_get(v___x_4789_, 0);
                    v_isSharedCheck_4806_ = (!crate::leanh::lean_is_exclusive(v___x_4789_)) as u8;
                    if v_isSharedCheck_4806_ == 0 {
                        v___x_4801_ = v___x_4789_;
                        v_isShared_4802_ = v_isSharedCheck_4806_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4799_);
                        crate::leanh::lean_dec(v___x_4789_);
                        v___x_4801_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_4805_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4805_, 0, v_a_4799_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_4809_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_4810_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_4811_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_4812_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_4813_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_4814_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4815_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4816_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4817_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4818_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4819_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4820_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4821_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4822_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4823_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4824_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4825_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_4826_: u8 = 0;
    let mut v_sz_boxed_4827_: usize = 0;
    let mut v_i_boxed_4828_: usize = 0;
    let mut v_res_4829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4826_ = (crate::leanh::lean_unbox(v_isLower_4809_) as u8);
    v_sz_boxed_4827_ = crate::leanh::lean_unbox_usize(v_sz_4811_);
    crate::leanh::lean_dec(v_sz_4811_);
    v_i_boxed_4828_ = crate::leanh::lean_unbox_usize(v_i_4812_);
    crate::leanh::lean_dec(v_i_4812_);
    v_res_4829_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_boxed_4826_, v_as_4810_, v_sz_boxed_4827_, v_i_boxed_4828_, v_b_4813_, v___y_4814_, v___y_4815_, v___y_4816_, v___y_4817_, v___y_4818_, v___y_4819_, v___y_4820_, v___y_4821_, v___y_4822_, v___y_4823_, v___y_4824_);
    crate::leanh::lean_dec(v___y_4824_);
    crate::leanh::lean_dec_ref(v___y_4823_);
    crate::leanh::lean_dec(v___y_4822_);
    crate::leanh::lean_dec_ref(v___y_4821_);
    crate::leanh::lean_dec(v___y_4820_);
    crate::leanh::lean_dec_ref(v___y_4819_);
    crate::leanh::lean_dec(v___y_4818_);
    crate::leanh::lean_dec_ref(v___y_4817_);
    crate::leanh::lean_dec(v___y_4816_);
    crate::leanh::lean_dec(v___y_4815_);
    crate::leanh::lean_dec(v___y_4814_);
    crate::leanh::lean_dec_ref(v_as_4810_);
    return v_res_4829_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(
    mut v_init_4830_: *mut crate::leanh::LeanObject,
    mut v_isLower_4831_: u8,
    mut v_n_4832_: *mut crate::leanh::LeanObject,
    mut v_b_4833_: *mut crate::leanh::LeanObject,
    mut v___y_4834_: *mut crate::leanh::LeanObject,
    mut v___y_4835_: *mut crate::leanh::LeanObject,
    mut v___y_4836_: *mut crate::leanh::LeanObject,
    mut v___y_4837_: *mut crate::leanh::LeanObject,
    mut v___y_4838_: *mut crate::leanh::LeanObject,
    mut v___y_4839_: *mut crate::leanh::LeanObject,
    mut v___y_4840_: *mut crate::leanh::LeanObject,
    mut v___y_4841_: *mut crate::leanh::LeanObject,
    mut v___y_4842_: *mut crate::leanh::LeanObject,
    mut v___y_4843_: *mut crate::leanh::LeanObject,
    mut v___y_4844_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_4846_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4847_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4848_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4849_: usize = 0;
    let mut v___x_4850_: usize = 0;
    let mut v___x_4851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4852_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4854_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4855_: u8 = 0;
    let mut v_fst_4856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4864_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4865_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4866_: u8 = 0;
    let mut v_a_4867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4870_: u8 = 0;
    let mut v___x_4872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4874_: u8 = 0;
    let mut v_vs_4875_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4877_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_4878_: usize = 0;
    let mut v___x_4879_: usize = 0;
    let mut v___x_4880_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4881_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4883_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4884_: u8 = 0;
    let mut v_fst_4885_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4886_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4887_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4889_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4890_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_4891_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4893_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4894_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4895_: u8 = 0;
    let mut v_a_4896_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4898_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4899_: u8 = 0;
    let mut v___x_4901_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4902_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4903_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_4832_) == 0 {
                    v_cs_4846_ = crate::leanh::lean_ctor_get(v_n_4832_, 0);
                    v___x_4847_ = crate::leanh::lean_box(0);
                    v___x_4848_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4848_, 0, v___x_4847_);
                    crate::leanh::lean_ctor_set(v___x_4848_, 1, v_b_4833_);
                    v_sz_4849_ = lean_array_size(v_cs_4846_);
                    v___x_4850_ = 0usize;
                    v___x_4851_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_4830_, v_isLower_4831_, v_cs_4846_, v_sz_4849_, v___x_4850_, v___x_4848_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
                    if crate::leanh::lean_obj_tag(v___x_4851_) == 0 {
                        v_a_4852_ = crate::leanh::lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4866_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4866_ == 0 {
                            v___x_4854_ = v___x_4851_;
                            v_isShared_4855_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4852_);
                            crate::leanh::lean_dec(v___x_4851_);
                            v___x_4854_ = crate::leanh::lean_box(0);
                            v_isShared_4855_ = v_isSharedCheck_4866_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_4867_ = crate::leanh::lean_ctor_get(v___x_4851_, 0);
                        v_isSharedCheck_4874_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4851_)) as u8;
                        if v_isSharedCheck_4874_ == 0 {
                            v___x_4869_ = v___x_4851_;
                            v_isShared_4870_ = v_isSharedCheck_4874_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4867_);
                            crate::leanh::lean_dec(v___x_4851_);
                            v___x_4869_ = crate::leanh::lean_box(0);
                            v_isShared_4870_ = v_isSharedCheck_4874_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_4875_ = crate::leanh::lean_ctor_get(v_n_4832_, 0);
                    v___x_4876_ = crate::leanh::lean_box(0);
                    v___x_4877_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4877_, 0, v___x_4876_);
                    crate::leanh::lean_ctor_set(v___x_4877_, 1, v_b_4833_);
                    v_sz_4878_ = lean_array_size(v_vs_4875_);
                    v___x_4879_ = 0usize;
                    v___x_4880_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__9(v_isLower_4831_, v_vs_4875_, v_sz_4878_, v___x_4879_, v___x_4877_, v___y_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_, v___y_4839_, v___y_4840_, v___y_4841_, v___y_4842_, v___y_4843_, v___y_4844_);
                    if crate::leanh::lean_obj_tag(v___x_4880_) == 0 {
                        v_a_4881_ = crate::leanh::lean_ctor_get(v___x_4880_, 0);
                        v_isSharedCheck_4895_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4880_)) as u8;
                        if v_isSharedCheck_4895_ == 0 {
                            v___x_4883_ = v___x_4880_;
                            v_isShared_4884_ = v_isSharedCheck_4895_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4881_);
                            crate::leanh::lean_dec(v___x_4880_);
                            v___x_4883_ = crate::leanh::lean_box(0);
                            v_isShared_4884_ = v_isSharedCheck_4895_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_4896_ = crate::leanh::lean_ctor_get(v___x_4880_, 0);
                        v_isSharedCheck_4903_ =
                            (!crate::leanh::lean_is_exclusive(v___x_4880_)) as u8;
                        if v_isSharedCheck_4903_ == 0 {
                            v___x_4898_ = v___x_4880_;
                            v_isShared_4899_ = v_isSharedCheck_4903_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_4896_);
                            crate::leanh::lean_dec(v___x_4880_);
                            v___x_4898_ = crate::leanh::lean_box(0);
                            v_isShared_4899_ = v_isSharedCheck_4903_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_4856_ = crate::leanh::lean_ctor_get(v_a_4852_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4856_) == 0 {
                    v_snd_4857_ = crate::leanh::lean_ctor_get(v_a_4852_, 1);
                    crate::leanh::lean_inc(v_snd_4857_);
                    crate::leanh::lean_dec(v_a_4852_);
                    v___x_4858_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4858_, 0, v_snd_4857_);
                    if v_isShared_4855_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4854_, 0, v___x_4858_);
                        v___x_4860_ = v___x_4854_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_4861_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4861_, 0, v___x_4858_);
                        v___x_4860_ = v_reuseFailAlloc_4861_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4856_);
                    crate::leanh::lean_dec(v_a_4852_);
                    v_val_4862_ = crate::leanh::lean_ctor_get(v_fst_4856_, 0);
                    crate::leanh::lean_inc(v_val_4862_);
                    crate::leanh::lean_dec_ref_known(v_fst_4856_, 1);
                    if v_isShared_4855_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4854_, 0, v_val_4862_);
                        v___x_4864_ = v___x_4854_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4865_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4865_, 0, v_val_4862_);
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
                    v_reuseFailAlloc_4873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4873_, 0, v_a_4867_);
                    v___x_4872_ = v_reuseFailAlloc_4873_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_4872_;
            }
            6 => {
                v_fst_4885_ = crate::leanh::lean_ctor_get(v_a_4881_, 0);
                if crate::leanh::lean_obj_tag(v_fst_4885_) == 0 {
                    v_snd_4886_ = crate::leanh::lean_ctor_get(v_a_4881_, 1);
                    crate::leanh::lean_inc(v_snd_4886_);
                    crate::leanh::lean_dec(v_a_4881_);
                    v___x_4887_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4887_, 0, v_snd_4886_);
                    if v_isShared_4884_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4883_, 0, v___x_4887_);
                        v___x_4889_ = v___x_4883_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_4890_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
                        v___x_4889_ = v_reuseFailAlloc_4890_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_4885_);
                    crate::leanh::lean_dec(v_a_4881_);
                    v_val_4891_ = crate::leanh::lean_ctor_get(v_fst_4885_, 0);
                    crate::leanh::lean_inc(v_val_4891_);
                    crate::leanh::lean_dec_ref_known(v_fst_4885_, 1);
                    if v_isShared_4884_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4883_, 0, v_val_4891_);
                        v___x_4893_ = v___x_4883_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_4894_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_val_4891_);
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
                    v_reuseFailAlloc_4902_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4902_, 0, v_a_4896_);
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
    mut v_init_4904_: *mut crate::leanh::LeanObject,
    mut v_isLower_4905_: u8,
    mut v_as_4906_: *mut crate::leanh::LeanObject,
    mut v_sz_4907_: usize,
    mut v_i_4908_: usize,
    mut v_b_4909_: *mut crate::leanh::LeanObject,
    mut v___y_4910_: *mut crate::leanh::LeanObject,
    mut v___y_4911_: *mut crate::leanh::LeanObject,
    mut v___y_4912_: *mut crate::leanh::LeanObject,
    mut v___y_4913_: *mut crate::leanh::LeanObject,
    mut v___y_4914_: *mut crate::leanh::LeanObject,
    mut v___y_4915_: *mut crate::leanh::LeanObject,
    mut v___y_4916_: *mut crate::leanh::LeanObject,
    mut v___y_4917_: *mut crate::leanh::LeanObject,
    mut v___y_4918_: *mut crate::leanh::LeanObject,
    mut v___y_4919_: *mut crate::leanh::LeanObject,
    mut v___y_4920_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_4922_: u8 = 0;
    let mut v___x_4923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_4924_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4926_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4927_: u8 = 0;
    let mut v_a_4928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4933_: u8 = 0;
    let mut v___x_4934_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4938_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4940_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_4941_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4942_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4944_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4945_: usize = 0;
    let mut v___x_4946_: usize = 0;
    let mut v_reuseFailAlloc_4948_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4949_: u8 = 0;
    let mut v_a_4950_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_4952_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_4953_: u8 = 0;
    let mut v___x_4955_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_4956_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_4957_: u8 = 0;
    let mut v_isSharedCheck_4958_: u8 = 0;
    let mut v_unused_4959_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_4922_ = lean_usize_dec_lt(v_i_4908_, v_sz_4907_);
                if v___x_4922_ == 0 {
                    v___x_4923_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4923_, 0, v_b_4909_);
                    return v___x_4923_;
                } else {
                    v_snd_4924_ = crate::leanh::lean_ctor_get(v_b_4909_, 1);
                    v_isSharedCheck_4958_ = (!crate::leanh::lean_is_exclusive(v_b_4909_)) as u8;
                    if v_isSharedCheck_4958_ == 0 {
                        v_unused_4959_ = crate::leanh::lean_ctor_get(v_b_4909_, 0);
                        crate::leanh::lean_dec(v_unused_4959_);
                        v___x_4926_ = v_b_4909_;
                        v_isShared_4927_ = v_isSharedCheck_4958_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_4924_);
                        crate::leanh::lean_dec(v_b_4909_);
                        v___x_4926_ = crate::leanh::lean_box(0);
                        v_isShared_4927_ = v_isSharedCheck_4958_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_4928_ = lean_array_uget_borrowed(v_as_4906_, v_i_4908_);
                crate::leanh::lean_inc(v_snd_4924_);
                v___x_4929_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_4904_, v_isLower_4905_, v_a_4928_, v_snd_4924_, v___y_4910_, v___y_4911_, v___y_4912_, v___y_4913_, v___y_4914_, v___y_4915_, v___y_4916_, v___y_4917_, v___y_4918_, v___y_4919_, v___y_4920_);
                if crate::leanh::lean_obj_tag(v___x_4929_) == 0 {
                    v_a_4930_ = crate::leanh::lean_ctor_get(v___x_4929_, 0);
                    v_isSharedCheck_4949_ = (!crate::leanh::lean_is_exclusive(v___x_4929_)) as u8;
                    if v_isSharedCheck_4949_ == 0 {
                        v___x_4932_ = v___x_4929_;
                        v_isShared_4933_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4930_);
                        crate::leanh::lean_dec(v___x_4929_);
                        v___x_4932_ = crate::leanh::lean_box(0);
                        v_isShared_4933_ = v_isSharedCheck_4949_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4926_);
                    crate::leanh::lean_dec(v_snd_4924_);
                    v_a_4950_ = crate::leanh::lean_ctor_get(v___x_4929_, 0);
                    v_isSharedCheck_4957_ = (!crate::leanh::lean_is_exclusive(v___x_4929_)) as u8;
                    if v_isSharedCheck_4957_ == 0 {
                        v___x_4952_ = v___x_4929_;
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_4950_);
                        crate::leanh::lean_dec(v___x_4929_);
                        v___x_4952_ = crate::leanh::lean_box(0);
                        v_isShared_4953_ = v_isSharedCheck_4957_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_4930_) == 0 {
                    v___x_4934_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_4934_, 0, v_a_4930_);
                    if v_isShared_4927_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4926_, 0, v___x_4934_);
                        v___x_4936_ = v___x_4926_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_4940_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4934_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4940_, 1, v_snd_4924_);
                        v___x_4936_ = v_reuseFailAlloc_4940_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_4932_);
                    crate::leanh::lean_dec(v_snd_4924_);
                    v_a_4941_ = crate::leanh::lean_ctor_get(v_a_4930_, 0);
                    crate::leanh::lean_inc(v_a_4941_);
                    crate::leanh::lean_dec_ref_known(v_a_4930_, 1);
                    v___x_4942_ = crate::leanh::lean_box(0);
                    if v_isShared_4927_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_4926_, 1, v_a_4941_);
                        crate::leanh::lean_ctor_set(v___x_4926_, 0, v___x_4942_);
                        v___x_4944_ = v___x_4926_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_4948_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 0, v___x_4942_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_4948_, 1, v_a_4941_);
                        v___x_4944_ = v_reuseFailAlloc_4948_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_4933_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_4932_, 0, v___x_4936_);
                    v___x_4938_ = v___x_4932_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_4939_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4936_);
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
                    v_reuseFailAlloc_4956_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_4956_, 0, v_a_4950_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_4960_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_isLower_4961_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_4962_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_4963_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_4964_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_4965_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_4966_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_4967_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_4968_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_4969_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_4970_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_4971_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_4972_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_4973_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_4974_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_4975_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_4976_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_4977_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_isLower_boxed_4978_: u8 = 0;
    let mut v_sz_boxed_4979_: usize = 0;
    let mut v_i_boxed_4980_: usize = 0;
    let mut v_res_4981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4978_ = (crate::leanh::lean_unbox(v_isLower_4961_) as u8);
    v_sz_boxed_4979_ = crate::leanh::lean_unbox_usize(v_sz_4963_);
    crate::leanh::lean_dec(v_sz_4963_);
    v_i_boxed_4980_ = crate::leanh::lean_unbox_usize(v_i_4964_);
    crate::leanh::lean_dec(v_i_4964_);
    v_res_4981_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4_spec__8(v_init_4960_, v_isLower_boxed_4978_, v_as_4962_, v_sz_boxed_4979_, v_i_boxed_4980_, v_b_4965_, v___y_4966_, v___y_4967_, v___y_4968_, v___y_4969_, v___y_4970_, v___y_4971_, v___y_4972_, v___y_4973_, v___y_4974_, v___y_4975_, v___y_4976_);
    crate::leanh::lean_dec(v___y_4976_);
    crate::leanh::lean_dec_ref(v___y_4975_);
    crate::leanh::lean_dec(v___y_4974_);
    crate::leanh::lean_dec_ref(v___y_4973_);
    crate::leanh::lean_dec(v___y_4972_);
    crate::leanh::lean_dec_ref(v___y_4971_);
    crate::leanh::lean_dec(v___y_4970_);
    crate::leanh::lean_dec_ref(v___y_4969_);
    crate::leanh::lean_dec(v___y_4968_);
    crate::leanh::lean_dec(v___y_4967_);
    crate::leanh::lean_dec(v___y_4966_);
    crate::leanh::lean_dec_ref(v_as_4962_);
    crate::leanh::lean_dec(v_init_4960_);
    return v_res_4981_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4___boxed(
    mut v_init_4982_: *mut crate::leanh::LeanObject,
    mut v_isLower_4983_: *mut crate::leanh::LeanObject,
    mut v_n_4984_: *mut crate::leanh::LeanObject,
    mut v_b_4985_: *mut crate::leanh::LeanObject,
    mut v___y_4986_: *mut crate::leanh::LeanObject,
    mut v___y_4987_: *mut crate::leanh::LeanObject,
    mut v___y_4988_: *mut crate::leanh::LeanObject,
    mut v___y_4989_: *mut crate::leanh::LeanObject,
    mut v___y_4990_: *mut crate::leanh::LeanObject,
    mut v___y_4991_: *mut crate::leanh::LeanObject,
    mut v___y_4992_: *mut crate::leanh::LeanObject,
    mut v___y_4993_: *mut crate::leanh::LeanObject,
    mut v___y_4994_: *mut crate::leanh::LeanObject,
    mut v___y_4995_: *mut crate::leanh::LeanObject,
    mut v___y_4996_: *mut crate::leanh::LeanObject,
    mut v___y_4997_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_boxed_4998_: u8 = 0;
    let mut v_res_4999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_4998_ = (crate::leanh::lean_unbox(v_isLower_4983_) as u8);
    v_res_4999_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_4982_, v_isLower_boxed_4998_, v_n_4984_, v_b_4985_, v___y_4986_, v___y_4987_, v___y_4988_, v___y_4989_, v___y_4990_, v___y_4991_, v___y_4992_, v___y_4993_, v___y_4994_, v___y_4995_, v___y_4996_);
    crate::leanh::lean_dec(v___y_4996_);
    crate::leanh::lean_dec_ref(v___y_4995_);
    crate::leanh::lean_dec(v___y_4994_);
    crate::leanh::lean_dec_ref(v___y_4993_);
    crate::leanh::lean_dec(v___y_4992_);
    crate::leanh::lean_dec_ref(v___y_4991_);
    crate::leanh::lean_dec(v___y_4990_);
    crate::leanh::lean_dec_ref(v___y_4989_);
    crate::leanh::lean_dec(v___y_4988_);
    crate::leanh::lean_dec(v___y_4987_);
    crate::leanh::lean_dec(v___y_4986_);
    crate::leanh::lean_dec_ref(v_n_4984_);
    crate::leanh::lean_dec(v_init_4982_);
    return v_res_4999_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(
    mut v_isLower_5000_: u8,
    mut v_as_5001_: *mut crate::leanh::LeanObject,
    mut v_sz_5002_: usize,
    mut v_i_5003_: usize,
    mut v_b_5004_: *mut crate::leanh::LeanObject,
    mut v___y_5005_: *mut crate::leanh::LeanObject,
    mut v___y_5006_: *mut crate::leanh::LeanObject,
    mut v___y_5007_: *mut crate::leanh::LeanObject,
    mut v___y_5008_: *mut crate::leanh::LeanObject,
    mut v___y_5009_: *mut crate::leanh::LeanObject,
    mut v___y_5010_: *mut crate::leanh::LeanObject,
    mut v___y_5011_: *mut crate::leanh::LeanObject,
    mut v___y_5012_: *mut crate::leanh::LeanObject,
    mut v___y_5013_: *mut crate::leanh::LeanObject,
    mut v___y_5014_: *mut crate::leanh::LeanObject,
    mut v___y_5015_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5017_: u8 = 0;
    let mut v___x_5018_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5019_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5022_: u8 = 0;
    let mut v_a_5023_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5024_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5025_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5026_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5027_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5028_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5030_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5031_: usize = 0;
    let mut v___x_5032_: usize = 0;
    let mut v_reuseFailAlloc_5034_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5037_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5038_: u8 = 0;
    let mut v___x_5040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5041_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5042_: u8 = 0;
    let mut v_isSharedCheck_5043_: u8 = 0;
    let mut v_unused_5044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5017_ = lean_usize_dec_lt(v_i_5003_, v_sz_5002_);
                if v___x_5017_ == 0 {
                    v___x_5018_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5018_, 0, v_b_5004_);
                    return v___x_5018_;
                } else {
                    v_snd_5019_ = crate::leanh::lean_ctor_get(v_b_5004_, 1);
                    v_isSharedCheck_5043_ = (!crate::leanh::lean_is_exclusive(v_b_5004_)) as u8;
                    if v_isSharedCheck_5043_ == 0 {
                        v_unused_5044_ = crate::leanh::lean_ctor_get(v_b_5004_, 0);
                        crate::leanh::lean_dec(v_unused_5044_);
                        v___x_5021_ = v_b_5004_;
                        v_isShared_5022_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5019_);
                        crate::leanh::lean_dec(v_b_5004_);
                        v___x_5021_ = crate::leanh::lean_box(0);
                        v_isShared_5022_ = v_isSharedCheck_5043_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5023_ = lean_array_uget_borrowed(v_as_5001_, v_i_5003_);
                v___x_5024_ = crate::leanh::lean_box(0);
                v___x_5025_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_5019_, v_isLower_5000_, v_a_5023_, v___x_5024_, v___y_5005_, v___y_5006_, v___y_5007_, v___y_5008_, v___y_5009_, v___y_5010_, v___y_5011_, v___y_5012_, v___y_5013_, v___y_5014_, v___y_5015_);
                if crate::leanh::lean_obj_tag(v___x_5025_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5025_, 1);
                    v___x_5026_ = crate::leanh::lean_box(0);
                    v___x_5027_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5028_ = lean_nat_add(v_snd_5019_, v___x_5027_);
                    crate::leanh::lean_dec(v_snd_5019_);
                    if v_isShared_5022_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5021_, 1, v___x_5028_);
                        crate::leanh::lean_ctor_set(v___x_5021_, 0, v___x_5026_);
                        v___x_5030_ = v___x_5021_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5034_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5034_, 0, v___x_5026_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5034_, 1, v___x_5028_);
                        v___x_5030_ = v_reuseFailAlloc_5034_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5021_);
                    crate::leanh::lean_dec(v_snd_5019_);
                    v_a_5035_ = crate::leanh::lean_ctor_get(v___x_5025_, 0);
                    v_isSharedCheck_5042_ = (!crate::leanh::lean_is_exclusive(v___x_5025_)) as u8;
                    if v_isSharedCheck_5042_ == 0 {
                        v___x_5037_ = v___x_5025_;
                        v_isShared_5038_ = v_isSharedCheck_5042_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5035_);
                        crate::leanh::lean_dec(v___x_5025_);
                        v___x_5037_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5041_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5041_, 0, v_a_5035_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_5045_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_5046_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_5047_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_5048_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_5049_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5050_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5051_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5052_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5053_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5054_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5055_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5056_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5057_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5058_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5059_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5060_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5061_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5062_: u8 = 0;
    let mut v_sz_boxed_5063_: usize = 0;
    let mut v_i_boxed_5064_: usize = 0;
    let mut v_res_5065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5062_ = (crate::leanh::lean_unbox(v_isLower_5045_) as u8);
    v_sz_boxed_5063_ = crate::leanh::lean_unbox_usize(v_sz_5047_);
    crate::leanh::lean_dec(v_sz_5047_);
    v_i_boxed_5064_ = crate::leanh::lean_unbox_usize(v_i_5048_);
    crate::leanh::lean_dec(v_i_5048_);
    v_res_5065_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5_spec__11(v_isLower_boxed_5062_, v_as_5046_, v_sz_boxed_5063_, v_i_boxed_5064_, v_b_5049_, v___y_5050_, v___y_5051_, v___y_5052_, v___y_5053_, v___y_5054_, v___y_5055_, v___y_5056_, v___y_5057_, v___y_5058_, v___y_5059_, v___y_5060_);
    crate::leanh::lean_dec(v___y_5060_);
    crate::leanh::lean_dec_ref(v___y_5059_);
    crate::leanh::lean_dec(v___y_5058_);
    crate::leanh::lean_dec_ref(v___y_5057_);
    crate::leanh::lean_dec(v___y_5056_);
    crate::leanh::lean_dec_ref(v___y_5055_);
    crate::leanh::lean_dec(v___y_5054_);
    crate::leanh::lean_dec_ref(v___y_5053_);
    crate::leanh::lean_dec(v___y_5052_);
    crate::leanh::lean_dec(v___y_5051_);
    crate::leanh::lean_dec(v___y_5050_);
    crate::leanh::lean_dec_ref(v_as_5046_);
    return v_res_5065_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(
    mut v_isLower_5066_: u8,
    mut v_as_5067_: *mut crate::leanh::LeanObject,
    mut v_sz_5068_: usize,
    mut v_i_5069_: usize,
    mut v_b_5070_: *mut crate::leanh::LeanObject,
    mut v___y_5071_: *mut crate::leanh::LeanObject,
    mut v___y_5072_: *mut crate::leanh::LeanObject,
    mut v___y_5073_: *mut crate::leanh::LeanObject,
    mut v___y_5074_: *mut crate::leanh::LeanObject,
    mut v___y_5075_: *mut crate::leanh::LeanObject,
    mut v___y_5076_: *mut crate::leanh::LeanObject,
    mut v___y_5077_: *mut crate::leanh::LeanObject,
    mut v___y_5078_: *mut crate::leanh::LeanObject,
    mut v___y_5079_: *mut crate::leanh::LeanObject,
    mut v___y_5080_: *mut crate::leanh::LeanObject,
    mut v___y_5081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5083_: u8 = 0;
    let mut v___x_5084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5085_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5087_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5088_: u8 = 0;
    let mut v_a_5089_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5090_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5091_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5092_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5093_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5097_: usize = 0;
    let mut v___x_5098_: usize = 0;
    let mut v___x_5099_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5103_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5104_: u8 = 0;
    let mut v___x_5106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5107_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5108_: u8 = 0;
    let mut v_isSharedCheck_5109_: u8 = 0;
    let mut v_unused_5110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5083_ = lean_usize_dec_lt(v_i_5069_, v_sz_5068_);
                if v___x_5083_ == 0 {
                    v___x_5084_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5084_, 0, v_b_5070_);
                    return v___x_5084_;
                } else {
                    v_snd_5085_ = crate::leanh::lean_ctor_get(v_b_5070_, 1);
                    v_isSharedCheck_5109_ = (!crate::leanh::lean_is_exclusive(v_b_5070_)) as u8;
                    if v_isSharedCheck_5109_ == 0 {
                        v_unused_5110_ = crate::leanh::lean_ctor_get(v_b_5070_, 0);
                        crate::leanh::lean_dec(v_unused_5110_);
                        v___x_5087_ = v_b_5070_;
                        v_isShared_5088_ = v_isSharedCheck_5109_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5085_);
                        crate::leanh::lean_dec(v_b_5070_);
                        v___x_5087_ = crate::leanh::lean_box(0);
                        v_isShared_5088_ = v_isSharedCheck_5109_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5089_ = lean_array_uget_borrowed(v_as_5067_, v_i_5069_);
                v___x_5090_ = crate::leanh::lean_box(0);
                v___x_5091_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__1(v_snd_5085_, v_isLower_5066_, v_a_5089_, v___x_5090_, v___y_5071_, v___y_5072_, v___y_5073_, v___y_5074_, v___y_5075_, v___y_5076_, v___y_5077_, v___y_5078_, v___y_5079_, v___y_5080_, v___y_5081_);
                if crate::leanh::lean_obj_tag(v___x_5091_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5091_, 1);
                    v___x_5092_ = crate::leanh::lean_box(0);
                    v___x_5093_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5094_ = lean_nat_add(v_snd_5085_, v___x_5093_);
                    crate::leanh::lean_dec(v_snd_5085_);
                    if v_isShared_5088_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5087_, 1, v___x_5094_);
                        crate::leanh::lean_ctor_set(v___x_5087_, 0, v___x_5092_);
                        v___x_5096_ = v___x_5087_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5100_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5100_, 0, v___x_5092_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5100_, 1, v___x_5094_);
                        v___x_5096_ = v_reuseFailAlloc_5100_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5087_);
                    crate::leanh::lean_dec(v_snd_5085_);
                    v_a_5101_ = crate::leanh::lean_ctor_get(v___x_5091_, 0);
                    v_isSharedCheck_5108_ = (!crate::leanh::lean_is_exclusive(v___x_5091_)) as u8;
                    if v_isSharedCheck_5108_ == 0 {
                        v___x_5103_ = v___x_5091_;
                        v_isShared_5104_ = v_isSharedCheck_5108_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5101_);
                        crate::leanh::lean_dec(v___x_5091_);
                        v___x_5103_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5107_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5107_, 0, v_a_5101_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_5111_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_5112_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_5113_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_5114_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_5115_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5116_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5117_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5118_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5119_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5120_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5121_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5122_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5123_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5124_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5125_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5126_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5127_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_isLower_boxed_5128_: u8 = 0;
    let mut v_sz_boxed_5129_: usize = 0;
    let mut v_i_boxed_5130_: usize = 0;
    let mut v_res_5131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5128_ = (crate::leanh::lean_unbox(v_isLower_5111_) as u8);
    v_sz_boxed_5129_ = crate::leanh::lean_unbox_usize(v_sz_5113_);
    crate::leanh::lean_dec(v_sz_5113_);
    v_i_boxed_5130_ = crate::leanh::lean_unbox_usize(v_i_5114_);
    crate::leanh::lean_dec(v_i_5114_);
    v_res_5131_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_boxed_5128_, v_as_5112_, v_sz_boxed_5129_, v_i_boxed_5130_, v_b_5115_, v___y_5116_, v___y_5117_, v___y_5118_, v___y_5119_, v___y_5120_, v___y_5121_, v___y_5122_, v___y_5123_, v___y_5124_, v___y_5125_, v___y_5126_);
    crate::leanh::lean_dec(v___y_5126_);
    crate::leanh::lean_dec_ref(v___y_5125_);
    crate::leanh::lean_dec(v___y_5124_);
    crate::leanh::lean_dec_ref(v___y_5123_);
    crate::leanh::lean_dec(v___y_5122_);
    crate::leanh::lean_dec_ref(v___y_5121_);
    crate::leanh::lean_dec(v___y_5120_);
    crate::leanh::lean_dec_ref(v___y_5119_);
    crate::leanh::lean_dec(v___y_5118_);
    crate::leanh::lean_dec(v___y_5117_);
    crate::leanh::lean_dec(v___y_5116_);
    crate::leanh::lean_dec_ref(v_as_5112_);
    return v_res_5131_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(
    mut v_isLower_5132_: u8,
    mut v_t_5133_: *mut crate::leanh::LeanObject,
    mut v_init_5134_: *mut crate::leanh::LeanObject,
    mut v___y_5135_: *mut crate::leanh::LeanObject,
    mut v___y_5136_: *mut crate::leanh::LeanObject,
    mut v___y_5137_: *mut crate::leanh::LeanObject,
    mut v___y_5138_: *mut crate::leanh::LeanObject,
    mut v___y_5139_: *mut crate::leanh::LeanObject,
    mut v___y_5140_: *mut crate::leanh::LeanObject,
    mut v___y_5141_: *mut crate::leanh::LeanObject,
    mut v___y_5142_: *mut crate::leanh::LeanObject,
    mut v___y_5143_: *mut crate::leanh::LeanObject,
    mut v___y_5144_: *mut crate::leanh::LeanObject,
    mut v___y_5145_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5149_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5153_: u8 = 0;
    let mut v_a_5154_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5157_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5158_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5160_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5161_: usize = 0;
    let mut v___x_5162_: usize = 0;
    let mut v___x_5163_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5164_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5166_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5167_: u8 = 0;
    let mut v_fst_5168_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5169_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5171_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5177_: u8 = 0;
    let mut v_a_5178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5181_: u8 = 0;
    let mut v___x_5183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5184_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5185_: u8 = 0;
    let mut v_isSharedCheck_5186_: u8 = 0;
    let mut v_a_5187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5190_: u8 = 0;
    let mut v___x_5192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5194_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5147_ = crate::leanh::lean_ctor_get(v_t_5133_, 0);
                v_tail_5148_ = crate::leanh::lean_ctor_get(v_t_5133_, 1);
                crate::leanh::lean_inc(v_init_5134_);
                v___x_5149_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__4(v_init_5134_, v_isLower_5132_, v_root_5147_, v_init_5134_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
                crate::leanh::lean_dec(v_init_5134_);
                if crate::leanh::lean_obj_tag(v___x_5149_) == 0 {
                    v_a_5150_ = crate::leanh::lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5186_ = (!crate::leanh::lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5186_ == 0 {
                        v___x_5152_ = v___x_5149_;
                        v_isShared_5153_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5150_);
                        crate::leanh::lean_dec(v___x_5149_);
                        v___x_5152_ = crate::leanh::lean_box(0);
                        v_isShared_5153_ = v_isSharedCheck_5186_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5187_ = crate::leanh::lean_ctor_get(v___x_5149_, 0);
                    v_isSharedCheck_5194_ = (!crate::leanh::lean_is_exclusive(v___x_5149_)) as u8;
                    if v_isSharedCheck_5194_ == 0 {
                        v___x_5189_ = v___x_5149_;
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5187_);
                        crate::leanh::lean_dec(v___x_5149_);
                        v___x_5189_ = crate::leanh::lean_box(0);
                        v_isShared_5190_ = v_isSharedCheck_5194_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5150_) == 0 {
                    v_a_5154_ = crate::leanh::lean_ctor_get(v_a_5150_, 0);
                    crate::leanh::lean_inc(v_a_5154_);
                    crate::leanh::lean_dec_ref_known(v_a_5150_, 1);
                    if v_isShared_5153_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5152_, 0, v_a_5154_);
                        v___x_5156_ = v___x_5152_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5157_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5157_, 0, v_a_5154_);
                        v___x_5156_ = v_reuseFailAlloc_5157_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5152_);
                    v_a_5158_ = crate::leanh::lean_ctor_get(v_a_5150_, 0);
                    crate::leanh::lean_inc(v_a_5158_);
                    crate::leanh::lean_dec_ref_known(v_a_5150_, 1);
                    v___x_5159_ = crate::leanh::lean_box(0);
                    v___x_5160_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5160_, 0, v___x_5159_);
                    crate::leanh::lean_ctor_set(v___x_5160_, 1, v_a_5158_);
                    v_sz_5161_ = lean_array_size(v_tail_5148_);
                    v___x_5162_ = 0usize;
                    v___x_5163_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2_spec__5(v_isLower_5132_, v_tail_5148_, v_sz_5161_, v___x_5162_, v___x_5160_, v___y_5135_, v___y_5136_, v___y_5137_, v___y_5138_, v___y_5139_, v___y_5140_, v___y_5141_, v___y_5142_, v___y_5143_, v___y_5144_, v___y_5145_);
                    if crate::leanh::lean_obj_tag(v___x_5163_) == 0 {
                        v_a_5164_ = crate::leanh::lean_ctor_get(v___x_5163_, 0);
                        v_isSharedCheck_5177_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5163_)) as u8;
                        if v_isSharedCheck_5177_ == 0 {
                            v___x_5166_ = v___x_5163_;
                            v_isShared_5167_ = v_isSharedCheck_5177_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5164_);
                            crate::leanh::lean_dec(v___x_5163_);
                            v___x_5166_ = crate::leanh::lean_box(0);
                            v_isShared_5167_ = v_isSharedCheck_5177_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5178_ = crate::leanh::lean_ctor_get(v___x_5163_, 0);
                        v_isSharedCheck_5185_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5163_)) as u8;
                        if v_isSharedCheck_5185_ == 0 {
                            v___x_5180_ = v___x_5163_;
                            v_isShared_5181_ = v_isSharedCheck_5185_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5178_);
                            crate::leanh::lean_dec(v___x_5163_);
                            v___x_5180_ = crate::leanh::lean_box(0);
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
                v_fst_5168_ = crate::leanh::lean_ctor_get(v_a_5164_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5168_) == 0 {
                    v_snd_5169_ = crate::leanh::lean_ctor_get(v_a_5164_, 1);
                    crate::leanh::lean_inc(v_snd_5169_);
                    crate::leanh::lean_dec(v_a_5164_);
                    if v_isShared_5167_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5166_, 0, v_snd_5169_);
                        v___x_5171_ = v___x_5166_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5172_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5172_, 0, v_snd_5169_);
                        v___x_5171_ = v_reuseFailAlloc_5172_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5168_);
                    crate::leanh::lean_dec(v_a_5164_);
                    v_val_5173_ = crate::leanh::lean_ctor_get(v_fst_5168_, 0);
                    crate::leanh::lean_inc(v_val_5173_);
                    crate::leanh::lean_dec_ref_known(v_fst_5168_, 1);
                    if v_isShared_5167_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5166_, 0, v_val_5173_);
                        v___x_5175_ = v___x_5166_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5176_, 0, v_val_5173_);
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
                    v_reuseFailAlloc_5184_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5184_, 0, v_a_5178_);
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
                    v_reuseFailAlloc_5193_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5193_, 0, v_a_5187_);
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
    mut v_isLower_5195_: *mut crate::leanh::LeanObject,
    mut v_t_5196_: *mut crate::leanh::LeanObject,
    mut v_init_5197_: *mut crate::leanh::LeanObject,
    mut v___y_5198_: *mut crate::leanh::LeanObject,
    mut v___y_5199_: *mut crate::leanh::LeanObject,
    mut v___y_5200_: *mut crate::leanh::LeanObject,
    mut v___y_5201_: *mut crate::leanh::LeanObject,
    mut v___y_5202_: *mut crate::leanh::LeanObject,
    mut v___y_5203_: *mut crate::leanh::LeanObject,
    mut v___y_5204_: *mut crate::leanh::LeanObject,
    mut v___y_5205_: *mut crate::leanh::LeanObject,
    mut v___y_5206_: *mut crate::leanh::LeanObject,
    mut v___y_5207_: *mut crate::leanh::LeanObject,
    mut v___y_5208_: *mut crate::leanh::LeanObject,
    mut v___y_5209_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_boxed_5210_: u8 = 0;
    let mut v_res_5211_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5210_ = (crate::leanh::lean_unbox(v_isLower_5195_) as u8);
    v_res_5211_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_boxed_5210_, v_t_5196_, v_init_5197_, v___y_5198_, v___y_5199_, v___y_5200_, v___y_5201_, v___y_5202_, v___y_5203_, v___y_5204_, v___y_5205_, v___y_5206_, v___y_5207_, v___y_5208_);
    crate::leanh::lean_dec(v___y_5208_);
    crate::leanh::lean_dec_ref(v___y_5207_);
    crate::leanh::lean_dec(v___y_5206_);
    crate::leanh::lean_dec_ref(v___y_5205_);
    crate::leanh::lean_dec(v___y_5204_);
    crate::leanh::lean_dec_ref(v___y_5203_);
    crate::leanh::lean_dec(v___y_5202_);
    crate::leanh::lean_dec_ref(v___y_5201_);
    crate::leanh::lean_dec(v___y_5200_);
    crate::leanh::lean_dec(v___y_5199_);
    crate::leanh::lean_dec(v___y_5198_);
    crate::leanh::lean_dec_ref(v_t_5196_);
    return v_res_5211_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(
    mut v_css_5212_: *mut crate::leanh::LeanObject,
    mut v_isLower_5213_: u8,
    mut v_a_5214_: *mut crate::leanh::LeanObject,
    mut v_a_5215_: *mut crate::leanh::LeanObject,
    mut v_a_5216_: *mut crate::leanh::LeanObject,
    mut v_a_5217_: *mut crate::leanh::LeanObject,
    mut v_a_5218_: *mut crate::leanh::LeanObject,
    mut v_a_5219_: *mut crate::leanh::LeanObject,
    mut v_a_5220_: *mut crate::leanh::LeanObject,
    mut v_a_5221_: *mut crate::leanh::LeanObject,
    mut v_a_5222_: *mut crate::leanh::LeanObject,
    mut v_a_5223_: *mut crate::leanh::LeanObject,
    mut v_a_5224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_x_5226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5227_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5229_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5230_: u8 = 0;
    let mut v___x_5231_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5233_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5234_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5235_: u8 = 0;
    let mut v_unused_5236_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5237_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5239_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5240_: u8 = 0;
    let mut v___x_5242_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5243_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5244_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_x_5226_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_5227_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs_spec__2(v_isLower_5213_, v_css_5212_, v_x_5226_, v_a_5214_, v_a_5215_, v_a_5216_, v_a_5217_, v_a_5218_, v_a_5219_, v_a_5220_, v_a_5221_, v_a_5222_, v_a_5223_, v_a_5224_);
                if crate::leanh::lean_obj_tag(v___x_5227_) == 0 {
                    v_isSharedCheck_5235_ = (!crate::leanh::lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5235_ == 0 {
                        v_unused_5236_ = crate::leanh::lean_ctor_get(v___x_5227_, 0);
                        crate::leanh::lean_dec(v_unused_5236_);
                        v___x_5229_ = v___x_5227_;
                        v_isShared_5230_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_dec(v___x_5227_);
                        v___x_5229_ = crate::leanh::lean_box(0);
                        v_isShared_5230_ = v_isSharedCheck_5235_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5237_ = crate::leanh::lean_ctor_get(v___x_5227_, 0);
                    v_isSharedCheck_5244_ = (!crate::leanh::lean_is_exclusive(v___x_5227_)) as u8;
                    if v_isSharedCheck_5244_ == 0 {
                        v___x_5239_ = v___x_5227_;
                        v_isShared_5240_ = v_isSharedCheck_5244_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5237_);
                        crate::leanh::lean_dec(v___x_5227_);
                        v___x_5239_ = crate::leanh::lean_box(0);
                        v_isShared_5240_ = v_isSharedCheck_5244_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v___x_5231_ = crate::leanh::lean_box(0);
                if v_isShared_5230_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5229_, 0, v___x_5231_);
                    v___x_5233_ = v___x_5229_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_5234_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5234_, 0, v___x_5231_);
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
                    v_reuseFailAlloc_5243_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5243_, 0, v_a_5237_);
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
    mut v_css_5245_: *mut crate::leanh::LeanObject,
    mut v_isLower_5246_: *mut crate::leanh::LeanObject,
    mut v_a_5247_: *mut crate::leanh::LeanObject,
    mut v_a_5248_: *mut crate::leanh::LeanObject,
    mut v_a_5249_: *mut crate::leanh::LeanObject,
    mut v_a_5250_: *mut crate::leanh::LeanObject,
    mut v_a_5251_: *mut crate::leanh::LeanObject,
    mut v_a_5252_: *mut crate::leanh::LeanObject,
    mut v_a_5253_: *mut crate::leanh::LeanObject,
    mut v_a_5254_: *mut crate::leanh::LeanObject,
    mut v_a_5255_: *mut crate::leanh::LeanObject,
    mut v_a_5256_: *mut crate::leanh::LeanObject,
    mut v_a_5257_: *mut crate::leanh::LeanObject,
    mut v_a_5258_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_isLower_boxed_5259_: u8 = 0;
    let mut v_res_5260_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_isLower_boxed_5259_ = (crate::leanh::lean_unbox(v_isLower_5246_) as u8);
    v_res_5260_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_css_5245_, v_isLower_boxed_5259_, v_a_5247_, v_a_5248_, v_a_5249_, v_a_5250_, v_a_5251_, v_a_5252_, v_a_5253_, v_a_5254_, v_a_5255_, v_a_5256_, v_a_5257_);
    crate::leanh::lean_dec(v_a_5257_);
    crate::leanh::lean_dec_ref(v_a_5256_);
    crate::leanh::lean_dec(v_a_5255_);
    crate::leanh::lean_dec_ref(v_a_5254_);
    crate::leanh::lean_dec(v_a_5253_);
    crate::leanh::lean_dec_ref(v_a_5252_);
    crate::leanh::lean_dec(v_a_5251_);
    crate::leanh::lean_dec_ref(v_a_5250_);
    crate::leanh::lean_dec(v_a_5249_);
    crate::leanh::lean_dec(v_a_5248_);
    crate::leanh::lean_dec(v_a_5247_);
    crate::leanh::lean_dec_ref(v_css_5245_);
    return v_res_5260_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5267_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5263_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__1;
    v___x_5264_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5265_ = crate::leanh::lean_unsigned_to_nat(63);
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
    mut v_a_5269_: *mut crate::leanh::LeanObject,
    mut v_a_5270_: *mut crate::leanh::LeanObject,
    mut v_a_5271_: *mut crate::leanh::LeanObject,
    mut v_a_5272_: *mut crate::leanh::LeanObject,
    mut v_a_5273_: *mut crate::leanh::LeanObject,
    mut v_a_5274_: *mut crate::leanh::LeanObject,
    mut v_a_5275_: *mut crate::leanh::LeanObject,
    mut v_a_5276_: *mut crate::leanh::LeanObject,
    mut v_a_5277_: *mut crate::leanh::LeanObject,
    mut v_a_5278_: *mut crate::leanh::LeanObject,
    mut v_a_5279_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5281_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_lowers_5283_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5286_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5287_: u8 = 0;
    let mut v___x_5288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5290_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5293_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5294_: u8 = 0;
    let mut v___x_5296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5297_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5298_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5281_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_,
                    v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_,
                );
                if crate::leanh::lean_obj_tag(v___x_5281_) == 0 {
                    v_a_5282_ = crate::leanh::lean_ctor_get(v___x_5281_, 0);
                    crate::leanh::lean_inc(v_a_5282_);
                    crate::leanh::lean_dec_ref_known(v___x_5281_, 1);
                    v_lowers_5283_ = crate::leanh::lean_ctor_get(v_a_5282_, 32);
                    crate::leanh::lean_inc_ref(v_lowers_5283_);
                    v_vars_5284_ = crate::leanh::lean_ctor_get(v_a_5282_, 30);
                    crate::leanh::lean_inc_ref(v_vars_5284_);
                    crate::leanh::lean_dec(v_a_5282_);
                    v_size_5285_ = crate::leanh::lean_ctor_get(v_lowers_5283_, 2);
                    v_size_5286_ = crate::leanh::lean_ctor_get(v_vars_5284_, 2);
                    crate::leanh::lean_inc(v_size_5286_);
                    crate::leanh::lean_dec_ref(v_vars_5284_);
                    v___x_5287_ = lean_nat_dec_eq(v_size_5285_, v_size_5286_);
                    crate::leanh::lean_dec(v_size_5286_);
                    if v___x_5287_ == 0 {
                        crate::leanh::lean_dec_ref(v_lowers_5283_);
                        v___x_5288_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers___closed__2);
                        v___x_5289_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_5288_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
                        return v___x_5289_;
                    } else {
                        v___x_5290_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_lowers_5283_, v___x_5287_, v_a_5269_, v_a_5270_, v_a_5271_, v_a_5272_, v_a_5273_, v_a_5274_, v_a_5275_, v_a_5276_, v_a_5277_, v_a_5278_, v_a_5279_);
                        crate::leanh::lean_dec_ref(v_lowers_5283_);
                        return v___x_5290_;
                    }
                } else {
                    v_a_5291_ = crate::leanh::lean_ctor_get(v___x_5281_, 0);
                    v_isSharedCheck_5298_ = (!crate::leanh::lean_is_exclusive(v___x_5281_)) as u8;
                    if v_isSharedCheck_5298_ == 0 {
                        v___x_5293_ = v___x_5281_;
                        v_isShared_5294_ = v_isSharedCheck_5298_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5291_);
                        crate::leanh::lean_dec(v___x_5281_);
                        v___x_5293_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5297_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5297_, 0, v_a_5291_);
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
    mut v_a_5299_: *mut crate::leanh::LeanObject,
    mut v_a_5300_: *mut crate::leanh::LeanObject,
    mut v_a_5301_: *mut crate::leanh::LeanObject,
    mut v_a_5302_: *mut crate::leanh::LeanObject,
    mut v_a_5303_: *mut crate::leanh::LeanObject,
    mut v_a_5304_: *mut crate::leanh::LeanObject,
    mut v_a_5305_: *mut crate::leanh::LeanObject,
    mut v_a_5306_: *mut crate::leanh::LeanObject,
    mut v_a_5307_: *mut crate::leanh::LeanObject,
    mut v_a_5308_: *mut crate::leanh::LeanObject,
    mut v_a_5309_: *mut crate::leanh::LeanObject,
    mut v_a_5310_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5311_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5311_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_5299_, v_a_5300_, v_a_5301_, v_a_5302_, v_a_5303_, v_a_5304_, v_a_5305_, v_a_5306_, v_a_5307_, v_a_5308_, v_a_5309_);
    crate::leanh::lean_dec(v_a_5309_);
    crate::leanh::lean_dec_ref(v_a_5308_);
    crate::leanh::lean_dec(v_a_5307_);
    crate::leanh::lean_dec_ref(v_a_5306_);
    crate::leanh::lean_dec(v_a_5305_);
    crate::leanh::lean_dec_ref(v_a_5304_);
    crate::leanh::lean_dec(v_a_5303_);
    crate::leanh::lean_dec_ref(v_a_5302_);
    crate::leanh::lean_dec(v_a_5301_);
    crate::leanh::lean_dec(v_a_5300_);
    crate::leanh::lean_dec(v_a_5299_);
    return v_res_5311_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_5314_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5315_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5316_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5317_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5318_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5319_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_5314_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__1;
    v___x_5315_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_5316_ = crate::leanh::lean_unsigned_to_nat(68);
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
    mut v_a_5320_: *mut crate::leanh::LeanObject,
    mut v_a_5321_: *mut crate::leanh::LeanObject,
    mut v_a_5322_: *mut crate::leanh::LeanObject,
    mut v_a_5323_: *mut crate::leanh::LeanObject,
    mut v_a_5324_: *mut crate::leanh::LeanObject,
    mut v_a_5325_: *mut crate::leanh::LeanObject,
    mut v_a_5326_: *mut crate::leanh::LeanObject,
    mut v_a_5327_: *mut crate::leanh::LeanObject,
    mut v_a_5328_: *mut crate::leanh::LeanObject,
    mut v_a_5329_: *mut crate::leanh::LeanObject,
    mut v_a_5330_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_uppers_5334_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_5335_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5336_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_5337_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5338_: u8 = 0;
    let mut v___x_5339_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5340_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5341_: u8 = 0;
    let mut v___x_5342_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5343_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5345_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5346_: u8 = 0;
    let mut v___x_5348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5350_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5332_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_,
                    v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_,
                );
                if crate::leanh::lean_obj_tag(v___x_5332_) == 0 {
                    v_a_5333_ = crate::leanh::lean_ctor_get(v___x_5332_, 0);
                    crate::leanh::lean_inc(v_a_5333_);
                    crate::leanh::lean_dec_ref_known(v___x_5332_, 1);
                    v_uppers_5334_ = crate::leanh::lean_ctor_get(v_a_5333_, 33);
                    crate::leanh::lean_inc_ref(v_uppers_5334_);
                    v_vars_5335_ = crate::leanh::lean_ctor_get(v_a_5333_, 30);
                    crate::leanh::lean_inc_ref(v_vars_5335_);
                    crate::leanh::lean_dec(v_a_5333_);
                    v_size_5336_ = crate::leanh::lean_ctor_get(v_uppers_5334_, 2);
                    v_size_5337_ = crate::leanh::lean_ctor_get(v_vars_5335_, 2);
                    crate::leanh::lean_inc(v_size_5337_);
                    crate::leanh::lean_dec_ref(v_vars_5335_);
                    v___x_5338_ = lean_nat_dec_eq(v_size_5336_, v_size_5337_);
                    crate::leanh::lean_dec(v_size_5337_);
                    if v___x_5338_ == 0 {
                        crate::leanh::lean_dec_ref(v_uppers_5334_);
                        v___x_5339_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers___closed__2);
                        v___x_5340_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_5339_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
                        return v___x_5340_;
                    } else {
                        v___x_5341_ = 0;
                        v___x_5342_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLeCnstrs(v_uppers_5334_, v___x_5341_, v_a_5320_, v_a_5321_, v_a_5322_, v_a_5323_, v_a_5324_, v_a_5325_, v_a_5326_, v_a_5327_, v_a_5328_, v_a_5329_, v_a_5330_);
                        crate::leanh::lean_dec_ref(v_uppers_5334_);
                        return v___x_5342_;
                    }
                } else {
                    v_a_5343_ = crate::leanh::lean_ctor_get(v___x_5332_, 0);
                    v_isSharedCheck_5350_ = (!crate::leanh::lean_is_exclusive(v___x_5332_)) as u8;
                    if v_isSharedCheck_5350_ == 0 {
                        v___x_5345_ = v___x_5332_;
                        v_isShared_5346_ = v_isSharedCheck_5350_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5343_);
                        crate::leanh::lean_dec(v___x_5332_);
                        v___x_5345_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5349_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5349_, 0, v_a_5343_);
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
    mut v_a_5351_: *mut crate::leanh::LeanObject,
    mut v_a_5352_: *mut crate::leanh::LeanObject,
    mut v_a_5353_: *mut crate::leanh::LeanObject,
    mut v_a_5354_: *mut crate::leanh::LeanObject,
    mut v_a_5355_: *mut crate::leanh::LeanObject,
    mut v_a_5356_: *mut crate::leanh::LeanObject,
    mut v_a_5357_: *mut crate::leanh::LeanObject,
    mut v_a_5358_: *mut crate::leanh::LeanObject,
    mut v_a_5359_: *mut crate::leanh::LeanObject,
    mut v_a_5360_: *mut crate::leanh::LeanObject,
    mut v_a_5361_: *mut crate::leanh::LeanObject,
    mut v_a_5362_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5363_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_5351_, v_a_5352_, v_a_5353_, v_a_5354_, v_a_5355_, v_a_5356_, v_a_5357_, v_a_5358_, v_a_5359_, v_a_5360_, v_a_5361_);
    crate::leanh::lean_dec(v_a_5361_);
    crate::leanh::lean_dec_ref(v_a_5360_);
    crate::leanh::lean_dec(v_a_5359_);
    crate::leanh::lean_dec_ref(v_a_5358_);
    crate::leanh::lean_dec(v_a_5357_);
    crate::leanh::lean_dec_ref(v_a_5356_);
    crate::leanh::lean_dec(v_a_5355_);
    crate::leanh::lean_dec_ref(v_a_5354_);
    crate::leanh::lean_dec(v_a_5353_);
    crate::leanh::lean_dec(v_a_5352_);
    crate::leanh::lean_dec(v_a_5351_);
    return v_res_5363_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(
    mut v_____s_5367_: *mut crate::leanh::LeanObject,
    mut v_as_5368_: *mut crate::leanh::LeanObject,
    mut v_sz_5369_: usize,
    mut v_i_5370_: usize,
    mut v_b_5371_: *mut crate::leanh::LeanObject,
    mut v___y_5372_: *mut crate::leanh::LeanObject,
    mut v___y_5373_: *mut crate::leanh::LeanObject,
    mut v___y_5374_: *mut crate::leanh::LeanObject,
    mut v___y_5375_: *mut crate::leanh::LeanObject,
    mut v___y_5376_: *mut crate::leanh::LeanObject,
    mut v___y_5377_: *mut crate::leanh::LeanObject,
    mut v___y_5378_: *mut crate::leanh::LeanObject,
    mut v___y_5379_: *mut crate::leanh::LeanObject,
    mut v___y_5380_: *mut crate::leanh::LeanObject,
    mut v___y_5381_: *mut crate::leanh::LeanObject,
    mut v___y_5382_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5384_: u8 = 0;
    let mut v___x_5385_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5386_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5387_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5388_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5389_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5390_: usize = 0;
    let mut v___x_5391_: usize = 0;
    let mut v_a_5393_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5396_: u8 = 0;
    let mut v___x_5398_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5399_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5400_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5384_ = lean_usize_dec_lt(v_i_5370_, v_sz_5369_);
                if v___x_5384_ == 0 {
                    v___x_5385_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5385_, 0, v_b_5371_);
                    return v___x_5385_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5371_);
                    v_a_5386_ = lean_array_uget_borrowed(v_as_5368_, v_i_5370_);
                    v_p_5387_ = crate::leanh::lean_ctor_get(v_a_5386_, 0);
                    v___x_5388_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5387_, v_____s_5367_, v___y_5372_, v___y_5373_, v___y_5374_, v___y_5375_, v___y_5376_, v___y_5377_, v___y_5378_, v___y_5379_, v___y_5380_, v___y_5381_, v___y_5382_);
                    if crate::leanh::lean_obj_tag(v___x_5388_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5388_, 1);
                        v___x_5389_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_5390_ = 1usize;
                        v___x_5391_ = lean_usize_add(v_i_5370_, v___x_5390_);
                        v_i_5370_ = v___x_5391_;
                        v_b_5371_ = v___x_5389_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5393_ = crate::leanh::lean_ctor_get(v___x_5388_, 0);
                        v_isSharedCheck_5400_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5388_)) as u8;
                        if v_isSharedCheck_5400_ == 0 {
                            v___x_5395_ = v___x_5388_;
                            v_isShared_5396_ = v_isSharedCheck_5400_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5393_);
                            crate::leanh::lean_dec(v___x_5388_);
                            v___x_5395_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5399_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5399_, 0, v_a_5393_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_5401_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_5402_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_5403_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_5404_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_5405_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5406_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5407_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5408_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5409_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5410_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5411_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5412_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5413_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5414_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5415_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5416_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5417_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5418_: usize = 0;
    let mut v_i_boxed_5419_: usize = 0;
    let mut v_res_5420_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5418_ = crate::leanh::lean_unbox_usize(v_sz_5403_);
    crate::leanh::lean_dec(v_sz_5403_);
    v_i_boxed_5419_ = crate::leanh::lean_unbox_usize(v_i_5404_);
    crate::leanh::lean_dec(v_i_5404_);
    v_res_5420_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_5401_, v_as_5402_, v_sz_boxed_5418_, v_i_boxed_5419_, v_b_5405_, v___y_5406_, v___y_5407_, v___y_5408_, v___y_5409_, v___y_5410_, v___y_5411_, v___y_5412_, v___y_5413_, v___y_5414_, v___y_5415_, v___y_5416_);
    crate::leanh::lean_dec(v___y_5416_);
    crate::leanh::lean_dec_ref(v___y_5415_);
    crate::leanh::lean_dec(v___y_5414_);
    crate::leanh::lean_dec_ref(v___y_5413_);
    crate::leanh::lean_dec(v___y_5412_);
    crate::leanh::lean_dec_ref(v___y_5411_);
    crate::leanh::lean_dec(v___y_5410_);
    crate::leanh::lean_dec_ref(v___y_5409_);
    crate::leanh::lean_dec(v___y_5408_);
    crate::leanh::lean_dec(v___y_5407_);
    crate::leanh::lean_dec(v___y_5406_);
    crate::leanh::lean_dec_ref(v_as_5402_);
    crate::leanh::lean_dec(v_____s_5401_);
    return v_res_5420_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(
    mut v_____s_5421_: *mut crate::leanh::LeanObject,
    mut v_as_5422_: *mut crate::leanh::LeanObject,
    mut v_sz_5423_: usize,
    mut v_i_5424_: usize,
    mut v_b_5425_: *mut crate::leanh::LeanObject,
    mut v___y_5426_: *mut crate::leanh::LeanObject,
    mut v___y_5427_: *mut crate::leanh::LeanObject,
    mut v___y_5428_: *mut crate::leanh::LeanObject,
    mut v___y_5429_: *mut crate::leanh::LeanObject,
    mut v___y_5430_: *mut crate::leanh::LeanObject,
    mut v___y_5431_: *mut crate::leanh::LeanObject,
    mut v___y_5432_: *mut crate::leanh::LeanObject,
    mut v___y_5433_: *mut crate::leanh::LeanObject,
    mut v___y_5434_: *mut crate::leanh::LeanObject,
    mut v___y_5435_: *mut crate::leanh::LeanObject,
    mut v___y_5436_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5438_: u8 = 0;
    let mut v___x_5439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5441_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5442_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5443_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5444_: usize = 0;
    let mut v___x_5445_: usize = 0;
    let mut v___x_5446_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5447_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5449_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5450_: u8 = 0;
    let mut v___x_5452_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5453_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5454_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5438_ = lean_usize_dec_lt(v_i_5424_, v_sz_5423_);
                if v___x_5438_ == 0 {
                    v___x_5439_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5439_, 0, v_b_5425_);
                    return v___x_5439_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5425_);
                    v_a_5440_ = lean_array_uget_borrowed(v_as_5422_, v_i_5424_);
                    v_p_5441_ = crate::leanh::lean_ctor_get(v_a_5440_, 0);
                    v___x_5442_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5441_, v_____s_5421_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
                    if crate::leanh::lean_obj_tag(v___x_5442_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5442_, 1);
                        v___x_5443_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4___closed__0;
                        v___x_5444_ = 1usize;
                        v___x_5445_ = lean_usize_add(v_i_5424_, v___x_5444_);
                        v___x_5446_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2_spec__4(v_____s_5421_, v_as_5422_, v_sz_5423_, v___x_5445_, v___x_5443_, v___y_5426_, v___y_5427_, v___y_5428_, v___y_5429_, v___y_5430_, v___y_5431_, v___y_5432_, v___y_5433_, v___y_5434_, v___y_5435_, v___y_5436_);
                        return v___x_5446_;
                    } else {
                        v_a_5447_ = crate::leanh::lean_ctor_get(v___x_5442_, 0);
                        v_isSharedCheck_5454_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5442_)) as u8;
                        if v_isSharedCheck_5454_ == 0 {
                            v___x_5449_ = v___x_5442_;
                            v_isShared_5450_ = v_isSharedCheck_5454_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5447_);
                            crate::leanh::lean_dec(v___x_5442_);
                            v___x_5449_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5453_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5453_, 0, v_a_5447_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_5455_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_5456_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_5457_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_5458_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_5459_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5460_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5461_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5462_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5463_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5464_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5465_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5466_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5467_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5468_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5469_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5470_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5471_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5472_: usize = 0;
    let mut v_i_boxed_5473_: usize = 0;
    let mut v_res_5474_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5472_ = crate::leanh::lean_unbox_usize(v_sz_5457_);
    crate::leanh::lean_dec(v_sz_5457_);
    v_i_boxed_5473_ = crate::leanh::lean_unbox_usize(v_i_5458_);
    crate::leanh::lean_dec(v_i_5458_);
    v_res_5474_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_5455_, v_as_5456_, v_sz_boxed_5472_, v_i_boxed_5473_, v_b_5459_, v___y_5460_, v___y_5461_, v___y_5462_, v___y_5463_, v___y_5464_, v___y_5465_, v___y_5466_, v___y_5467_, v___y_5468_, v___y_5469_, v___y_5470_);
    crate::leanh::lean_dec(v___y_5470_);
    crate::leanh::lean_dec_ref(v___y_5469_);
    crate::leanh::lean_dec(v___y_5468_);
    crate::leanh::lean_dec_ref(v___y_5467_);
    crate::leanh::lean_dec(v___y_5466_);
    crate::leanh::lean_dec_ref(v___y_5465_);
    crate::leanh::lean_dec(v___y_5464_);
    crate::leanh::lean_dec_ref(v___y_5463_);
    crate::leanh::lean_dec(v___y_5462_);
    crate::leanh::lean_dec(v___y_5461_);
    crate::leanh::lean_dec(v___y_5460_);
    crate::leanh::lean_dec_ref(v_as_5456_);
    crate::leanh::lean_dec(v_____s_5455_);
    return v_res_5474_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(
    mut v_init_5475_: *mut crate::leanh::LeanObject,
    mut v_____s_5476_: *mut crate::leanh::LeanObject,
    mut v_n_5477_: *mut crate::leanh::LeanObject,
    mut v_b_5478_: *mut crate::leanh::LeanObject,
    mut v___y_5479_: *mut crate::leanh::LeanObject,
    mut v___y_5480_: *mut crate::leanh::LeanObject,
    mut v___y_5481_: *mut crate::leanh::LeanObject,
    mut v___y_5482_: *mut crate::leanh::LeanObject,
    mut v___y_5483_: *mut crate::leanh::LeanObject,
    mut v___y_5484_: *mut crate::leanh::LeanObject,
    mut v___y_5485_: *mut crate::leanh::LeanObject,
    mut v___y_5486_: *mut crate::leanh::LeanObject,
    mut v___y_5487_: *mut crate::leanh::LeanObject,
    mut v___y_5488_: *mut crate::leanh::LeanObject,
    mut v___y_5489_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_5491_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5492_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5493_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5494_: usize = 0;
    let mut v___x_5495_: usize = 0;
    let mut v___x_5496_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5497_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5499_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5500_: u8 = 0;
    let mut v_fst_5501_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5502_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5503_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5505_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5506_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5507_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5509_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5510_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5511_: u8 = 0;
    let mut v_a_5512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5515_: u8 = 0;
    let mut v___x_5517_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5519_: u8 = 0;
    let mut v_vs_5520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5521_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5522_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5523_: usize = 0;
    let mut v___x_5524_: usize = 0;
    let mut v___x_5525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5528_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5529_: u8 = 0;
    let mut v_fst_5530_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5532_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5535_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5539_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5540_: u8 = 0;
    let mut v_a_5541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5544_: u8 = 0;
    let mut v___x_5546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_5477_) == 0 {
                    v_cs_5491_ = crate::leanh::lean_ctor_get(v_n_5477_, 0);
                    v___x_5492_ = crate::leanh::lean_box(0);
                    v___x_5493_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5493_, 0, v___x_5492_);
                    crate::leanh::lean_ctor_set(v___x_5493_, 1, v_b_5478_);
                    v_sz_5494_ = lean_array_size(v_cs_5491_);
                    v___x_5495_ = 0usize;
                    v___x_5496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_5475_, v_____s_5476_, v_cs_5491_, v_sz_5494_, v___x_5495_, v___x_5493_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
                    if crate::leanh::lean_obj_tag(v___x_5496_) == 0 {
                        v_a_5497_ = crate::leanh::lean_ctor_get(v___x_5496_, 0);
                        v_isSharedCheck_5511_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5496_)) as u8;
                        if v_isSharedCheck_5511_ == 0 {
                            v___x_5499_ = v___x_5496_;
                            v_isShared_5500_ = v_isSharedCheck_5511_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5497_);
                            crate::leanh::lean_dec(v___x_5496_);
                            v___x_5499_ = crate::leanh::lean_box(0);
                            v_isShared_5500_ = v_isSharedCheck_5511_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_5512_ = crate::leanh::lean_ctor_get(v___x_5496_, 0);
                        v_isSharedCheck_5519_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5496_)) as u8;
                        if v_isSharedCheck_5519_ == 0 {
                            v___x_5514_ = v___x_5496_;
                            v_isShared_5515_ = v_isSharedCheck_5519_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5512_);
                            crate::leanh::lean_dec(v___x_5496_);
                            v___x_5514_ = crate::leanh::lean_box(0);
                            v_isShared_5515_ = v_isSharedCheck_5519_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_5520_ = crate::leanh::lean_ctor_get(v_n_5477_, 0);
                    v___x_5521_ = crate::leanh::lean_box(0);
                    v___x_5522_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5522_, 0, v___x_5521_);
                    crate::leanh::lean_ctor_set(v___x_5522_, 1, v_b_5478_);
                    v_sz_5523_ = lean_array_size(v_vs_5520_);
                    v___x_5524_ = 0usize;
                    v___x_5525_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__2(v_____s_5476_, v_vs_5520_, v_sz_5523_, v___x_5524_, v___x_5522_, v___y_5479_, v___y_5480_, v___y_5481_, v___y_5482_, v___y_5483_, v___y_5484_, v___y_5485_, v___y_5486_, v___y_5487_, v___y_5488_, v___y_5489_);
                    if crate::leanh::lean_obj_tag(v___x_5525_) == 0 {
                        v_a_5526_ = crate::leanh::lean_ctor_get(v___x_5525_, 0);
                        v_isSharedCheck_5540_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5525_)) as u8;
                        if v_isSharedCheck_5540_ == 0 {
                            v___x_5528_ = v___x_5525_;
                            v_isShared_5529_ = v_isSharedCheck_5540_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5526_);
                            crate::leanh::lean_dec(v___x_5525_);
                            v___x_5528_ = crate::leanh::lean_box(0);
                            v_isShared_5529_ = v_isSharedCheck_5540_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_5541_ = crate::leanh::lean_ctor_get(v___x_5525_, 0);
                        v_isSharedCheck_5548_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5525_)) as u8;
                        if v_isSharedCheck_5548_ == 0 {
                            v___x_5543_ = v___x_5525_;
                            v_isShared_5544_ = v_isSharedCheck_5548_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5541_);
                            crate::leanh::lean_dec(v___x_5525_);
                            v___x_5543_ = crate::leanh::lean_box(0);
                            v_isShared_5544_ = v_isSharedCheck_5548_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_5501_ = crate::leanh::lean_ctor_get(v_a_5497_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5501_) == 0 {
                    v_snd_5502_ = crate::leanh::lean_ctor_get(v_a_5497_, 1);
                    crate::leanh::lean_inc(v_snd_5502_);
                    crate::leanh::lean_dec(v_a_5497_);
                    v___x_5503_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5503_, 0, v_snd_5502_);
                    if v_isShared_5500_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5499_, 0, v___x_5503_);
                        v___x_5505_ = v___x_5499_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5506_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5506_, 0, v___x_5503_);
                        v___x_5505_ = v_reuseFailAlloc_5506_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5501_);
                    crate::leanh::lean_dec(v_a_5497_);
                    v_val_5507_ = crate::leanh::lean_ctor_get(v_fst_5501_, 0);
                    crate::leanh::lean_inc(v_val_5507_);
                    crate::leanh::lean_dec_ref_known(v_fst_5501_, 1);
                    if v_isShared_5500_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5499_, 0, v_val_5507_);
                        v___x_5509_ = v___x_5499_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5510_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5510_, 0, v_val_5507_);
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
                    v_reuseFailAlloc_5518_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5518_, 0, v_a_5512_);
                    v___x_5517_ = v_reuseFailAlloc_5518_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_5517_;
            }
            6 => {
                v_fst_5530_ = crate::leanh::lean_ctor_get(v_a_5526_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5530_) == 0 {
                    v_snd_5531_ = crate::leanh::lean_ctor_get(v_a_5526_, 1);
                    crate::leanh::lean_inc(v_snd_5531_);
                    crate::leanh::lean_dec(v_a_5526_);
                    v___x_5532_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5532_, 0, v_snd_5531_);
                    if v_isShared_5529_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5528_, 0, v___x_5532_);
                        v___x_5534_ = v___x_5528_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_5535_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5535_, 0, v___x_5532_);
                        v___x_5534_ = v_reuseFailAlloc_5535_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5530_);
                    crate::leanh::lean_dec(v_a_5526_);
                    v_val_5536_ = crate::leanh::lean_ctor_get(v_fst_5530_, 0);
                    crate::leanh::lean_inc(v_val_5536_);
                    crate::leanh::lean_dec_ref_known(v_fst_5530_, 1);
                    if v_isShared_5529_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5528_, 0, v_val_5536_);
                        v___x_5538_ = v___x_5528_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_5539_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5539_, 0, v_val_5536_);
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
                    v_reuseFailAlloc_5547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5547_, 0, v_a_5541_);
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
    mut v_init_5549_: *mut crate::leanh::LeanObject,
    mut v_____s_5550_: *mut crate::leanh::LeanObject,
    mut v_as_5551_: *mut crate::leanh::LeanObject,
    mut v_sz_5552_: usize,
    mut v_i_5553_: usize,
    mut v_b_5554_: *mut crate::leanh::LeanObject,
    mut v___y_5555_: *mut crate::leanh::LeanObject,
    mut v___y_5556_: *mut crate::leanh::LeanObject,
    mut v___y_5557_: *mut crate::leanh::LeanObject,
    mut v___y_5558_: *mut crate::leanh::LeanObject,
    mut v___y_5559_: *mut crate::leanh::LeanObject,
    mut v___y_5560_: *mut crate::leanh::LeanObject,
    mut v___y_5561_: *mut crate::leanh::LeanObject,
    mut v___y_5562_: *mut crate::leanh::LeanObject,
    mut v___y_5563_: *mut crate::leanh::LeanObject,
    mut v___y_5564_: *mut crate::leanh::LeanObject,
    mut v___y_5565_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5567_: u8 = 0;
    let mut v___x_5568_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5569_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5571_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5572_: u8 = 0;
    let mut v_a_5573_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5574_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5575_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5577_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5578_: u8 = 0;
    let mut v___x_5579_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5581_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5584_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5590_: usize = 0;
    let mut v___x_5591_: usize = 0;
    let mut v_reuseFailAlloc_5593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5594_: u8 = 0;
    let mut v_a_5595_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5597_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5598_: u8 = 0;
    let mut v___x_5600_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5601_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5602_: u8 = 0;
    let mut v_isSharedCheck_5603_: u8 = 0;
    let mut v_unused_5604_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5567_ = lean_usize_dec_lt(v_i_5553_, v_sz_5552_);
                if v___x_5567_ == 0 {
                    v___x_5568_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5568_, 0, v_b_5554_);
                    return v___x_5568_;
                } else {
                    v_snd_5569_ = crate::leanh::lean_ctor_get(v_b_5554_, 1);
                    v_isSharedCheck_5603_ = (!crate::leanh::lean_is_exclusive(v_b_5554_)) as u8;
                    if v_isSharedCheck_5603_ == 0 {
                        v_unused_5604_ = crate::leanh::lean_ctor_get(v_b_5554_, 0);
                        crate::leanh::lean_dec(v_unused_5604_);
                        v___x_5571_ = v_b_5554_;
                        v_isShared_5572_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5569_);
                        crate::leanh::lean_dec(v_b_5554_);
                        v___x_5571_ = crate::leanh::lean_box(0);
                        v_isShared_5572_ = v_isSharedCheck_5603_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5573_ = lean_array_uget_borrowed(v_as_5551_, v_i_5553_);
                crate::leanh::lean_inc(v_snd_5569_);
                v___x_5574_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5549_, v_____s_5550_, v_a_5573_, v_snd_5569_, v___y_5555_, v___y_5556_, v___y_5557_, v___y_5558_, v___y_5559_, v___y_5560_, v___y_5561_, v___y_5562_, v___y_5563_, v___y_5564_, v___y_5565_);
                if crate::leanh::lean_obj_tag(v___x_5574_) == 0 {
                    v_a_5575_ = crate::leanh::lean_ctor_get(v___x_5574_, 0);
                    v_isSharedCheck_5594_ = (!crate::leanh::lean_is_exclusive(v___x_5574_)) as u8;
                    if v_isSharedCheck_5594_ == 0 {
                        v___x_5577_ = v___x_5574_;
                        v_isShared_5578_ = v_isSharedCheck_5594_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5575_);
                        crate::leanh::lean_dec(v___x_5574_);
                        v___x_5577_ = crate::leanh::lean_box(0);
                        v_isShared_5578_ = v_isSharedCheck_5594_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5571_);
                    crate::leanh::lean_dec(v_snd_5569_);
                    v_a_5595_ = crate::leanh::lean_ctor_get(v___x_5574_, 0);
                    v_isSharedCheck_5602_ = (!crate::leanh::lean_is_exclusive(v___x_5574_)) as u8;
                    if v_isSharedCheck_5602_ == 0 {
                        v___x_5597_ = v___x_5574_;
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5595_);
                        crate::leanh::lean_dec(v___x_5574_);
                        v___x_5597_ = crate::leanh::lean_box(0);
                        v_isShared_5598_ = v_isSharedCheck_5602_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_5575_) == 0 {
                    v___x_5579_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5579_, 0, v_a_5575_);
                    if v_isShared_5572_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5571_, 0, v___x_5579_);
                        v___x_5581_ = v___x_5571_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_5585_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5579_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_snd_5569_);
                        v___x_5581_ = v_reuseFailAlloc_5585_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5577_);
                    crate::leanh::lean_dec(v_snd_5569_);
                    v_a_5586_ = crate::leanh::lean_ctor_get(v_a_5575_, 0);
                    crate::leanh::lean_inc(v_a_5586_);
                    crate::leanh::lean_dec_ref_known(v_a_5575_, 1);
                    v___x_5587_ = crate::leanh::lean_box(0);
                    if v_isShared_5572_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5571_, 1, v_a_5586_);
                        crate::leanh::lean_ctor_set(v___x_5571_, 0, v___x_5587_);
                        v___x_5589_ = v___x_5571_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5593_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 0, v___x_5587_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5593_, 1, v_a_5586_);
                        v___x_5589_ = v_reuseFailAlloc_5593_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_5578_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_5577_, 0, v___x_5581_);
                    v___x_5583_ = v___x_5577_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_5584_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5581_);
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
                    v_reuseFailAlloc_5601_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5601_, 0, v_a_5595_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_5605_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_____s_5606_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_as_5607_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_sz_5608_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_i_5609_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_b_5610_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5611_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5612_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5613_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5614_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5615_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5616_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5617_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5618_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5619_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5620_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5621_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_5622_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_sz_boxed_5623_: usize = 0;
    let mut v_i_boxed_5624_: usize = 0;
    let mut v_res_5625_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5623_ = crate::leanh::lean_unbox_usize(v_sz_5608_);
    crate::leanh::lean_dec(v_sz_5608_);
    v_i_boxed_5624_ = crate::leanh::lean_unbox_usize(v_i_5609_);
    crate::leanh::lean_dec(v_i_5609_);
    v_res_5625_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0_spec__1(v_init_5605_, v_____s_5606_, v_as_5607_, v_sz_boxed_5623_, v_i_boxed_5624_, v_b_5610_, v___y_5611_, v___y_5612_, v___y_5613_, v___y_5614_, v___y_5615_, v___y_5616_, v___y_5617_, v___y_5618_, v___y_5619_, v___y_5620_, v___y_5621_);
    crate::leanh::lean_dec(v___y_5621_);
    crate::leanh::lean_dec_ref(v___y_5620_);
    crate::leanh::lean_dec(v___y_5619_);
    crate::leanh::lean_dec_ref(v___y_5618_);
    crate::leanh::lean_dec(v___y_5617_);
    crate::leanh::lean_dec_ref(v___y_5616_);
    crate::leanh::lean_dec(v___y_5615_);
    crate::leanh::lean_dec_ref(v___y_5614_);
    crate::leanh::lean_dec(v___y_5613_);
    crate::leanh::lean_dec(v___y_5612_);
    crate::leanh::lean_dec(v___y_5611_);
    crate::leanh::lean_dec_ref(v_as_5607_);
    crate::leanh::lean_dec(v_____s_5606_);
    return v_res_5625_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0___boxed(
    mut v_init_5626_: *mut crate::leanh::LeanObject,
    mut v_____s_5627_: *mut crate::leanh::LeanObject,
    mut v_n_5628_: *mut crate::leanh::LeanObject,
    mut v_b_5629_: *mut crate::leanh::LeanObject,
    mut v___y_5630_: *mut crate::leanh::LeanObject,
    mut v___y_5631_: *mut crate::leanh::LeanObject,
    mut v___y_5632_: *mut crate::leanh::LeanObject,
    mut v___y_5633_: *mut crate::leanh::LeanObject,
    mut v___y_5634_: *mut crate::leanh::LeanObject,
    mut v___y_5635_: *mut crate::leanh::LeanObject,
    mut v___y_5636_: *mut crate::leanh::LeanObject,
    mut v___y_5637_: *mut crate::leanh::LeanObject,
    mut v___y_5638_: *mut crate::leanh::LeanObject,
    mut v___y_5639_: *mut crate::leanh::LeanObject,
    mut v___y_5640_: *mut crate::leanh::LeanObject,
    mut v___y_5641_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5642_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5626_, v_____s_5627_, v_n_5628_, v_b_5629_, v___y_5630_, v___y_5631_, v___y_5632_, v___y_5633_, v___y_5634_, v___y_5635_, v___y_5636_, v___y_5637_, v___y_5638_, v___y_5639_, v___y_5640_);
    crate::leanh::lean_dec(v___y_5640_);
    crate::leanh::lean_dec_ref(v___y_5639_);
    crate::leanh::lean_dec(v___y_5638_);
    crate::leanh::lean_dec_ref(v___y_5637_);
    crate::leanh::lean_dec(v___y_5636_);
    crate::leanh::lean_dec_ref(v___y_5635_);
    crate::leanh::lean_dec(v___y_5634_);
    crate::leanh::lean_dec_ref(v___y_5633_);
    crate::leanh::lean_dec(v___y_5632_);
    crate::leanh::lean_dec(v___y_5631_);
    crate::leanh::lean_dec(v___y_5630_);
    crate::leanh::lean_dec_ref(v_n_5628_);
    crate::leanh::lean_dec(v_____s_5627_);
    return v_res_5642_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(
    mut v_____s_5646_: *mut crate::leanh::LeanObject,
    mut v_as_5647_: *mut crate::leanh::LeanObject,
    mut v_sz_5648_: usize,
    mut v_i_5649_: usize,
    mut v_b_5650_: *mut crate::leanh::LeanObject,
    mut v___y_5651_: *mut crate::leanh::LeanObject,
    mut v___y_5652_: *mut crate::leanh::LeanObject,
    mut v___y_5653_: *mut crate::leanh::LeanObject,
    mut v___y_5654_: *mut crate::leanh::LeanObject,
    mut v___y_5655_: *mut crate::leanh::LeanObject,
    mut v___y_5656_: *mut crate::leanh::LeanObject,
    mut v___y_5657_: *mut crate::leanh::LeanObject,
    mut v___y_5658_: *mut crate::leanh::LeanObject,
    mut v___y_5659_: *mut crate::leanh::LeanObject,
    mut v___y_5660_: *mut crate::leanh::LeanObject,
    mut v___y_5661_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5663_: u8 = 0;
    let mut v___x_5664_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5665_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5666_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5667_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5668_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5669_: usize = 0;
    let mut v___x_5670_: usize = 0;
    let mut v_a_5672_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5674_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5675_: u8 = 0;
    let mut v___x_5677_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5679_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5663_ = lean_usize_dec_lt(v_i_5649_, v_sz_5648_);
                if v___x_5663_ == 0 {
                    v___x_5664_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5664_, 0, v_b_5650_);
                    return v___x_5664_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5650_);
                    v_a_5665_ = lean_array_uget_borrowed(v_as_5647_, v_i_5649_);
                    v_p_5666_ = crate::leanh::lean_ctor_get(v_a_5665_, 0);
                    v___x_5667_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5666_, v_____s_5646_, v___y_5651_, v___y_5652_, v___y_5653_, v___y_5654_, v___y_5655_, v___y_5656_, v___y_5657_, v___y_5658_, v___y_5659_, v___y_5660_, v___y_5661_);
                    if crate::leanh::lean_obj_tag(v___x_5667_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5667_, 1);
                        v___x_5668_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_5669_ = 1usize;
                        v___x_5670_ = lean_usize_add(v_i_5649_, v___x_5669_);
                        v_i_5649_ = v___x_5670_;
                        v_b_5650_ = v___x_5668_;
                        state = 0;
                        continue;
                    } else {
                        v_a_5672_ = crate::leanh::lean_ctor_get(v___x_5667_, 0);
                        v_isSharedCheck_5679_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5667_)) as u8;
                        if v_isSharedCheck_5679_ == 0 {
                            v___x_5674_ = v___x_5667_;
                            v_isShared_5675_ = v_isSharedCheck_5679_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5672_);
                            crate::leanh::lean_dec(v___x_5667_);
                            v___x_5674_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5678_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5678_, 0, v_a_5672_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_5680_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_5681_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_5682_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_5683_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_5684_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5685_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5686_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5687_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5688_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5689_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5690_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5691_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5692_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5693_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5694_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5695_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5696_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5697_: usize = 0;
    let mut v_i_boxed_5698_: usize = 0;
    let mut v_res_5699_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5697_ = crate::leanh::lean_unbox_usize(v_sz_5682_);
    crate::leanh::lean_dec(v_sz_5682_);
    v_i_boxed_5698_ = crate::leanh::lean_unbox_usize(v_i_5683_);
    crate::leanh::lean_dec(v_i_5683_);
    v_res_5699_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_5680_, v_as_5681_, v_sz_boxed_5697_, v_i_boxed_5698_, v_b_5684_, v___y_5685_, v___y_5686_, v___y_5687_, v___y_5688_, v___y_5689_, v___y_5690_, v___y_5691_, v___y_5692_, v___y_5693_, v___y_5694_, v___y_5695_);
    crate::leanh::lean_dec(v___y_5695_);
    crate::leanh::lean_dec_ref(v___y_5694_);
    crate::leanh::lean_dec(v___y_5693_);
    crate::leanh::lean_dec_ref(v___y_5692_);
    crate::leanh::lean_dec(v___y_5691_);
    crate::leanh::lean_dec_ref(v___y_5690_);
    crate::leanh::lean_dec(v___y_5689_);
    crate::leanh::lean_dec_ref(v___y_5688_);
    crate::leanh::lean_dec(v___y_5687_);
    crate::leanh::lean_dec(v___y_5686_);
    crate::leanh::lean_dec(v___y_5685_);
    crate::leanh::lean_dec_ref(v_as_5681_);
    crate::leanh::lean_dec(v_____s_5680_);
    return v_res_5699_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(
    mut v_____s_5700_: *mut crate::leanh::LeanObject,
    mut v_as_5701_: *mut crate::leanh::LeanObject,
    mut v_sz_5702_: usize,
    mut v_i_5703_: usize,
    mut v_b_5704_: *mut crate::leanh::LeanObject,
    mut v___y_5705_: *mut crate::leanh::LeanObject,
    mut v___y_5706_: *mut crate::leanh::LeanObject,
    mut v___y_5707_: *mut crate::leanh::LeanObject,
    mut v___y_5708_: *mut crate::leanh::LeanObject,
    mut v___y_5709_: *mut crate::leanh::LeanObject,
    mut v___y_5710_: *mut crate::leanh::LeanObject,
    mut v___y_5711_: *mut crate::leanh::LeanObject,
    mut v___y_5712_: *mut crate::leanh::LeanObject,
    mut v___y_5713_: *mut crate::leanh::LeanObject,
    mut v___y_5714_: *mut crate::leanh::LeanObject,
    mut v___y_5715_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5717_: u8 = 0;
    let mut v___x_5718_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5719_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_p_5720_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5721_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5722_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5723_: usize = 0;
    let mut v___x_5724_: usize = 0;
    let mut v___x_5725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5726_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5728_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5729_: u8 = 0;
    let mut v___x_5731_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5732_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5733_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5717_ = lean_usize_dec_lt(v_i_5703_, v_sz_5702_);
                if v___x_5717_ == 0 {
                    v___x_5718_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5718_, 0, v_b_5704_);
                    return v___x_5718_;
                } else {
                    crate::leanh::lean_dec_ref(v_b_5704_);
                    v_a_5719_ = lean_array_uget_borrowed(v_as_5701_, v_i_5703_);
                    v_p_5720_ = crate::leanh::lean_ctor_get(v_a_5719_, 0);
                    v___x_5721_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf(v_p_5720_, v_____s_5700_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
                    if crate::leanh::lean_obj_tag(v___x_5721_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_5721_, 1);
                        v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4___closed__0;
                        v___x_5723_ = 1usize;
                        v___x_5724_ = lean_usize_add(v_i_5703_, v___x_5723_);
                        v___x_5725_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1_spec__4(v_____s_5700_, v_as_5701_, v_sz_5702_, v___x_5724_, v___x_5722_, v___y_5705_, v___y_5706_, v___y_5707_, v___y_5708_, v___y_5709_, v___y_5710_, v___y_5711_, v___y_5712_, v___y_5713_, v___y_5714_, v___y_5715_);
                        return v___x_5725_;
                    } else {
                        v_a_5726_ = crate::leanh::lean_ctor_get(v___x_5721_, 0);
                        v_isSharedCheck_5733_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5721_)) as u8;
                        if v_isSharedCheck_5733_ == 0 {
                            v___x_5728_ = v___x_5721_;
                            v_isShared_5729_ = v_isSharedCheck_5733_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5726_);
                            crate::leanh::lean_dec(v___x_5721_);
                            v___x_5728_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5732_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5732_, 0, v_a_5726_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_____s_5734_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_5735_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_5736_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_5737_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_5738_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_5739_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_5740_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_5741_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_5742_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_5743_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_5744_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_5745_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_5746_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_5747_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_5748_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_5749_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_5750_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_5751_: usize = 0;
    let mut v_i_boxed_5752_: usize = 0;
    let mut v_res_5753_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5751_ = crate::leanh::lean_unbox_usize(v_sz_5736_);
    crate::leanh::lean_dec(v_sz_5736_);
    v_i_boxed_5752_ = crate::leanh::lean_unbox_usize(v_i_5737_);
    crate::leanh::lean_dec(v_i_5737_);
    v_res_5753_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_5734_, v_as_5735_, v_sz_boxed_5751_, v_i_boxed_5752_, v_b_5738_, v___y_5739_, v___y_5740_, v___y_5741_, v___y_5742_, v___y_5743_, v___y_5744_, v___y_5745_, v___y_5746_, v___y_5747_, v___y_5748_, v___y_5749_);
    crate::leanh::lean_dec(v___y_5749_);
    crate::leanh::lean_dec_ref(v___y_5748_);
    crate::leanh::lean_dec(v___y_5747_);
    crate::leanh::lean_dec_ref(v___y_5746_);
    crate::leanh::lean_dec(v___y_5745_);
    crate::leanh::lean_dec_ref(v___y_5744_);
    crate::leanh::lean_dec(v___y_5743_);
    crate::leanh::lean_dec_ref(v___y_5742_);
    crate::leanh::lean_dec(v___y_5741_);
    crate::leanh::lean_dec(v___y_5740_);
    crate::leanh::lean_dec(v___y_5739_);
    crate::leanh::lean_dec_ref(v_as_5735_);
    crate::leanh::lean_dec(v_____s_5734_);
    return v_res_5753_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(
    mut v_____s_5754_: *mut crate::leanh::LeanObject,
    mut v_t_5755_: *mut crate::leanh::LeanObject,
    mut v_init_5756_: *mut crate::leanh::LeanObject,
    mut v___y_5757_: *mut crate::leanh::LeanObject,
    mut v___y_5758_: *mut crate::leanh::LeanObject,
    mut v___y_5759_: *mut crate::leanh::LeanObject,
    mut v___y_5760_: *mut crate::leanh::LeanObject,
    mut v___y_5761_: *mut crate::leanh::LeanObject,
    mut v___y_5762_: *mut crate::leanh::LeanObject,
    mut v___y_5763_: *mut crate::leanh::LeanObject,
    mut v___y_5764_: *mut crate::leanh::LeanObject,
    mut v___y_5765_: *mut crate::leanh::LeanObject,
    mut v___y_5766_: *mut crate::leanh::LeanObject,
    mut v___y_5767_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_5769_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_5770_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5771_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5772_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5774_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5775_: u8 = 0;
    let mut v_a_5776_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_5783_: usize = 0;
    let mut v___x_5784_: usize = 0;
    let mut v___x_5785_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5786_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5788_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5789_: u8 = 0;
    let mut v_fst_5790_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5791_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5793_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5794_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_5795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5799_: u8 = 0;
    let mut v_a_5800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5803_: u8 = 0;
    let mut v___x_5805_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5807_: u8 = 0;
    let mut v_isSharedCheck_5808_: u8 = 0;
    let mut v_a_5809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5811_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5812_: u8 = 0;
    let mut v___x_5814_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5816_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_5769_ = crate::leanh::lean_ctor_get(v_t_5755_, 0);
                v_tail_5770_ = crate::leanh::lean_ctor_get(v_t_5755_, 1);
                v___x_5771_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__0(v_init_5756_, v_____s_5754_, v_root_5769_, v_init_5756_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                if crate::leanh::lean_obj_tag(v___x_5771_) == 0 {
                    v_a_5772_ = crate::leanh::lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5808_ = (!crate::leanh::lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5808_ == 0 {
                        v___x_5774_ = v___x_5771_;
                        v_isShared_5775_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5772_);
                        crate::leanh::lean_dec(v___x_5771_);
                        v___x_5774_ = crate::leanh::lean_box(0);
                        v_isShared_5775_ = v_isSharedCheck_5808_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_5809_ = crate::leanh::lean_ctor_get(v___x_5771_, 0);
                    v_isSharedCheck_5816_ = (!crate::leanh::lean_is_exclusive(v___x_5771_)) as u8;
                    if v_isSharedCheck_5816_ == 0 {
                        v___x_5811_ = v___x_5771_;
                        v_isShared_5812_ = v_isSharedCheck_5816_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5809_);
                        crate::leanh::lean_dec(v___x_5771_);
                        v___x_5811_ = crate::leanh::lean_box(0);
                        v_isShared_5812_ = v_isSharedCheck_5816_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_5772_) == 0 {
                    v_a_5776_ = crate::leanh::lean_ctor_get(v_a_5772_, 0);
                    crate::leanh::lean_inc(v_a_5776_);
                    crate::leanh::lean_dec_ref_known(v_a_5772_, 1);
                    if v_isShared_5775_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5774_, 0, v_a_5776_);
                        v___x_5778_ = v___x_5774_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5779_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5779_, 0, v_a_5776_);
                        v___x_5778_ = v_reuseFailAlloc_5779_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5774_);
                    v_a_5780_ = crate::leanh::lean_ctor_get(v_a_5772_, 0);
                    crate::leanh::lean_inc(v_a_5780_);
                    crate::leanh::lean_dec_ref_known(v_a_5772_, 1);
                    v___x_5781_ = crate::leanh::lean_box(0);
                    v___x_5782_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5782_, 0, v___x_5781_);
                    crate::leanh::lean_ctor_set(v___x_5782_, 1, v_a_5780_);
                    v_sz_5783_ = lean_array_size(v_tail_5770_);
                    v___x_5784_ = 0usize;
                    v___x_5785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0_spec__1(v_____s_5754_, v_tail_5770_, v_sz_5783_, v___x_5784_, v___x_5782_, v___y_5757_, v___y_5758_, v___y_5759_, v___y_5760_, v___y_5761_, v___y_5762_, v___y_5763_, v___y_5764_, v___y_5765_, v___y_5766_, v___y_5767_);
                    if crate::leanh::lean_obj_tag(v___x_5785_) == 0 {
                        v_a_5786_ = crate::leanh::lean_ctor_get(v___x_5785_, 0);
                        v_isSharedCheck_5799_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5785_)) as u8;
                        if v_isSharedCheck_5799_ == 0 {
                            v___x_5788_ = v___x_5785_;
                            v_isShared_5789_ = v_isSharedCheck_5799_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5786_);
                            crate::leanh::lean_dec(v___x_5785_);
                            v___x_5788_ = crate::leanh::lean_box(0);
                            v_isShared_5789_ = v_isSharedCheck_5799_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_5800_ = crate::leanh::lean_ctor_get(v___x_5785_, 0);
                        v_isSharedCheck_5807_ =
                            (!crate::leanh::lean_is_exclusive(v___x_5785_)) as u8;
                        if v_isSharedCheck_5807_ == 0 {
                            v___x_5802_ = v___x_5785_;
                            v_isShared_5803_ = v_isSharedCheck_5807_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_5800_);
                            crate::leanh::lean_dec(v___x_5785_);
                            v___x_5802_ = crate::leanh::lean_box(0);
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
                v_fst_5790_ = crate::leanh::lean_ctor_get(v_a_5786_, 0);
                if crate::leanh::lean_obj_tag(v_fst_5790_) == 0 {
                    v_snd_5791_ = crate::leanh::lean_ctor_get(v_a_5786_, 1);
                    crate::leanh::lean_inc(v_snd_5791_);
                    crate::leanh::lean_dec(v_a_5786_);
                    if v_isShared_5789_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5788_, 0, v_snd_5791_);
                        v___x_5793_ = v___x_5788_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_5794_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5794_, 0, v_snd_5791_);
                        v___x_5793_ = v_reuseFailAlloc_5794_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_5790_);
                    crate::leanh::lean_dec(v_a_5786_);
                    v_val_5795_ = crate::leanh::lean_ctor_get(v_fst_5790_, 0);
                    crate::leanh::lean_inc(v_val_5795_);
                    crate::leanh::lean_dec_ref_known(v_fst_5790_, 1);
                    if v_isShared_5789_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5788_, 0, v_val_5795_);
                        v___x_5797_ = v___x_5788_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_5798_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5798_, 0, v_val_5795_);
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
                    v_reuseFailAlloc_5806_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5806_, 0, v_a_5800_);
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
                    v_reuseFailAlloc_5815_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5815_, 0, v_a_5809_);
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
    mut v_____s_5817_: *mut crate::leanh::LeanObject,
    mut v_t_5818_: *mut crate::leanh::LeanObject,
    mut v_init_5819_: *mut crate::leanh::LeanObject,
    mut v___y_5820_: *mut crate::leanh::LeanObject,
    mut v___y_5821_: *mut crate::leanh::LeanObject,
    mut v___y_5822_: *mut crate::leanh::LeanObject,
    mut v___y_5823_: *mut crate::leanh::LeanObject,
    mut v___y_5824_: *mut crate::leanh::LeanObject,
    mut v___y_5825_: *mut crate::leanh::LeanObject,
    mut v___y_5826_: *mut crate::leanh::LeanObject,
    mut v___y_5827_: *mut crate::leanh::LeanObject,
    mut v___y_5828_: *mut crate::leanh::LeanObject,
    mut v___y_5829_: *mut crate::leanh::LeanObject,
    mut v___y_5830_: *mut crate::leanh::LeanObject,
    mut v___y_5831_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_5832_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_5832_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_____s_5817_, v_t_5818_, v_init_5819_, v___y_5820_, v___y_5821_, v___y_5822_, v___y_5823_, v___y_5824_, v___y_5825_, v___y_5826_, v___y_5827_, v___y_5828_, v___y_5829_, v___y_5830_);
    crate::leanh::lean_dec(v___y_5830_);
    crate::leanh::lean_dec_ref(v___y_5829_);
    crate::leanh::lean_dec(v___y_5828_);
    crate::leanh::lean_dec_ref(v___y_5827_);
    crate::leanh::lean_dec(v___y_5826_);
    crate::leanh::lean_dec_ref(v___y_5825_);
    crate::leanh::lean_dec(v___y_5824_);
    crate::leanh::lean_dec_ref(v___y_5823_);
    crate::leanh::lean_dec(v___y_5822_);
    crate::leanh::lean_dec(v___y_5821_);
    crate::leanh::lean_dec(v___y_5820_);
    crate::leanh::lean_dec_ref(v_t_5818_);
    crate::leanh::lean_dec(v_____s_5817_);
    return v_res_5832_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(
    mut v_as_5833_: *mut crate::leanh::LeanObject,
    mut v_sz_5834_: usize,
    mut v_i_5835_: usize,
    mut v_b_5836_: *mut crate::leanh::LeanObject,
    mut v___y_5837_: *mut crate::leanh::LeanObject,
    mut v___y_5838_: *mut crate::leanh::LeanObject,
    mut v___y_5839_: *mut crate::leanh::LeanObject,
    mut v___y_5840_: *mut crate::leanh::LeanObject,
    mut v___y_5841_: *mut crate::leanh::LeanObject,
    mut v___y_5842_: *mut crate::leanh::LeanObject,
    mut v___y_5843_: *mut crate::leanh::LeanObject,
    mut v___y_5844_: *mut crate::leanh::LeanObject,
    mut v___y_5845_: *mut crate::leanh::LeanObject,
    mut v___y_5846_: *mut crate::leanh::LeanObject,
    mut v___y_5847_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5849_: u8 = 0;
    let mut v___x_5850_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5851_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5853_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5854_: u8 = 0;
    let mut v_a_5855_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5856_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5857_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5858_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5859_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5860_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5862_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5863_: usize = 0;
    let mut v___x_5864_: usize = 0;
    let mut v_reuseFailAlloc_5866_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5867_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5869_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5870_: u8 = 0;
    let mut v___x_5872_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5873_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5874_: u8 = 0;
    let mut v_isSharedCheck_5875_: u8 = 0;
    let mut v_unused_5876_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5849_ = lean_usize_dec_lt(v_i_5835_, v_sz_5834_);
                if v___x_5849_ == 0 {
                    v___x_5850_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5850_, 0, v_b_5836_);
                    return v___x_5850_;
                } else {
                    v_snd_5851_ = crate::leanh::lean_ctor_get(v_b_5836_, 1);
                    v_isSharedCheck_5875_ = (!crate::leanh::lean_is_exclusive(v_b_5836_)) as u8;
                    if v_isSharedCheck_5875_ == 0 {
                        v_unused_5876_ = crate::leanh::lean_ctor_get(v_b_5836_, 0);
                        crate::leanh::lean_dec(v_unused_5876_);
                        v___x_5853_ = v_b_5836_;
                        v_isShared_5854_ = v_isSharedCheck_5875_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5851_);
                        crate::leanh::lean_dec(v_b_5836_);
                        v___x_5853_ = crate::leanh::lean_box(0);
                        v_isShared_5854_ = v_isSharedCheck_5875_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5855_ = lean_array_uget_borrowed(v_as_5833_, v_i_5835_);
                v___x_5856_ = crate::leanh::lean_box(0);
                v___x_5857_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5851_, v_a_5855_, v___x_5856_, v___y_5837_, v___y_5838_, v___y_5839_, v___y_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
                if crate::leanh::lean_obj_tag(v___x_5857_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5857_, 1);
                    v___x_5858_ = crate::leanh::lean_box(0);
                    v___x_5859_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5860_ = lean_nat_add(v_snd_5851_, v___x_5859_);
                    crate::leanh::lean_dec(v_snd_5851_);
                    if v_isShared_5854_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5853_, 1, v___x_5860_);
                        crate::leanh::lean_ctor_set(v___x_5853_, 0, v___x_5858_);
                        v___x_5862_ = v___x_5853_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5866_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 0, v___x_5858_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5866_, 1, v___x_5860_);
                        v___x_5862_ = v_reuseFailAlloc_5866_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5853_);
                    crate::leanh::lean_dec(v_snd_5851_);
                    v_a_5867_ = crate::leanh::lean_ctor_get(v___x_5857_, 0);
                    v_isSharedCheck_5874_ = (!crate::leanh::lean_is_exclusive(v___x_5857_)) as u8;
                    if v_isSharedCheck_5874_ == 0 {
                        v___x_5869_ = v___x_5857_;
                        v_isShared_5870_ = v_isSharedCheck_5874_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5867_);
                        crate::leanh::lean_dec(v___x_5857_);
                        v___x_5869_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5873_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5873_, 0, v_a_5867_);
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
    mut v_as_5877_: *mut crate::leanh::LeanObject,
    mut v_sz_5878_: *mut crate::leanh::LeanObject,
    mut v_i_5879_: *mut crate::leanh::LeanObject,
    mut v_b_5880_: *mut crate::leanh::LeanObject,
    mut v___y_5881_: *mut crate::leanh::LeanObject,
    mut v___y_5882_: *mut crate::leanh::LeanObject,
    mut v___y_5883_: *mut crate::leanh::LeanObject,
    mut v___y_5884_: *mut crate::leanh::LeanObject,
    mut v___y_5885_: *mut crate::leanh::LeanObject,
    mut v___y_5886_: *mut crate::leanh::LeanObject,
    mut v___y_5887_: *mut crate::leanh::LeanObject,
    mut v___y_5888_: *mut crate::leanh::LeanObject,
    mut v___y_5889_: *mut crate::leanh::LeanObject,
    mut v___y_5890_: *mut crate::leanh::LeanObject,
    mut v___y_5891_: *mut crate::leanh::LeanObject,
    mut v___y_5892_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5893_: usize = 0;
    let mut v_i_boxed_5894_: usize = 0;
    let mut v_res_5895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5893_ = crate::leanh::lean_unbox_usize(v_sz_5878_);
    crate::leanh::lean_dec(v_sz_5878_);
    v_i_boxed_5894_ = crate::leanh::lean_unbox_usize(v_i_5879_);
    crate::leanh::lean_dec(v_i_5879_);
    v_res_5895_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4_spec__10(v_as_5877_, v_sz_boxed_5893_, v_i_boxed_5894_, v_b_5880_, v___y_5881_, v___y_5882_, v___y_5883_, v___y_5884_, v___y_5885_, v___y_5886_, v___y_5887_, v___y_5888_, v___y_5889_, v___y_5890_, v___y_5891_);
    crate::leanh::lean_dec(v___y_5891_);
    crate::leanh::lean_dec_ref(v___y_5890_);
    crate::leanh::lean_dec(v___y_5889_);
    crate::leanh::lean_dec_ref(v___y_5888_);
    crate::leanh::lean_dec(v___y_5887_);
    crate::leanh::lean_dec_ref(v___y_5886_);
    crate::leanh::lean_dec(v___y_5885_);
    crate::leanh::lean_dec_ref(v___y_5884_);
    crate::leanh::lean_dec(v___y_5883_);
    crate::leanh::lean_dec(v___y_5882_);
    crate::leanh::lean_dec(v___y_5881_);
    crate::leanh::lean_dec_ref(v_as_5877_);
    return v_res_5895_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(
    mut v_as_5896_: *mut crate::leanh::LeanObject,
    mut v_sz_5897_: usize,
    mut v_i_5898_: usize,
    mut v_b_5899_: *mut crate::leanh::LeanObject,
    mut v___y_5900_: *mut crate::leanh::LeanObject,
    mut v___y_5901_: *mut crate::leanh::LeanObject,
    mut v___y_5902_: *mut crate::leanh::LeanObject,
    mut v___y_5903_: *mut crate::leanh::LeanObject,
    mut v___y_5904_: *mut crate::leanh::LeanObject,
    mut v___y_5905_: *mut crate::leanh::LeanObject,
    mut v___y_5906_: *mut crate::leanh::LeanObject,
    mut v___y_5907_: *mut crate::leanh::LeanObject,
    mut v___y_5908_: *mut crate::leanh::LeanObject,
    mut v___y_5909_: *mut crate::leanh::LeanObject,
    mut v___y_5910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5912_: u8 = 0;
    let mut v___x_5913_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5914_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5916_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5917_: u8 = 0;
    let mut v_a_5918_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5919_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5920_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5921_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5922_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5923_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5925_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5926_: usize = 0;
    let mut v___x_5927_: usize = 0;
    let mut v___x_5928_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5929_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5932_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5933_: u8 = 0;
    let mut v___x_5935_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5936_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_5937_: u8 = 0;
    let mut v_isSharedCheck_5938_: u8 = 0;
    let mut v_unused_5939_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5912_ = lean_usize_dec_lt(v_i_5898_, v_sz_5897_);
                if v___x_5912_ == 0 {
                    v___x_5913_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5913_, 0, v_b_5899_);
                    return v___x_5913_;
                } else {
                    v_snd_5914_ = crate::leanh::lean_ctor_get(v_b_5899_, 1);
                    v_isSharedCheck_5938_ = (!crate::leanh::lean_is_exclusive(v_b_5899_)) as u8;
                    if v_isSharedCheck_5938_ == 0 {
                        v_unused_5939_ = crate::leanh::lean_ctor_get(v_b_5899_, 0);
                        crate::leanh::lean_dec(v_unused_5939_);
                        v___x_5916_ = v_b_5899_;
                        v_isShared_5917_ = v_isSharedCheck_5938_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5914_);
                        crate::leanh::lean_dec(v_b_5899_);
                        v___x_5916_ = crate::leanh::lean_box(0);
                        v_isShared_5917_ = v_isSharedCheck_5938_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5918_ = lean_array_uget_borrowed(v_as_5896_, v_i_5898_);
                v___x_5919_ = crate::leanh::lean_box(0);
                v___x_5920_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5914_, v_a_5918_, v___x_5919_, v___y_5900_, v___y_5901_, v___y_5902_, v___y_5903_, v___y_5904_, v___y_5905_, v___y_5906_, v___y_5907_, v___y_5908_, v___y_5909_, v___y_5910_);
                if crate::leanh::lean_obj_tag(v___x_5920_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5920_, 1);
                    v___x_5921_ = crate::leanh::lean_box(0);
                    v___x_5922_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5923_ = lean_nat_add(v_snd_5914_, v___x_5922_);
                    crate::leanh::lean_dec(v_snd_5914_);
                    if v_isShared_5917_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5916_, 1, v___x_5923_);
                        crate::leanh::lean_ctor_set(v___x_5916_, 0, v___x_5921_);
                        v___x_5925_ = v___x_5916_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5929_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 0, v___x_5921_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5929_, 1, v___x_5923_);
                        v___x_5925_ = v_reuseFailAlloc_5929_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5916_);
                    crate::leanh::lean_dec(v_snd_5914_);
                    v_a_5930_ = crate::leanh::lean_ctor_get(v___x_5920_, 0);
                    v_isSharedCheck_5937_ = (!crate::leanh::lean_is_exclusive(v___x_5920_)) as u8;
                    if v_isSharedCheck_5937_ == 0 {
                        v___x_5932_ = v___x_5920_;
                        v_isShared_5933_ = v_isSharedCheck_5937_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5930_);
                        crate::leanh::lean_dec(v___x_5920_);
                        v___x_5932_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5936_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5936_, 0, v_a_5930_);
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
    mut v_as_5940_: *mut crate::leanh::LeanObject,
    mut v_sz_5941_: *mut crate::leanh::LeanObject,
    mut v_i_5942_: *mut crate::leanh::LeanObject,
    mut v_b_5943_: *mut crate::leanh::LeanObject,
    mut v___y_5944_: *mut crate::leanh::LeanObject,
    mut v___y_5945_: *mut crate::leanh::LeanObject,
    mut v___y_5946_: *mut crate::leanh::LeanObject,
    mut v___y_5947_: *mut crate::leanh::LeanObject,
    mut v___y_5948_: *mut crate::leanh::LeanObject,
    mut v___y_5949_: *mut crate::leanh::LeanObject,
    mut v___y_5950_: *mut crate::leanh::LeanObject,
    mut v___y_5951_: *mut crate::leanh::LeanObject,
    mut v___y_5952_: *mut crate::leanh::LeanObject,
    mut v___y_5953_: *mut crate::leanh::LeanObject,
    mut v___y_5954_: *mut crate::leanh::LeanObject,
    mut v___y_5955_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_5956_: usize = 0;
    let mut v_i_boxed_5957_: usize = 0;
    let mut v_res_5958_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_5956_ = crate::leanh::lean_unbox_usize(v_sz_5941_);
    crate::leanh::lean_dec(v_sz_5941_);
    v_i_boxed_5957_ = crate::leanh::lean_unbox_usize(v_i_5942_);
    crate::leanh::lean_dec(v_i_5942_);
    v_res_5958_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_as_5940_, v_sz_boxed_5956_, v_i_boxed_5957_, v_b_5943_, v___y_5944_, v___y_5945_, v___y_5946_, v___y_5947_, v___y_5948_, v___y_5949_, v___y_5950_, v___y_5951_, v___y_5952_, v___y_5953_, v___y_5954_);
    crate::leanh::lean_dec(v___y_5954_);
    crate::leanh::lean_dec_ref(v___y_5953_);
    crate::leanh::lean_dec(v___y_5952_);
    crate::leanh::lean_dec_ref(v___y_5951_);
    crate::leanh::lean_dec(v___y_5950_);
    crate::leanh::lean_dec_ref(v___y_5949_);
    crate::leanh::lean_dec(v___y_5948_);
    crate::leanh::lean_dec_ref(v___y_5947_);
    crate::leanh::lean_dec(v___y_5946_);
    crate::leanh::lean_dec(v___y_5945_);
    crate::leanh::lean_dec(v___y_5944_);
    crate::leanh::lean_dec_ref(v_as_5940_);
    return v_res_5958_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(
    mut v_as_5959_: *mut crate::leanh::LeanObject,
    mut v_sz_5960_: usize,
    mut v_i_5961_: usize,
    mut v_b_5962_: *mut crate::leanh::LeanObject,
    mut v___y_5963_: *mut crate::leanh::LeanObject,
    mut v___y_5964_: *mut crate::leanh::LeanObject,
    mut v___y_5965_: *mut crate::leanh::LeanObject,
    mut v___y_5966_: *mut crate::leanh::LeanObject,
    mut v___y_5967_: *mut crate::leanh::LeanObject,
    mut v___y_5968_: *mut crate::leanh::LeanObject,
    mut v___y_5969_: *mut crate::leanh::LeanObject,
    mut v___y_5970_: *mut crate::leanh::LeanObject,
    mut v___y_5971_: *mut crate::leanh::LeanObject,
    mut v___y_5972_: *mut crate::leanh::LeanObject,
    mut v___y_5973_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_5975_: u8 = 0;
    let mut v___x_5976_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_5977_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5979_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5980_: u8 = 0;
    let mut v_a_5981_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5982_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5983_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5984_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5985_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5986_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5988_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5989_: usize = 0;
    let mut v___x_5990_: usize = 0;
    let mut v_reuseFailAlloc_5992_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_5993_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5995_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_5996_: u8 = 0;
    let mut v___x_5998_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_5999_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6000_: u8 = 0;
    let mut v_isSharedCheck_6001_: u8 = 0;
    let mut v_unused_6002_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_5975_ = lean_usize_dec_lt(v_i_5961_, v_sz_5960_);
                if v___x_5975_ == 0 {
                    v___x_5976_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_5976_, 0, v_b_5962_);
                    return v___x_5976_;
                } else {
                    v_snd_5977_ = crate::leanh::lean_ctor_get(v_b_5962_, 1);
                    v_isSharedCheck_6001_ = (!crate::leanh::lean_is_exclusive(v_b_5962_)) as u8;
                    if v_isSharedCheck_6001_ == 0 {
                        v_unused_6002_ = crate::leanh::lean_ctor_get(v_b_5962_, 0);
                        crate::leanh::lean_dec(v_unused_6002_);
                        v___x_5979_ = v_b_5962_;
                        v_isShared_5980_ = v_isSharedCheck_6001_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_5977_);
                        crate::leanh::lean_dec(v_b_5962_);
                        v___x_5979_ = crate::leanh::lean_box(0);
                        v_isShared_5980_ = v_isSharedCheck_6001_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_5981_ = lean_array_uget_borrowed(v_as_5959_, v_i_5961_);
                v___x_5982_ = crate::leanh::lean_box(0);
                v___x_5983_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_5977_, v_a_5981_, v___x_5982_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_, v___y_5967_, v___y_5968_, v___y_5969_, v___y_5970_, v___y_5971_, v___y_5972_, v___y_5973_);
                if crate::leanh::lean_obj_tag(v___x_5983_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_5983_, 1);
                    v___x_5984_ = crate::leanh::lean_box(0);
                    v___x_5985_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_5986_ = lean_nat_add(v_snd_5977_, v___x_5985_);
                    crate::leanh::lean_dec(v_snd_5977_);
                    if v_isShared_5980_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_5979_, 1, v___x_5986_);
                        crate::leanh::lean_ctor_set(v___x_5979_, 0, v___x_5984_);
                        v___x_5988_ = v___x_5979_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_5992_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 0, v___x_5984_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_5992_, 1, v___x_5986_);
                        v___x_5988_ = v_reuseFailAlloc_5992_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_5979_);
                    crate::leanh::lean_dec(v_snd_5977_);
                    v_a_5993_ = crate::leanh::lean_ctor_get(v___x_5983_, 0);
                    v_isSharedCheck_6000_ = (!crate::leanh::lean_is_exclusive(v___x_5983_)) as u8;
                    if v_isSharedCheck_6000_ == 0 {
                        v___x_5995_ = v___x_5983_;
                        v_isShared_5996_ = v_isSharedCheck_6000_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_5993_);
                        crate::leanh::lean_dec(v___x_5983_);
                        v___x_5995_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_5999_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_5999_, 0, v_a_5993_);
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
    mut v_as_6003_: *mut crate::leanh::LeanObject,
    mut v_sz_6004_: *mut crate::leanh::LeanObject,
    mut v_i_6005_: *mut crate::leanh::LeanObject,
    mut v_b_6006_: *mut crate::leanh::LeanObject,
    mut v___y_6007_: *mut crate::leanh::LeanObject,
    mut v___y_6008_: *mut crate::leanh::LeanObject,
    mut v___y_6009_: *mut crate::leanh::LeanObject,
    mut v___y_6010_: *mut crate::leanh::LeanObject,
    mut v___y_6011_: *mut crate::leanh::LeanObject,
    mut v___y_6012_: *mut crate::leanh::LeanObject,
    mut v___y_6013_: *mut crate::leanh::LeanObject,
    mut v___y_6014_: *mut crate::leanh::LeanObject,
    mut v___y_6015_: *mut crate::leanh::LeanObject,
    mut v___y_6016_: *mut crate::leanh::LeanObject,
    mut v___y_6017_: *mut crate::leanh::LeanObject,
    mut v___y_6018_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6019_: usize = 0;
    let mut v_i_boxed_6020_: usize = 0;
    let mut v_res_6021_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6019_ = crate::leanh::lean_unbox_usize(v_sz_6004_);
    crate::leanh::lean_dec(v_sz_6004_);
    v_i_boxed_6020_ = crate::leanh::lean_unbox_usize(v_i_6005_);
    crate::leanh::lean_dec(v_i_6005_);
    v_res_6021_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8_spec__10(v_as_6003_, v_sz_boxed_6019_, v_i_boxed_6020_, v_b_6006_, v___y_6007_, v___y_6008_, v___y_6009_, v___y_6010_, v___y_6011_, v___y_6012_, v___y_6013_, v___y_6014_, v___y_6015_, v___y_6016_, v___y_6017_);
    crate::leanh::lean_dec(v___y_6017_);
    crate::leanh::lean_dec_ref(v___y_6016_);
    crate::leanh::lean_dec(v___y_6015_);
    crate::leanh::lean_dec_ref(v___y_6014_);
    crate::leanh::lean_dec(v___y_6013_);
    crate::leanh::lean_dec_ref(v___y_6012_);
    crate::leanh::lean_dec(v___y_6011_);
    crate::leanh::lean_dec_ref(v___y_6010_);
    crate::leanh::lean_dec(v___y_6009_);
    crate::leanh::lean_dec(v___y_6008_);
    crate::leanh::lean_dec(v___y_6007_);
    crate::leanh::lean_dec_ref(v_as_6003_);
    return v_res_6021_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(
    mut v_as_6022_: *mut crate::leanh::LeanObject,
    mut v_sz_6023_: usize,
    mut v_i_6024_: usize,
    mut v_b_6025_: *mut crate::leanh::LeanObject,
    mut v___y_6026_: *mut crate::leanh::LeanObject,
    mut v___y_6027_: *mut crate::leanh::LeanObject,
    mut v___y_6028_: *mut crate::leanh::LeanObject,
    mut v___y_6029_: *mut crate::leanh::LeanObject,
    mut v___y_6030_: *mut crate::leanh::LeanObject,
    mut v___y_6031_: *mut crate::leanh::LeanObject,
    mut v___y_6032_: *mut crate::leanh::LeanObject,
    mut v___y_6033_: *mut crate::leanh::LeanObject,
    mut v___y_6034_: *mut crate::leanh::LeanObject,
    mut v___y_6035_: *mut crate::leanh::LeanObject,
    mut v___y_6036_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6038_: u8 = 0;
    let mut v___x_6039_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6040_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6042_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6043_: u8 = 0;
    let mut v_a_6044_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6045_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6046_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6047_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6048_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6049_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6051_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6052_: usize = 0;
    let mut v___x_6053_: usize = 0;
    let mut v___x_6054_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6055_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6056_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6059_: u8 = 0;
    let mut v___x_6061_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6062_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6063_: u8 = 0;
    let mut v_isSharedCheck_6064_: u8 = 0;
    let mut v_unused_6065_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6038_ = lean_usize_dec_lt(v_i_6024_, v_sz_6023_);
                if v___x_6038_ == 0 {
                    v___x_6039_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6039_, 0, v_b_6025_);
                    return v___x_6039_;
                } else {
                    v_snd_6040_ = crate::leanh::lean_ctor_get(v_b_6025_, 1);
                    v_isSharedCheck_6064_ = (!crate::leanh::lean_is_exclusive(v_b_6025_)) as u8;
                    if v_isSharedCheck_6064_ == 0 {
                        v_unused_6065_ = crate::leanh::lean_ctor_get(v_b_6025_, 0);
                        crate::leanh::lean_dec(v_unused_6065_);
                        v___x_6042_ = v_b_6025_;
                        v_isShared_6043_ = v_isSharedCheck_6064_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6040_);
                        crate::leanh::lean_dec(v_b_6025_);
                        v___x_6042_ = crate::leanh::lean_box(0);
                        v_isShared_6043_ = v_isSharedCheck_6064_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6044_ = lean_array_uget_borrowed(v_as_6022_, v_i_6024_);
                v___x_6045_ = crate::leanh::lean_box(0);
                v___x_6046_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__0(v_snd_6040_, v_a_6044_, v___x_6045_, v___y_6026_, v___y_6027_, v___y_6028_, v___y_6029_, v___y_6030_, v___y_6031_, v___y_6032_, v___y_6033_, v___y_6034_, v___y_6035_, v___y_6036_);
                if crate::leanh::lean_obj_tag(v___x_6046_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___x_6046_, 1);
                    v___x_6047_ = crate::leanh::lean_box(0);
                    v___x_6048_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_6049_ = lean_nat_add(v_snd_6040_, v___x_6048_);
                    crate::leanh::lean_dec(v_snd_6040_);
                    if v_isShared_6043_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6042_, 1, v___x_6049_);
                        crate::leanh::lean_ctor_set(v___x_6042_, 0, v___x_6047_);
                        v___x_6051_ = v___x_6042_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6055_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 0, v___x_6047_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6055_, 1, v___x_6049_);
                        v___x_6051_ = v_reuseFailAlloc_6055_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6042_);
                    crate::leanh::lean_dec(v_snd_6040_);
                    v_a_6056_ = crate::leanh::lean_ctor_get(v___x_6046_, 0);
                    v_isSharedCheck_6063_ = (!crate::leanh::lean_is_exclusive(v___x_6046_)) as u8;
                    if v_isSharedCheck_6063_ == 0 {
                        v___x_6058_ = v___x_6046_;
                        v_isShared_6059_ = v_isSharedCheck_6063_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6056_);
                        crate::leanh::lean_dec(v___x_6046_);
                        v___x_6058_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6062_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6062_, 0, v_a_6056_);
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
    mut v_as_6066_: *mut crate::leanh::LeanObject,
    mut v_sz_6067_: *mut crate::leanh::LeanObject,
    mut v_i_6068_: *mut crate::leanh::LeanObject,
    mut v_b_6069_: *mut crate::leanh::LeanObject,
    mut v___y_6070_: *mut crate::leanh::LeanObject,
    mut v___y_6071_: *mut crate::leanh::LeanObject,
    mut v___y_6072_: *mut crate::leanh::LeanObject,
    mut v___y_6073_: *mut crate::leanh::LeanObject,
    mut v___y_6074_: *mut crate::leanh::LeanObject,
    mut v___y_6075_: *mut crate::leanh::LeanObject,
    mut v___y_6076_: *mut crate::leanh::LeanObject,
    mut v___y_6077_: *mut crate::leanh::LeanObject,
    mut v___y_6078_: *mut crate::leanh::LeanObject,
    mut v___y_6079_: *mut crate::leanh::LeanObject,
    mut v___y_6080_: *mut crate::leanh::LeanObject,
    mut v___y_6081_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_sz_boxed_6082_: usize = 0;
    let mut v_i_boxed_6083_: usize = 0;
    let mut v_res_6084_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6082_ = crate::leanh::lean_unbox_usize(v_sz_6067_);
    crate::leanh::lean_dec(v_sz_6067_);
    v_i_boxed_6083_ = crate::leanh::lean_unbox_usize(v_i_6068_);
    crate::leanh::lean_dec(v_i_6068_);
    v_res_6084_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_as_6066_, v_sz_boxed_6082_, v_i_boxed_6083_, v_b_6069_, v___y_6070_, v___y_6071_, v___y_6072_, v___y_6073_, v___y_6074_, v___y_6075_, v___y_6076_, v___y_6077_, v___y_6078_, v___y_6079_, v___y_6080_);
    crate::leanh::lean_dec(v___y_6080_);
    crate::leanh::lean_dec_ref(v___y_6079_);
    crate::leanh::lean_dec(v___y_6078_);
    crate::leanh::lean_dec_ref(v___y_6077_);
    crate::leanh::lean_dec(v___y_6076_);
    crate::leanh::lean_dec_ref(v___y_6075_);
    crate::leanh::lean_dec(v___y_6074_);
    crate::leanh::lean_dec_ref(v___y_6073_);
    crate::leanh::lean_dec(v___y_6072_);
    crate::leanh::lean_dec(v___y_6071_);
    crate::leanh::lean_dec(v___y_6070_);
    crate::leanh::lean_dec_ref(v_as_6066_);
    return v_res_6084_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(
    mut v_init_6085_: *mut crate::leanh::LeanObject,
    mut v_n_6086_: *mut crate::leanh::LeanObject,
    mut v_b_6087_: *mut crate::leanh::LeanObject,
    mut v___y_6088_: *mut crate::leanh::LeanObject,
    mut v___y_6089_: *mut crate::leanh::LeanObject,
    mut v___y_6090_: *mut crate::leanh::LeanObject,
    mut v___y_6091_: *mut crate::leanh::LeanObject,
    mut v___y_6092_: *mut crate::leanh::LeanObject,
    mut v___y_6093_: *mut crate::leanh::LeanObject,
    mut v___y_6094_: *mut crate::leanh::LeanObject,
    mut v___y_6095_: *mut crate::leanh::LeanObject,
    mut v___y_6096_: *mut crate::leanh::LeanObject,
    mut v___y_6097_: *mut crate::leanh::LeanObject,
    mut v___y_6098_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_cs_6100_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6101_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6102_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6103_: usize = 0;
    let mut v___x_6104_: usize = 0;
    let mut v___x_6105_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6106_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6108_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6109_: u8 = 0;
    let mut v_fst_6110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6111_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6112_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6119_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6120_: u8 = 0;
    let mut v_a_6121_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6123_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6124_: u8 = 0;
    let mut v___x_6126_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6127_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6128_: u8 = 0;
    let mut v_vs_6129_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6130_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6131_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6132_: usize = 0;
    let mut v___x_6133_: usize = 0;
    let mut v___x_6134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6138_: u8 = 0;
    let mut v_fst_6139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6140_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6141_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6145_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6147_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6148_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6149_: u8 = 0;
    let mut v_a_6150_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6152_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6153_: u8 = 0;
    let mut v___x_6155_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6156_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6157_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_n_6086_) == 0 {
                    v_cs_6100_ = crate::leanh::lean_ctor_get(v_n_6086_, 0);
                    v___x_6101_ = crate::leanh::lean_box(0);
                    v___x_6102_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6102_, 0, v___x_6101_);
                    crate::leanh::lean_ctor_set(v___x_6102_, 1, v_b_6087_);
                    v_sz_6103_ = lean_array_size(v_cs_6100_);
                    v___x_6104_ = 0usize;
                    v___x_6105_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_6085_, v_cs_6100_, v_sz_6103_, v___x_6104_, v___x_6102_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
                    if crate::leanh::lean_obj_tag(v___x_6105_) == 0 {
                        v_a_6106_ = crate::leanh::lean_ctor_get(v___x_6105_, 0);
                        v_isSharedCheck_6120_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6120_ == 0 {
                            v___x_6108_ = v___x_6105_;
                            v_isShared_6109_ = v_isSharedCheck_6120_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6106_);
                            crate::leanh::lean_dec(v___x_6105_);
                            v___x_6108_ = crate::leanh::lean_box(0);
                            v_isShared_6109_ = v_isSharedCheck_6120_;
                            state = 1;
                            continue;
                        }
                    } else {
                        v_a_6121_ = crate::leanh::lean_ctor_get(v___x_6105_, 0);
                        v_isSharedCheck_6128_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6105_)) as u8;
                        if v_isSharedCheck_6128_ == 0 {
                            v___x_6123_ = v___x_6105_;
                            v_isShared_6124_ = v_isSharedCheck_6128_;
                            state = 4;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6121_);
                            crate::leanh::lean_dec(v___x_6105_);
                            v___x_6123_ = crate::leanh::lean_box(0);
                            v_isShared_6124_ = v_isSharedCheck_6128_;
                            state = 4;
                            continue;
                        }
                    }
                } else {
                    v_vs_6129_ = crate::leanh::lean_ctor_get(v_n_6086_, 0);
                    v___x_6130_ = crate::leanh::lean_box(0);
                    v___x_6131_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6131_, 0, v___x_6130_);
                    crate::leanh::lean_ctor_set(v___x_6131_, 1, v_b_6087_);
                    v_sz_6132_ = lean_array_size(v_vs_6129_);
                    v___x_6133_ = 0usize;
                    v___x_6134_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__8(v_vs_6129_, v_sz_6132_, v___x_6133_, v___x_6131_, v___y_6088_, v___y_6089_, v___y_6090_, v___y_6091_, v___y_6092_, v___y_6093_, v___y_6094_, v___y_6095_, v___y_6096_, v___y_6097_, v___y_6098_);
                    if crate::leanh::lean_obj_tag(v___x_6134_) == 0 {
                        v_a_6135_ = crate::leanh::lean_ctor_get(v___x_6134_, 0);
                        v_isSharedCheck_6149_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6134_)) as u8;
                        if v_isSharedCheck_6149_ == 0 {
                            v___x_6137_ = v___x_6134_;
                            v_isShared_6138_ = v_isSharedCheck_6149_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6135_);
                            crate::leanh::lean_dec(v___x_6134_);
                            v___x_6137_ = crate::leanh::lean_box(0);
                            v_isShared_6138_ = v_isSharedCheck_6149_;
                            state = 6;
                            continue;
                        }
                    } else {
                        v_a_6150_ = crate::leanh::lean_ctor_get(v___x_6134_, 0);
                        v_isSharedCheck_6157_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6134_)) as u8;
                        if v_isSharedCheck_6157_ == 0 {
                            v___x_6152_ = v___x_6134_;
                            v_isShared_6153_ = v_isSharedCheck_6157_;
                            state = 9;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6150_);
                            crate::leanh::lean_dec(v___x_6134_);
                            v___x_6152_ = crate::leanh::lean_box(0);
                            v_isShared_6153_ = v_isSharedCheck_6157_;
                            state = 9;
                            continue;
                        }
                    }
                }
            }
            1 => {
                v_fst_6110_ = crate::leanh::lean_ctor_get(v_a_6106_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6110_) == 0 {
                    v_snd_6111_ = crate::leanh::lean_ctor_get(v_a_6106_, 1);
                    crate::leanh::lean_inc(v_snd_6111_);
                    crate::leanh::lean_dec(v_a_6106_);
                    v___x_6112_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6112_, 0, v_snd_6111_);
                    if v_isShared_6109_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6108_, 0, v___x_6112_);
                        v___x_6114_ = v___x_6108_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6115_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6115_, 0, v___x_6112_);
                        v___x_6114_ = v_reuseFailAlloc_6115_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6110_);
                    crate::leanh::lean_dec(v_a_6106_);
                    v_val_6116_ = crate::leanh::lean_ctor_get(v_fst_6110_, 0);
                    crate::leanh::lean_inc(v_val_6116_);
                    crate::leanh::lean_dec_ref_known(v_fst_6110_, 1);
                    if v_isShared_6109_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6108_, 0, v_val_6116_);
                        v___x_6118_ = v___x_6108_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6119_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6119_, 0, v_val_6116_);
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
                    v_reuseFailAlloc_6127_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6127_, 0, v_a_6121_);
                    v___x_6126_ = v_reuseFailAlloc_6127_;
                    state = 5;
                    continue;
                }
            }
            5 => {
                return v___x_6126_;
            }
            6 => {
                v_fst_6139_ = crate::leanh::lean_ctor_get(v_a_6135_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6139_) == 0 {
                    v_snd_6140_ = crate::leanh::lean_ctor_get(v_a_6135_, 1);
                    crate::leanh::lean_inc(v_snd_6140_);
                    crate::leanh::lean_dec(v_a_6135_);
                    v___x_6141_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6141_, 0, v_snd_6140_);
                    if v_isShared_6138_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6137_, 0, v___x_6141_);
                        v___x_6143_ = v___x_6137_;
                        state = 7;
                        continue;
                    } else {
                        v_reuseFailAlloc_6144_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6144_, 0, v___x_6141_);
                        v___x_6143_ = v_reuseFailAlloc_6144_;
                        state = 7;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6139_);
                    crate::leanh::lean_dec(v_a_6135_);
                    v_val_6145_ = crate::leanh::lean_ctor_get(v_fst_6139_, 0);
                    crate::leanh::lean_inc(v_val_6145_);
                    crate::leanh::lean_dec_ref_known(v_fst_6139_, 1);
                    if v_isShared_6138_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6137_, 0, v_val_6145_);
                        v___x_6147_ = v___x_6137_;
                        state = 8;
                        continue;
                    } else {
                        v_reuseFailAlloc_6148_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6148_, 0, v_val_6145_);
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
                    v_reuseFailAlloc_6156_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6156_, 0, v_a_6150_);
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
    mut v_init_6158_: *mut crate::leanh::LeanObject,
    mut v_as_6159_: *mut crate::leanh::LeanObject,
    mut v_sz_6160_: usize,
    mut v_i_6161_: usize,
    mut v_b_6162_: *mut crate::leanh::LeanObject,
    mut v___y_6163_: *mut crate::leanh::LeanObject,
    mut v___y_6164_: *mut crate::leanh::LeanObject,
    mut v___y_6165_: *mut crate::leanh::LeanObject,
    mut v___y_6166_: *mut crate::leanh::LeanObject,
    mut v___y_6167_: *mut crate::leanh::LeanObject,
    mut v___y_6168_: *mut crate::leanh::LeanObject,
    mut v___y_6169_: *mut crate::leanh::LeanObject,
    mut v___y_6170_: *mut crate::leanh::LeanObject,
    mut v___y_6171_: *mut crate::leanh::LeanObject,
    mut v___y_6172_: *mut crate::leanh::LeanObject,
    mut v___y_6173_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6175_: u8 = 0;
    let mut v___x_6176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6180_: u8 = 0;
    let mut v_a_6181_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6183_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6186_: u8 = 0;
    let mut v___x_6187_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6192_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6193_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6197_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6198_: usize = 0;
    let mut v___x_6199_: usize = 0;
    let mut v_reuseFailAlloc_6201_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6202_: u8 = 0;
    let mut v_a_6203_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6205_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6206_: u8 = 0;
    let mut v___x_6208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6209_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6210_: u8 = 0;
    let mut v_isSharedCheck_6211_: u8 = 0;
    let mut v_unused_6212_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6175_ = lean_usize_dec_lt(v_i_6161_, v_sz_6160_);
                if v___x_6175_ == 0 {
                    v___x_6176_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6176_, 0, v_b_6162_);
                    return v___x_6176_;
                } else {
                    v_snd_6177_ = crate::leanh::lean_ctor_get(v_b_6162_, 1);
                    v_isSharedCheck_6211_ = (!crate::leanh::lean_is_exclusive(v_b_6162_)) as u8;
                    if v_isSharedCheck_6211_ == 0 {
                        v_unused_6212_ = crate::leanh::lean_ctor_get(v_b_6162_, 0);
                        crate::leanh::lean_dec(v_unused_6212_);
                        v___x_6179_ = v_b_6162_;
                        v_isShared_6180_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_snd_6177_);
                        crate::leanh::lean_dec(v_b_6162_);
                        v___x_6179_ = crate::leanh::lean_box(0);
                        v_isShared_6180_ = v_isSharedCheck_6211_;
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6181_ = lean_array_uget_borrowed(v_as_6159_, v_i_6161_);
                crate::leanh::lean_inc(v_snd_6177_);
                v___x_6182_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6158_, v_a_6181_, v_snd_6177_, v___y_6163_, v___y_6164_, v___y_6165_, v___y_6166_, v___y_6167_, v___y_6168_, v___y_6169_, v___y_6170_, v___y_6171_, v___y_6172_, v___y_6173_);
                if crate::leanh::lean_obj_tag(v___x_6182_) == 0 {
                    v_a_6183_ = crate::leanh::lean_ctor_get(v___x_6182_, 0);
                    v_isSharedCheck_6202_ = (!crate::leanh::lean_is_exclusive(v___x_6182_)) as u8;
                    if v_isSharedCheck_6202_ == 0 {
                        v___x_6185_ = v___x_6182_;
                        v_isShared_6186_ = v_isSharedCheck_6202_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6183_);
                        crate::leanh::lean_dec(v___x_6182_);
                        v___x_6185_ = crate::leanh::lean_box(0);
                        v_isShared_6186_ = v_isSharedCheck_6202_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6179_);
                    crate::leanh::lean_dec(v_snd_6177_);
                    v_a_6203_ = crate::leanh::lean_ctor_get(v___x_6182_, 0);
                    v_isSharedCheck_6210_ = (!crate::leanh::lean_is_exclusive(v___x_6182_)) as u8;
                    if v_isSharedCheck_6210_ == 0 {
                        v___x_6205_ = v___x_6182_;
                        v_isShared_6206_ = v_isSharedCheck_6210_;
                        state = 6;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6203_);
                        crate::leanh::lean_dec(v___x_6182_);
                        v___x_6205_ = crate::leanh::lean_box(0);
                        v_isShared_6206_ = v_isSharedCheck_6210_;
                        state = 6;
                        continue;
                    }
                }
            }
            2 => {
                if crate::leanh::lean_obj_tag(v_a_6183_) == 0 {
                    v___x_6187_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6187_, 0, v_a_6183_);
                    if v_isShared_6180_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6179_, 0, v___x_6187_);
                        v___x_6189_ = v___x_6179_;
                        state = 3;
                        continue;
                    } else {
                        v_reuseFailAlloc_6193_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 0, v___x_6187_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6193_, 1, v_snd_6177_);
                        v___x_6189_ = v_reuseFailAlloc_6193_;
                        state = 3;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6185_);
                    crate::leanh::lean_dec(v_snd_6177_);
                    v_a_6194_ = crate::leanh::lean_ctor_get(v_a_6183_, 0);
                    crate::leanh::lean_inc(v_a_6194_);
                    crate::leanh::lean_dec_ref_known(v_a_6183_, 1);
                    v___x_6195_ = crate::leanh::lean_box(0);
                    if v_isShared_6180_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6179_, 1, v_a_6194_);
                        crate::leanh::lean_ctor_set(v___x_6179_, 0, v___x_6195_);
                        v___x_6197_ = v___x_6179_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6201_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 0, v___x_6195_);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6201_, 1, v_a_6194_);
                        v___x_6197_ = v_reuseFailAlloc_6201_;
                        state = 5;
                        continue;
                    }
                }
            }
            3 => {
                if v_isShared_6186_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6185_, 0, v___x_6189_);
                    v___x_6191_ = v___x_6185_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6192_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6192_, 0, v___x_6189_);
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
                    v_reuseFailAlloc_6209_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6209_, 0, v_a_6203_);
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
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_init_6213_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_6214_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_sz_6215_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_6216_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_6217_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_6218_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_6219_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6220_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6221_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6222_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6223_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6224_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6225_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6226_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6227_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6228_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6229_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_sz_boxed_6230_: usize = 0;
    let mut v_i_boxed_6231_: usize = 0;
    let mut v_res_6232_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_sz_boxed_6230_ = crate::leanh::lean_unbox_usize(v_sz_6215_);
    crate::leanh::lean_dec(v_sz_6215_);
    v_i_boxed_6231_ = crate::leanh::lean_unbox_usize(v_i_6216_);
    crate::leanh::lean_dec(v_i_6216_);
    v_res_6232_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3_spec__7(v_init_6213_, v_as_6214_, v_sz_boxed_6230_, v_i_boxed_6231_, v_b_6217_, v___y_6218_, v___y_6219_, v___y_6220_, v___y_6221_, v___y_6222_, v___y_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_, v___y_6228_);
    crate::leanh::lean_dec(v___y_6228_);
    crate::leanh::lean_dec_ref(v___y_6227_);
    crate::leanh::lean_dec(v___y_6226_);
    crate::leanh::lean_dec_ref(v___y_6225_);
    crate::leanh::lean_dec(v___y_6224_);
    crate::leanh::lean_dec_ref(v___y_6223_);
    crate::leanh::lean_dec(v___y_6222_);
    crate::leanh::lean_dec_ref(v___y_6221_);
    crate::leanh::lean_dec(v___y_6220_);
    crate::leanh::lean_dec(v___y_6219_);
    crate::leanh::lean_dec(v___y_6218_);
    crate::leanh::lean_dec_ref(v_as_6214_);
    crate::leanh::lean_dec(v_init_6213_);
    return v_res_6232_;
}
pub unsafe fn l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3___boxed(
    mut v_init_6233_: *mut crate::leanh::LeanObject,
    mut v_n_6234_: *mut crate::leanh::LeanObject,
    mut v_b_6235_: *mut crate::leanh::LeanObject,
    mut v___y_6236_: *mut crate::leanh::LeanObject,
    mut v___y_6237_: *mut crate::leanh::LeanObject,
    mut v___y_6238_: *mut crate::leanh::LeanObject,
    mut v___y_6239_: *mut crate::leanh::LeanObject,
    mut v___y_6240_: *mut crate::leanh::LeanObject,
    mut v___y_6241_: *mut crate::leanh::LeanObject,
    mut v___y_6242_: *mut crate::leanh::LeanObject,
    mut v___y_6243_: *mut crate::leanh::LeanObject,
    mut v___y_6244_: *mut crate::leanh::LeanObject,
    mut v___y_6245_: *mut crate::leanh::LeanObject,
    mut v___y_6246_: *mut crate::leanh::LeanObject,
    mut v___y_6247_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6248_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6248_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6233_, v_n_6234_, v_b_6235_, v___y_6236_, v___y_6237_, v___y_6238_, v___y_6239_, v___y_6240_, v___y_6241_, v___y_6242_, v___y_6243_, v___y_6244_, v___y_6245_, v___y_6246_);
    crate::leanh::lean_dec(v___y_6246_);
    crate::leanh::lean_dec_ref(v___y_6245_);
    crate::leanh::lean_dec(v___y_6244_);
    crate::leanh::lean_dec_ref(v___y_6243_);
    crate::leanh::lean_dec(v___y_6242_);
    crate::leanh::lean_dec_ref(v___y_6241_);
    crate::leanh::lean_dec(v___y_6240_);
    crate::leanh::lean_dec_ref(v___y_6239_);
    crate::leanh::lean_dec(v___y_6238_);
    crate::leanh::lean_dec(v___y_6237_);
    crate::leanh::lean_dec(v___y_6236_);
    crate::leanh::lean_dec_ref(v_n_6234_);
    crate::leanh::lean_dec(v_init_6233_);
    return v_res_6248_;
}
pub unsafe fn l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(
    mut v_t_6249_: *mut crate::leanh::LeanObject,
    mut v_init_6250_: *mut crate::leanh::LeanObject,
    mut v___y_6251_: *mut crate::leanh::LeanObject,
    mut v___y_6252_: *mut crate::leanh::LeanObject,
    mut v___y_6253_: *mut crate::leanh::LeanObject,
    mut v___y_6254_: *mut crate::leanh::LeanObject,
    mut v___y_6255_: *mut crate::leanh::LeanObject,
    mut v___y_6256_: *mut crate::leanh::LeanObject,
    mut v___y_6257_: *mut crate::leanh::LeanObject,
    mut v___y_6258_: *mut crate::leanh::LeanObject,
    mut v___y_6259_: *mut crate::leanh::LeanObject,
    mut v___y_6260_: *mut crate::leanh::LeanObject,
    mut v___y_6261_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_root_6263_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_tail_6264_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6265_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6266_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6268_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6269_: u8 = 0;
    let mut v_a_6270_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6272_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6273_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6274_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6275_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6276_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_sz_6277_: usize = 0;
    let mut v___x_6278_: usize = 0;
    let mut v___x_6279_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6280_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6282_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6283_: u8 = 0;
    let mut v_fst_6284_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6285_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6287_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6288_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6289_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6291_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6292_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6293_: u8 = 0;
    let mut v_a_6294_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6296_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6297_: u8 = 0;
    let mut v___x_6299_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6300_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6301_: u8 = 0;
    let mut v_isSharedCheck_6302_: u8 = 0;
    let mut v_a_6303_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6305_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6306_: u8 = 0;
    let mut v___x_6308_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6309_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6310_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_root_6263_ = crate::leanh::lean_ctor_get(v_t_6249_, 0);
                v_tail_6264_ = crate::leanh::lean_ctor_get(v_t_6249_, 1);
                crate::leanh::lean_inc(v_init_6250_);
                v___x_6265_ = l_Lean_PersistentArray_forInAux___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__3(v_init_6250_, v_root_6263_, v_init_6250_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
                crate::leanh::lean_dec(v_init_6250_);
                if crate::leanh::lean_obj_tag(v___x_6265_) == 0 {
                    v_a_6266_ = crate::leanh::lean_ctor_get(v___x_6265_, 0);
                    v_isSharedCheck_6302_ = (!crate::leanh::lean_is_exclusive(v___x_6265_)) as u8;
                    if v_isSharedCheck_6302_ == 0 {
                        v___x_6268_ = v___x_6265_;
                        v_isShared_6269_ = v_isSharedCheck_6302_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6266_);
                        crate::leanh::lean_dec(v___x_6265_);
                        v___x_6268_ = crate::leanh::lean_box(0);
                        v_isShared_6269_ = v_isSharedCheck_6302_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6303_ = crate::leanh::lean_ctor_get(v___x_6265_, 0);
                    v_isSharedCheck_6310_ = (!crate::leanh::lean_is_exclusive(v___x_6265_)) as u8;
                    if v_isSharedCheck_6310_ == 0 {
                        v___x_6305_ = v___x_6265_;
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6303_);
                        crate::leanh::lean_dec(v___x_6265_);
                        v___x_6305_ = crate::leanh::lean_box(0);
                        v_isShared_6306_ = v_isSharedCheck_6310_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6266_) == 0 {
                    v_a_6270_ = crate::leanh::lean_ctor_get(v_a_6266_, 0);
                    crate::leanh::lean_inc(v_a_6270_);
                    crate::leanh::lean_dec_ref_known(v_a_6266_, 1);
                    if v_isShared_6269_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6268_, 0, v_a_6270_);
                        v___x_6272_ = v___x_6268_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6273_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6273_, 0, v_a_6270_);
                        v___x_6272_ = v_reuseFailAlloc_6273_;
                        state = 2;
                        continue;
                    }
                } else {
                    crate::leanh::lean_del_object(v___x_6268_);
                    v_a_6274_ = crate::leanh::lean_ctor_get(v_a_6266_, 0);
                    crate::leanh::lean_inc(v_a_6274_);
                    crate::leanh::lean_dec_ref_known(v_a_6266_, 1);
                    v___x_6275_ = crate::leanh::lean_box(0);
                    v___x_6276_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6276_, 0, v___x_6275_);
                    crate::leanh::lean_ctor_set(v___x_6276_, 1, v_a_6274_);
                    v_sz_6277_ = lean_array_size(v_tail_6264_);
                    v___x_6278_ = 0usize;
                    v___x_6279_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1_spec__4(v_tail_6264_, v_sz_6277_, v___x_6278_, v___x_6276_, v___y_6251_, v___y_6252_, v___y_6253_, v___y_6254_, v___y_6255_, v___y_6256_, v___y_6257_, v___y_6258_, v___y_6259_, v___y_6260_, v___y_6261_);
                    if crate::leanh::lean_obj_tag(v___x_6279_) == 0 {
                        v_a_6280_ = crate::leanh::lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6293_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6293_ == 0 {
                            v___x_6282_ = v___x_6279_;
                            v_isShared_6283_ = v_isSharedCheck_6293_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6280_);
                            crate::leanh::lean_dec(v___x_6279_);
                            v___x_6282_ = crate::leanh::lean_box(0);
                            v_isShared_6283_ = v_isSharedCheck_6293_;
                            state = 3;
                            continue;
                        }
                    } else {
                        v_a_6294_ = crate::leanh::lean_ctor_get(v___x_6279_, 0);
                        v_isSharedCheck_6301_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6279_)) as u8;
                        if v_isSharedCheck_6301_ == 0 {
                            v___x_6296_ = v___x_6279_;
                            v_isShared_6297_ = v_isSharedCheck_6301_;
                            state = 6;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6294_);
                            crate::leanh::lean_dec(v___x_6279_);
                            v___x_6296_ = crate::leanh::lean_box(0);
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
                v_fst_6284_ = crate::leanh::lean_ctor_get(v_a_6280_, 0);
                if crate::leanh::lean_obj_tag(v_fst_6284_) == 0 {
                    v_snd_6285_ = crate::leanh::lean_ctor_get(v_a_6280_, 1);
                    crate::leanh::lean_inc(v_snd_6285_);
                    crate::leanh::lean_dec(v_a_6280_);
                    if v_isShared_6283_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6282_, 0, v_snd_6285_);
                        v___x_6287_ = v___x_6282_;
                        state = 4;
                        continue;
                    } else {
                        v_reuseFailAlloc_6288_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6288_, 0, v_snd_6285_);
                        v___x_6287_ = v_reuseFailAlloc_6288_;
                        state = 4;
                        continue;
                    }
                } else {
                    crate::leanh::lean_inc_ref(v_fst_6284_);
                    crate::leanh::lean_dec(v_a_6280_);
                    v_val_6289_ = crate::leanh::lean_ctor_get(v_fst_6284_, 0);
                    crate::leanh::lean_inc(v_val_6289_);
                    crate::leanh::lean_dec_ref_known(v_fst_6284_, 1);
                    if v_isShared_6283_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6282_, 0, v_val_6289_);
                        v___x_6291_ = v___x_6282_;
                        state = 5;
                        continue;
                    } else {
                        v_reuseFailAlloc_6292_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6292_, 0, v_val_6289_);
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
                    v_reuseFailAlloc_6300_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6300_, 0, v_a_6294_);
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
                    v_reuseFailAlloc_6309_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6309_, 0, v_a_6303_);
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
    mut v_t_6311_: *mut crate::leanh::LeanObject,
    mut v_init_6312_: *mut crate::leanh::LeanObject,
    mut v___y_6313_: *mut crate::leanh::LeanObject,
    mut v___y_6314_: *mut crate::leanh::LeanObject,
    mut v___y_6315_: *mut crate::leanh::LeanObject,
    mut v___y_6316_: *mut crate::leanh::LeanObject,
    mut v___y_6317_: *mut crate::leanh::LeanObject,
    mut v___y_6318_: *mut crate::leanh::LeanObject,
    mut v___y_6319_: *mut crate::leanh::LeanObject,
    mut v___y_6320_: *mut crate::leanh::LeanObject,
    mut v___y_6321_: *mut crate::leanh::LeanObject,
    mut v___y_6322_: *mut crate::leanh::LeanObject,
    mut v___y_6323_: *mut crate::leanh::LeanObject,
    mut v___y_6324_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6325_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6325_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_t_6311_, v_init_6312_, v___y_6313_, v___y_6314_, v___y_6315_, v___y_6316_, v___y_6317_, v___y_6318_, v___y_6319_, v___y_6320_, v___y_6321_, v___y_6322_, v___y_6323_);
    crate::leanh::lean_dec(v___y_6323_);
    crate::leanh::lean_dec_ref(v___y_6322_);
    crate::leanh::lean_dec(v___y_6321_);
    crate::leanh::lean_dec_ref(v___y_6320_);
    crate::leanh::lean_dec(v___y_6319_);
    crate::leanh::lean_dec_ref(v___y_6318_);
    crate::leanh::lean_dec(v___y_6317_);
    crate::leanh::lean_dec_ref(v___y_6316_);
    crate::leanh::lean_dec(v___y_6315_);
    crate::leanh::lean_dec(v___y_6314_);
    crate::leanh::lean_dec(v___y_6313_);
    crate::leanh::lean_dec_ref(v_t_6311_);
    return v_res_6325_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6328_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6329_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6330_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6331_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6332_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6333_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6328_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__1;
    v___x_6329_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_6330_ = crate::leanh::lean_unsigned_to_nat(73);
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
    mut v_a_6334_: *mut crate::leanh::LeanObject,
    mut v_a_6335_: *mut crate::leanh::LeanObject,
    mut v_a_6336_: *mut crate::leanh::LeanObject,
    mut v_a_6337_: *mut crate::leanh::LeanObject,
    mut v_a_6338_: *mut crate::leanh::LeanObject,
    mut v_a_6339_: *mut crate::leanh::LeanObject,
    mut v_a_6340_: *mut crate::leanh::LeanObject,
    mut v_a_6341_: *mut crate::leanh::LeanObject,
    mut v_a_6342_: *mut crate::leanh::LeanObject,
    mut v_a_6343_: *mut crate::leanh::LeanObject,
    mut v_a_6344_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6346_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6347_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6348_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_diseqs_6349_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6350_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6351_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6352_: u8 = 0;
    let mut v___x_6353_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6354_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6355_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6356_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6358_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6359_: u8 = 0;
    let mut v___x_6360_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6362_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6363_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6364_: u8 = 0;
    let mut v_unused_6365_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6366_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6368_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6369_: u8 = 0;
    let mut v___x_6371_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6372_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6373_: u8 = 0;
    let mut v_a_6374_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6376_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6377_: u8 = 0;
    let mut v___x_6379_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6380_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6381_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6346_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_,
                    v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_,
                );
                if crate::leanh::lean_obj_tag(v___x_6346_) == 0 {
                    v_a_6347_ = crate::leanh::lean_ctor_get(v___x_6346_, 0);
                    crate::leanh::lean_inc(v_a_6347_);
                    crate::leanh::lean_dec_ref_known(v___x_6346_, 1);
                    v_vars_6348_ = crate::leanh::lean_ctor_get(v_a_6347_, 30);
                    crate::leanh::lean_inc_ref(v_vars_6348_);
                    v_diseqs_6349_ = crate::leanh::lean_ctor_get(v_a_6347_, 34);
                    crate::leanh::lean_inc_ref(v_diseqs_6349_);
                    crate::leanh::lean_dec(v_a_6347_);
                    v_size_6350_ = crate::leanh::lean_ctor_get(v_vars_6348_, 2);
                    crate::leanh::lean_inc(v_size_6350_);
                    crate::leanh::lean_dec_ref(v_vars_6348_);
                    v_size_6351_ = crate::leanh::lean_ctor_get(v_diseqs_6349_, 2);
                    v___x_6352_ = lean_nat_dec_eq(v_size_6350_, v_size_6351_);
                    crate::leanh::lean_dec(v_size_6350_);
                    if v___x_6352_ == 0 {
                        crate::leanh::lean_dec_ref(v_diseqs_6349_);
                        v___x_6353_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs___closed__2);
                        v___x_6354_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6353_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_);
                        return v___x_6354_;
                    } else {
                        v___x_6355_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_6356_ = l_Lean_PersistentArray_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs_spec__1(v_diseqs_6349_, v___x_6355_, v_a_6334_, v_a_6335_, v_a_6336_, v_a_6337_, v_a_6338_, v_a_6339_, v_a_6340_, v_a_6341_, v_a_6342_, v_a_6343_, v_a_6344_);
                        crate::leanh::lean_dec_ref(v_diseqs_6349_);
                        if crate::leanh::lean_obj_tag(v___x_6356_) == 0 {
                            v_isSharedCheck_6364_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6356_)) as u8;
                            if v_isSharedCheck_6364_ == 0 {
                                v_unused_6365_ = crate::leanh::lean_ctor_get(v___x_6356_, 0);
                                crate::leanh::lean_dec(v_unused_6365_);
                                v___x_6358_ = v___x_6356_;
                                v_isShared_6359_ = v_isSharedCheck_6364_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_6356_);
                                v___x_6358_ = crate::leanh::lean_box(0);
                                v_isShared_6359_ = v_isSharedCheck_6364_;
                                state = 1;
                                continue;
                            }
                        } else {
                            v_a_6366_ = crate::leanh::lean_ctor_get(v___x_6356_, 0);
                            v_isSharedCheck_6373_ =
                                (!crate::leanh::lean_is_exclusive(v___x_6356_)) as u8;
                            if v_isSharedCheck_6373_ == 0 {
                                v___x_6368_ = v___x_6356_;
                                v_isShared_6369_ = v_isSharedCheck_6373_;
                                state = 3;
                                continue;
                            } else {
                                crate::leanh::lean_inc(v_a_6366_);
                                crate::leanh::lean_dec(v___x_6356_);
                                v___x_6368_ = crate::leanh::lean_box(0);
                                v_isShared_6369_ = v_isSharedCheck_6373_;
                                state = 3;
                                continue;
                            }
                        }
                    }
                } else {
                    v_a_6374_ = crate::leanh::lean_ctor_get(v___x_6346_, 0);
                    v_isSharedCheck_6381_ = (!crate::leanh::lean_is_exclusive(v___x_6346_)) as u8;
                    if v_isSharedCheck_6381_ == 0 {
                        v___x_6376_ = v___x_6346_;
                        v_isShared_6377_ = v_isSharedCheck_6381_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6374_);
                        crate::leanh::lean_dec(v___x_6346_);
                        v___x_6376_ = crate::leanh::lean_box(0);
                        v_isShared_6377_ = v_isSharedCheck_6381_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6360_ = crate::leanh::lean_box(0);
                if v_isShared_6359_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6358_, 0, v___x_6360_);
                    v___x_6362_ = v___x_6358_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6363_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6363_, 0, v___x_6360_);
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
                    v_reuseFailAlloc_6372_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6372_, 0, v_a_6366_);
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
                    v_reuseFailAlloc_6380_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6380_, 0, v_a_6374_);
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
    mut v_a_6382_: *mut crate::leanh::LeanObject,
    mut v_a_6383_: *mut crate::leanh::LeanObject,
    mut v_a_6384_: *mut crate::leanh::LeanObject,
    mut v_a_6385_: *mut crate::leanh::LeanObject,
    mut v_a_6386_: *mut crate::leanh::LeanObject,
    mut v_a_6387_: *mut crate::leanh::LeanObject,
    mut v_a_6388_: *mut crate::leanh::LeanObject,
    mut v_a_6389_: *mut crate::leanh::LeanObject,
    mut v_a_6390_: *mut crate::leanh::LeanObject,
    mut v_a_6391_: *mut crate::leanh::LeanObject,
    mut v_a_6392_: *mut crate::leanh::LeanObject,
    mut v_a_6393_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6394_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6394_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkDiseqCnstrs(v_a_6382_, v_a_6383_, v_a_6384_, v_a_6385_, v_a_6386_, v_a_6387_, v_a_6388_, v_a_6389_, v_a_6390_, v_a_6391_, v_a_6392_);
    crate::leanh::lean_dec(v_a_6392_);
    crate::leanh::lean_dec_ref(v_a_6391_);
    crate::leanh::lean_dec(v_a_6390_);
    crate::leanh::lean_dec_ref(v_a_6389_);
    crate::leanh::lean_dec(v_a_6388_);
    crate::leanh::lean_dec_ref(v_a_6387_);
    crate::leanh::lean_dec(v_a_6386_);
    crate::leanh::lean_dec_ref(v_a_6385_);
    crate::leanh::lean_dec(v_a_6384_);
    crate::leanh::lean_dec(v_a_6383_);
    crate::leanh::lean_dec(v_a_6382_);
    return v_res_6394_;
}
pub unsafe fn _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6395_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6395_ = l_Lean_Meta_Grind_instInhabitedGoalM(crate::leanh::lean_box(0));
    return v___x_6395_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(
    mut v_msg_6396_: *mut crate::leanh::LeanObject,
    mut v___y_6397_: *mut crate::leanh::LeanObject,
    mut v___y_6398_: *mut crate::leanh::LeanObject,
    mut v___y_6399_: *mut crate::leanh::LeanObject,
    mut v___y_6400_: *mut crate::leanh::LeanObject,
    mut v___y_6401_: *mut crate::leanh::LeanObject,
    mut v___y_6402_: *mut crate::leanh::LeanObject,
    mut v___y_6403_: *mut crate::leanh::LeanObject,
    mut v___y_6404_: *mut crate::leanh::LeanObject,
    mut v___y_6405_: *mut crate::leanh::LeanObject,
    mut v___y_6406_: *mut crate::leanh::LeanObject,
    mut v___y_6407_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6409_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6410_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_5472__overap_6411_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6412_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6409_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0), core::ptr::addr_of_mut!(l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0_once), _init_l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___closed__0);
    v___f_6410_ = crate::leanh::lean_alloc_closure(
        l_instInhabitedForall___redArg___lam__0___boxed as *mut core::ffi::c_void,
        2,
        1,
    );
    crate::leanh::lean_closure_set(v___f_6410_, 0, v___x_6409_);
    v___x_5472__overap_6411_ = lean_panic_fn_borrowed(v___f_6410_, v_msg_6396_);
    crate::leanh::lean_dec_ref(v___f_6410_);
    crate::leanh::lean_inc(v___y_6407_);
    crate::leanh::lean_inc_ref(v___y_6406_);
    crate::leanh::lean_inc(v___y_6405_);
    crate::leanh::lean_inc_ref(v___y_6404_);
    crate::leanh::lean_inc(v___y_6403_);
    crate::leanh::lean_inc_ref(v___y_6402_);
    crate::leanh::lean_inc(v___y_6401_);
    crate::leanh::lean_inc_ref(v___y_6400_);
    crate::leanh::lean_inc(v___y_6399_);
    crate::leanh::lean_inc(v___y_6398_);
    crate::leanh::lean_inc(v___y_6397_);
    v___x_6412_ = crate::leanh::lean_apply_12(
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
        crate::leanh::lean_box(0),
    );
    return v___x_6412_;
}
pub unsafe fn l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0___boxed(
    mut v_msg_6413_: *mut crate::leanh::LeanObject,
    mut v___y_6414_: *mut crate::leanh::LeanObject,
    mut v___y_6415_: *mut crate::leanh::LeanObject,
    mut v___y_6416_: *mut crate::leanh::LeanObject,
    mut v___y_6417_: *mut crate::leanh::LeanObject,
    mut v___y_6418_: *mut crate::leanh::LeanObject,
    mut v___y_6419_: *mut crate::leanh::LeanObject,
    mut v___y_6420_: *mut crate::leanh::LeanObject,
    mut v___y_6421_: *mut crate::leanh::LeanObject,
    mut v___y_6422_: *mut crate::leanh::LeanObject,
    mut v___y_6423_: *mut crate::leanh::LeanObject,
    mut v___y_6424_: *mut crate::leanh::LeanObject,
    mut v___y_6425_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6426_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6426_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v_msg_6413_, v___y_6414_, v___y_6415_, v___y_6416_, v___y_6417_, v___y_6418_, v___y_6419_, v___y_6420_, v___y_6421_, v___y_6422_, v___y_6423_, v___y_6424_);
    crate::leanh::lean_dec(v___y_6424_);
    crate::leanh::lean_dec_ref(v___y_6423_);
    crate::leanh::lean_dec(v___y_6422_);
    crate::leanh::lean_dec_ref(v___y_6421_);
    crate::leanh::lean_dec(v___y_6420_);
    crate::leanh::lean_dec_ref(v___y_6419_);
    crate::leanh::lean_dec(v___y_6418_);
    crate::leanh::lean_dec_ref(v___y_6417_);
    crate::leanh::lean_dec(v___y_6416_);
    crate::leanh::lean_dec(v___y_6415_);
    crate::leanh::lean_dec(v___y_6414_);
    return v_res_6426_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6428_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6429_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6430_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6431_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6432_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6433_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6428_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkCnstrOf___closed__3;
    v___x_6429_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_6430_ = crate::leanh::lean_unsigned_to_nat(89);
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
-> *mut crate::leanh::LeanObject {
    let mut v___x_6435_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6436_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6437_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6438_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6439_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6440_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6435_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__2;
    v___x_6436_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_6437_ = crate::leanh::lean_unsigned_to_nat(87);
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
    mut v_vars_6441_: *mut crate::leanh::LeanObject,
    mut v_x_6442_: *mut crate::leanh::LeanObject,
    mut v_____s_6443_: *mut crate::leanh::LeanObject,
    mut v___y_6444_: *mut crate::leanh::LeanObject,
    mut v___y_6445_: *mut crate::leanh::LeanObject,
    mut v___y_6446_: *mut crate::leanh::LeanObject,
    mut v___y_6447_: *mut crate::leanh::LeanObject,
    mut v___y_6448_: *mut crate::leanh::LeanObject,
    mut v___y_6449_: *mut crate::leanh::LeanObject,
    mut v___y_6450_: *mut crate::leanh::LeanObject,
    mut v___y_6451_: *mut crate::leanh::LeanObject,
    mut v___y_6452_: *mut crate::leanh::LeanObject,
    mut v___y_6453_: *mut crate::leanh::LeanObject,
    mut v___y_6454_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6457_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6458_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6459_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6460_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_fst_6461_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_snd_6462_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_size_6463_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6464_: u8 = 0;
    let mut v___x_6465_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6466_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6467_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6469_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6470_: u8 = 0;
    let mut v___x_6472_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6473_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6474_: u8 = 0;
    let mut v___x_6475_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6476_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6477_: u8 = 0;
    let mut v___x_6478_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6479_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_fst_6461_ = crate::leanh::lean_ctor_get(v_x_6442_, 0);
                v_snd_6462_ = crate::leanh::lean_ctor_get(v_x_6442_, 1);
                v_size_6463_ = crate::leanh::lean_ctor_get(v_vars_6441_, 2);
                v___x_6464_ = lean_nat_dec_lt(v_snd_6462_, v_size_6463_);
                if v___x_6464_ == 0 {
                    v___x_6465_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__1);
                    v___x_6466_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6465_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
                    if crate::leanh::lean_obj_tag(v___x_6466_) == 0 {
                        crate::leanh::lean_dec_ref_known(v___x_6466_, 1);
                        state = 1;
                        continue;
                    } else {
                        v_a_6467_ = crate::leanh::lean_ctor_get(v___x_6466_, 0);
                        v_isSharedCheck_6474_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6466_)) as u8;
                        if v_isSharedCheck_6474_ == 0 {
                            v___x_6469_ = v___x_6466_;
                            v_isShared_6470_ = v_isSharedCheck_6474_;
                            state = 2;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6467_);
                            crate::leanh::lean_dec(v___x_6466_);
                            v___x_6469_ = crate::leanh::lean_box(0);
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
                    crate::leanh::lean_dec(v___x_6476_);
                    if v___x_6477_ == 0 {
                        v___x_6478_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___closed__3);
                        v___x_6479_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__0(v___x_6478_, v___y_6444_, v___y_6445_, v___y_6446_, v___y_6447_, v___y_6448_, v___y_6449_, v___y_6450_, v___y_6451_, v___y_6452_, v___y_6453_, v___y_6454_);
                        return v___x_6479_;
                    } else {
                        state = 1;
                        continue;
                    }
                }
            }
            1 => {
                v___x_6457_ = crate::leanh::lean_unsigned_to_nat(1);
                v___x_6458_ = lean_nat_add(v_____s_6443_, v___x_6457_);
                v___x_6459_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6459_, 0, v___x_6458_);
                v___x_6460_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6460_, 0, v___x_6459_);
                return v___x_6460_;
            }
            2 => {
                if v_isShared_6470_ == 0 {
                    v___x_6472_ = v___x_6469_;
                    state = 3;
                    continue;
                } else {
                    v_reuseFailAlloc_6473_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6473_, 0, v_a_6467_);
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
    mut v_vars_6480_: *mut crate::leanh::LeanObject,
    mut v_x_6481_: *mut crate::leanh::LeanObject,
    mut v_____s_6482_: *mut crate::leanh::LeanObject,
    mut v___y_6483_: *mut crate::leanh::LeanObject,
    mut v___y_6484_: *mut crate::leanh::LeanObject,
    mut v___y_6485_: *mut crate::leanh::LeanObject,
    mut v___y_6486_: *mut crate::leanh::LeanObject,
    mut v___y_6487_: *mut crate::leanh::LeanObject,
    mut v___y_6488_: *mut crate::leanh::LeanObject,
    mut v___y_6489_: *mut crate::leanh::LeanObject,
    mut v___y_6490_: *mut crate::leanh::LeanObject,
    mut v___y_6491_: *mut crate::leanh::LeanObject,
    mut v___y_6492_: *mut crate::leanh::LeanObject,
    mut v___y_6493_: *mut crate::leanh::LeanObject,
    mut v___y_6494_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6495_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6495_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0(v_vars_6480_, v_x_6481_, v_____s_6482_, v___y_6483_, v___y_6484_, v___y_6485_, v___y_6486_, v___y_6487_, v___y_6488_, v___y_6489_, v___y_6490_, v___y_6491_, v___y_6492_, v___y_6493_);
    crate::leanh::lean_dec(v___y_6493_);
    crate::leanh::lean_dec_ref(v___y_6492_);
    crate::leanh::lean_dec(v___y_6491_);
    crate::leanh::lean_dec_ref(v___y_6490_);
    crate::leanh::lean_dec(v___y_6489_);
    crate::leanh::lean_dec_ref(v___y_6488_);
    crate::leanh::lean_dec(v___y_6487_);
    crate::leanh::lean_dec_ref(v___y_6486_);
    crate::leanh::lean_dec(v___y_6485_);
    crate::leanh::lean_dec(v___y_6484_);
    crate::leanh::lean_dec(v___y_6483_);
    crate::leanh::lean_dec(v_____s_6482_);
    crate::leanh::lean_dec_ref(v_x_6481_);
    crate::leanh::lean_dec_ref(v_vars_6480_);
    return v_res_6495_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(
    mut v_f_6496_: *mut crate::leanh::LeanObject,
    mut v_s_6497_: *mut crate::leanh::LeanObject,
    mut v_a_6498_: *mut crate::leanh::LeanObject,
    mut v_b_6499_: *mut crate::leanh::LeanObject,
    mut v___y_6500_: *mut crate::leanh::LeanObject,
    mut v___y_6501_: *mut crate::leanh::LeanObject,
    mut v___y_6502_: *mut crate::leanh::LeanObject,
    mut v___y_6503_: *mut crate::leanh::LeanObject,
    mut v___y_6504_: *mut crate::leanh::LeanObject,
    mut v___y_6505_: *mut crate::leanh::LeanObject,
    mut v___y_6506_: *mut crate::leanh::LeanObject,
    mut v___y_6507_: *mut crate::leanh::LeanObject,
    mut v___y_6508_: *mut crate::leanh::LeanObject,
    mut v___y_6509_: *mut crate::leanh::LeanObject,
    mut v___y_6510_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6512_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6513_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6514_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6516_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6517_: u8 = 0;
    let mut v_a_6518_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6520_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6521_: u8 = 0;
    let mut v___x_6523_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6525_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6526_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6527_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6528_: u8 = 0;
    let mut v_a_6529_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6531_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6532_: u8 = 0;
    let mut v___x_6534_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6536_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6537_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6538_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6539_: u8 = 0;
    let mut v_isSharedCheck_6540_: u8 = 0;
    let mut v_a_6541_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6543_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6544_: u8 = 0;
    let mut v___x_6546_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6547_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6548_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6512_ = crate::leanh::lean_alloc_ctor(0, 2, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6512_, 0, v_a_6498_);
                crate::leanh::lean_ctor_set(v___x_6512_, 1, v_b_6499_);
                crate::leanh::lean_inc(v___y_6510_);
                crate::leanh::lean_inc_ref(v___y_6509_);
                crate::leanh::lean_inc(v___y_6508_);
                crate::leanh::lean_inc_ref(v___y_6507_);
                crate::leanh::lean_inc(v___y_6506_);
                crate::leanh::lean_inc_ref(v___y_6505_);
                crate::leanh::lean_inc(v___y_6504_);
                crate::leanh::lean_inc_ref(v___y_6503_);
                crate::leanh::lean_inc(v___y_6502_);
                crate::leanh::lean_inc(v___y_6501_);
                crate::leanh::lean_inc(v___y_6500_);
                v___x_6513_ = crate::leanh::lean_apply_14(
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
                    crate::leanh::lean_box(0),
                );
                if crate::leanh::lean_obj_tag(v___x_6513_) == 0 {
                    v_a_6514_ = crate::leanh::lean_ctor_get(v___x_6513_, 0);
                    v_isSharedCheck_6540_ = (!crate::leanh::lean_is_exclusive(v___x_6513_)) as u8;
                    if v_isSharedCheck_6540_ == 0 {
                        v___x_6516_ = v___x_6513_;
                        v_isShared_6517_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6514_);
                        crate::leanh::lean_dec(v___x_6513_);
                        v___x_6516_ = crate::leanh::lean_box(0);
                        v_isShared_6517_ = v_isSharedCheck_6540_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6541_ = crate::leanh::lean_ctor_get(v___x_6513_, 0);
                    v_isSharedCheck_6548_ = (!crate::leanh::lean_is_exclusive(v___x_6513_)) as u8;
                    if v_isSharedCheck_6548_ == 0 {
                        v___x_6543_ = v___x_6513_;
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 8;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6541_);
                        crate::leanh::lean_dec(v___x_6513_);
                        v___x_6543_ = crate::leanh::lean_box(0);
                        v_isShared_6544_ = v_isSharedCheck_6548_;
                        state = 8;
                        continue;
                    }
                }
            }
            1 => {
                if crate::leanh::lean_obj_tag(v_a_6514_) == 0 {
                    v_a_6518_ = crate::leanh::lean_ctor_get(v_a_6514_, 0);
                    v_isSharedCheck_6528_ = (!crate::leanh::lean_is_exclusive(v_a_6514_)) as u8;
                    if v_isSharedCheck_6528_ == 0 {
                        v___x_6520_ = v_a_6514_;
                        v_isShared_6521_ = v_isSharedCheck_6528_;
                        state = 2;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6518_);
                        crate::leanh::lean_dec(v_a_6514_);
                        v___x_6520_ = crate::leanh::lean_box(0);
                        v_isShared_6521_ = v_isSharedCheck_6528_;
                        state = 2;
                        continue;
                    }
                } else {
                    v_a_6529_ = crate::leanh::lean_ctor_get(v_a_6514_, 0);
                    v_isSharedCheck_6539_ = (!crate::leanh::lean_is_exclusive(v_a_6514_)) as u8;
                    if v_isSharedCheck_6539_ == 0 {
                        v___x_6531_ = v_a_6514_;
                        v_isShared_6532_ = v_isSharedCheck_6539_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6529_);
                        crate::leanh::lean_dec(v_a_6514_);
                        v___x_6531_ = crate::leanh::lean_box(0);
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
                    v_reuseFailAlloc_6527_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6527_, 0, v_a_6518_);
                    v___x_6523_ = v_reuseFailAlloc_6527_;
                    state = 3;
                    continue;
                }
            }
            3 => {
                if v_isShared_6517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6516_, 0, v___x_6523_);
                    v___x_6525_ = v___x_6516_;
                    state = 4;
                    continue;
                } else {
                    v_reuseFailAlloc_6526_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6526_, 0, v___x_6523_);
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
                    v_reuseFailAlloc_6538_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6538_, 0, v_a_6529_);
                    v___x_6534_ = v_reuseFailAlloc_6538_;
                    state = 6;
                    continue;
                }
            }
            6 => {
                if v_isShared_6517_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6516_, 0, v___x_6534_);
                    v___x_6536_ = v___x_6516_;
                    state = 7;
                    continue;
                } else {
                    v_reuseFailAlloc_6537_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6537_, 0, v___x_6534_);
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
                    v_reuseFailAlloc_6547_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6547_, 0, v_a_6541_);
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
    mut v_f_6549_: *mut crate::leanh::LeanObject,
    mut v_s_6550_: *mut crate::leanh::LeanObject,
    mut v_a_6551_: *mut crate::leanh::LeanObject,
    mut v_b_6552_: *mut crate::leanh::LeanObject,
    mut v___y_6553_: *mut crate::leanh::LeanObject,
    mut v___y_6554_: *mut crate::leanh::LeanObject,
    mut v___y_6555_: *mut crate::leanh::LeanObject,
    mut v___y_6556_: *mut crate::leanh::LeanObject,
    mut v___y_6557_: *mut crate::leanh::LeanObject,
    mut v___y_6558_: *mut crate::leanh::LeanObject,
    mut v___y_6559_: *mut crate::leanh::LeanObject,
    mut v___y_6560_: *mut crate::leanh::LeanObject,
    mut v___y_6561_: *mut crate::leanh::LeanObject,
    mut v___y_6562_: *mut crate::leanh::LeanObject,
    mut v___y_6563_: *mut crate::leanh::LeanObject,
    mut v___y_6564_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6565_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6565_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0(v_f_6549_, v_s_6550_, v_a_6551_, v_b_6552_, v___y_6553_, v___y_6554_, v___y_6555_, v___y_6556_, v___y_6557_, v___y_6558_, v___y_6559_, v___y_6560_, v___y_6561_, v___y_6562_, v___y_6563_);
    crate::leanh::lean_dec(v___y_6563_);
    crate::leanh::lean_dec_ref(v___y_6562_);
    crate::leanh::lean_dec(v___y_6561_);
    crate::leanh::lean_dec_ref(v___y_6560_);
    crate::leanh::lean_dec(v___y_6559_);
    crate::leanh::lean_dec_ref(v___y_6558_);
    crate::leanh::lean_dec(v___y_6557_);
    crate::leanh::lean_dec_ref(v___y_6556_);
    crate::leanh::lean_dec(v___y_6555_);
    crate::leanh::lean_dec(v___y_6554_);
    crate::leanh::lean_dec(v___y_6553_);
    return v_res_6565_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(
    mut v_f_6566_: *mut crate::leanh::LeanObject,
    mut v_keys_6567_: *mut crate::leanh::LeanObject,
    mut v_vals_6568_: *mut crate::leanh::LeanObject,
    mut v_i_6569_: *mut crate::leanh::LeanObject,
    mut v_acc_6570_: *mut crate::leanh::LeanObject,
    mut v___y_6571_: *mut crate::leanh::LeanObject,
    mut v___y_6572_: *mut crate::leanh::LeanObject,
    mut v___y_6573_: *mut crate::leanh::LeanObject,
    mut v___y_6574_: *mut crate::leanh::LeanObject,
    mut v___y_6575_: *mut crate::leanh::LeanObject,
    mut v___y_6576_: *mut crate::leanh::LeanObject,
    mut v___y_6577_: *mut crate::leanh::LeanObject,
    mut v___y_6578_: *mut crate::leanh::LeanObject,
    mut v___y_6579_: *mut crate::leanh::LeanObject,
    mut v___y_6580_: *mut crate::leanh::LeanObject,
    mut v___y_6581_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6583_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6584_: u8 = 0;
    let mut v___x_6585_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6586_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_k_6587_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_v_6588_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6589_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6590_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6591_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6592_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6593_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6583_ = lean_array_get_size(v_keys_6567_);
                v___x_6584_ = lean_nat_dec_lt(v_i_6569_, v___x_6583_);
                if v___x_6584_ == 0 {
                    crate::leanh::lean_dec(v_i_6569_);
                    crate::leanh::lean_dec_ref(v_f_6566_);
                    v___x_6585_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6585_, 0, v_acc_6570_);
                    v___x_6586_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6586_, 0, v___x_6585_);
                    return v___x_6586_;
                } else {
                    v_k_6587_ = lean_array_fget_borrowed(v_keys_6567_, v_i_6569_);
                    v_v_6588_ = lean_array_fget_borrowed(v_vals_6568_, v_i_6569_);
                    crate::leanh::lean_inc_ref(v_f_6566_);
                    crate::leanh::lean_inc(v___y_6581_);
                    crate::leanh::lean_inc_ref(v___y_6580_);
                    crate::leanh::lean_inc(v___y_6579_);
                    crate::leanh::lean_inc_ref(v___y_6578_);
                    crate::leanh::lean_inc(v___y_6577_);
                    crate::leanh::lean_inc_ref(v___y_6576_);
                    crate::leanh::lean_inc(v___y_6575_);
                    crate::leanh::lean_inc_ref(v___y_6574_);
                    crate::leanh::lean_inc(v___y_6573_);
                    crate::leanh::lean_inc(v___y_6572_);
                    crate::leanh::lean_inc(v___y_6571_);
                    crate::leanh::lean_inc(v_v_6588_);
                    crate::leanh::lean_inc(v_k_6587_);
                    v___x_6589_ = crate::leanh::lean_apply_15(
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
                        crate::leanh::lean_box(0),
                    );
                    if crate::leanh::lean_obj_tag(v___x_6589_) == 0 {
                        v_a_6590_ = crate::leanh::lean_ctor_get(v___x_6589_, 0);
                        crate::leanh::lean_inc(v_a_6590_);
                        if crate::leanh::lean_obj_tag(v_a_6590_) == 0 {
                            crate::leanh::lean_dec_ref_known(v_a_6590_, 1);
                            crate::leanh::lean_dec(v_i_6569_);
                            crate::leanh::lean_dec_ref(v_f_6566_);
                            return v___x_6589_;
                        } else {
                            crate::leanh::lean_dec_ref_known(v___x_6589_, 1);
                            v_a_6591_ = crate::leanh::lean_ctor_get(v_a_6590_, 0);
                            crate::leanh::lean_inc(v_a_6591_);
                            crate::leanh::lean_dec_ref_known(v_a_6590_, 1);
                            v___x_6592_ = crate::leanh::lean_unsigned_to_nat(1);
                            v___x_6593_ = lean_nat_add(v_i_6569_, v___x_6592_);
                            crate::leanh::lean_dec(v_i_6569_);
                            v_i_6569_ = v___x_6593_;
                            v_acc_6570_ = v_a_6591_;
                            state = 0;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec(v_i_6569_);
                        crate::leanh::lean_dec_ref(v_f_6566_);
                        return v___x_6589_;
                    }
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_6595_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_keys_6596_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_vals_6597_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_i_6598_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_acc_6599_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_6600_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_6601_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6602_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6603_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6604_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6605_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6606_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6607_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6608_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6609_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6610_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6611_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_6612_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6612_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_6595_, v_keys_6596_, v_vals_6597_, v_i_6598_, v_acc_6599_, v___y_6600_, v___y_6601_, v___y_6602_, v___y_6603_, v___y_6604_, v___y_6605_, v___y_6606_, v___y_6607_, v___y_6608_, v___y_6609_, v___y_6610_);
    crate::leanh::lean_dec(v___y_6610_);
    crate::leanh::lean_dec_ref(v___y_6609_);
    crate::leanh::lean_dec(v___y_6608_);
    crate::leanh::lean_dec_ref(v___y_6607_);
    crate::leanh::lean_dec(v___y_6606_);
    crate::leanh::lean_dec_ref(v___y_6605_);
    crate::leanh::lean_dec(v___y_6604_);
    crate::leanh::lean_dec_ref(v___y_6603_);
    crate::leanh::lean_dec(v___y_6602_);
    crate::leanh::lean_dec(v___y_6601_);
    crate::leanh::lean_dec(v___y_6600_);
    crate::leanh::lean_dec_ref(v_vals_6597_);
    crate::leanh::lean_dec_ref(v_keys_6596_);
    return v_res_6612_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(
    mut v_f_6613_: *mut crate::leanh::LeanObject,
    mut v_x_6614_: *mut crate::leanh::LeanObject,
    mut v_x_6615_: *mut crate::leanh::LeanObject,
    mut v___y_6616_: *mut crate::leanh::LeanObject,
    mut v___y_6617_: *mut crate::leanh::LeanObject,
    mut v___y_6618_: *mut crate::leanh::LeanObject,
    mut v___y_6619_: *mut crate::leanh::LeanObject,
    mut v___y_6620_: *mut crate::leanh::LeanObject,
    mut v___y_6621_: *mut crate::leanh::LeanObject,
    mut v___y_6622_: *mut crate::leanh::LeanObject,
    mut v___y_6623_: *mut crate::leanh::LeanObject,
    mut v___y_6624_: *mut crate::leanh::LeanObject,
    mut v___y_6625_: *mut crate::leanh::LeanObject,
    mut v___y_6626_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_es_6628_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6630_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6631_: u8 = 0;
    let mut v___x_6632_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6633_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6634_: u8 = 0;
    let mut v___x_6636_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6637_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6638_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6639_: u8 = 0;
    let mut v___x_6641_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6642_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6643_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6644_: usize = 0;
    let mut v___x_6645_: usize = 0;
    let mut v___x_6646_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6647_: usize = 0;
    let mut v___x_6648_: usize = 0;
    let mut v___x_6649_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6650_: u8 = 0;
    let mut v_ks_6651_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vs_6652_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6653_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6654_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                if crate::leanh::lean_obj_tag(v_x_6614_) == 0 {
                    v_es_6628_ = crate::leanh::lean_ctor_get(v_x_6614_, 0);
                    v_isSharedCheck_6650_ = (!crate::leanh::lean_is_exclusive(v_x_6614_)) as u8;
                    if v_isSharedCheck_6650_ == 0 {
                        v___x_6630_ = v_x_6614_;
                        v_isShared_6631_ = v_isSharedCheck_6650_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_es_6628_);
                        crate::leanh::lean_dec(v_x_6614_);
                        v___x_6630_ = crate::leanh::lean_box(0);
                        v_isShared_6631_ = v_isSharedCheck_6650_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_ks_6651_ = crate::leanh::lean_ctor_get(v_x_6614_, 0);
                    crate::leanh::lean_inc_ref(v_ks_6651_);
                    v_vs_6652_ = crate::leanh::lean_ctor_get(v_x_6614_, 1);
                    crate::leanh::lean_inc_ref(v_vs_6652_);
                    crate::leanh::lean_dec_ref_known(v_x_6614_, 2);
                    v___x_6653_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6654_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_6613_, v_ks_6651_, v_vs_6652_, v___x_6653_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                    crate::leanh::lean_dec_ref(v_vs_6652_);
                    crate::leanh::lean_dec_ref(v_ks_6651_);
                    return v___x_6654_;
                }
            }
            1 => {
                v___x_6632_ = crate::leanh::lean_unsigned_to_nat(0);
                v___x_6633_ = lean_array_get_size(v_es_6628_);
                v___x_6634_ = lean_nat_dec_lt(v___x_6632_, v___x_6633_);
                if v___x_6634_ == 0 {
                    crate::leanh::lean_dec_ref(v_es_6628_);
                    crate::leanh::lean_dec_ref(v_f_6613_);
                    if v_isShared_6631_ == 0 {
                        crate::leanh::lean_ctor_set_tag(v___x_6630_, 1);
                        crate::leanh::lean_ctor_set(v___x_6630_, 0, v_x_6615_);
                        v___x_6636_ = v___x_6630_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6638_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6638_, 0, v_x_6615_);
                        v___x_6636_ = v_reuseFailAlloc_6638_;
                        state = 2;
                        continue;
                    }
                } else {
                    v___x_6639_ = lean_nat_dec_le(v___x_6633_, v___x_6633_);
                    if v___x_6639_ == 0 {
                        if v___x_6634_ == 0 {
                            crate::leanh::lean_dec_ref(v_es_6628_);
                            crate::leanh::lean_dec_ref(v_f_6613_);
                            if v_isShared_6631_ == 0 {
                                crate::leanh::lean_ctor_set_tag(v___x_6630_, 1);
                                crate::leanh::lean_ctor_set(v___x_6630_, 0, v_x_6615_);
                                v___x_6641_ = v___x_6630_;
                                state = 3;
                                continue;
                            } else {
                                v_reuseFailAlloc_6643_ =
                                    crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                                crate::leanh::lean_ctor_set(v_reuseFailAlloc_6643_, 0, v_x_6615_);
                                v___x_6641_ = v_reuseFailAlloc_6643_;
                                state = 3;
                                continue;
                            }
                        } else {
                            crate::leanh::lean_del_object(v___x_6630_);
                            v___x_6644_ = 0usize;
                            v___x_6645_ = lean_usize_of_nat(v___x_6633_);
                            v___x_6646_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6613_, v_es_6628_, v___x_6644_, v___x_6645_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                            crate::leanh::lean_dec_ref(v_es_6628_);
                            return v___x_6646_;
                        }
                    } else {
                        crate::leanh::lean_del_object(v___x_6630_);
                        v___x_6647_ = 0usize;
                        v___x_6648_ = lean_usize_of_nat(v___x_6633_);
                        v___x_6649_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6613_, v_es_6628_, v___x_6647_, v___x_6648_, v_x_6615_, v___y_6616_, v___y_6617_, v___y_6618_, v___y_6619_, v___y_6620_, v___y_6621_, v___y_6622_, v___y_6623_, v___y_6624_, v___y_6625_, v___y_6626_);
                        crate::leanh::lean_dec_ref(v_es_6628_);
                        return v___x_6649_;
                    }
                }
            }
            2 => {
                v___x_6637_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6637_, 0, v___x_6636_);
                return v___x_6637_;
            }
            3 => {
                v___x_6642_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                crate::leanh::lean_ctor_set(v___x_6642_, 0, v___x_6641_);
                return v___x_6642_;
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(
    mut v_f_6655_: *mut crate::leanh::LeanObject,
    mut v_as_6656_: *mut crate::leanh::LeanObject,
    mut v_i_6657_: usize,
    mut v_stop_6658_: usize,
    mut v_b_6659_: *mut crate::leanh::LeanObject,
    mut v___y_6660_: *mut crate::leanh::LeanObject,
    mut v___y_6661_: *mut crate::leanh::LeanObject,
    mut v___y_6662_: *mut crate::leanh::LeanObject,
    mut v___y_6663_: *mut crate::leanh::LeanObject,
    mut v___y_6664_: *mut crate::leanh::LeanObject,
    mut v___y_6665_: *mut crate::leanh::LeanObject,
    mut v___y_6666_: *mut crate::leanh::LeanObject,
    mut v___y_6667_: *mut crate::leanh::LeanObject,
    mut v___y_6668_: *mut crate::leanh::LeanObject,
    mut v___y_6669_: *mut crate::leanh::LeanObject,
    mut v___y_6670_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_a_6673_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6674_: usize = 0;
    let mut v___x_6675_: usize = 0;
    let mut v___y_6678_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6679_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6680_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6681_: u8 = 0;
    let mut v___x_6682_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_key_6683_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_val_6684_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6685_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_node_6686_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6687_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6688_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6689_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6681_ = lean_usize_dec_eq(v_i_6657_, v_stop_6658_);
                if v___x_6681_ == 0 {
                    v___x_6682_ = lean_array_uget_borrowed(v_as_6656_, v_i_6657_);
                    match crate::leanh::lean_obj_tag(v___x_6682_) {
                        0 => {
                            v_key_6683_ = crate::leanh::lean_ctor_get(v___x_6682_, 0);
                            v_val_6684_ = crate::leanh::lean_ctor_get(v___x_6682_, 1);
                            crate::leanh::lean_inc_ref(v_f_6655_);
                            crate::leanh::lean_inc(v___y_6670_);
                            crate::leanh::lean_inc_ref(v___y_6669_);
                            crate::leanh::lean_inc(v___y_6668_);
                            crate::leanh::lean_inc_ref(v___y_6667_);
                            crate::leanh::lean_inc(v___y_6666_);
                            crate::leanh::lean_inc_ref(v___y_6665_);
                            crate::leanh::lean_inc(v___y_6664_);
                            crate::leanh::lean_inc_ref(v___y_6663_);
                            crate::leanh::lean_inc(v___y_6662_);
                            crate::leanh::lean_inc(v___y_6661_);
                            crate::leanh::lean_inc(v___y_6660_);
                            crate::leanh::lean_inc(v_val_6684_);
                            crate::leanh::lean_inc(v_key_6683_);
                            v___x_6685_ = crate::leanh::lean_apply_15(
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
                                crate::leanh::lean_box(0),
                            );
                            v___y_6678_ = v___x_6685_;
                            state = 2;
                            continue;
                        }
                        1 => {
                            v_node_6686_ = crate::leanh::lean_ctor_get(v___x_6682_, 0);
                            crate::leanh::lean_inc(v_node_6686_);
                            crate::leanh::lean_inc_ref(v_f_6655_);
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
                    crate::leanh::lean_dec_ref(v_f_6655_);
                    v___x_6688_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6688_, 0, v_b_6659_);
                    v___x_6689_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_6689_, 0, v___x_6688_);
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
                if crate::leanh::lean_obj_tag(v___y_6678_) == 0 {
                    v_a_6679_ = crate::leanh::lean_ctor_get(v___y_6678_, 0);
                    if crate::leanh::lean_obj_tag(v_a_6679_) == 0 {
                        crate::leanh::lean_dec_ref(v_f_6655_);
                        return v___y_6678_;
                    } else {
                        crate::leanh::lean_inc_ref(v_a_6679_);
                        crate::leanh::lean_dec_ref_known(v___y_6678_, 1);
                        v_a_6680_ = crate::leanh::lean_ctor_get(v_a_6679_, 0);
                        crate::leanh::lean_inc(v_a_6680_);
                        crate::leanh::lean_dec_ref_known(v_a_6679_, 1);
                        v_a_6673_ = v_a_6680_;
                        state = 1;
                        continue;
                    }
                } else {
                    crate::leanh::lean_dec_ref(v_f_6655_);
                    return v___y_6678_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_f_6690_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_as_6691_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_i_6692_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_stop_6693_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_6694_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_6695_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_6696_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6697_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6698_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6699_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6700_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6701_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6702_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6703_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6704_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6705_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6706_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_i_boxed_6707_: usize = 0;
    let mut v_stop_boxed_6708_: usize = 0;
    let mut v_res_6709_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_6707_ = crate::leanh::lean_unbox_usize(v_i_6692_);
    crate::leanh::lean_dec(v_i_6692_);
    v_stop_boxed_6708_ = crate::leanh::lean_unbox_usize(v_stop_6693_);
    crate::leanh::lean_dec(v_stop_6693_);
    v_res_6709_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6690_, v_as_6691_, v_i_boxed_6707_, v_stop_boxed_6708_, v_b_6694_, v___y_6695_, v___y_6696_, v___y_6697_, v___y_6698_, v___y_6699_, v___y_6700_, v___y_6701_, v___y_6702_, v___y_6703_, v___y_6704_, v___y_6705_);
    crate::leanh::lean_dec(v___y_6705_);
    crate::leanh::lean_dec_ref(v___y_6704_);
    crate::leanh::lean_dec(v___y_6703_);
    crate::leanh::lean_dec_ref(v___y_6702_);
    crate::leanh::lean_dec(v___y_6701_);
    crate::leanh::lean_dec_ref(v___y_6700_);
    crate::leanh::lean_dec(v___y_6699_);
    crate::leanh::lean_dec_ref(v___y_6698_);
    crate::leanh::lean_dec(v___y_6697_);
    crate::leanh::lean_dec(v___y_6696_);
    crate::leanh::lean_dec(v___y_6695_);
    crate::leanh::lean_dec_ref(v_as_6691_);
    return v_res_6709_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg___boxed(
    mut v_f_6710_: *mut crate::leanh::LeanObject,
    mut v_x_6711_: *mut crate::leanh::LeanObject,
    mut v_x_6712_: *mut crate::leanh::LeanObject,
    mut v___y_6713_: *mut crate::leanh::LeanObject,
    mut v___y_6714_: *mut crate::leanh::LeanObject,
    mut v___y_6715_: *mut crate::leanh::LeanObject,
    mut v___y_6716_: *mut crate::leanh::LeanObject,
    mut v___y_6717_: *mut crate::leanh::LeanObject,
    mut v___y_6718_: *mut crate::leanh::LeanObject,
    mut v___y_6719_: *mut crate::leanh::LeanObject,
    mut v___y_6720_: *mut crate::leanh::LeanObject,
    mut v___y_6721_: *mut crate::leanh::LeanObject,
    mut v___y_6722_: *mut crate::leanh::LeanObject,
    mut v___y_6723_: *mut crate::leanh::LeanObject,
    mut v___y_6724_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6725_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6725_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6710_, v_x_6711_, v_x_6712_, v___y_6713_, v___y_6714_, v___y_6715_, v___y_6716_, v___y_6717_, v___y_6718_, v___y_6719_, v___y_6720_, v___y_6721_, v___y_6722_, v___y_6723_);
    crate::leanh::lean_dec(v___y_6723_);
    crate::leanh::lean_dec_ref(v___y_6722_);
    crate::leanh::lean_dec(v___y_6721_);
    crate::leanh::lean_dec_ref(v___y_6720_);
    crate::leanh::lean_dec(v___y_6719_);
    crate::leanh::lean_dec_ref(v___y_6718_);
    crate::leanh::lean_dec(v___y_6717_);
    crate::leanh::lean_dec_ref(v___y_6716_);
    crate::leanh::lean_dec(v___y_6715_);
    crate::leanh::lean_dec(v___y_6714_);
    crate::leanh::lean_dec(v___y_6713_);
    return v_res_6725_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(
    mut v_map_6726_: *mut crate::leanh::LeanObject,
    mut v_init_6727_: *mut crate::leanh::LeanObject,
    mut v_f_6728_: *mut crate::leanh::LeanObject,
    mut v___y_6729_: *mut crate::leanh::LeanObject,
    mut v___y_6730_: *mut crate::leanh::LeanObject,
    mut v___y_6731_: *mut crate::leanh::LeanObject,
    mut v___y_6732_: *mut crate::leanh::LeanObject,
    mut v___y_6733_: *mut crate::leanh::LeanObject,
    mut v___y_6734_: *mut crate::leanh::LeanObject,
    mut v___y_6735_: *mut crate::leanh::LeanObject,
    mut v___y_6736_: *mut crate::leanh::LeanObject,
    mut v___y_6737_: *mut crate::leanh::LeanObject,
    mut v___y_6738_: *mut crate::leanh::LeanObject,
    mut v___y_6739_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___f_6741_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6742_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6743_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6745_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6746_: u8 = 0;
    let mut v_a_6747_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6749_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6750_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6751_: u8 = 0;
    let mut v_a_6752_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6754_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6755_: u8 = 0;
    let mut v___x_6757_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6758_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6759_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___f_6741_ = crate::leanh::lean_alloc_closure(l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg___lam__0___boxed as *mut core::ffi::c_void, 16, 1);
                crate::leanh::lean_closure_set(v___f_6741_, 0, v_f_6728_);
                crate::leanh::lean_inc_ref(v_map_6726_);
                v___x_6742_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v___f_6741_, v_map_6726_, v_init_6727_, v___y_6729_, v___y_6730_, v___y_6731_, v___y_6732_, v___y_6733_, v___y_6734_, v___y_6735_, v___y_6736_, v___y_6737_, v___y_6738_, v___y_6739_);
                if crate::leanh::lean_obj_tag(v___x_6742_) == 0 {
                    v_a_6743_ = crate::leanh::lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6751_ = (!crate::leanh::lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6751_ == 0 {
                        v___x_6745_ = v___x_6742_;
                        v_isShared_6746_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6743_);
                        crate::leanh::lean_dec(v___x_6742_);
                        v___x_6745_ = crate::leanh::lean_box(0);
                        v_isShared_6746_ = v_isSharedCheck_6751_;
                        state = 1;
                        continue;
                    }
                } else {
                    v_a_6752_ = crate::leanh::lean_ctor_get(v___x_6742_, 0);
                    v_isSharedCheck_6759_ = (!crate::leanh::lean_is_exclusive(v___x_6742_)) as u8;
                    if v_isSharedCheck_6759_ == 0 {
                        v___x_6754_ = v___x_6742_;
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 3;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6752_);
                        crate::leanh::lean_dec(v___x_6742_);
                        v___x_6754_ = crate::leanh::lean_box(0);
                        v_isShared_6755_ = v_isSharedCheck_6759_;
                        state = 3;
                        continue;
                    }
                }
            }
            1 => {
                v_a_6747_ = crate::leanh::lean_ctor_get(v_a_6743_, 0);
                crate::leanh::lean_inc(v_a_6747_);
                crate::leanh::lean_dec(v_a_6743_);
                if v_isShared_6746_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_6745_, 0, v_a_6747_);
                    v___x_6749_ = v___x_6745_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_6750_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6750_, 0, v_a_6747_);
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
                    v_reuseFailAlloc_6758_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6758_, 0, v_a_6752_);
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
    mut v_map_6760_: *mut crate::leanh::LeanObject,
    mut v_init_6761_: *mut crate::leanh::LeanObject,
    mut v_f_6762_: *mut crate::leanh::LeanObject,
    mut v___y_6763_: *mut crate::leanh::LeanObject,
    mut v___y_6764_: *mut crate::leanh::LeanObject,
    mut v___y_6765_: *mut crate::leanh::LeanObject,
    mut v___y_6766_: *mut crate::leanh::LeanObject,
    mut v___y_6767_: *mut crate::leanh::LeanObject,
    mut v___y_6768_: *mut crate::leanh::LeanObject,
    mut v___y_6769_: *mut crate::leanh::LeanObject,
    mut v___y_6770_: *mut crate::leanh::LeanObject,
    mut v___y_6771_: *mut crate::leanh::LeanObject,
    mut v___y_6772_: *mut crate::leanh::LeanObject,
    mut v___y_6773_: *mut crate::leanh::LeanObject,
    mut v___y_6774_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6775_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6775_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_6760_, v_init_6761_, v_f_6762_, v___y_6763_, v___y_6764_, v___y_6765_, v___y_6766_, v___y_6767_, v___y_6768_, v___y_6769_, v___y_6770_, v___y_6771_, v___y_6772_, v___y_6773_);
    crate::leanh::lean_dec(v___y_6773_);
    crate::leanh::lean_dec_ref(v___y_6772_);
    crate::leanh::lean_dec(v___y_6771_);
    crate::leanh::lean_dec_ref(v___y_6770_);
    crate::leanh::lean_dec(v___y_6769_);
    crate::leanh::lean_dec_ref(v___y_6768_);
    crate::leanh::lean_dec(v___y_6767_);
    crate::leanh::lean_dec_ref(v___y_6766_);
    crate::leanh::lean_dec(v___y_6765_);
    crate::leanh::lean_dec(v___y_6764_);
    crate::leanh::lean_dec(v___y_6763_);
    crate::leanh::lean_dec_ref(v_map_6760_);
    return v_res_6775_;
}
pub unsafe fn _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1()
-> *mut crate::leanh::LeanObject {
    let mut v___x_6777_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6778_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6779_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6780_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6781_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6782_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6777_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__0;
    v___x_6778_ = crate::leanh::lean_unsigned_to_nat(2);
    v___x_6779_ = crate::leanh::lean_unsigned_to_nat(91);
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
    mut v_a_6783_: *mut crate::leanh::LeanObject,
    mut v_a_6784_: *mut crate::leanh::LeanObject,
    mut v_a_6785_: *mut crate::leanh::LeanObject,
    mut v_a_6786_: *mut crate::leanh::LeanObject,
    mut v_a_6787_: *mut crate::leanh::LeanObject,
    mut v_a_6788_: *mut crate::leanh::LeanObject,
    mut v_a_6789_: *mut crate::leanh::LeanObject,
    mut v_a_6790_: *mut crate::leanh::LeanObject,
    mut v_a_6791_: *mut crate::leanh::LeanObject,
    mut v_a_6792_: *mut crate::leanh::LeanObject,
    mut v_a_6793_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6795_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6796_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_vars_6797_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_varMap_6798_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___f_6799_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6800_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6801_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_6802_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6804_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6805_: u8 = 0;
    let mut v_size_6806_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6807_: u8 = 0;
    let mut v___x_6808_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6809_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6810_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6812_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6813_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6814_: u8 = 0;
    let mut v_a_6815_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6817_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6818_: u8 = 0;
    let mut v___x_6820_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6821_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6822_: u8 = 0;
    let mut v_a_6823_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_6825_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_6826_: u8 = 0;
    let mut v___x_6828_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_6829_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_6830_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_6795_ = l_Lean_Meta_Grind_Arith_Linear_LinearM_getStruct(
                    v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_,
                    v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_,
                );
                if crate::leanh::lean_obj_tag(v___x_6795_) == 0 {
                    v_a_6796_ = crate::leanh::lean_ctor_get(v___x_6795_, 0);
                    crate::leanh::lean_inc(v_a_6796_);
                    crate::leanh::lean_dec_ref_known(v___x_6795_, 1);
                    v_vars_6797_ = crate::leanh::lean_ctor_get(v_a_6796_, 30);
                    crate::leanh::lean_inc_ref_n(v_vars_6797_, 2);
                    v_varMap_6798_ = crate::leanh::lean_ctor_get(v_a_6796_, 31);
                    crate::leanh::lean_inc_ref(v_varMap_6798_);
                    crate::leanh::lean_dec(v_a_6796_);
                    v___f_6799_ = crate::leanh::lean_alloc_closure(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___lam__0___boxed as *mut core::ffi::c_void, 15, 1);
                    crate::leanh::lean_closure_set(v___f_6799_, 0, v_vars_6797_);
                    v___x_6800_ = crate::leanh::lean_unsigned_to_nat(0);
                    v___x_6801_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_varMap_6798_, v___x_6800_, v___f_6799_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
                    crate::leanh::lean_dec_ref(v_varMap_6798_);
                    if crate::leanh::lean_obj_tag(v___x_6801_) == 0 {
                        v_a_6802_ = crate::leanh::lean_ctor_get(v___x_6801_, 0);
                        v_isSharedCheck_6814_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6801_)) as u8;
                        if v_isSharedCheck_6814_ == 0 {
                            v___x_6804_ = v___x_6801_;
                            v_isShared_6805_ = v_isSharedCheck_6814_;
                            state = 1;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6802_);
                            crate::leanh::lean_dec(v___x_6801_);
                            v___x_6804_ = crate::leanh::lean_box(0);
                            v_isShared_6805_ = v_isSharedCheck_6814_;
                            state = 1;
                            continue;
                        }
                    } else {
                        crate::leanh::lean_dec_ref(v_vars_6797_);
                        v_a_6815_ = crate::leanh::lean_ctor_get(v___x_6801_, 0);
                        v_isSharedCheck_6822_ =
                            (!crate::leanh::lean_is_exclusive(v___x_6801_)) as u8;
                        if v_isSharedCheck_6822_ == 0 {
                            v___x_6817_ = v___x_6801_;
                            v_isShared_6818_ = v_isSharedCheck_6822_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_6815_);
                            crate::leanh::lean_dec(v___x_6801_);
                            v___x_6817_ = crate::leanh::lean_box(0);
                            v_isShared_6818_ = v_isSharedCheck_6822_;
                            state = 3;
                            continue;
                        }
                    }
                } else {
                    v_a_6823_ = crate::leanh::lean_ctor_get(v___x_6795_, 0);
                    v_isSharedCheck_6830_ = (!crate::leanh::lean_is_exclusive(v___x_6795_)) as u8;
                    if v_isSharedCheck_6830_ == 0 {
                        v___x_6825_ = v___x_6795_;
                        v_isShared_6826_ = v_isSharedCheck_6830_;
                        state = 5;
                        continue;
                    } else {
                        crate::leanh::lean_inc(v_a_6823_);
                        crate::leanh::lean_dec(v___x_6795_);
                        v___x_6825_ = crate::leanh::lean_box(0);
                        v_isShared_6826_ = v_isSharedCheck_6830_;
                        state = 5;
                        continue;
                    }
                }
            }
            1 => {
                v_size_6806_ = crate::leanh::lean_ctor_get(v_vars_6797_, 2);
                crate::leanh::lean_inc(v_size_6806_);
                crate::leanh::lean_dec_ref(v_vars_6797_);
                v___x_6807_ = lean_nat_dec_eq(v_size_6806_, v_a_6802_);
                crate::leanh::lean_dec(v_a_6802_);
                crate::leanh::lean_dec(v_size_6806_);
                if v___x_6807_ == 0 {
                    crate::leanh::lean_del_object(v___x_6804_);
                    v___x_6808_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1), core::ptr::addr_of_mut!(l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1_once), _init_l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars___closed__1);
                    v___x_6809_ = l_panic___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Grind_Linarith_Poly_checkOccs_go_spec__1(v___x_6808_, v_a_6783_, v_a_6784_, v_a_6785_, v_a_6786_, v_a_6787_, v_a_6788_, v_a_6789_, v_a_6790_, v_a_6791_, v_a_6792_, v_a_6793_);
                    return v___x_6809_;
                } else {
                    v___x_6810_ = crate::leanh::lean_box(0);
                    if v_isShared_6805_ == 0 {
                        crate::leanh::lean_ctor_set(v___x_6804_, 0, v___x_6810_);
                        v___x_6812_ = v___x_6804_;
                        state = 2;
                        continue;
                    } else {
                        v_reuseFailAlloc_6813_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                        crate::leanh::lean_ctor_set(v_reuseFailAlloc_6813_, 0, v___x_6810_);
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
                    v_reuseFailAlloc_6821_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6821_, 0, v_a_6815_);
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
                    v_reuseFailAlloc_6829_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_6829_, 0, v_a_6823_);
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
    mut v_a_6831_: *mut crate::leanh::LeanObject,
    mut v_a_6832_: *mut crate::leanh::LeanObject,
    mut v_a_6833_: *mut crate::leanh::LeanObject,
    mut v_a_6834_: *mut crate::leanh::LeanObject,
    mut v_a_6835_: *mut crate::leanh::LeanObject,
    mut v_a_6836_: *mut crate::leanh::LeanObject,
    mut v_a_6837_: *mut crate::leanh::LeanObject,
    mut v_a_6838_: *mut crate::leanh::LeanObject,
    mut v_a_6839_: *mut crate::leanh::LeanObject,
    mut v_a_6840_: *mut crate::leanh::LeanObject,
    mut v_a_6841_: *mut crate::leanh::LeanObject,
    mut v_a_6842_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6843_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6843_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_6831_, v_a_6832_, v_a_6833_, v_a_6834_, v_a_6835_, v_a_6836_, v_a_6837_, v_a_6838_, v_a_6839_, v_a_6840_, v_a_6841_);
    crate::leanh::lean_dec(v_a_6841_);
    crate::leanh::lean_dec_ref(v_a_6840_);
    crate::leanh::lean_dec(v_a_6839_);
    crate::leanh::lean_dec_ref(v_a_6838_);
    crate::leanh::lean_dec(v_a_6837_);
    crate::leanh::lean_dec_ref(v_a_6836_);
    crate::leanh::lean_dec(v_a_6835_);
    crate::leanh::lean_dec_ref(v_a_6834_);
    crate::leanh::lean_dec(v_a_6833_);
    crate::leanh::lean_dec(v_a_6832_);
    crate::leanh::lean_dec(v_a_6831_);
    return v_res_6843_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(
    mut v_00_u03c3_6844_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6845_: *mut crate::leanh::LeanObject,
    mut v_map_6846_: *mut crate::leanh::LeanObject,
    mut v_init_6847_: *mut crate::leanh::LeanObject,
    mut v_f_6848_: *mut crate::leanh::LeanObject,
    mut v___y_6849_: *mut crate::leanh::LeanObject,
    mut v___y_6850_: *mut crate::leanh::LeanObject,
    mut v___y_6851_: *mut crate::leanh::LeanObject,
    mut v___y_6852_: *mut crate::leanh::LeanObject,
    mut v___y_6853_: *mut crate::leanh::LeanObject,
    mut v___y_6854_: *mut crate::leanh::LeanObject,
    mut v___y_6855_: *mut crate::leanh::LeanObject,
    mut v___y_6856_: *mut crate::leanh::LeanObject,
    mut v___y_6857_: *mut crate::leanh::LeanObject,
    mut v___y_6858_: *mut crate::leanh::LeanObject,
    mut v___y_6859_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6861_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6861_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___redArg(v_map_6846_, v_init_6847_, v_f_6848_, v___y_6849_, v___y_6850_, v___y_6851_, v___y_6852_, v___y_6853_, v___y_6854_, v___y_6855_, v___y_6856_, v___y_6857_, v___y_6858_, v___y_6859_);
    return v___x_6861_;
}
pub unsafe fn l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_6862_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b2_6863_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_map_6864_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_init_6865_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_6866_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v___y_6867_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_6868_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6869_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6870_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6871_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6872_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6873_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6874_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6875_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6876_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6877_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6878_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_6879_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6879_ = l_Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1(v_00_u03c3_6862_, v_00_u03b2_6863_, v_map_6864_, v_init_6865_, v_f_6866_, v___y_6867_, v___y_6868_, v___y_6869_, v___y_6870_, v___y_6871_, v___y_6872_, v___y_6873_, v___y_6874_, v___y_6875_, v___y_6876_, v___y_6877_);
    crate::leanh::lean_dec(v___y_6877_);
    crate::leanh::lean_dec_ref(v___y_6876_);
    crate::leanh::lean_dec(v___y_6875_);
    crate::leanh::lean_dec_ref(v___y_6874_);
    crate::leanh::lean_dec(v___y_6873_);
    crate::leanh::lean_dec_ref(v___y_6872_);
    crate::leanh::lean_dec(v___y_6871_);
    crate::leanh::lean_dec_ref(v___y_6870_);
    crate::leanh::lean_dec(v___y_6869_);
    crate::leanh::lean_dec(v___y_6868_);
    crate::leanh::lean_dec(v___y_6867_);
    crate::leanh::lean_dec_ref(v_map_6864_);
    return v_res_6879_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(
    mut v_map_6880_: *mut crate::leanh::LeanObject,
    mut v_f_6881_: *mut crate::leanh::LeanObject,
    mut v_init_6882_: *mut crate::leanh::LeanObject,
    mut v___y_6883_: *mut crate::leanh::LeanObject,
    mut v___y_6884_: *mut crate::leanh::LeanObject,
    mut v___y_6885_: *mut crate::leanh::LeanObject,
    mut v___y_6886_: *mut crate::leanh::LeanObject,
    mut v___y_6887_: *mut crate::leanh::LeanObject,
    mut v___y_6888_: *mut crate::leanh::LeanObject,
    mut v___y_6889_: *mut crate::leanh::LeanObject,
    mut v___y_6890_: *mut crate::leanh::LeanObject,
    mut v___y_6891_: *mut crate::leanh::LeanObject,
    mut v___y_6892_: *mut crate::leanh::LeanObject,
    mut v___y_6893_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6895_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6895_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6881_, v_map_6880_, v_init_6882_, v___y_6883_, v___y_6884_, v___y_6885_, v___y_6886_, v___y_6887_, v___y_6888_, v___y_6889_, v___y_6890_, v___y_6891_, v___y_6892_, v___y_6893_);
    return v___x_6895_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg___boxed(
    mut v_map_6896_: *mut crate::leanh::LeanObject,
    mut v_f_6897_: *mut crate::leanh::LeanObject,
    mut v_init_6898_: *mut crate::leanh::LeanObject,
    mut v___y_6899_: *mut crate::leanh::LeanObject,
    mut v___y_6900_: *mut crate::leanh::LeanObject,
    mut v___y_6901_: *mut crate::leanh::LeanObject,
    mut v___y_6902_: *mut crate::leanh::LeanObject,
    mut v___y_6903_: *mut crate::leanh::LeanObject,
    mut v___y_6904_: *mut crate::leanh::LeanObject,
    mut v___y_6905_: *mut crate::leanh::LeanObject,
    mut v___y_6906_: *mut crate::leanh::LeanObject,
    mut v___y_6907_: *mut crate::leanh::LeanObject,
    mut v___y_6908_: *mut crate::leanh::LeanObject,
    mut v___y_6909_: *mut crate::leanh::LeanObject,
    mut v___y_6910_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_6911_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6911_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___redArg(v_map_6896_, v_f_6897_, v_init_6898_, v___y_6899_, v___y_6900_, v___y_6901_, v___y_6902_, v___y_6903_, v___y_6904_, v___y_6905_, v___y_6906_, v___y_6907_, v___y_6908_, v___y_6909_);
    crate::leanh::lean_dec(v___y_6909_);
    crate::leanh::lean_dec_ref(v___y_6908_);
    crate::leanh::lean_dec(v___y_6907_);
    crate::leanh::lean_dec_ref(v___y_6906_);
    crate::leanh::lean_dec(v___y_6905_);
    crate::leanh::lean_dec_ref(v___y_6904_);
    crate::leanh::lean_dec(v___y_6903_);
    crate::leanh::lean_dec_ref(v___y_6902_);
    crate::leanh::lean_dec(v___y_6901_);
    crate::leanh::lean_dec(v___y_6900_);
    crate::leanh::lean_dec(v___y_6899_);
    return v_res_6911_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(
    mut v_00_u03c3_6912_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6913_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6914_: *mut crate::leanh::LeanObject,
    mut v_map_6915_: *mut crate::leanh::LeanObject,
    mut v_f_6916_: *mut crate::leanh::LeanObject,
    mut v_init_6917_: *mut crate::leanh::LeanObject,
    mut v___y_6918_: *mut crate::leanh::LeanObject,
    mut v___y_6919_: *mut crate::leanh::LeanObject,
    mut v___y_6920_: *mut crate::leanh::LeanObject,
    mut v___y_6921_: *mut crate::leanh::LeanObject,
    mut v___y_6922_: *mut crate::leanh::LeanObject,
    mut v___y_6923_: *mut crate::leanh::LeanObject,
    mut v___y_6924_: *mut crate::leanh::LeanObject,
    mut v___y_6925_: *mut crate::leanh::LeanObject,
    mut v___y_6926_: *mut crate::leanh::LeanObject,
    mut v___y_6927_: *mut crate::leanh::LeanObject,
    mut v___y_6928_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6930_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6930_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6916_, v_map_6915_, v_init_6917_, v___y_6918_, v___y_6919_, v___y_6920_, v___y_6921_, v___y_6922_, v___y_6923_, v___y_6924_, v___y_6925_, v___y_6926_, v___y_6927_, v___y_6928_);
    return v___x_6930_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_6931_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_6932_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b2_6933_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_map_6934_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_6935_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_init_6936_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_6937_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6938_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6939_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6940_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6941_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6942_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6943_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6944_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6945_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6946_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6947_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6948_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v_res_6949_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6949_ = l_Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1(v_00_u03c3_6931_, v_00_u03c3_6932_, v_00_u03b2_6933_, v_map_6934_, v_f_6935_, v_init_6936_, v___y_6937_, v___y_6938_, v___y_6939_, v___y_6940_, v___y_6941_, v___y_6942_, v___y_6943_, v___y_6944_, v___y_6945_, v___y_6946_, v___y_6947_);
    crate::leanh::lean_dec(v___y_6947_);
    crate::leanh::lean_dec_ref(v___y_6946_);
    crate::leanh::lean_dec(v___y_6945_);
    crate::leanh::lean_dec_ref(v___y_6944_);
    crate::leanh::lean_dec(v___y_6943_);
    crate::leanh::lean_dec_ref(v___y_6942_);
    crate::leanh::lean_dec(v___y_6941_);
    crate::leanh::lean_dec_ref(v___y_6940_);
    crate::leanh::lean_dec(v___y_6939_);
    crate::leanh::lean_dec(v___y_6938_);
    crate::leanh::lean_dec(v___y_6937_);
    return v_res_6949_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(
    mut v_00_u03c3_6950_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6951_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_6952_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6953_: *mut crate::leanh::LeanObject,
    mut v_f_6954_: *mut crate::leanh::LeanObject,
    mut v_x_6955_: *mut crate::leanh::LeanObject,
    mut v_x_6956_: *mut crate::leanh::LeanObject,
    mut v___y_6957_: *mut crate::leanh::LeanObject,
    mut v___y_6958_: *mut crate::leanh::LeanObject,
    mut v___y_6959_: *mut crate::leanh::LeanObject,
    mut v___y_6960_: *mut crate::leanh::LeanObject,
    mut v___y_6961_: *mut crate::leanh::LeanObject,
    mut v___y_6962_: *mut crate::leanh::LeanObject,
    mut v___y_6963_: *mut crate::leanh::LeanObject,
    mut v___y_6964_: *mut crate::leanh::LeanObject,
    mut v___y_6965_: *mut crate::leanh::LeanObject,
    mut v___y_6966_: *mut crate::leanh::LeanObject,
    mut v___y_6967_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_6969_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_6969_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___redArg(v_f_6954_, v_x_6955_, v_x_6956_, v___y_6957_, v___y_6958_, v___y_6959_, v___y_6960_, v___y_6961_, v___y_6962_, v___y_6963_, v___y_6964_, v___y_6965_, v___y_6966_, v___y_6967_);
    return v___x_6969_;
}
pub unsafe fn l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_6970_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_6971_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b1_6972_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b2_6973_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_6974_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_x_6975_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_x_6976_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_6977_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_6978_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_6979_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_6980_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_6981_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_6982_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_6983_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_6984_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_6985_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_6986_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_6987_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_6988_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v_res_6989_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_6989_ = l_Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2(v_00_u03c3_6970_, v_00_u03c3_6971_, v_00_u03b1_6972_, v_00_u03b2_6973_, v_f_6974_, v_x_6975_, v_x_6976_, v___y_6977_, v___y_6978_, v___y_6979_, v___y_6980_, v___y_6981_, v___y_6982_, v___y_6983_, v___y_6984_, v___y_6985_, v___y_6986_, v___y_6987_);
    crate::leanh::lean_dec(v___y_6987_);
    crate::leanh::lean_dec_ref(v___y_6986_);
    crate::leanh::lean_dec(v___y_6985_);
    crate::leanh::lean_dec_ref(v___y_6984_);
    crate::leanh::lean_dec(v___y_6983_);
    crate::leanh::lean_dec_ref(v___y_6982_);
    crate::leanh::lean_dec(v___y_6981_);
    crate::leanh::lean_dec_ref(v___y_6980_);
    crate::leanh::lean_dec(v___y_6979_);
    crate::leanh::lean_dec(v___y_6978_);
    crate::leanh::lean_dec(v___y_6977_);
    return v_res_6989_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(
    mut v_00_u03b1_6990_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_6991_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6992_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_6993_: *mut crate::leanh::LeanObject,
    mut v_f_6994_: *mut crate::leanh::LeanObject,
    mut v_as_6995_: *mut crate::leanh::LeanObject,
    mut v_i_6996_: usize,
    mut v_stop_6997_: usize,
    mut v_b_6998_: *mut crate::leanh::LeanObject,
    mut v___y_6999_: *mut crate::leanh::LeanObject,
    mut v___y_7000_: *mut crate::leanh::LeanObject,
    mut v___y_7001_: *mut crate::leanh::LeanObject,
    mut v___y_7002_: *mut crate::leanh::LeanObject,
    mut v___y_7003_: *mut crate::leanh::LeanObject,
    mut v___y_7004_: *mut crate::leanh::LeanObject,
    mut v___y_7005_: *mut crate::leanh::LeanObject,
    mut v___y_7006_: *mut crate::leanh::LeanObject,
    mut v___y_7007_: *mut crate::leanh::LeanObject,
    mut v___y_7008_: *mut crate::leanh::LeanObject,
    mut v___y_7009_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7011_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7011_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___redArg(v_f_6994_, v_as_6995_, v_i_6996_, v_stop_6997_, v_b_6998_, v___y_6999_, v___y_7000_, v___y_7001_, v___y_7002_, v___y_7003_, v___y_7004_, v___y_7005_, v___y_7006_, v___y_7007_, v___y_7008_, v___y_7009_);
    return v___x_7011_;
}
pub unsafe fn l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03b1_7012_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03b2_7013_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03c3_7014_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03c3_7015_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_7016_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_as_7017_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_i_7018_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_stop_7019_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_b_7020_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_7021_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_7022_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_7023_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_7024_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_7025_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_7026_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_7027_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_7028_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_7029_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_7030_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_7031_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_7032_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v_i_boxed_7033_: usize = 0;
    let mut v_stop_boxed_7034_: usize = 0;
    let mut v_res_7035_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_i_boxed_7033_ = crate::leanh::lean_unbox_usize(v_i_7018_);
    crate::leanh::lean_dec(v_i_7018_);
    v_stop_boxed_7034_ = crate::leanh::lean_unbox_usize(v_stop_7019_);
    crate::leanh::lean_dec(v_stop_7019_);
    v_res_7035_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__3(v_00_u03b1_7012_, v_00_u03b2_7013_, v_00_u03c3_7014_, v_00_u03c3_7015_, v_f_7016_, v_as_7017_, v_i_boxed_7033_, v_stop_boxed_7034_, v_b_7020_, v___y_7021_, v___y_7022_, v___y_7023_, v___y_7024_, v___y_7025_, v___y_7026_, v___y_7027_, v___y_7028_, v___y_7029_, v___y_7030_, v___y_7031_);
    crate::leanh::lean_dec(v___y_7031_);
    crate::leanh::lean_dec_ref(v___y_7030_);
    crate::leanh::lean_dec(v___y_7029_);
    crate::leanh::lean_dec_ref(v___y_7028_);
    crate::leanh::lean_dec(v___y_7027_);
    crate::leanh::lean_dec_ref(v___y_7026_);
    crate::leanh::lean_dec(v___y_7025_);
    crate::leanh::lean_dec_ref(v___y_7024_);
    crate::leanh::lean_dec(v___y_7023_);
    crate::leanh::lean_dec(v___y_7022_);
    crate::leanh::lean_dec(v___y_7021_);
    crate::leanh::lean_dec_ref(v_as_7017_);
    return v_res_7035_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(
    mut v_00_u03c3_7036_: *mut crate::leanh::LeanObject,
    mut v_00_u03c3_7037_: *mut crate::leanh::LeanObject,
    mut v_00_u03b1_7038_: *mut crate::leanh::LeanObject,
    mut v_00_u03b2_7039_: *mut crate::leanh::LeanObject,
    mut v_f_7040_: *mut crate::leanh::LeanObject,
    mut v_keys_7041_: *mut crate::leanh::LeanObject,
    mut v_vals_7042_: *mut crate::leanh::LeanObject,
    mut v_heq_7043_: *mut crate::leanh::LeanObject,
    mut v_i_7044_: *mut crate::leanh::LeanObject,
    mut v_acc_7045_: *mut crate::leanh::LeanObject,
    mut v___y_7046_: *mut crate::leanh::LeanObject,
    mut v___y_7047_: *mut crate::leanh::LeanObject,
    mut v___y_7048_: *mut crate::leanh::LeanObject,
    mut v___y_7049_: *mut crate::leanh::LeanObject,
    mut v___y_7050_: *mut crate::leanh::LeanObject,
    mut v___y_7051_: *mut crate::leanh::LeanObject,
    mut v___y_7052_: *mut crate::leanh::LeanObject,
    mut v___y_7053_: *mut crate::leanh::LeanObject,
    mut v___y_7054_: *mut crate::leanh::LeanObject,
    mut v___y_7055_: *mut crate::leanh::LeanObject,
    mut v___y_7056_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7058_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7058_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___redArg(v_f_7040_, v_keys_7041_, v_vals_7042_, v_i_7044_, v_acc_7045_, v___y_7046_, v___y_7047_, v___y_7048_, v___y_7049_, v___y_7050_, v___y_7051_, v___y_7052_, v___y_7053_, v___y_7054_, v___y_7055_, v___y_7056_);
    return v___x_7058_;
}
pub unsafe fn l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_00_u03c3_7059_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_00_u03c3_7060_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_00_u03b1_7061_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_00_u03b2_7062_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_f_7063_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_keys_7064_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v_vals_7065_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v_heq_7066_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v_i_7067_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v_acc_7068_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_7069_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_7070_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_7071_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_7072_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_7073_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_7074_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_7075_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v___y_7076_: *mut crate::leanh::LeanObject = *_args.add(17);
    let mut v___y_7077_: *mut crate::leanh::LeanObject = *_args.add(18);
    let mut v___y_7078_: *mut crate::leanh::LeanObject = *_args.add(19);
    let mut v___y_7079_: *mut crate::leanh::LeanObject = *_args.add(20);
    let mut v___y_7080_: *mut crate::leanh::LeanObject = *_args.add(21);
    let mut v_res_7081_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7081_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_foldlMAux_traverse___at___00Lean_PersistentHashMap_foldlMAux___at___00Lean_PersistentHashMap_foldlM___at___00Lean_PersistentHashMap_forIn___at___00__private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars_spec__1_spec__1_spec__2_spec__4(v_00_u03c3_7059_, v_00_u03c3_7060_, v_00_u03b1_7061_, v_00_u03b2_7062_, v_f_7063_, v_keys_7064_, v_vals_7065_, v_heq_7066_, v_i_7067_, v_acc_7068_, v___y_7069_, v___y_7070_, v___y_7071_, v___y_7072_, v___y_7073_, v___y_7074_, v___y_7075_, v___y_7076_, v___y_7077_, v___y_7078_, v___y_7079_);
    crate::leanh::lean_dec(v___y_7079_);
    crate::leanh::lean_dec_ref(v___y_7078_);
    crate::leanh::lean_dec(v___y_7077_);
    crate::leanh::lean_dec_ref(v___y_7076_);
    crate::leanh::lean_dec(v___y_7075_);
    crate::leanh::lean_dec_ref(v___y_7074_);
    crate::leanh::lean_dec(v___y_7073_);
    crate::leanh::lean_dec_ref(v___y_7072_);
    crate::leanh::lean_dec(v___y_7071_);
    crate::leanh::lean_dec(v___y_7070_);
    crate::leanh::lean_dec(v___y_7069_);
    crate::leanh::lean_dec_ref(v_vals_7065_);
    crate::leanh::lean_dec_ref(v_keys_7064_);
    return v_res_7081_;
}
pub unsafe fn l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(
    mut v_a_7082_: *mut crate::leanh::LeanObject,
    mut v_a_7083_: *mut crate::leanh::LeanObject,
    mut v_a_7084_: *mut crate::leanh::LeanObject,
    mut v_a_7085_: *mut crate::leanh::LeanObject,
    mut v_a_7086_: *mut crate::leanh::LeanObject,
    mut v_a_7087_: *mut crate::leanh::LeanObject,
    mut v_a_7088_: *mut crate::leanh::LeanObject,
    mut v_a_7089_: *mut crate::leanh::LeanObject,
    mut v_a_7090_: *mut crate::leanh::LeanObject,
    mut v_a_7091_: *mut crate::leanh::LeanObject,
    mut v_a_7092_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7094_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7094_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkVars(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
    if crate::leanh::lean_obj_tag(v___x_7094_) == 0 {
        let mut v___x_7095_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
        crate::leanh::lean_dec_ref_known(v___x_7094_, 1);
        v___x_7095_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkLowers(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
        if crate::leanh::lean_obj_tag(v___x_7095_) == 0 {
            let mut v___x_7096_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
            crate::leanh::lean_dec_ref_known(v___x_7095_, 1);
            v___x_7096_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkUppers(v_a_7082_, v_a_7083_, v_a_7084_, v_a_7085_, v_a_7086_, v_a_7087_, v_a_7088_, v_a_7089_, v_a_7090_, v_a_7091_, v_a_7092_);
            if crate::leanh::lean_obj_tag(v___x_7096_) == 0 {
                let mut v___x_7097_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
                crate::leanh::lean_dec_ref_known(v___x_7096_, 1);
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
    mut v_a_7098_: *mut crate::leanh::LeanObject,
    mut v_a_7099_: *mut crate::leanh::LeanObject,
    mut v_a_7100_: *mut crate::leanh::LeanObject,
    mut v_a_7101_: *mut crate::leanh::LeanObject,
    mut v_a_7102_: *mut crate::leanh::LeanObject,
    mut v_a_7103_: *mut crate::leanh::LeanObject,
    mut v_a_7104_: *mut crate::leanh::LeanObject,
    mut v_a_7105_: *mut crate::leanh::LeanObject,
    mut v_a_7106_: *mut crate::leanh::LeanObject,
    mut v_a_7107_: *mut crate::leanh::LeanObject,
    mut v_a_7108_: *mut crate::leanh::LeanObject,
    mut v_a_7109_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7110_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7110_ = l___private_Lean_Meta_Tactic_Grind_Arith_Linear_Inv_0__Lean_Meta_Grind_Arith_Linear_checkStructInvs(v_a_7098_, v_a_7099_, v_a_7100_, v_a_7101_, v_a_7102_, v_a_7103_, v_a_7104_, v_a_7105_, v_a_7106_, v_a_7107_, v_a_7108_);
    crate::leanh::lean_dec(v_a_7108_);
    crate::leanh::lean_dec_ref(v_a_7107_);
    crate::leanh::lean_dec(v_a_7106_);
    crate::leanh::lean_dec_ref(v_a_7105_);
    crate::leanh::lean_dec(v_a_7104_);
    crate::leanh::lean_dec_ref(v_a_7103_);
    crate::leanh::lean_dec(v_a_7102_);
    crate::leanh::lean_dec_ref(v_a_7101_);
    crate::leanh::lean_dec(v_a_7100_);
    crate::leanh::lean_dec(v_a_7099_);
    crate::leanh::lean_dec(v_a_7098_);
    return v_res_7110_;
}
pub unsafe fn _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2()
-> *mut crate::leanh::LeanObject {
    let mut v___x_7113_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7114_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7115_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7116_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7117_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7118_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7113_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__1;
    v___x_7114_ = crate::leanh::lean_unsigned_to_nat(6);
    v___x_7115_ = crate::leanh::lean_unsigned_to_nat(103);
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
    mut v_upperBound_7119_: *mut crate::leanh::LeanObject,
    mut v_a_7120_: *mut crate::leanh::LeanObject,
    mut v_b_7121_: *mut crate::leanh::LeanObject,
    mut v___y_7122_: *mut crate::leanh::LeanObject,
    mut v___y_7123_: *mut crate::leanh::LeanObject,
    mut v___y_7124_: *mut crate::leanh::LeanObject,
    mut v___y_7125_: *mut crate::leanh::LeanObject,
    mut v___y_7126_: *mut crate::leanh::LeanObject,
    mut v___y_7127_: *mut crate::leanh::LeanObject,
    mut v___y_7128_: *mut crate::leanh::LeanObject,
    mut v___y_7129_: *mut crate::leanh::LeanObject,
    mut v___y_7130_: *mut crate::leanh::LeanObject,
    mut v___y_7131_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7133_: u8 = 0;
    let mut v___x_7134_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7135_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___y_7137_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7138_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7139_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7141_: u8 = 0;
    let mut v___x_7142_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7143_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7144_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut state = 0;
    loop {
        match state {
            0 => {
                v___x_7133_ = lean_nat_dec_lt(v_a_7120_, v_upperBound_7119_);
                if v___x_7133_ == 0 {
                    crate::leanh::lean_dec(v_a_7120_);
                    v___x_7134_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7134_, 0, v_b_7121_);
                    return v___x_7134_;
                } else {
                    v___x_7135_ = crate::leanh::lean_box(0);
                    v___x_7141_ = lean_nat_dec_eq(v_a_7120_, v_a_7120_);
                    if v___x_7141_ == 0 {
                        v___x_7142_ = crate::leanh::lean_obj_once(core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2), core::ptr::addr_of_mut!(l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2_once), _init_l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___closed__2);
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
                if crate::leanh::lean_obj_tag(v___y_7137_) == 0 {
                    crate::leanh::lean_dec_ref_known(v___y_7137_, 1);
                    v___x_7138_ = crate::leanh::lean_unsigned_to_nat(1);
                    v___x_7139_ = lean_nat_add(v_a_7120_, v___x_7138_);
                    crate::leanh::lean_dec(v_a_7120_);
                    v_a_7120_ = v___x_7139_;
                    v_b_7121_ = v___x_7135_;
                    state = 0;
                    continue;
                } else {
                    crate::leanh::lean_dec(v_a_7120_);
                    return v___y_7137_;
                }
            }
            _ => {}
        }
    }
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg___boxed(
    mut v_upperBound_7145_: *mut crate::leanh::LeanObject,
    mut v_a_7146_: *mut crate::leanh::LeanObject,
    mut v_b_7147_: *mut crate::leanh::LeanObject,
    mut v___y_7148_: *mut crate::leanh::LeanObject,
    mut v___y_7149_: *mut crate::leanh::LeanObject,
    mut v___y_7150_: *mut crate::leanh::LeanObject,
    mut v___y_7151_: *mut crate::leanh::LeanObject,
    mut v___y_7152_: *mut crate::leanh::LeanObject,
    mut v___y_7153_: *mut crate::leanh::LeanObject,
    mut v___y_7154_: *mut crate::leanh::LeanObject,
    mut v___y_7155_: *mut crate::leanh::LeanObject,
    mut v___y_7156_: *mut crate::leanh::LeanObject,
    mut v___y_7157_: *mut crate::leanh::LeanObject,
    mut v___y_7158_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7159_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7159_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_7145_, v_a_7146_, v_b_7147_, v___y_7148_, v___y_7149_, v___y_7150_, v___y_7151_, v___y_7152_, v___y_7153_, v___y_7154_, v___y_7155_, v___y_7156_, v___y_7157_);
    crate::leanh::lean_dec(v___y_7157_);
    crate::leanh::lean_dec_ref(v___y_7156_);
    crate::leanh::lean_dec(v___y_7155_);
    crate::leanh::lean_dec_ref(v___y_7154_);
    crate::leanh::lean_dec(v___y_7153_);
    crate::leanh::lean_dec_ref(v___y_7152_);
    crate::leanh::lean_dec(v___y_7151_);
    crate::leanh::lean_dec_ref(v___y_7150_);
    crate::leanh::lean_dec(v___y_7149_);
    crate::leanh::lean_dec(v___y_7148_);
    crate::leanh::lean_dec(v_upperBound_7145_);
    return v_res_7159_;
}
pub unsafe fn l_Lean_Meta_Grind_Arith_Linear_checkInvariants(
    mut v_a_7160_: *mut crate::leanh::LeanObject,
    mut v_a_7161_: *mut crate::leanh::LeanObject,
    mut v_a_7162_: *mut crate::leanh::LeanObject,
    mut v_a_7163_: *mut crate::leanh::LeanObject,
    mut v_a_7164_: *mut crate::leanh::LeanObject,
    mut v_a_7165_: *mut crate::leanh::LeanObject,
    mut v_a_7166_: *mut crate::leanh::LeanObject,
    mut v_a_7167_: *mut crate::leanh::LeanObject,
    mut v_a_7168_: *mut crate::leanh::LeanObject,
    mut v_a_7169_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_debug_7171_: u8 = 0;
    let mut v___x_7172_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7173_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7174_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7175_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_structs_7176_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7177_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7178_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7179_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7180_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7182_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7183_: u8 = 0;
    let mut v___x_7185_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7186_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7187_: u8 = 0;
    let mut v_unused_7188_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_a_7189_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v___x_7191_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isShared_7192_: u8 = 0;
    let mut v___x_7194_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_reuseFailAlloc_7195_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    let mut v_isSharedCheck_7196_: u8 = 0;
    let mut state = 0;
    loop {
        match state {
            0 => {
                v_debug_7171_ = crate::leanh::lean_ctor_get_uint8(
                    v_a_7162_,
                    (core::mem::size_of::<*mut crate::leanh::LeanObject>() * 8 + 2) as u32,
                );
                if v_debug_7171_ == 0 {
                    v___x_7172_ = crate::leanh::lean_box(0);
                    v___x_7173_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v___x_7173_, 0, v___x_7172_);
                    return v___x_7173_;
                } else {
                    v___x_7174_ =
                        l_Lean_Meta_Grind_Arith_Linear_get_x27___redArg(v_a_7160_, v_a_7168_);
                    if crate::leanh::lean_obj_tag(v___x_7174_) == 0 {
                        v_a_7175_ = crate::leanh::lean_ctor_get(v___x_7174_, 0);
                        crate::leanh::lean_inc(v_a_7175_);
                        crate::leanh::lean_dec_ref_known(v___x_7174_, 1);
                        v_structs_7176_ = crate::leanh::lean_ctor_get(v_a_7175_, 0);
                        crate::leanh::lean_inc_ref(v_structs_7176_);
                        crate::leanh::lean_dec(v_a_7175_);
                        v___x_7177_ = lean_array_get_size(v_structs_7176_);
                        crate::leanh::lean_dec_ref(v_structs_7176_);
                        v___x_7178_ = crate::leanh::lean_unsigned_to_nat(0);
                        v___x_7179_ = crate::leanh::lean_box(0);
                        v___x_7180_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v___x_7177_, v___x_7178_, v___x_7179_, v_a_7160_, v_a_7161_, v_a_7162_, v_a_7163_, v_a_7164_, v_a_7165_, v_a_7166_, v_a_7167_, v_a_7168_, v_a_7169_);
                        if crate::leanh::lean_obj_tag(v___x_7180_) == 0 {
                            v_isSharedCheck_7187_ =
                                (!crate::leanh::lean_is_exclusive(v___x_7180_)) as u8;
                            if v_isSharedCheck_7187_ == 0 {
                                v_unused_7188_ = crate::leanh::lean_ctor_get(v___x_7180_, 0);
                                crate::leanh::lean_dec(v_unused_7188_);
                                v___x_7182_ = v___x_7180_;
                                v_isShared_7183_ = v_isSharedCheck_7187_;
                                state = 1;
                                continue;
                            } else {
                                crate::leanh::lean_dec(v___x_7180_);
                                v___x_7182_ = crate::leanh::lean_box(0);
                                v_isShared_7183_ = v_isSharedCheck_7187_;
                                state = 1;
                                continue;
                            }
                        } else {
                            return v___x_7180_;
                        }
                    } else {
                        v_a_7189_ = crate::leanh::lean_ctor_get(v___x_7174_, 0);
                        v_isSharedCheck_7196_ =
                            (!crate::leanh::lean_is_exclusive(v___x_7174_)) as u8;
                        if v_isSharedCheck_7196_ == 0 {
                            v___x_7191_ = v___x_7174_;
                            v_isShared_7192_ = v_isSharedCheck_7196_;
                            state = 3;
                            continue;
                        } else {
                            crate::leanh::lean_inc(v_a_7189_);
                            crate::leanh::lean_dec(v___x_7174_);
                            v___x_7191_ = crate::leanh::lean_box(0);
                            v_isShared_7192_ = v_isSharedCheck_7196_;
                            state = 3;
                            continue;
                        }
                    }
                }
            }
            1 => {
                if v_isShared_7183_ == 0 {
                    crate::leanh::lean_ctor_set(v___x_7182_, 0, v___x_7179_);
                    v___x_7185_ = v___x_7182_;
                    state = 2;
                    continue;
                } else {
                    v_reuseFailAlloc_7186_ = crate::leanh::lean_alloc_ctor(0, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7186_, 0, v___x_7179_);
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
                    v_reuseFailAlloc_7195_ = crate::leanh::lean_alloc_ctor(1, 1, (0) as u32);
                    crate::leanh::lean_ctor_set(v_reuseFailAlloc_7195_, 0, v_a_7189_);
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
    mut v_a_7197_: *mut crate::leanh::LeanObject,
    mut v_a_7198_: *mut crate::leanh::LeanObject,
    mut v_a_7199_: *mut crate::leanh::LeanObject,
    mut v_a_7200_: *mut crate::leanh::LeanObject,
    mut v_a_7201_: *mut crate::leanh::LeanObject,
    mut v_a_7202_: *mut crate::leanh::LeanObject,
    mut v_a_7203_: *mut crate::leanh::LeanObject,
    mut v_a_7204_: *mut crate::leanh::LeanObject,
    mut v_a_7205_: *mut crate::leanh::LeanObject,
    mut v_a_7206_: *mut crate::leanh::LeanObject,
    mut v_a_7207_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_res_7208_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v_res_7208_ = l_Lean_Meta_Grind_Arith_Linear_checkInvariants(
        v_a_7197_, v_a_7198_, v_a_7199_, v_a_7200_, v_a_7201_, v_a_7202_, v_a_7203_, v_a_7204_,
        v_a_7205_, v_a_7206_,
    );
    crate::leanh::lean_dec(v_a_7206_);
    crate::leanh::lean_dec_ref(v_a_7205_);
    crate::leanh::lean_dec(v_a_7204_);
    crate::leanh::lean_dec_ref(v_a_7203_);
    crate::leanh::lean_dec(v_a_7202_);
    crate::leanh::lean_dec_ref(v_a_7201_);
    crate::leanh::lean_dec(v_a_7200_);
    crate::leanh::lean_dec_ref(v_a_7199_);
    crate::leanh::lean_dec(v_a_7198_);
    crate::leanh::lean_dec(v_a_7197_);
    return v_res_7208_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0(
    mut v_upperBound_7209_: *mut crate::leanh::LeanObject,
    mut v_inst_7210_: *mut crate::leanh::LeanObject,
    mut v_R_7211_: *mut crate::leanh::LeanObject,
    mut v_a_7212_: *mut crate::leanh::LeanObject,
    mut v_b_7213_: *mut crate::leanh::LeanObject,
    mut v_c_7214_: *mut crate::leanh::LeanObject,
    mut v___y_7215_: *mut crate::leanh::LeanObject,
    mut v___y_7216_: *mut crate::leanh::LeanObject,
    mut v___y_7217_: *mut crate::leanh::LeanObject,
    mut v___y_7218_: *mut crate::leanh::LeanObject,
    mut v___y_7219_: *mut crate::leanh::LeanObject,
    mut v___y_7220_: *mut crate::leanh::LeanObject,
    mut v___y_7221_: *mut crate::leanh::LeanObject,
    mut v___y_7222_: *mut crate::leanh::LeanObject,
    mut v___y_7223_: *mut crate::leanh::LeanObject,
    mut v___y_7224_: *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v___x_7226_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
    v___x_7226_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___redArg(v_upperBound_7209_, v_a_7212_, v_b_7213_, v___y_7215_, v___y_7216_, v___y_7217_, v___y_7218_, v___y_7219_, v___y_7220_, v___y_7221_, v___y_7222_, v___y_7223_, v___y_7224_);
    return v___x_7226_;
}
pub unsafe fn l_WellFounded_opaqueFix_u2083___at___00Lean_Meta_Grind_Arith_Linear_checkInvariants_spec__0___boxed(
    _args: *mut *mut crate::leanh::LeanObject,
) -> *mut crate::leanh::LeanObject {
    let mut v_upperBound_7227_: *mut crate::leanh::LeanObject = *_args.add(0);
    let mut v_inst_7228_: *mut crate::leanh::LeanObject = *_args.add(1);
    let mut v_R_7229_: *mut crate::leanh::LeanObject = *_args.add(2);
    let mut v_a_7230_: *mut crate::leanh::LeanObject = *_args.add(3);
    let mut v_b_7231_: *mut crate::leanh::LeanObject = *_args.add(4);
    let mut v_c_7232_: *mut crate::leanh::LeanObject = *_args.add(5);
    let mut v___y_7233_: *mut crate::leanh::LeanObject = *_args.add(6);
    let mut v___y_7234_: *mut crate::leanh::LeanObject = *_args.add(7);
    let mut v___y_7235_: *mut crate::leanh::LeanObject = *_args.add(8);
    let mut v___y_7236_: *mut crate::leanh::LeanObject = *_args.add(9);
    let mut v___y_7237_: *mut crate::leanh::LeanObject = *_args.add(10);
    let mut v___y_7238_: *mut crate::leanh::LeanObject = *_args.add(11);
    let mut v___y_7239_: *mut crate::leanh::LeanObject = *_args.add(12);
    let mut v___y_7240_: *mut crate::leanh::LeanObject = *_args.add(13);
    let mut v___y_7241_: *mut crate::leanh::LeanObject = *_args.add(14);
    let mut v___y_7242_: *mut crate::leanh::LeanObject = *_args.add(15);
    let mut v___y_7243_: *mut crate::leanh::LeanObject = *_args.add(16);
    let mut v_res_7244_: *mut crate::leanh::LeanObject = core::ptr::null_mut();
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
    crate::leanh::lean_dec(v___y_7242_);
    crate::leanh::lean_dec_ref(v___y_7241_);
    crate::leanh::lean_dec(v___y_7240_);
    crate::leanh::lean_dec_ref(v___y_7239_);
    crate::leanh::lean_dec(v___y_7238_);
    crate::leanh::lean_dec_ref(v___y_7237_);
    crate::leanh::lean_dec(v___y_7236_);
    crate::leanh::lean_dec_ref(v___y_7235_);
    crate::leanh::lean_dec(v___y_7234_);
    crate::leanh::lean_dec(v___y_7233_);
    crate::leanh::lean_dec(v_upperBound_7227_);
    return v_res_7244_;
}
static mut _G_runtime_initialized: bool = false;
pub unsafe fn runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
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
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return crate::leanh::lean_io_result_mk_ok(crate::leanh::lean_box(0));
}
static mut _G_meta_initialized: bool = false;
pub unsafe fn meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
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
pub unsafe fn initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(
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
    res = initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Util(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
    if crate::leanh::lean_io_result_is_error(res) {
        return res;
    }
    crate::leanh::lean_dec_ref(res);
    return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_Inv(builtin);
}
